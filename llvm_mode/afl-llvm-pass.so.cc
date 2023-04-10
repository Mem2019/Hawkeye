/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <fstream>

#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/dijkstra_shortest_paths.hpp>
namespace bo = boost;

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/CommandLine.h"

#if defined(LLVM34)
#include "llvm/DebugInfo.h"
#else
#include "llvm/IR/DebugInfo.h"
#endif

#if defined(LLVM34) || defined(LLVM35) || defined(LLVM36)
#define LLVM_OLD_DEBUG_API
#endif

using namespace llvm;

cl::opt<std::string> TargetsFile(
    "targets",
    cl::desc("Input file containing the target lines of code."),
    cl::value_desc("targets"));

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}


char AFLCoverage::ID = 0;

namespace {

using Weight = double;
using Property = bo::property<bo::edge_weight_t, Weight>;
using Graph = bo::adjacency_list<
  bo::vecS, bo::vecS, bo::directedS, bo::no_property,
  Property>;
using Vertex = bo::graph_traits<Graph>::vertex_descriptor;
using Edge = std::pair<Vertex, Vertex>;

bool isBlacklisted(const Function *F) {

  static const SmallVector<std::string, 8> Blacklist = {
    "asan.",
    "__asan",
    "llvm.",
    "sancov.",
    "__ubsan_handle_",
    "free",
    "malloc",
    "calloc",
    "realloc"
  };

  for (auto const &BlacklistFunc : Blacklist) {
    if (F->getName().startswith(BlacklistFunc)) {
      return true;
    }
  }

  return false;
}

void getDebugLoc(const Instruction *I, std::string &Filename,
                        unsigned &Line) {
#ifdef LLVM_OLD_DEBUG_API
  DebugLoc Loc = I->getDebugLoc();
  if (!Loc.isUnknown()) {
    DILocation cDILoc(Loc.getAsMDNode(M.getContext()));
    DILocation oDILoc = cDILoc.getOrigLocation();

    Line = oDILoc.getLineNumber();
    Filename = oDILoc.getFilename().str();

    if (filename.empty()) {
      Line = cDILoc.getLineNumber();
      Filename = cDILoc.getFilename().str();
    }
  }
#else
  if (DILocation *Loc = I->getDebugLoc()) {
    Line = Loc->getLine();
    Filename = Loc->getFilename().str();

    if (Filename.empty()) {
      DILocation *oDILoc = Loc->getInlinedAt();
      if (oDILoc) {
        Line = oDILoc->getLine();
        Filename = oDILoc->getFilename().str();
      }
    }
  }
#endif /* LLVM_OLD_DEBUG_API */
}

/*
Given function f, we get all outgoing edges with weight according to its CFG.
We should note same callee function can appear in different call sites.
*/
std::unordered_map<Function*, Weight> getOutEdges(Function& F) {

  using namespace std;

  // TODO: call edges of Hawkeye

  return {};
}

/* Obtain Call graph with weight, which is obtained using getOutEdges. */
std::tuple<Graph, std::vector<Function*>, std::unordered_map<Function*, Vertex>>
  getCallGraph(Module& M) {

  using namespace std;
  vector<Function*> functions;
  unordered_map<Function*, Vertex> func_to_id;
  for (auto& F : M) {

    if (isBlacklisted(&F) || F.begin() == F.end())
      continue;

    func_to_id.emplace(&F, functions.size());
    functions.push_back(&F);

  }

  vector<Edge> edges; vector<Weight> weights;
  for (const auto& func_id : func_to_id) {

    auto out_edges = getOutEdges(*func_id.first);
    for (const auto& edge : out_edges) {

      // Inverse the edge.
      edges.emplace_back(func_to_id.find(edge.first)->second, func_id.second);
      weights.push_back(edge.second);

    }

  }

  return make_tuple<Graph, vector<Function*>, unordered_map<Function*, Vertex>>(
    Graph(edges.begin(), edges.end(), weights.begin(), functions.size()),
    std::move(functions), std::move(func_to_id));

}

std::unordered_set<std::string> parseTargets(void) {
  using namespace std;
  unordered_set<string> targets;
  if (TargetsFile.empty())
    return targets;
  ifstream targetsfile(TargetsFile); assert(targetsfile.is_open());
  string line;
  while (getline(targetsfile, line)) {
    size_t found = line.find_last_of("/\\");
    if (found != string::npos)
      line = line.substr(found + 1);
    targets.insert(line);
  }
  targetsfile.close();
  return targets;
}

/*
We identify and record each target Block, and Function that contains them.
We also decide the order of targets in this function.
*/
std::vector<std::pair<BasicBlock*, Function*>> getTargetBlocks(Module& M) {

  using namespace std;

  vector<pair<BasicBlock*, Function*>> ret;
  auto targets = parseTargets();
  for (auto& F : M) {

    if (isBlacklisted(&F))
      continue;

    for (auto& BB : F) {

      for (auto& I : BB) {

        string filename; unsigned line = 0;
        getDebugLoc(&I, filename, line);
        static const string Xlibs("/usr/");
        if (filename.empty() || line == 0 ||
          !filename.compare(0, Xlibs.size(), Xlibs))
          continue;

        size_t found = filename.find_last_of("/\\");
        if (found != string::npos)
          filename = filename.substr(found + 1);

        // If instructin debug info is target, we mark the BasicBlock as target.
        if (targets.count(filename + ':' + to_string(line)) > 0) {
          ret.emplace_back(&BB, &F);
          break; // We only append each BasicBlock once.
        }

      }

    }

  }

  return ret;
}

// TODO: getDists()

}

bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M)
    for (auto &BB : F) {

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;

    }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPassLTO(
    PassManagerBuilder::EP_FullLinkTimeOptimizationLast, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
