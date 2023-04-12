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
#include <memory>
#include <numeric>

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

  // Fst: Map each callee to call-site occurence count.
  // Snd: Map each callee to all basic blocks that contain its call site.
  unordered_map<Function*, pair<size_t, unordered_set<BasicBlock*>>> c_n_c_b;

  for (auto& BB : F) {

    for (auto& I : BB) {

      if (auto *c = dyn_cast<CallInst>(&I)) {

        if (Function *CalledF = c->getCalledFunction()) {

          if (!isBlacklisted(CalledF) && CalledF->begin() != CalledF->end()) {

            auto it = c_n_c_b.emplace(CalledF,
              make_pair<size_t, unordered_set<BasicBlock*>>(
                0, unordered_set<BasicBlock*>())).first;
            ++it->second.first;
            it->second.second.insert(&BB);

          }

        }

      }

    }

  }

  unordered_map<Function*, Weight> ret;
  for (const auto& callee : c_n_c_b) {

    double phi_cn = 2.0 * callee.second.first;
    phi_cn = (phi_cn + 1) / phi_cn;
    double psi_cb = 2.0 * callee.second.second.size();
    psi_cb = (psi_cb + 1) / psi_cb;
    ret.emplace(callee.first, phi_cn * psi_cb);

  }

  return ret;
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
*/
std::pair<std::unordered_set<BasicBlock*>, std::unordered_set<Function*>>
  getTargets(Module& M) {

  using namespace std;

  unordered_set<BasicBlock*> target_blocks;
  unordered_set<Function*> target_funcs;
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
          target_blocks.insert(&BB);
          target_funcs.insert(&F);
          break; // We only append each BasicBlock once.
        }

      }

    }

  }

  return make_pair<>(std::move(target_blocks), std::move(target_funcs));
}

/*
Given a function F and call graph distance value for each function,
we obtain all TransB in F associated with minimum d_f of each callee.
*/
std::unordered_map<BasicBlock*, double> getTransBlockDist(
  Function& F, const std::unordered_map<Function*, double>& d_f,
  const std::unordered_set<BasicBlock*>& target_blocks) {

  std::unordered_map<BasicBlock*, double> ret;

  for (auto& BB : F) {

    // For target blocks, we regard it as trans block with distance 0,
    // which is identical to implementation of AFLGo.
    if (target_blocks.count(&BB) > 0) {
      ret.emplace(&BB, 0);
      continue;
    }

    double min_dist = std::numeric_limits<double>::infinity();

    for (auto& I : BB) {
      if (auto *c = dyn_cast<CallInst>(&I)) {
        if (Function *CalledF = c->getCalledFunction()) {
          if (!isBlacklisted(CalledF) && CalledF->begin() != CalledF->end()) {

            auto it = d_f.find(CalledF);
            if (it != d_f.end())
              min_dist = std::min(min_dist, it->second);

          }
        }
      }
    }

    if (!std::isinf(min_dist))
      ret.emplace(&BB, min_dist);

  }

  return ret;
}

std::tuple<Graph,
  std::vector<BasicBlock*>,
  std::unordered_map<BasicBlock*, Vertex>>
  getControlFlowGraph(Function& F) {

  using namespace std;

  vector<BasicBlock*> blocks;
  unordered_map<BasicBlock*, Vertex> block_to_id;

  for (auto& BB : F) {

    block_to_id.emplace(&BB, blocks.size());
    blocks.push_back(&BB);

  }

  vector<Edge> edges; vector<Weight> weights;
  for (const auto& block_id : block_to_id) {

    Instruction* Term = block_id.first->getTerminator();
    unsigned n = Term->getNumSuccessors();
    for (unsigned i = 0; i < n; ++i) {
      Vertex v = block_to_id.find(Term->getSuccessor(i))->second;
      edges.emplace_back(v, block_id.second); // Inverse edge
      weights.push_back(1);
    }

  }

  return make_tuple(
    Graph(edges.begin(), edges.end(), weights.begin(), blocks.size()),
    std::move(blocks), std::move(block_to_id));

}


std::tuple<std::unordered_map<BasicBlock*, double>, std::vector<Function*>, size_t>
  calcDists(Module& M,
  const std::unordered_set<BasicBlock*>& target_blocks,
  const std::unordered_set<Function*>& target_funcs) {

  constexpr double kMagnifier = 10;

  Graph cg;
  std::vector<Function*> functions;
  std::unordered_map<Function*, Vertex> func_to_id;
  std::tie(cg, functions, func_to_id) = getCallGraph(M);

  size_t num_functions = functions.size();
  std::unique_ptr<Weight[]> d = std::make_unique<Weight[]>(num_functions);
  std::unique_ptr<Vertex[]> p = std::make_unique<Vertex[]>(num_functions);

  // Map each function to distances from it to each target.
  std::unordered_map<Function*, std::vector<Weight>> distances;

  for (Function* tf : target_funcs) {

    Vertex t = func_to_id.find(tf)->second;
    dijkstra_shortest_paths(cg, t,
      bo::predecessor_map(p.get()).distance_map(d.get()));

    bo::graph_traits<Graph>::vertex_iterator vi, vend;
    for (bo::tie(vi, vend) = bo::vertices(cg); vi != vend; ++vi) {

      // Skip unreachable functions.
      if (p[*vi] == *vi && *vi != t) continue;

      distances[functions[*vi]].push_back(d[*vi]);

    }

  }

  // Calculate average function to targets distance.
  std::unordered_map<Function*, double> d_f;
  for (const auto& func_dists : distances) {

    double sum = 0;
    for (const Weight& dist : func_dists.second)
      sum += 1.0 / (1 + dist);
    d_f.emplace(func_dists.first, func_dists.second.size() / sum);

  }
  distances.clear();

  std::unordered_map<BasicBlock*, double> d_b;
  for (auto& F : M) {

    auto trans_dists = getTransBlockDist(F, d_f, target_blocks);

    for (auto& BB : F) {

      // For trans blocks, distance is c * minimum c_f.
      auto it = trans_dists.find(&BB);
      if (it != trans_dists.end())
        d_b.emplace(&BB, kMagnifier * it->second);

    }

    Graph cfg;
    std::vector<BasicBlock*> blocks;
    std::unordered_map<BasicBlock*, Vertex> block_to_id;
    std::tie(cfg, blocks, block_to_id) = getControlFlowGraph(F);
    size_t num_blocks = blocks.size();
    std::unique_ptr<Weight[]> d = std::make_unique<Weight[]>(num_blocks);
    std::unique_ptr<Vertex[]> p = std::make_unique<Vertex[]>(num_blocks);

    // Map each basic block to distances generated from all trans blocks.
    std::unordered_map<BasicBlock*, std::vector<double>> d_n_t;

    for (const auto& trans : trans_dists) {

      Vertex t = block_to_id.find(trans.first)->second;
      dijkstra_shortest_paths(cfg, t,
        bo::predecessor_map(p.get()).distance_map(d.get()));

      bo::graph_traits<Graph>::vertex_iterator vi, vend;
      for (bo::tie(vi, vend) = bo::vertices(cfg); vi != vend; ++vi) {
        if (p[*vi] == *vi && *vi != t) continue;

        d_n_t[blocks[*vi]].push_back(
          1 / (1 + kMagnifier * trans.second + d[*vi]));

      }

    }

    for (const auto& block_dists : d_n_t) {

      // We skip all trans blocks, since their distances are already calculated.
      if (trans_dists.find(block_dists.first) != trans_dists.end())
        continue;

      d_b.emplace(block_dists.first,
        block_dists.second.size() / std::accumulate(
          block_dists.second.begin(), block_dists.second.end(), 0.0));

    }

  }

  std::vector<Function*> ordered;
  for (const auto& f : d_f)
    ordered.push_back(f.first);
  for (Function* F : functions)
    if (d_f.count(F) == 0)
      ordered.push_back(F);
  assert(ordered.size() == num_functions);

  return make_tuple(std::move(d_b), std::move(ordered), d_f.size());
}

}

bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);
  IntegerType *Int64Ty = IntegerType::getInt64Ty(C);

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

  auto targets = getTargets(M);
  std::unordered_map<BasicBlock*, double> block_dist;
  std::vector<Function*> funcs;
  size_t num_closures;
  std::tie(block_dist, funcs, num_closures) =
    calcDists(M, targets.first, targets.second);
  size_t num_funcs = funcs.size();

  Type *Arg64[] = {Int64Ty};
  FunctionType* FTy64 = FunctionType::get(Type::getVoidTy(C), Arg64, false);

  for (const auto& bd : block_dist) {

    IRBuilder<> IRB(&(*bd.first->getFirstInsertionPt()));
    ConstantInt* Dist = ConstantInt::get(Int64Ty, 100 * bd.second);
    IRB.CreateCall(M.getOrInsertFunction("hawkeye_dist_inst", FTy64), {Dist});

  }

  for (size_t i = 0; i < num_funcs; ++i) {

    IRBuilder<> IRB(&(*funcs[i]->getEntryBlock().getFirstInsertionPt()));
    ConstantInt* FuncIdx = ConstantInt::get(Int64Ty, i);
    IRB.CreateCall(M.getOrInsertFunction("hawkeye_func_inst", FTy64), {FuncIdx});

  }

  new GlobalVariable(M, Int64Ty, true, GlobalValue::ExternalLinkage,
    ConstantInt::get(Int64Ty, num_funcs), "__hawkeye_num_funcs");

  char buf[64];
  int r = snprintf(buf, sizeof(buf), NUM_CLOS_SIG"%lu", num_closures);
  if (r <= 0 || r >= sizeof(buf))
    FATAL("snprintf error");
  new GlobalVariable(M, ArrayType::get(Int8Ty, r + 1),
    true, GlobalValue::ExternalLinkage,
    ConstantDataArray::getString(C, buf), "__hawkeye_num_closures_str");
  r = snprintf(buf, sizeof(buf), NUM_FUNCS_SIG"%lu", num_funcs);
  if (r <= 0 || r >= sizeof(buf))
    FATAL("snprintf error");
  new GlobalVariable(M, ArrayType::get(Int8Ty, r + 1),
    true, GlobalValue::ExternalLinkage,
    ConstantDataArray::getString(C, buf), "__hawkeye_num_funcs_str");

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations and %lu targets (%s mode, ratio %u%%).",
             inst_blocks, targets.first.size(), getenv("AFL_HARDEN") ? "hardened" :
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
