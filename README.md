# Hawkeye (Unofficial Implementation)

This is an unofficial implementation of the paper "Hawkeye: Towards a Desired Directed Grey-box Fuzzer". However, the inclusion-based pointer analysis and the adaptive mutation are not implemented, because we only want the energy assignment components of the work.

## Usage

```bash
# LLVM 12 must be used for LTO
sudo apt-get install clang-12

# Environment variables
export CC=clang-12
export CXX=clang++-12
export LLVM_CONFIG=llvm-config-12
export AFL_REAL_LD=ld.lld-12

# Compile Hawkeye
cd Hawkeye && make clean all && cd llvm_mode && make clean all

# Set AFL compilers
export CC="/path/to/Hawkeye/afl-clang-fast"
export CXX="/path/to/Hawkeye/afl-clang-fast++"

# Make sure all compilation tools are using the LLVM 12 tool chain
export AS="$(which llvm-as-12)"
export RANLIB="$(which llvm-ranlib-12)"
export AR="$(which llvm-ar-12)"
export LD="$(which ld.lld-12)"
export NM="$(which llvm-nm-12)"
export AFL_CC=clang-12
export AFL_CXX=clang++-12

# Set the targets, the file BBtargets.txt has the same format as that in AFLGo
export HAWKEYE_BB_TARGETS="/path/to/BBtargets.txt"
# Set the programs used for directed fuzzing, separated by ':'
export HAWKEYE_TARGETS="prog1:prog2" # or "::" for all programs

# Use Hawkeye to compile the target program
$CC prog1.c -o prog1

# Run the directed fuzzer
Hawkeye/afl-fuzz -d -m none -i ./in -o ./out -- ./prog1 @@
```