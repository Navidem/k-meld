#!/bin/bash -e

ROOT="$(pwd)"
#cd $ROOT/llvm-8.0.0

if [ ! -d "build" ]; then
  mkdir build
fi

cd build
cmake -DLLVM_TARGET_ARCH="ARM;X86;AArch64" -DLLVM_TARGETS_TO_BUILD="ARM;X86;AArch64" -DCMAKE_BUILD_TYPE=Release ../llvm
make -j8

if [ ! -d "$ROOT/prefix" ]; then
  mkdir $ROOT/prefix
fi

cmake -DCMAKE_INSTALL_PREFIX=$ROOT/prefix -P cmake_install.cmake 
