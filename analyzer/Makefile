CUR_DIR = $(shell pwd)
LLVM_SRC := ${CUR_DIR}/../llvm-8.0.0/llvm
LLVM_BUILD := ${CUR_DIR}/../llvm-8.0.0/prefix
KMELD_DIR := ${CURDIR}/src
KMELD_BUILD := ${CURDIR}/build


build_kmeld_func = \
	(mkdir -p ${2} \
		&& cd ${2} \
		&& PATH=${LLVM_BUILD}/bin:${PATH} \
			LLVM_ROOT_DIR=${LLVM_BUILD}/bin \
			LLVM_LIBRARY_DIRS=${LLVM_BUILD}/lib \
			LLVM_INCLUDE_DIRS=${LLVM_BUILD}/include \
			CC=clang CXX=clang++ \
            cmake ${1} -DCMAKE_BUILD_TYPE=Release \
                -DCMAKE_CXX_FLAGS_RELEASE="-std=c++11 -fno-rtti -fpic -g" \
		&& make -j4)

all: kmeld

kmeld:
	$(call build_kmeld_func, ${KMELD_DIR}, ${KMELD_BUILD})
