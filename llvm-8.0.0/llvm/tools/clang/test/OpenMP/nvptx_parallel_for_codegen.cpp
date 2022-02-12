// Test target codegen - host bc file has to be created first.
// RUN: %clang_cc1 -verify -fopenmp -x c++ -triple powerpc64le-unknown-unknown -fopenmp-targets=nvptx64-nvidia-cuda -emit-llvm-bc %s -o %t-ppc-host.bc
// RUN: %clang_cc1 -verify -fopenmp -x c++ -triple nvptx64-unknown-unknown -fopenmp-targets=nvptx64-nvidia-cuda -emit-llvm %s -fopenmp-is-device -fopenmp-host-ir-file-path %t-ppc-host.bc -o - | FileCheck %s --check-prefix CHECK --check-prefix CHECK-64
// expected-no-diagnostics
#ifndef HEADER
#define HEADER

template<typename tx>
tx ftemplate(int n) {
  tx b[10];

  #pragma omp target
  {
    tx d = n;
    #pragma omp parallel for
    for(int i=0; i<10; i++) {
      b[i] += d;
    }
    b[3] += 1;
  }

  return b[3];
}

int bar(int n){
  int a = 0;

  a += ftemplate<int>(n);

  return a;
}

// CHECK-LABEL: define {{.*}}void {{@__omp_offloading_.+template.+l12}}_worker()
// CHECK: call void @llvm.nvvm.barrier0()
// CHECK: call i1 @__kmpc_kernel_parallel(
// CHECK: call void @__omp_outlined___wrapper(

// CHECK: define weak void @__omp_offloading_{{.*}}l12(
// CHECK: call void @__omp_offloading_{{.*}}l12_worker()
// CHECK: call void @__kmpc_kernel_init(
// CHECK: call void @__kmpc_data_sharing_init_stack()
// CHECK: call i8* @__kmpc_data_sharing_push_stack(i64 4, i16 0)
// CHECK: call void @__kmpc_kernel_prepare_parallel(
// CHECK: call void @__kmpc_begin_sharing_variables({{.*}}, i64 2)
// CHECK: call void @llvm.nvvm.barrier0()
// CHECK: call void @llvm.nvvm.barrier0()
// CHECK: call void @__kmpc_end_sharing_variables()
// CHECK: call void @__kmpc_data_sharing_pop_stack(
// CHECK: call void @__kmpc_kernel_deinit(i16 1)

// CHECK: define internal void @__omp_outlined__(
// CHECK: alloca
// CHECK: alloca
// CHECK: alloca
// CHECK: alloca
// CHECK: [[OMP_IV:%.*]] = alloca i32
// CHECK: store i32 0, {{.*}} [[OMP_LB:%.+]],
// CHECK: store i32 9, {{.*}} [[OMP_UB:%.+]],
// CHECK: store i32 1, {{.*}} [[OMP_ST:%.+]],
// CHECK: call void @__kmpc_for_static_init_4({{.*}} i32 34, {{.*}} [[OMP_LB]], {{.*}} [[OMP_UB]], {{.*}} [[OMP_ST]], i32 1, i32 1)
// CHECK: [[OMP_UB_1:%.+]] = load {{.*}} [[OMP_UB]]
// CHECK: [[COMP_1:%.+]] = icmp sgt {{.*}} [[OMP_UB_1]]
// CHECK: br i1 [[COMP_1]], label %[[COND_TRUE:.+]], label %[[COND_FALSE:.+]]

// CHECK: [[COND_TRUE]]
// CHECK: br label %[[COND_END:.+]]

// CHECK: [[COND_FALSE]]
// CHECK: [[OMP_UB_2:%.+]] = load {{.*}}* [[OMP_UB]]
// CHECK: br label %[[COND_END]]

// CHECK: [[COND_END]]
// CHECK: [[COND_RES:%.+]] = phi i32 [ 9, %[[COND_TRUE]] ], [ [[OMP_UB_2]], %[[COND_FALSE]] ]
// CHECK: store i32 [[COND_RES]], i32* [[OMP_UB]]
// CHECK: [[OMP_LB_1:%.+]] = load i32, i32* [[OMP_LB]]
// CHECK: store i32 [[OMP_LB_1]], i32* [[OMP_IV]]
// CHECK: br label %[[OMP_INNER_FOR_COND:.+]]

// CHECK: [[OMP_INNER_FOR_COND]]
// CHECK: [[OMP_IV_2:%.+]] = load i32, i32* [[OMP_IV]]
// CHECK: [[OMP_UB_4:%.+]] = load i32, i32* [[OMP_UB]]
// CHECK: [[COMP_3:%.+]] = icmp sle i32 [[OMP_IV_2]], [[OMP_UB_4]]
// CHECK: br i1 [[COMP_3]], label %[[OMP_INNER_FOR_BODY:.+]], label %[[OMP_INNER_FOR_END:.+]]

// CHECK: [[OMP_INNER_FOR_BODY]]
// CHECK: br label %[[OMP_BODY_CONTINUE:.+]]

// CHECK: [[OMP_BODY_CONTINUE]]
// CHECK: br label %[[OMP_INNER_FOR_INC:.+]]

// CHECK: [[OMP_INNER_FOR_INC]]
// CHECK: [[OMP_IV_3:%.+]] = load i32, i32* [[OMP_IV]]
// CHECK: [[ADD_1:%.+]] = add nsw i32 [[OMP_IV_3]], 1
// CHECK: store i32 [[ADD_1]], i32* [[OMP_IV]]
// CHECK: br label %[[OMP_INNER_FOR_COND]]

// CHECK: [[OMP_INNER_FOR_END]]
// CHECK: call void @__kmpc_for_static_fini(
// CHECK: ret void

#endif
