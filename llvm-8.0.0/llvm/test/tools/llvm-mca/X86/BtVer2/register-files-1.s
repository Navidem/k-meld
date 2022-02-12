# NOTE: Assertions have been autogenerated by utils/update_mca_test_checks.py
# RUN: llvm-mca -mtriple=x86_64-unknown-unknown -mcpu=btver2 -iterations=5 -instruction-info=false -dispatch-stats -register-file-stats -timeline < %s | FileCheck %s

vaddps %xmm0, %xmm0, %xmm0
vmulps %xmm0, %xmm0, %xmm0

# CHECK:      Iterations:        5
# CHECK-NEXT: Instructions:      10
# CHECK-NEXT: Total Cycles:      28
# CHECK-NEXT: Total uOps:        10

# CHECK:      Dispatch Width:    2
# CHECK-NEXT: uOps Per Cycle:    0.36
# CHECK-NEXT: IPC:               0.36
# CHECK-NEXT: Block RThroughput: 1.0

# CHECK:      Dynamic Dispatch Stall Cycles:
# CHECK-NEXT: RAT     - Register unavailable:                      0
# CHECK-NEXT: RCU     - Retire tokens unavailable:                 0
# CHECK-NEXT: SCHEDQ  - Scheduler full:                            0
# CHECK-NEXT: LQ      - Load queue full:                           0
# CHECK-NEXT: SQ      - Store queue full:                          0
# CHECK-NEXT: GROUP   - Static restrictions on the dispatch group: 0

# CHECK:      Dispatch Logic - number of cycles where we saw N micro opcodes dispatched:
# CHECK-NEXT: [# dispatched], [# cycles]
# CHECK-NEXT:  0,              23  (82.1%)
# CHECK-NEXT:  2,              5  (17.9%)

# CHECK:      Register File statistics:
# CHECK-NEXT: Total number of mappings created:    10
# CHECK-NEXT: Max number of mappings used:         10

# CHECK:      *  Register File #1 -- JFpuPRF:
# CHECK-NEXT:    Number of physical registers:     72
# CHECK-NEXT:    Total number of mappings created: 10
# CHECK-NEXT:    Max number of mappings used:      10

# CHECK:      *  Register File #2 -- JIntegerPRF:
# CHECK-NEXT:    Number of physical registers:     64
# CHECK-NEXT:    Total number of mappings created: 0
# CHECK-NEXT:    Max number of mappings used:      0

# CHECK:      Resources:
# CHECK-NEXT: [0]   - JALU0
# CHECK-NEXT: [1]   - JALU1
# CHECK-NEXT: [2]   - JDiv
# CHECK-NEXT: [3]   - JFPA
# CHECK-NEXT: [4]   - JFPM
# CHECK-NEXT: [5]   - JFPU0
# CHECK-NEXT: [6]   - JFPU1
# CHECK-NEXT: [7]   - JLAGU
# CHECK-NEXT: [8]   - JMul
# CHECK-NEXT: [9]   - JSAGU
# CHECK-NEXT: [10]  - JSTC
# CHECK-NEXT: [11]  - JVALU0
# CHECK-NEXT: [12]  - JVALU1
# CHECK-NEXT: [13]  - JVIMUL

# CHECK:      Resource pressure per iteration:
# CHECK-NEXT: [0]    [1]    [2]    [3]    [4]    [5]    [6]    [7]    [8]    [9]    [10]   [11]   [12]   [13]
# CHECK-NEXT:  -      -      -     1.00   1.00   1.00   1.00    -      -      -      -      -      -      -

# CHECK:      Resource pressure by instruction:
# CHECK-NEXT: [0]    [1]    [2]    [3]    [4]    [5]    [6]    [7]    [8]    [9]    [10]   [11]   [12]   [13]   Instructions:
# CHECK-NEXT:  -      -      -     1.00    -     1.00    -      -      -      -      -      -      -      -     vaddps	%xmm0, %xmm0, %xmm0
# CHECK-NEXT:  -      -      -      -     1.00    -     1.00    -      -      -      -      -      -      -     vmulps	%xmm0, %xmm0, %xmm0

# CHECK:      Timeline view:
# CHECK-NEXT:                     0123456789
# CHECK-NEXT: Index     0123456789          01234567

# CHECK:      [0,0]     DeeeER    .    .    .    . .   vaddps	%xmm0, %xmm0, %xmm0
# CHECK-NEXT: [0,1]     D===eeER  .    .    .    . .   vmulps	%xmm0, %xmm0, %xmm0
# CHECK-NEXT: [1,0]     .D====eeeER    .    .    . .   vaddps	%xmm0, %xmm0, %xmm0
# CHECK-NEXT: [1,1]     .D=======eeER  .    .    . .   vmulps	%xmm0, %xmm0, %xmm0
# CHECK-NEXT: [2,0]     . D========eeeER    .    . .   vaddps	%xmm0, %xmm0, %xmm0
# CHECK-NEXT: [2,1]     . D===========eeER  .    . .   vmulps	%xmm0, %xmm0, %xmm0
# CHECK-NEXT: [3,0]     .  D============eeeER    . .   vaddps	%xmm0, %xmm0, %xmm0
# CHECK-NEXT: [3,1]     .  D===============eeER  . .   vmulps	%xmm0, %xmm0, %xmm0
# CHECK-NEXT: [4,0]     .   D================eeeER .   vaddps	%xmm0, %xmm0, %xmm0
# CHECK-NEXT: [4,1]     .   D===================eeER   vmulps	%xmm0, %xmm0, %xmm0

# CHECK:      Average Wait times (based on the timeline view):
# CHECK-NEXT: [0]: Executions
# CHECK-NEXT: [1]: Average time spent waiting in a scheduler's queue
# CHECK-NEXT: [2]: Average time spent waiting in a scheduler's queue while ready
# CHECK-NEXT: [3]: Average time elapsed from WB until retire stage

# CHECK:            [0]    [1]    [2]    [3]
# CHECK-NEXT: 0.     5     9.0    0.2    0.0       vaddps	%xmm0, %xmm0, %xmm0
# CHECK-NEXT: 1.     5     12.0   0.0    0.0       vmulps	%xmm0, %xmm0, %xmm0
