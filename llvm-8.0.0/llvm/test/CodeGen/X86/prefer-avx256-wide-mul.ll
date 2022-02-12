; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx512vl,+avx512bw,+prefer-256-bit | FileCheck %s --check-prefix=CHECK --check-prefix=AVX256BW
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx512vl,+avx512bw,-prefer-256-bit | FileCheck %s --check-prefix=CHECK --check-prefix=AVX512BW
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx512bw,+prefer-256-bit | FileCheck %s --check-prefix=CHECK --check-prefix=AVX512BW
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx512bw,-prefer-256-bit | FileCheck %s --check-prefix=CHECK --check-prefix=AVX512BW

define <32 x i8> @test_div7_32i8(<32 x i8> %a) {
; AVX256BW-LABEL: test_div7_32i8:
; AVX256BW:       # %bb.0:
; AVX256BW-NEXT:    vextracti128 $1, %ymm0, %xmm1
; AVX256BW-NEXT:    vpmovzxbw {{.*#+}} ymm1 = xmm1[0],zero,xmm1[1],zero,xmm1[2],zero,xmm1[3],zero,xmm1[4],zero,xmm1[5],zero,xmm1[6],zero,xmm1[7],zero,xmm1[8],zero,xmm1[9],zero,xmm1[10],zero,xmm1[11],zero,xmm1[12],zero,xmm1[13],zero,xmm1[14],zero,xmm1[15],zero
; AVX256BW-NEXT:    vmovdqa {{.*#+}} ymm2 = [37,37,37,37,37,37,37,37,37,37,37,37,37,37,37,37]
; AVX256BW-NEXT:    vpmullw %ymm2, %ymm1, %ymm1
; AVX256BW-NEXT:    vpsrlw $8, %ymm1, %ymm1
; AVX256BW-NEXT:    vpmovzxbw {{.*#+}} ymm3 = xmm0[0],zero,xmm0[1],zero,xmm0[2],zero,xmm0[3],zero,xmm0[4],zero,xmm0[5],zero,xmm0[6],zero,xmm0[7],zero,xmm0[8],zero,xmm0[9],zero,xmm0[10],zero,xmm0[11],zero,xmm0[12],zero,xmm0[13],zero,xmm0[14],zero,xmm0[15],zero
; AVX256BW-NEXT:    vpmullw %ymm2, %ymm3, %ymm2
; AVX256BW-NEXT:    vpsrlw $8, %ymm2, %ymm2
; AVX256BW-NEXT:    vpackuswb %ymm1, %ymm2, %ymm1
; AVX256BW-NEXT:    vpermq {{.*#+}} ymm1 = ymm1[0,2,1,3]
; AVX256BW-NEXT:    vpsubb %ymm1, %ymm0, %ymm0
; AVX256BW-NEXT:    vpsrlw $1, %ymm0, %ymm0
; AVX256BW-NEXT:    vpand {{.*}}(%rip), %ymm0, %ymm0
; AVX256BW-NEXT:    vpaddb %ymm1, %ymm0, %ymm0
; AVX256BW-NEXT:    vpsrlw $2, %ymm0, %ymm0
; AVX256BW-NEXT:    vpand {{.*}}(%rip), %ymm0, %ymm0
; AVX256BW-NEXT:    retq
;
; AVX512BW-LABEL: test_div7_32i8:
; AVX512BW:       # %bb.0:
; AVX512BW-NEXT:    vpmovzxbw {{.*#+}} zmm1 = ymm0[0],zero,ymm0[1],zero,ymm0[2],zero,ymm0[3],zero,ymm0[4],zero,ymm0[5],zero,ymm0[6],zero,ymm0[7],zero,ymm0[8],zero,ymm0[9],zero,ymm0[10],zero,ymm0[11],zero,ymm0[12],zero,ymm0[13],zero,ymm0[14],zero,ymm0[15],zero,ymm0[16],zero,ymm0[17],zero,ymm0[18],zero,ymm0[19],zero,ymm0[20],zero,ymm0[21],zero,ymm0[22],zero,ymm0[23],zero,ymm0[24],zero,ymm0[25],zero,ymm0[26],zero,ymm0[27],zero,ymm0[28],zero,ymm0[29],zero,ymm0[30],zero,ymm0[31],zero
; AVX512BW-NEXT:    vpmullw {{.*}}(%rip), %zmm1, %zmm1
; AVX512BW-NEXT:    vpsrlw $8, %zmm1, %zmm1
; AVX512BW-NEXT:    vpmovwb %zmm1, %ymm1
; AVX512BW-NEXT:    vpsubb %ymm1, %ymm0, %ymm0
; AVX512BW-NEXT:    vpsrlw $1, %ymm0, %ymm0
; AVX512BW-NEXT:    vpand {{.*}}(%rip), %ymm0, %ymm0
; AVX512BW-NEXT:    vpaddb %ymm1, %ymm0, %ymm0
; AVX512BW-NEXT:    vpsrlw $2, %ymm0, %ymm0
; AVX512BW-NEXT:    vpand {{.*}}(%rip), %ymm0, %ymm0
; AVX512BW-NEXT:    retq
  %res = udiv <32 x i8> %a, <i8 7, i8 7, i8 7, i8 7,i8 7, i8 7, i8 7, i8 7, i8 7, i8 7, i8 7, i8 7,i8 7, i8 7, i8 7, i8 7, i8 7, i8 7, i8 7, i8 7,i8 7, i8 7, i8 7, i8 7, i8 7, i8 7, i8 7, i8 7,i8 7, i8 7, i8 7, i8 7>
  ret <32 x i8> %res
}