# Exact delta=0 degrees: proof verification run

Date: 2026-09-15 20:20, host jts-pc.
Command: systemd-run --user --scope -p MemoryMax=8G timeout 600 python3 code/oneoff/delta0_exact_degree_proof_check.py

Verifies every step of the proof written up in
working-notes/delta0-exact-degrees-proof.org (open problem 2 of article 2
Section 9.2; Remark rem-delta0-degrees): for n = 2..8, the structural facts
A[j][j+1] = 1 and A[j][j] = C(n,j)-1, the triangularity/nilpotency claims,
the corner-entry values u N^{n+1} 1 = prod_j C(n,j) (improper) and
u' N'^{n-1} 1 = prod_{j>=2} C(n,j) (proper), and the assembled polynomial
sum_k C(r-1,k) c_k against the independent ff_count of
code/linusson_ff_counting.py for r = 1..n+4.  Result: 0 mismatches.

```
Running as unit: run-p49394-i58336.scope; invocation ID: 7ede7d133c0949c8aba823ae15167bde
========================================================================
n = 2   (matrix size 4x4)
S1  A[j][j+1] = 1, j=0..n:                  True
S2  A[j][j] = C(n,j)-1, j=1..n; row -1 = e0: True
support rho <= tau+1:                        True
improper: T(0) upper-triangular True, unit diagonal True, N^4 = 0: True
  c_k = u N^k 1, k=0..4: [5, 9, 7, 2, 0]
  largest nonzero k = 3  (want n+1 = 3): True
  c_{n+1} = 2  (predicted prod_j C(n,j) = 2): True
  poly vs ff_count, r=1..6: True   values [5, 14, 30, 55, 91, 140]
  finite-difference degree = 3, (n+1)!*lead = 2 (want 2): True
proper: cols tau'=-1,0 of T'(0) zero True; u' supported on tau>=1 with u'[1]=1 True
  block tau=1..n upper-triangular True, unit diagonal True, N'^2 = 0: True
  c'_k = u' N'^k 1, k=0..2: [2, 1, 0]
  largest nonzero k = 1  (want n-1 = 1): True
  c'_{n-1} = 1  (predicted prod_{j>=2} C(n,j) = 1): True
  poly vs ff_count (proper), r=1..6: True   values [2, 3, 4, 5, 6, 7]
  finite-difference degree = 1, (n-1)!*lead = 1 (want 1): True
========================================================================
n = 3   (matrix size 5x5)
S1  A[j][j+1] = 1, j=0..n:                  True
S2  A[j][j] = C(n,j)-1, j=1..n; row -1 = e0: True
support rho <= tau+1:                        True
improper: T(0) upper-triangular True, unit diagonal True, N^5 = 0: True
  c_k = u N^k 1, k=0..5: [10, 33, 49, 34, 9, 0]
  largest nonzero k = 4  (want n+1 = 4): True
  c_{n+1} = 9  (predicted prod_j C(n,j) = 9): True
  poly vs ff_count, r=1..7: True   values [10, 43, 125, 290, 581, 1050, 1758]
  finite-difference degree = 4, (n+1)!*lead = 9 (want 9): True
proper: cols tau'=-1,0 of T'(0) zero True; u' supported on tau>=1 with u'[1]=1 True
  block tau=1..n upper-triangular True, unit diagonal True, N'^3 = 0: True
  c'_k = u' N'^k 1, k=0..3: [5, 7, 3, 0]
  largest nonzero k = 2  (want n-1 = 2): True
  c'_{n-1} = 3  (predicted prod_{j>=2} C(n,j) = 3): True
  poly vs ff_count (proper), r=1..7: True   values [5, 12, 22, 35, 51, 70, 92]
  finite-difference degree = 2, (n-1)!*lead = 3 (want 3): True
========================================================================
n = 4   (matrix size 6x6)
S1  A[j][j+1] = 1, j=0..n:                  True
S2  A[j][j] = C(n,j)-1, j=1..n; row -1 = e0: True
support rho <= tau+1:                        True
improper: T(0) upper-triangular True, unit diagonal True, N^6 = 0: True
  c_k = u N^k 1, k=0..6: [26, 168, 454, 599, 384, 96, 0]
  largest nonzero k = 5  (want n+1 = 5): True
  c_{n+1} = 96  (predicted prod_j C(n,j) = 96): True
  poly vs ff_count, r=1..8: True   values [26, 194, 816, 2491, 6202, 13412, 26160, 47157]
  finite-difference degree = 5, (n+1)!*lead = 96 (want 96): True
proper: cols tau'=-1,0 of T'(0) zero True; u' supported on tau>=1 with u'[1]=1 True
  block tau=1..n upper-triangular True, unit diagonal True, N'^4 = 0: True
  c'_k = u' N'^k 1, k=0..4: [16, 53, 62, 24, 0]
  largest nonzero k = 3  (want n-1 = 3): True
  c'_{n-1} = 24  (predicted prod_{j>=2} C(n,j) = 24): True
  poly vs ff_count (proper), r=1..8: True   values [16, 69, 184, 385, 696, 1141, 1744, 2529]
  finite-difference degree = 3, (n-1)!*lead = 24 (want 24): True
========================================================================
n = 5   (matrix size 7x7)
S1  A[j][j+1] = 1, j=0..n:                  True
S2  A[j][j] = C(n,j)-1, j=1..n; row -1 = e0: True
support rho <= tau+1:                        True
improper: T(0) upper-triangular True, unit diagonal True, N^7 = 0: True
  c_k = u N^k 1, k=0..7: [96, 1337, 6545, 15058, 17855, 10600, 2500, 0]
  largest nonzero k = 6  (want n+1 = 6): True
  c_{n+1} = 2500  (predicted prod_j C(n,j) = 2500): True
  poly vs ff_count, r=1..9: True   values [96, 1433, 9315, 38800, 122801, 322686, 741378, 1538955, 2950750]
  finite-difference degree = 6, (n+1)!*lead = 2500 (want 2500): True
proper: cols tau'=-1,0 of T'(0) zero True; u' supported on tau>=1 with u'[1]=1 True
  block tau=1..n upper-triangular True, unit diagonal True, N'^5 = 0: True
  c'_k = u' N'^k 1, k=0..5: [70, 557, 1408, 1420, 500, 0]
  largest nonzero k = 4  (want n-1 = 4): True
  c'_{n-1} = 500  (predicted prod_{j>=2} C(n,j) = 500): True
  poly vs ff_count (proper), r=1..9: True   values [70, 627, 2592, 7385, 16926, 33635, 60432, 100737, 158470]
  finite-difference degree = 4, (n-1)!*lead = 500 (want 500): True
========================================================================
n = 6   (matrix size 8x8)
S1  A[j][j+1] = 1, j=0..n:                  True
S2  A[j][j] = C(n,j)-1, j=1..n; row -1 = e0: True
support rho <= tau+1:                        True
improper: T(0) upper-triangular True, unit diagonal True, N^8 = 0: True
  c_k = u N^k 1, k=0..8: [553, 18592, 166404, 639595, 1260007, 1339196, 732420, 162000, 0]
  largest nonzero k = 7  (want n+1 = 7): True
  c_{n+1} = 162000  (predicted prod_j C(n,j) = 162000): True
  poly vs ff_count, r=1..10: True   values [553, 19145, 204141, 1195136, 4891732, 15792734, 43067766, 103523307, 225625147, 454739263]
  finite-difference degree = 7, (n+1)!*lead = 162000 (want 162000): True
proper: cols tau'=-1,0 of T'(0) zero True; u' supported on tau>=1 with u'[1]=1 True
  block tau=1..n upper-triangular True, unit diagonal True, N'^6 = 0: True
  c'_k = u' N'^k 1, k=0..6: [457, 9447, 48097, 96676, 84570, 27000, 0]
  largest nonzero k = 5  (want n-1 = 5): True
  c'_{n-1} = 27000  (predicted prod_{j>=2} C(n,j) = 27000): True
  poly vs ff_count (proper), r=1..10: True   values [457, 9904, 67448, 269765, 798101, 1945272, 4142664, 7987233, 14268505, 23995576]
  finite-difference degree = 5, (n-1)!*lead = 27000 (want 27000): True
========================================================================
n = 7   (matrix size 9x9)
S1  A[j][j+1] = 1, j=0..n:                  True
S2  A[j][j] = C(n,j)-1, j=1..n; row -1 = e0: True
support rho <= tau+1:                        True
improper: T(0) upper-triangular True, unit diagonal True, N^9 = 0: True
  c_k = u N^k 1, k=0..9: [5461, 497256, 8231057, 51458426, 158708739, 268813069, 255594682, 128242212, 26471025, 0]
  largest nonzero k = 8  (want n+1 = 8): True
  c_{n+1} = 26471025  (predicted prod_j C(n,j) = 26471025): True
  poly vs ff_count, r=1..11: True   values [5461, 502717, 9231030, 77648826, 415923270, 1661743335, 5404727553, 15094668660, 37488328372, 84815966554, 177875260069]
  finite-difference degree = 8, (n+1)!*lead = 26471025 (want 26471025): True
proper: cols tau'=-1,0 of T'(0) zero True; u' supported on tau>=1 with u'[1]=1 True
  block tau=1..n upper-triangular True, unit diagonal True, N'^7 = 0: True
  c'_k = u' N'^k 1, k=0..7: [4908, 291381, 2910732, 10501939, 17194247, 13098141, 3781575, 0]
  largest nonzero k = 6  (want n-1 = 6): True
  c'_{n-1} = 3781575  (predicted prod_{j>=2} C(n,j) = 3781575): True
  poly vs ff_count (proper), r=1..11: True   values [4908, 296289, 3498402, 20113186, 77836827, 234657899, 595737080, 1334068443, 2714922322, 5124069753, 9099788490]
  finite-difference degree = 6, (n-1)!*lead = 3781575 (want 3781575): True
========================================================================
n = 8   (matrix size 10x10)
S1  A[j][j+1] = 1, j=0..n:                  True
S2  A[j][j] = C(n,j)-1, j=1..n; row -1 = e0: True
support rho <= tau+1:                        True
improper: T(0) upper-triangular True, unit diagonal True, N^10 = 0: True
  c_k = u N^k 1, k=0..10: [100709, 27555193, 851507199, 8492371466, 39446822920, 99767254760, 146362408192, 124680084480, 57321062400, 11014635520, 0]
  largest nonzero k = 9  (want n+1 = 9): True
  c_{n+1} = 11014635520  (predicted prod_j C(n,j) = 11014635520): True
  poly vs ff_count, r=1..12: True   values [100709, 27655902, 906718294, 11129659351, 78635673459, 390578032684, 1519453749724, 4940275733533, 14000788584497, 35595064873962, 82870169086354, 179385941371091]
  finite-difference degree = 9, (n+1)!*lead = 11014635520 (want 11014635520): True
proper: cols tau'=-1,0 of T'(0) zero True; u' supported on tau>=1 with u'[1]=1 True
  block tau=1..n upper-triangular True, unit diagonal True, N'^8 = 0: True
  c'_k = u' N'^k 1, k=0..8: [95248, 17914141, 347282222, 2125785408, 5799237920, 7898078720, 5271992320, 1376829440, 0]
  largest nonzero k = 7  (want n-1 = 7): True
  c'_{n-1} = 1376829440  (predicted prod_{j>=2} C(n,j) = 1376829440): True
  poly vs ff_count (proper), r=1..12: True   values [95248, 18009389, 383205752, 3221469745, 16457824696, 61714610573, 187481555024, 488934666177, 1135780776640, 2409504568141, 4751394906248, 8822727314609]
  finite-difference degree = 7, (n-1)!*lead = 1376829440 (want 1376829440): True
========================================================================
TOTAL mismatches over n = 2..8: 0
```
