# Transfer-matrix spectra, delta=0 degrees, and (p,n) polynomiality

Output of `code/oneoff/ff_transfer_spectra.py`, 2026-09-05 (WP6 of
PLAN-linusson-ff-vector-counting.md); see `working-notes/counting-ff-vectors.org` §WP6.

```
== (1) Perron roots of T(delta)  (improper | proper)
   n=2 delta=1: 3.73205080757 | 2.00000000000
   n=2 delta=2: 4.79128784748 | 2.00000000000
   n=2 charpoly T(1) improper: lambda*(lambda - 1)*(lambda**2 - 4*lambda + 1)
   n=3 delta=1: 5.81880440823 | 4.30277563773
   n=3 delta=2: 9.01384360245 | 5.00000000000
   n=3 delta=3: 9.89897948557 | 5.00000000000
   n=3 charpoly T(1) improper: lambda*(lambda**4 - 9*lambda**3 + 21*lambda**2 - 15*lambda + 3)
   n=4 delta=1: 9.85573713748 | 8.75659130803
   n=4 delta=2: 20.5858856206 | 15.3484692283
   n=4 delta=3: 25.2490654920 | 16.0000000000
   n=4 delta=4: 25.9614813968 | 16.0000000000
   n=4 charpoly T(1) improper: lambda*(lambda**5 - 17*lambda**4 + 85*lambda**3 - 154*lambda**2 + 103*lambda - 22)
   n=5 delta=1: 17.7572562456 | 17.1251433867
   n=5 delta=2: 57.8411039274 | 52.1804305348
   n=5 delta=3: 87.4360230780 | 69.3802268753
   n=5 delta=4: 95.4658874872 | 70.0000000000
   n=5 delta=5: 95.9895822028 | 70.0000000000
   n=6 delta=1: 33.2369623329 | 32.9602917277
   n=6 delta=2: 191.452853846 | 186.717329983
   n=6 delta=3: 426.779081179 | 396.523367195
   n=6 delta=4: 534.818937148 | 456.415006088
   n=6 delta=5: 552.654398497 | 457.000000000
   n=6 delta=6: 552.998191676 | 457.000000000
== (2) delta = 0: polynomial degree of r |-> |FF(n;0^r)|
   n=2 proper=False: degree 3 (expected n+1 = 3)  values [5, 14, 30, 55, 91]
   n=2 proper=True: degree 1 (expected n+1 = 3)  values [2, 3, 4, 5, 6]
   n=3 proper=False: degree 4 (expected n+1 = 4)  values [10, 43, 125, 290, 581]
   n=3 proper=True: degree 2 (expected n+1 = 4)  values [5, 12, 22, 35, 51]
   n=4 proper=False: degree 5 (expected n+1 = 5)  values [26, 194, 816, 2491, 6202]
   n=4 proper=True: degree 3 (expected n+1 = 5)  values [16, 69, 184, 385, 696]
   n=5 proper=False: degree 6 (expected n+1 = 6)  values [96, 1433, 9315, 38800, 122801]
   n=5 proper=True: degree 4 (expected n+1 = 6)  values [70, 627, 2592, 7385, 16926]
   n=6 proper=False: degree 7 (expected n+1 = 7)  values [553, 19145, 204141, 1195136, 4891732]
   n=6 proper=True: degree 5 (expected n+1 = 7)  values [457, 9904, 67448, 269765, 798101]
   n=7 proper=False: degree 8 (expected n+1 = 8)  values [5461, 502717, 9231030, 77648826, 415923270]
   n=7 proper=True: degree 6 (expected n+1 = 8)  values [4908, 296289, 3498402, 20113186, 77836827]
== (3) two-parameter (p, n): transfer vs brute force, and p-degrees
   brute-force comparisons: 0 mismatches
   n=2 d=[0, 0]: |FF^(p)| = [14, 33, 69, 128] ... polynomial in p of degree 3
   n=2 d=[0, 1]: |FF^(p)| = [20, 58, 162, 404] ... polynomial in p of degree 5
   n=3 d=[0, 0]: |FF^(p)| = [43, 168, 627, 1981] ... polynomial in p of degree 6
   n=3 d=[0, 1]: |FF^(p)| = [69, 341, 1858, 8801] ... polynomial in p of degree 9
```
