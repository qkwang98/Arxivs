# Independent re-verification of the Alexander-duality proof

Run 2026-09-15 by the orchestrating session, re-checking the delegated proof of
`|S_n| = F^n(n-2)` before it entered article 2 draft 2 as Proposition prop-fnn2.
Distinct code from `code/oneoff/alexander_duality_snn2.py`.

```
=== 1. the identity at recursion level ===
   n= 1  |S_n|=1            F^n(n-2)=1             equal? True
   n= 2  |S_n|=2            F^n(n-2)=2             equal? True
   n= 3  |S_n|=5            F^n(n-2)=5             equal? True
   n= 4  |S_n|=16           F^n(n-2)=16            equal? True
   n= 5  |S_n|=70           F^n(n-2)=70            equal? True
   n= 6  |S_n|=457          F^n(n-2)=457           equal? True
   n= 7  |S_n|=4908         F^n(n-2)=4908          equal? True
   n= 8  |S_n|=95248        F^n(n-2)=95248         equal? True
   n= 9  |S_n|=3617645      F^n(n-2)=3617645       equal? True
   n=10  |S_n|=286007155    F^n(n-2)=286007155     equal? True
   n=11  |S_n|=49224068017  F^n(n-2)=49224068017   equal? True
   n=12  |S_n|=19039518484735 F^n(n-2)=19039518484735  equal? True
=== 2. D is an involution of F_n, and D(S_n) = {top <= n-2} ===
   n=2 |F_n|=5    involution=True  maps-into=True   D(S_n)=={top<=n-2}? True   |S_n|=2     F^n(n-2)=2
   n=3 |F_n|=10   involution=True  maps-into=True   D(S_n)=={top<=n-2}? True   |S_n|=5     F^n(n-2)=5
   n=4 |F_n|=26   involution=True  maps-into=True   D(S_n)=={top<=n-2}? True   |S_n|=16    F^n(n-2)=16
   n=5 |F_n|=96   involution=True  maps-into=True   D(S_n)=={top<=n-2}? True   |S_n|=70    F^n(n-2)=70
   n=6 |F_n|=553  involution=True  maps-into=True   D(S_n)=={top<=n-2}? True   |S_n|=457   F^n(n-2)=457
=== 3. persymmetry A[t][r] == A[n-r][n-t] ===
   n=1  persymmetric? True
   n=2  persymmetric? True
   n=3  persymmetric? True
   n=4  persymmetric? True
   n=5  persymmetric? True
   n=6  persymmetric? True
   n=7  persymmetric? True
   n=8  persymmetric? True
```
