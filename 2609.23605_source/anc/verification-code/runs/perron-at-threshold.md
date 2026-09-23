# Perron roots at and above the threshold

Output of `code/oneoff/perron_at_threshold.py`, 2026-09-14. Written while upgrading article 2's
Remark 25 to Proposition 25: `runs/ff-transfer-spectra.md` stopped at delta = n, one short of the
improper threshold delta = n+1, which is why the remark said "tends to" where the truth is
"equals". Rank-one check appended.

```
n  |F_n|  |S_n|   delta  improper-root        proper-root
   (improper threshold is delta >= n+1; proper is delta >= n-1)
2      5      2     1         3.7320508076         2.0000000000  == |S_n| EXACTLY
2      5      2     2         4.7912878475         2.0000000000  == |S_n| EXACTLY
2      5      2     3         5.0000000000  == |F_n| EXACTLY         2.0000000000  == |S_n| EXACTLY
2      5      2     4         5.0000000000  == |F_n| EXACTLY         2.0000000000  == |S_n| EXACTLY

3     10      5     1         5.8188044082         4.3027756377
3     10      5     2         9.0138436024         5.0000000000  == |S_n| EXACTLY
3     10      5     3         9.8989794856         5.0000000000  == |S_n| EXACTLY
3     10      5     4        10.0000000000  == |F_n| EXACTLY         5.0000000000  == |S_n| EXACTLY
3     10      5     5        10.0000000000  == |F_n| EXACTLY         5.0000000000  == |S_n| EXACTLY

4     26     16     1         9.8557371375         8.7565913080
4     26     16     2        20.5858856206        15.3484692283
4     26     16     3        25.2490654920        16.0000000000  == |S_n| EXACTLY
4     26     16     4        25.9614813968        16.0000000000  == |S_n| EXACTLY
4     26     16     5        26.0000000000  == |F_n| EXACTLY        16.0000000000  == |S_n| EXACTLY
4     26     16     6        26.0000000000  == |F_n| EXACTLY        16.0000000000  == |S_n| EXACTLY

5     96     70     1        17.7572562456        17.1251433867
5     96     70     2        57.8411039274        52.1804305348
5     96     70     3        87.4360230780        69.3802268753
5     96     70     4        95.4658874872        70.0000000000  == |S_n| EXACTLY
5     96     70     5        95.9895822028        70.0000000000  == |S_n| EXACTLY
5     96     70     6        96.0000000000  == |F_n| EXACTLY        70.0000000000  == |S_n| EXACTLY
5     96     70     7        96.0000000000  == |F_n| EXACTLY        70.0000000000  == |S_n| EXACTLY

6    553    457     1        33.2369623329        32.9602917277
6    553    457     2       191.4528538459       186.7173299826
6    553    457     3       426.7790811792       396.5233671949
6    553    457     4       534.8189371480       456.4150060878
6    553    457     5       552.6543984974       457.0000000000  == |S_n| EXACTLY
6    553    457     6       552.9981916758       457.0000000000  == |S_n| EXACTLY
6    553    457     7       553.0000000000  == |F_n| EXACTLY       457.0000000000  == |S_n| EXACTLY
6    553    457     8       553.0000000000  == |F_n| EXACTLY       457.0000000000  == |S_n| EXACTLY


n  case      delta  rank(T)  all rows equal?  row-sum   target
2  improper    3       1    True                  5         5
2  improper    4       1    True                  5         5
2  proper      1       1    True                  2         2
2  proper      2       1    True                  2         2
3  improper    4       1    True                 10        10
3  improper    5       1    True                 10        10
3  proper      2       1    True                  5         5
3  proper      3       1    True                  5         5
4  improper    5       1    True                 26        26
4  improper    6       1    True                 26        26
4  proper      3       1    True                 16        16
4  proper      4       1    True                 16        16
5  improper    6       1    True                 96        96
5  improper    7       1    True                 96        96
5  proper      4       1    True                 70        70
5  proper      5       1    True                 70        70
6  improper    7       1    True                553       553
6  improper    8       1    True                553       553
6  proper      5       1    True                457       457
6  proper      6       1    True                457       457
```
