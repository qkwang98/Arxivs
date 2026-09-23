# Re-verification of the proper p-asymptotics, and a measurement error of my own

Run 2026-09-16 by the orchestrating session, checking thm-asymptotics-p-proper before
accepting the delegated draft edit. Built from thm-proper + def-twoparam directly.

## The window trap, recorded because it cost two false alarms

Newton-difference interpolation over a window SHORTER than the true degree returns a
plausible wrong answer rather than failing. Two of my checks did exactly that and appeared
to refute the draft's claim that E^p(n,1) may replace |S_n^(p)|. With windows long enough
for the true degree the two agree exactly. ALWAYS CHECK WINDOW-STABILITY; the delegated
session asserted window-constancy in its own battery and was right to.

```
window-size sensitivity: deg/lc of E^p(n,1) and |S_n^(p)|
  n=5 W=12  E1=(11, Fraction(555011, 4989600)) S=(11, Fraction(558367, 4989600)) same=False
  n=5 W=20  E1=(14, Fraction(1, 2177280))   S=(14, Fraction(1, 2177280))   same=True
  n=5 W=30  E1=(14, Fraction(1, 2177280))   S=(14, Fraction(1, 2177280))   same=True
  n=5 W=40  E1=(14, Fraction(1, 2177280))   S=(14, Fraction(1, 2177280))   same=True
  n=6 W=12  E1=(11, Fraction(17737418989, 1995840)) S=(11, Fraction(14789870575, 1596672)) same=False
  n=6 W=20  E1=(19, Fraction(35011, 1624533926400)) S=(19, Fraction(35011, 1624533926400)) same=True
  n=6 W=30  E1=(20, Fraction(1, 12317184000)) S=(20, Fraction(1, 12317184000)) same=True
  n=6 W=40  E1=(20, Fraction(1, 12317184000)) S=(20, Fraction(1, 12317184000)) same=True

THEOREM B' at n=5 (where E^p(n,1) is NOT the dominant term of |S_n^(p)|)
  gaps [1]     deg 19 (pred 19, True)  lc 1/261273600
      with E^p(n,1): 1/261273600            match True
      with |S_n^(p)|: 1/261273600            match True
  gaps [2]     deg 23 (pred 23, True)  lc 1/14108774400
      with E^p(n,1): 1/14108774400          match True
      with |S_n^(p)|: 1/14108774400          match True
  gaps [3]     deg 26 (pred 26, True)  lc 1/338610585600
      with E^p(n,1): 1/338610585600         match True
      with |S_n^(p)|: 1/338610585600         match True
  gaps [1, 1]  deg 24 (pred 24, True)  lc 1/31352832000
      with E^p(n,1): 1/31352832000          match True
      with |S_n^(p)|: 1/31352832000          match True
```
