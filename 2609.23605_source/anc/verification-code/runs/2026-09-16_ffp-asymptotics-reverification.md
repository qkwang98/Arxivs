# Independent re-verification of the p-asymptotics

Run 2026-09-16 by the orchestrating session, checking Theorems A and B of
`working-notes/ffp-asymptotics-proof.org` before they entered article 2 draft 3 as
thm-asymptotics-p. Built from def-twoparam directly, not from the delegated script.

```
n r gaps        deg  A-pred  ok    lc               B-pred           ok
2 2 [1]            5      5  True  1/12             1/12             True
2 2 [2]            6      6  True  1/36             1/36             True
2 2 [3]            6      6  True  1/36             1/36             True
3 2 [1]            9      9  True  1/1080           1/1080           True
3 2 [2]           11     11  True  1/5400           1/5400           True
3 2 [3]           12     12  True  1/32400          1/32400          True
4 2 [1]           14     14  True  1/725760         1/725760         True
4 2 [2]           17     17  True  1/10160640       1/10160640       True
2 3 [1, 1]         7      7  True  1/24             1/24             True
3 3 [1, 1]        12     12  True  1/6480           1/6480           True
3 3 [2, 1]        14     14  True  1/32400          1/32400          True
2 2 [0]            3      3  True  1                -                n/a(0-gap)
3 2 [0]            6      6  True  7/90             -                n/a(0-gap)
2 3 [0, 1]         5      5  True  1/2              -                n/a(0-gap)
```
