# Run log: adversarial review attack on conj-kozlov-facets proofs

Date: 2026-09-06, host jts-pc. Script: code/oneoff/kozlov_facets_review_attack.sage
Review: working-notes/conj-kozlov-facets-review.org

```
=== (3) literal Q_Theta(a;(delta)) with delta>0 is an unbounded cylinder ===
  n=3 delta=1: literal Q_Theta bounded? False   (simplex is bounded: True)
  n=3 delta=2: literal Q_Theta bounded? False   (simplex is bounded: True)
  n=4 delta=3: literal Q_Theta bounded? False   (simplex is bounded: True)

=== (1)+(2) corner-configuration battery ===
  n=2 d=[0, 1] N=3: OK  
  n=2 d=[0, 1, 2] N=4: OK  
  n=2 d=[0, 1, 2, 3, 4] N=6: OK  
  n=3 d=[0, 1] N=4: OK  
  n=3 d=[0, 2] N=5: OK  
  n=3 d=[0, 1, 2] N=5: OK  
  n=3 d=[0, 2, 4] N=7: OK  
  n=3 d=[0, 1, 3] N=6: OK  
  n=3 d=[0, 1, 2, 3, 4] N=7: OK  
  n=4 d=[0, 1] N=5: OK  
  n=4 d=[0, 2] N=6: OK  
  n=4 d=[0, 3] N=7: OK  
  n=4 d=[0, 3, 6] N=10: OK  
  n=4 d=[0, 2, 4] N=8: OK  
  n=4 d=[0, 1, 4] N=8: OK  
  n=4 d=[0, 3, 4] N=8: OK  
  n=5 d=[0, 3] N=8: OK  
  n=5 d=[0, 4] N=9: OK  
  n=5 d=[0, 4, 8] N=13: OK  
  n=5 d=[0, 1, 2] N=7: OK  
  n=5 d=[0, 1, 2, 3] N=8: OK  
  n=6 d=[0, 4] N=10: OK  
  n=6 d=[0, 5] N=11: OK  
  n=7 d=[0, 1] N=8: OK  
  n=7 d=[0, 5] N=12: OK  
  n=7 d=[0, 6] N=13: OK  
battery all OK: True

=== (4) part-3 argmax formulas vs brute force + face dimensions ===
  n=4 d=[0, 3]: argmax formulas + face dims OK
  n=5 d=[0, 1]: argmax formulas + face dims OK
  n=2 d=[0, 1, 2]: argmax formulas + face dims OK
  n=4 d=[0, 2, 4]: argmax formulas + face dims OK
  n=7 d=[0, 6]: argmax formulas + face dims OK
  n=3 d=[0, 1, 2]: argmax formulas + face dims OK

=== (4b) the coverage-wording slip, concretely: n=4, d=(0,3), item2 p=2 j=3 ===
  window 1 argmax: [1, 2, 3, 4] -> span reaches coordinate 4 ; but c-1 = 5  (so 'windows q<p cover [2,c-1]' is FALSE here; window p's own lower span must fill in)

=== (5) reduction-3 threshold probe: is R a product at gap n-1? at n-2? ===
  n=3 gap=2 (n-1): f(R)==f(P1 x P2')? True   facets(R)=6, 2n=6
  n=3 gap=1 (n-2): facets(R)=6, 2n=6  (R claimed NOT a product; f-vector (1, 7, 11, 6, 1))
  n=4 gap=3 (n-1): f(R)==f(P1 x P2')? True   facets(R)=8, 2n=8
  n=4 gap=2 (n-2): facets(R)=8, 2n=8  (R claimed NOT a product; f-vector (1, 14, 37, 43, 26, 8, 1))
  n=5 gap=4 (n-1): f(R)==f(P1 x P2')? True   facets(R)=10, 2n=10
  n=5 gap=3 (n-2): facets(R)=10, 2n=10  (R claimed NOT a product; f-vector (1, 23, 85, 151, 159, 105, 43, 10, 1))

done
```
