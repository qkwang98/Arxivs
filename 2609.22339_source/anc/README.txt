Ancillary files for: D. Wachs, "A note on a recent claimed proof of the irrationality of Catalan's constant" (2026).

All scripts: Python 3 (standard library + mpmath). Run from this directory.
  sun_lib.py        exact construction of the residual matrix R (entries alpha + beta*G, alpha,beta in Q),
                    exact S x S minors as polynomials in G (fraction-free elimination + Lagrange interpolation).
  sun_rank.py       Proposition 2.1: all minors nonzero and coprime for S<=4, B<=30 (prints degree of gcd = 0).
  sun_final.py      Theorem 3.3 / Table 1: exact H_B, |q_hat_B(G)| with rounding bound, all row sets A.
                    Output: sun_final.out, sun_final.json (about 40 minutes; B=119 alone ~12 min). Its B-list starts at 21:
                    run sun_add20.py afterwards to append the B=20 row before make_table.py.
  sun_add20.py      adds the B=20 row to sun_final.json (same procedure).
  sun_gcd.py        Lemma 3.2 certificate: explicit coprime (a,q) with small gcd(H_B, Phi(a,q)). Output: sun_gcd.out/json.
  sun_sec5.py       Proposition 3.4: the paper's Section 5 definitions implemented literally; checks (5.13), Lemma 5.3
                    prime by prime, and evaluates the bound (5.24) exactly at B=20,21,25,30,40. Output: sun_sec5.json.
  sun_ranges.py     Section 3.4: exact layers m^A_{Q,B}, a_{Q,B} by prime range (greedy (7.6) checked vs brute force for S<=3).
  sun_detsize.py    Section 3.4: identity (5) and Table 3 (size of det R[A,J](G) vs the bound implied by Prop. 9.5).
  sun_checks_extra.py  (7.6) vs brute force for S=4,5; the layers m_p=-2S on N<p<=2N+1-2S and the 39/200 identification.
  sun_validate.py   direct N x N determinant det A_B at 400 digits vs formula (3.5); precision repeat at B=21;
                    interval-arithmetic (mpmath.iv) enclosure of q_hat_B(G) at B=21,40,100,119 (needs sun_final.json).
  make_table.py     regenerates table_main.tex from the two JSON files.
  sun_catalan.txt   text extraction of arXiv:2609.04176v1 (HTML rendering) used for the definitions.

EXECUTION ORDER (full reproduction from scratch; delete the .json/.out files first):
  1. python sun_rank.py            (~1 min)   -> Proposition 2.1
  2. python sun_final.py           (~40 min)  -> sun_final.json / sun_final.out (B = 21..119)
  3. python sun_add20.py           (~5 s)     -> appends the B = 20 row to sun_final.json
  4. python sun_gcd.py             (~1 min)   -> sun_gcd.json / sun_gcd.out (Lemma 3.2 witnesses)
  5. python make_table.py                     -> table_main.tex (Table 1)
  6. python sun_ranges.py          (~2 min)   -> sun_ranges.json (layers by prime range)
  7. python sun_detsize.py         (~1 s)     -> sun_detsize.json (identity (5), Table 3)
  8. python sun_sec5.py            (~3 min)   -> sun_sec5.json (Lemma 5.3 / (5.24), Table 2)
  9. python sun_validate.py        (~2 min)   -> formula (3.5) vs direct determinant; interval enclosures
 10. python sun_checks_extra.py    (~2 min)   -> (7.6) brute force for S=4,5; the -2S layers
Environment used for the shipped outputs: Python 3.11 and 3.14 (CPython), mpmath 1.3.0 (macOS). All algebra is exact (fractions);
mpmath is used only for the evaluation of q_hat_B(G) with a stated rounding bound and, in sun_validate.py, for
interval-arithmetic (mpmath.iv) enclosures with outward rounding.
