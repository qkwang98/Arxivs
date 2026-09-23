-- Changelog (reverse chronological):
-- 2026-08-02 - Claude: created. Verifies (a corrected reading of) Conjecture
--   6.2 of Snellman & Moreno-Socias, "Some conjectures about the Hilbert
--   series of generic ideals in the exterior algebra" (arXiv:math/0007089,
--   also published in Experimental Mathematics -- see
--   ../literature/REFERENCES.md), for the case n=7, d=3 (generic cubic
--   form). See ../LOGBOOK.md's 2026-08-02 entry for the full story,
--   including a notational bug found in the paper (both the arXiv and the
--   published version): Conjecture 6.2's formula is labeled p_{n,3}(t)
--   (elsewhere the paper's own symbol for the Hilbert series of the IDEAL
--   (f)) but its prose and its actual value only make sense as q_{n,3}(t)
--   (the Hilbert series of the QUOTIENT \bigwedge V_n/(f)) -- confirmed
--   here by direct computation, not just by re-reading the text.

kk = ZZ/31991  -- same characteristic the original paper's authors used
R = kk[e_1..e_7, SkewCommutative => true]

-- Conjectured value (reading Conjecture 6.2's formula as q_{7,3}(t), the
-- quotient's Hilbert series -- see the LOGBOOK entry for the derivation):
--   q_{7,3}(t) = 1 + 7t + 21t^2 + 34t^3 + 28t^4   (zero above degree 4)
conjectured = {1, 7, 21, 34, 28, 0, 0, 0}

print "Checking across 5 independent random cubics (random seeds 1..5):"
allMatch = true
for seed in {1,2,3,4,5} do (
  setRandomSeed seed;
  f = random(3,R);
  Q = R^1/(ideal f);
  hf := for i from 0 to 7 list hilbertFunction(i, Q);
  ok := hf === conjectured;
  allMatch = allMatch and ok;
  print (seed, hf, ok)
)
print ("All seeds match conjectured q_{7,3}(t): " | toString allMatch)
exit
