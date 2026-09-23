-- Changelog (reverse chronological):
-- 2026-08-07 - Claude: created as a companion to code/oneoff/check_good_vs_propergood.m2, to
--   check that its conclusion (in(M) forced improper for the g_1+g_2 example, forced proper for
--   the x_1x_2(g_1+g_2) example) is not an artifact of M2's default position order. Recomputes
--   both examples with generator priority reversed (MonomialOrder=>{Position=>Down}). Result:
--   the labels swap (which generator survives/dies, or which carries the (x_1x_2) ideal) but the
--   property itself (improper / proper) does not change -- confirms the phenomenon is a genuine
--   term-order-independent fact about M, not a POT-choice artifact. See
--   artefacts/proper-hilbert-functions-kozlov-minkowski.org for the theorem this supports.
needsPackage "ExteriorModules"
E = QQ[x_2,x_1, SkewCommutative=>true]  -- reversed variable order, shouldn't matter
F = E^{0,0}
Erev = QQ[x_1,x_2, MonomialOrder=>{Position=>Down}, SkewCommutative=>true]
Frev = Erev^{0,0}

-- reversed generator priority via Position=>Down on the free module presentation:
phiA = map(Frev, Erev^1, matrix{{1_Erev},{1_Erev}})
MA = image phiA
print ("A rev: H = ", hilbertSequence MA, " ideals = ", getIdeals initialModule MA)

phiB = map(Frev, Erev^1, matrix{{x_1*x_2},{x_1*x_2}})
MB = image phiB
print ("B rev: H = ", hilbertSequence MB, " ideals = ", getIdeals initialModule MB)
