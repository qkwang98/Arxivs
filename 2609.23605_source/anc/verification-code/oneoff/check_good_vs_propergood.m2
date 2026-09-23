-- Changelog (reverse chronological):
-- 2026-08-07 - Claude: created, per Jan's question "is in(M) of a 'good'/'proper good'
--   submodule itself Amata-Crupi?" (see artefacts/proper-hilbert-functions-kozlov-minkowski.org,
--   subsection right after the Prop 2.4 remark, for the full theorem this supports). Computes
--   in(M) for two n=2, r=2, d=(0,0) examples: (A) M=E.(g_1+g_2), the standing "good but not
--   proper good" counterexample (no proper N can match its Hilbert function at all); (B)
--   M=E.(x_1x_2 g_1 + x_1x_2 g_2), a genuinely non-monomial "proper good" witness. Confirms by
--   direct computation that in(M) is forced improper in case A and comes out proper in case B --
--   see code/oneoff/check_reversed_order.m2 for the companion check that this doesn't depend on
--   which of the two position orders is used.
needsPackage "ExteriorModules"
E = QQ[x_1,x_2, SkewCommutative=>true]
F = E^{0,0}

-- (A) the "good but not proper good" example: M = E.(g_1+g_2)
phiA = map(F, E^1, matrix{{1_E},{1_E}})
MA = image phiA
print ("A: H_{F/M} = ", hilbertSequence MA)
inMA = initialModule MA
print ("A: getIdeals(in(M)) = ", getIdeals inMA)

-- (B) a "proper good but not itself monomial" example: M = E.(x_1x_2 g_1 + x_1x_2 g_2)
phiB = map(F, E^1, matrix{{x_1*x_2},{x_1*x_2}})
MB = image phiB
print ("B: H_{F/M} = ", hilbertSequence MB)
inMB = initialModule MB
print ("B: getIdeals(in(M)) = ", getIdeals inMB)
