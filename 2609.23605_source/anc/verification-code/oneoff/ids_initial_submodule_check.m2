-- ids_initial_submodule_check.m2
--
-- Changelog (reverse chronological):
--   2026-09-05  Created.  Checks the proposition added to article draft 3 section 5
--               (and to working-notes/ids-modules-direct-sums-of-graded-ideals.org):
--               for an ids-module M = I_1 g_1 (+) ... (+) I_r g_r, the initial
--               submodule is computed COMPONENTWISE,
--                   in(M) = in(I_1) g_1 (+) ... (+) in(I_r) g_r,
--               and in(M) is proper (an Amata-Crupi monomial submodule) if and only
--               if M is.  Amata-Crupi's own reduction only says in(M) is *some*
--               monomial submodule; this says which one.
--
--               Two cases: both I_i non-monomial and proper (expect proper in(M)),
--               and one I_i with a degree-1 minimal generator (expect in(M) monomial
--               but NOT proper).
--
-- Run:  M2 --script code/oneoff/ids_initial_submodule_check.m2

needsPackage "ExteriorModules";

-- ExteriorModules gotcha: hilbertSequence takes the SUBMODULE, not the quotient;
-- and E^{d} puts the free generator in degree -d, so generator degrees (0,1)
-- means F = E^{0,-1}.

checkIds = (label, F, G, mat, gensList) -> (
    M := image map(F, G, mat);
    inM := initialModule M;
    J := getIdeals inM;
    sep := apply(gensList, gs -> ideal mingens ideal leadTerm gens gb ideal gs);
    print("=== " | label);
    print("  H(F/M)                    = ", hilbertSequence M);
    print("  H(F/in M)                 = ", hilbertSequence inM);
    print("  ideals of in(M)           = ", J);
    print("  in(I_i) computed alone    = ", sep);
    print("  componentwise equal?      = ", apply(#sep, i -> J#i == sep#i));
    print("  is in(M) a monomial mod?  = ", isMonomialModule inM);
    print("  least gen degree of in(I_i) = ",
          apply(#sep, i -> min flatten degrees source mingens J#i));
    );

E = QQ[e_1..e_4, SkewCommutative=>true];

-- Case 1: both components non-monomial and proper (no minimal generator of degree <= 1).
checkIds("proper: I_1 = (e1e2+e3e4), I_2 = (e1e2e3+e2e3e4, e1e4), d = (0,1)",
      E^{0,-1}, E^{-2,-3,-2},
      matrix {{e_1*e_2+e_3*e_4, 0,                       0      },
              {0,               e_1*e_2*e_3+e_2*e_3*e_4, e_1*e_4}},
      {{e_1*e_2+e_3*e_4}, {e_1*e_2*e_3+e_2*e_3*e_4, e_1*e_4}});

-- Case 2: I_2 has a degree-1 minimal generator, so M is NOT proper.  in(M) must be
-- monomial but must also fail properness -- properness is preserved in BOTH directions.
checkIds("not proper: I_2 = (e_1 + e_2, ...), d = (0,1)",
      E^{0,-1}, E^{-2,-1},
      matrix {{e_1*e_2+e_3*e_4, 0        },
              {0,               e_1+e_2  }},
      {{e_1*e_2+e_3*e_4}, {e_1+e_2}});
