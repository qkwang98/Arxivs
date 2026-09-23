# The two local principal weights of SO7(3) used for Omega7(3).

if LoadPackage("atlasrep") <> true then
  Error("The AtlasRep package is required.");
fi;

WeightQuotient := function(q, h)
  local n, c, qc, k, ct, degrees, pexp, dzdegrees;

  n := Normalizer(h, q);;
  c := Centralizer(h, q);;
  qc := ClosureGroup(q, c);;
  if Size(PCore(n, 2)) <> Size(q) then
    Error("The subgroup is not radical in H.");
  fi;
  # Centre(q) is contained in C_H(q), so equal order is equality.
  if Size(c) <> Size(Centre(q)) then
    Error("The centraliser does not have the required Sylow 2-subgroup.");
  fi;
  if Size(qc) <> Size(q) then
    Error("The equality Q*C_H(Q)=Q does not hold.");
  fi;
  if not IsNormal(n, qc) then
    Error("The subgroup Q*C_H(Q) is not normal in N_H(Q).");
  fi;

  k := FactorGroup(n, qc);;
  ct := CharacterTable(k);;
  degrees := List(Irr(ct), chi -> chi[1]);;
  pexp := Valuation(Size(k), 2);;
  dzdegrees := Filtered(degrees, d -> Valuation(d, 2) = pexp);;
  if Length(dzdegrees) <> 1 then
    Error("The quotient should have exactly one defect-zero character.");
  fi;
  return rec(
    qsize := Size(q),
    nsize := Size(n),
    csize := Size(c),
    zsize := Size(Centre(q)),
    qcsize := Size(qc),
    ksize := Size(k),
    kstructure := StructureDescription(k),
    degrees := degrees,
    twopart := 2 ^ pexp,
    dzdegrees := dzdegrees,
    dzcount := Length(dzdegrees)
  );
end;;

ScanSlice := function(s, h, iso, pp, targetOrder, expectedCentricCount)
  local classes, candidates, retained, sradical, qpc, q, ns, nh, os, oh;

  classes := ConjugacyClassesSubgroups(pp);;
  candidates := Filtered(List(classes, Representative),
    q -> Size(q) = targetOrder and
         Size(Centralizer(pp, q)) = Size(Centre(q)));;
  if Length(candidates) <> expectedCentricCount then
    Error("The number of P-centric subgroups of the specified order is unexpected.");
  fi;
  retained := [];;
  sradical := 0;;
  for qpc in candidates do
    q := PreImage(iso, qpc);;
    if not IsSubgroup(s, q) then
      Error("The subgroup is not contained in S.");
    fi;
    ns := Normalizer(s, q);;
    nh := Normalizer(h, q);;
    os := PCore(ns, 2);;
    oh := PCore(nh, 2);;
    if Size(os) = Size(q) then
      sradical := sradical + 1;
    fi;
    if Size(oh) = Size(q) then
      if Size(os) <> Size(q) then
        Error("A subgroup radical in H is not radical in S.");
      fi;
      Add(retained, q);
    fi;
  od;
  return rec(
    centricCount := Length(candidates),
    sradicalCount := sradical,
    hradicalCount := Length(retained),
    retained := retained
  );
end;;

h := AtlasGroup("O7(3).2", IsPermGroup, true, NrMovedPoints, 351);;
s := DerivedSubgroup(h);;
if not IsNormal(h, s) or Size(h) <> 2 * Size(s) then
  Error("The ATLAS action does not give the required index-two pair.");
fi;
p := SylowSubgroup(s, 2);;
iso := IsomorphismPcGroup(p);;
pp := Image(iso);;

slice128 := ScanSlice(s, h, iso, pp, 128, 53);;
slice256 := ScanSlice(s, h, iso, pp, 256, 15);;
if slice128.hradicalCount <> 1 or slice256.hradicalCount <> 1 then
  Error("There should be one H-class of radical subgroups of each specified order.");
fi;

weight128 := WeightQuotient(slice128.retained[1], h);;
weight256 := WeightQuotient(slice256.retained[1], h);;
if weight128.ksize <> 216 or weight128.dzdegrees <> [ 8 ] then
  Error("The weight quotient for the subgroup of order 128 is unexpected.");
fi;
if weight256.ksize <> 36 or weight256.dzdegrees <> [ 4 ] then
  Error("The weight quotient for the subgroup of order 256 is unexpected.");
fi;

Print("GAP_VERSION=", GAPInfo.Version, "\n");;
Print("ATLASREP_VERSION=", PackageInfo("atlasrep")[1].Version, "\n");;
Print("H_ORDER=", Size(h), "\n");;
Print("S_ORDER=", Size(s), "\n");;
Print("H_OVER_S=", Size(h) / Size(s), "\n");;
Print("H_CENTRE_ORDER=", Size(Centre(h)), "\n");;
Print("S_SYL2_ORDER=", Size(p), "\n");;
Print("P_CENTRIC_ORDER128_COUNT=", slice128.centricCount, "\n");;
Print("P_CENTRIC_ORDER128_S_RADICAL_COUNT=", slice128.sradicalCount, "\n");;
Print("P_CENTRIC_ORDER128_H_RADICAL_COUNT=", slice128.hradicalCount, "\n");;
Print("ORDER128_NH=", weight128.nsize, "\n");;
Print("ORDER128_CH=", weight128.csize, "\n");;
Print("ORDER128_ZQ=", weight128.zsize, "\n");;
Print("ORDER128_WEIGHT_QUOTIENT=", weight128.ksize, "\n");;
Print("ORDER128_WEIGHT_QUOTIENT_STRUCTURE=", weight128.kstructure, "\n");;
Print("ORDER128_DEFECT_ZERO_DEGREES=", weight128.dzdegrees, "\n");;
Print("P_CENTRIC_ORDER256_COUNT=", slice256.centricCount, "\n");;
Print("P_CENTRIC_ORDER256_S_RADICAL_COUNT=", slice256.sradicalCount, "\n");;
Print("P_CENTRIC_ORDER256_H_RADICAL_COUNT=", slice256.hradicalCount, "\n");;
Print("ORDER256_NH=", weight256.nsize, "\n");;
Print("ORDER256_CH=", weight256.csize, "\n");;
Print("ORDER256_ZQ=", weight256.zsize, "\n");;
Print("ORDER256_WEIGHT_QUOTIENT=", weight256.ksize, "\n");;
Print("ORDER256_WEIGHT_QUOTIENT_STRUCTURE=", weight256.kstructure, "\n");;
Print("ORDER256_DEFECT_ZERO_DEGREES=", weight256.dzdegrees, "\n");;
Print("LOCAL_PRINCIPAL_H_WEIGHT_COUNT=", weight128.dzcount + weight256.dzcount, "\n");;
Print("The two relevant local principal weights have the stated quotients.\n");;
QUIT_GAP(0);
