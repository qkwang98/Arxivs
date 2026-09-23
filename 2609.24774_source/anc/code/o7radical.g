# Radical subgroups and weight counts for 3.O7(3) at 2.

if LoadPackage("atlasrep") <> true then
  Error("The AtlasRep package is required.");
fi;
if LoadPackage("ctbllib") <> true then
  Error("The CTblLib package is required.");
fi;

Main := function()
  local G, P, z, cls, radicals, greps, i, j, Q, N, O, seen,
        epi, W, wz, ccls, zpos, tbl, irr, dz1, dzomega, dzomega2,
        chi, ratio, targetv, contributions, key, entry, totals;

  Print("GAP_VERSION=", GAPInfo.Version, "\n");
  Print("ATLASREP_VERSION=", PackageInfo("atlasrep")[1].Version, "\n");
  Print("CTBLLIB_VERSION=", PackageInfo("ctbllib")[1].Version, "\n");

  G := AtlasGroup("3.O7(3)", IsPermGroup, true);
  P := SylowSubgroup(G, 2);
  z := GeneratorsOfGroup(Centre(G))[1];
  cls := ConjugacyClassesSubgroups(P);
  Print("X_SIZE=", Size(G), "\n");
  Print("X_DEGREE=", LargestMovedPoint(G), "\n");
  Print("CENTRE_SIZE=", Size(Centre(G)), "\n");
  Print("SYLOW2_SIZE=", Size(P), "\n");
  Print("SYLOW2_STRUCTURE=", StructureDescription(P), "\n");
  Print("P_SUBGROUP_CLASS_COUNT=", Length(cls), "\n");
  if Length(cls) <> 3021 then
    Error("The Sylow subgroup should have 3021 conjugacy classes of subgroups.");
  fi;
  Print("P_SUBGROUP_ORDER_DISTRIBUTION=",
        Collected(List(cls, c -> Size(Representative(c)))), "\n");

  radicals := [];
  for i in [1..Length(cls)] do
    Q := Representative(cls[i]);
    N := Normalizer(G, Q);
    O := PCore(N, 2);
    if Size(O) = Size(Q) and IsSubgroup(Q, O) then
      Add(radicals, rec(pclass := i, subgroup := Q, normalizer := N));
      Print("P_RADICAL|pclass=", i, "|qsize=", Size(Q),
            "|nsize=", Size(N), "\n");
    fi;
    if i mod 100 = 0 then Print("PROGRESS=", i, "/", Length(cls), "\n"); fi;
  od;
  Print("P_RADICAL_COUNT=", Length(radicals), "\n");
  if Length(radicals) <> 26 then
    Error("The Sylow subgroup calculation should produce 26 radical subgroups.");
  fi;

  greps := [];
  for i in [1..Length(radicals)] do
    seen := false;
    for j in [1..Length(greps)] do
      if IsConjugate(G, radicals[i].subgroup, greps[j].subgroup) then
        Print("G_FUSION|pclass=", radicals[i].pclass,
              "|representative=", greps[j].pclass, "\n");
        seen := true;
        break;
      fi;
    od;
    if not seen then Add(greps, radicals[i]); fi;
  od;
  Print("G_RADICAL_CLASS_COUNT=", Length(greps), "\n");
  if Length(greps) <> 12 then
    Error("Fusion in the covering group should leave 12 radical classes.");
  fi;

  contributions := [];
  totals := [0, 0, 0];
  for i in [1..Length(greps)] do
    Q := greps[i].subgroup;
    N := greps[i].normalizer;
    dz1 := [];
    dzomega := [];
    dzomega2 := [];
    if Size(Q) = 1 then
      tbl := CharacterTable("3.O7(3)");
      zpos := ClassPositionsOfCenter(tbl)[2];
      irr := Irr(tbl);
      targetv := PValuation(Size(tbl), 2);
      for j in [1..Length(irr)] do
        chi := irr[j];
        if PValuation(chi[1], 2) = targetv then
          ratio := chi[zpos] / chi[1];
          if ratio = 1 then Add(dz1, j);
          elif ratio = E(3) then Add(dzomega, j);
          elif ratio = E(3)^2 then Add(dzomega2, j);
          else Error("The central scalar at Q=1 is unexpected.");
          fi;
        fi;
      od;
      Print("G_RADICAL|pclass=", greps[i].pclass,
            "|qsize=1|qstructure=1|nsize=", Size(N),
            "|wsize=", Size(G), "|wstructure=3.O7(3)",
            "|dz_z1=", dz1, "|dz_omega=", dzomega,
            "|dz_omega2=", dzomega2, "\n");
    else
      epi := NaturalHomomorphismByNormalSubgroup(N, Q);
      W := Image(epi);
      wz := Image(epi, z);
      ccls := ConjugacyClasses(W);
      zpos := PositionProperty(ccls, c -> wz in c);
      tbl := CharacterTable(W);
      irr := Irr(tbl);
      targetv := PValuation(Size(W), 2);
      for j in [1..Length(irr)] do
        chi := irr[j];
        if PValuation(chi[1], 2) = targetv then
          ratio := chi[zpos] / chi[1];
          if ratio = 1 then Add(dz1, j);
          elif ratio = E(3) then Add(dzomega, j);
          elif ratio = E(3)^2 then Add(dzomega2, j);
          else Error("The central scalar is unexpected.");
          fi;
        fi;
      od;
      Print("G_RADICAL|pclass=", greps[i].pclass,
            "|qsize=", Size(Q), "|qstructure=", StructureDescription(Q),
            "|nsize=", Size(N), "|wsize=", Size(W),
            "|wstructure=", StructureDescription(W),
            "|dz_z1=", dz1, "|dz_omega=", dzomega,
            "|dz_omega2=", dzomega2, "\n");
    fi;
    totals := totals + [Length(dz1), Length(dzomega), Length(dzomega2)];
    key := Size(Q);
    entry := First(contributions, r -> r[1] = key);
    if entry = fail then
      Add(contributions,
          [key, Length(dz1), Length(dzomega), Length(dzomega2)]);
    else
      entry[2] := entry[2] + Length(dz1);
      entry[3] := entry[3] + Length(dzomega);
      entry[4] := entry[4] + Length(dzomega2);
    fi;
  od;
  SortBy(contributions, r -> -r[1]);
  Print("ORDER_CONTRIBUTIONS_[QSIZE,Z1,OMEGA,OMEGA2]=", contributions, "\n");
  Print("TOTAL_WEIGHT_COUNTS_[Z1,OMEGA,OMEGA2]=", totals, "\n");
  if totals <> [17, 8, 8] then
    Error("The central character weight totals should be [17,8,8].");
  fi;
  Print("The central-character weight totals are [17,8,8].\n");
end;

Main();
QUIT_GAP(0);
