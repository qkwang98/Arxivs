# Reproduce the exceptional 3-weight calculation for 2.Sp6(2).
# Run GAP with --quitonbreak so that a failed assertion stops the calculation.

if LoadPackage("ctbllib") <> true then
  Error("The CTblLib package is required.");
fi;
if LoadPackage("atlasrep") <> true then
  Error("The AtlasRep package is required.");
fi;

RequireEqual := function(tag, got, expected)
  if got <> expected then
    Error(Concatenation(tag, ": got ", String(got),
                        ", expected ", String(expected)));
  fi;
end;

RequireTrue := function(tag, condition)
  if condition <> true then Error(tag); fi;
end;

DefectZeroAboveCore := function(tbl, p)
  local chars, coreClasses, coreOrder, quotientOrder, quotientPPart;
  chars := Irr(tbl);
  coreClasses := ClassPositionsOfPCore(tbl, p);
  coreOrder := Sum(SizesConjugacyClasses(tbl){coreClasses});
  quotientOrder := Size(tbl) / coreOrder;
  quotientPPart := 1;
  while quotientOrder mod p = 0 do
    quotientPPart := quotientPPart * p;
    quotientOrder := quotientOrder / p;
  od;
  return Filtered([1 .. Length(chars)], i ->
    IsSubset(ClassPositionsOfKernel(chars[i]), coreClasses) and
    chars[i][1] mod quotientPPart = 0);
end;

InducedBlockMatches := function(sourceTable, targetTable, fusion, p,
                                chi, targetBlocks)
  local omega, relevant, matches, b, representative;
  omega := CentralCharacter(targetTable,
    Induced(sourceTable, targetTable, [chi], fusion)[1]);
  relevant := ShallowCopy(targetBlocks.relevant);
  matches := [];
  for b in [1 .. Length(targetBlocks.defect)] do
    representative := Position(targetBlocks.block, b);
    if SameBlock(p, omega,
       CentralCharacter(Irr(targetTable)[representative]), relevant) then
      Add(matches, b);
    fi;
  od;
  return matches;
end;

CheckLocalTable := function(spec, targetTable, targetBlocks,
                            targetZPosition, targetBlockSigns)
  local sourceTable, chars, coreClasses, coreOrder, positions, fusion,
        localZPositions, localZPosition, degrees, signs, matches, assigned,
        i;
  sourceTable := CharacterTable(spec.name);
  if sourceTable = fail then
    Error(Concatenation("The local character table ", spec.name,
                        " is unavailable."));
  fi;
  chars := Irr(sourceTable);
  coreClasses := ClassPositionsOfPCore(sourceTable, 3);
  coreOrder := Sum(SizesConjugacyClasses(sourceTable){coreClasses});
  RequireEqual(Concatenation(spec.name, " normaliser order"),
               Size(sourceTable), spec.normalizerOrder);
  RequireEqual(Concatenation(spec.name, " radical core order"),
               coreOrder, spec.radicalOrder);
  RequireEqual(Concatenation(spec.name, " quotient normaliser order"),
               Size(sourceTable) / coreOrder, spec.quotientOrder);

  positions := DefectZeroAboveCore(sourceTable, 3);
  RequireEqual(Concatenation(spec.name, " defect-zero positions"),
               positions, spec.positions);
  degrees := List(positions, i -> chars[i][1]);
  RequireEqual(Concatenation(spec.name, " defect-zero degrees"),
               degrees, spec.degrees);

  if Identifier(sourceTable) = Identifier(targetTable) then
    fusion := [1 .. NrConjugacyClasses(targetTable)];
  else
    fusion := GetFusionMap(sourceTable, targetTable);
  fi;
  if fusion = fail then
    Error(Concatenation("The fusion from ", spec.name,
                        " to the global table is unavailable."));
  fi;
  localZPositions := Positions(fusion, targetZPosition);
  RequireEqual(Concatenation(spec.name, " central-class preimage count"),
               Length(localZPositions), 1);
  localZPosition := localZPositions[1];
  signs := List(positions,
                i -> chars[i][localZPosition] / chars[i][1]);
  RequireEqual(Concatenation(spec.name, " central signs"),
               signs, spec.signs);

  matches := List(positions, i ->
    InducedBlockMatches(sourceTable, targetTable, fusion, 3,
                        chars[i], targetBlocks));
  RequireTrue(Concatenation(spec.name, " block induction is not unique"),
              ForAll(matches, x -> Length(x) = 1));
  assigned := List(matches, x -> x[1]);
  RequireEqual(Concatenation(spec.name, " induced blocks"),
               assigned, spec.blocks);
  for i in [1 .. Length(assigned)] do
    RequireEqual(Concatenation(spec.name, " central sector at weight ",
                              String(i)),
                 signs[i], targetBlockSigns[assigned[i]]);
  od;
  return assigned;
end;

# Use the first faithful 240-point ATLAS representation singled out by its
# database identifier, so that two representations of the same degree cannot
# be interchanged silently.
atlasInfos := Filtered(AllAtlasGeneratingSetInfos("2.S6(2)"),
  x -> IsBound(x.type) and x.type = "perm" and
       IsBound(x.p) and x.p = 240 and
       IsBound(x.id) and x.id = "a");;
RequireEqual("ATLAS representation count", Length(atlasInfos), 1);
RequireEqual("ATLAS representation name", atlasInfos[1].repname,
             "2S62G1-p240aB0");
G := AtlasGroup(atlasInfos[1].identifier);;
if G = fail then Error("The ATLAS group is unavailable."); fi;
RequireEqual("cover order", Size(G), 2903040);
RequireEqual("permutation degree", NrMovedPoints(G), 240);
RequireEqual("centre order", Size(Centre(G)), 2);
RequireEqual("simple quotient order", Size(G) / Size(Centre(G)), 1451520);
RequireTrue("cover is not perfect", IsPerfectGroup(G));

# Every 3-subgroup is conjugate into P.  We enumerate the P-conjugacy classes
# of subgroups, test Q=O_3(N_G(Q)), and then fuse the surviving classes in G.
P := SylowSubgroup(G, 3);;
RequireEqual("Sylow subgroup order", Size(P), 81);
RequireEqual("Sylow subgroup identifier", IdGroup(P), [81, 7]);
RequireEqual("Sylow subgroup exponent", Exponent(P), 9);
pClasses := ConjugacyClassesSubgroups(P);;
RequireEqual("P-subgroup class count", Length(pClasses), 20);
RequireEqual("P-subgroup class orders",
  Collected(List(pClasses, c -> Size(Representative(c)))),
  [[1, 1], [3, 6], [9, 8], [27, 4], [81, 1]]);

radicalCandidates := [];;
for c in pClasses do
  Q := Representative(c);;
  N := Normalizer(G, Q);;
  if PCore(N, 3) = Q then
    Add(radicalCandidates, rec(Q := Q, N := N));
  fi;
od;
RequireEqual("P-radical candidate count", Length(radicalCandidates), 5);

radicals := [];;
for candidate in radicalCandidates do
  if ForAll(radicals,
            known -> not IsConjugate(G, candidate.Q, known.Q)) then
    Add(radicals, candidate);
  fi;
od;
RequireEqual("G-radical class count including Q=1", Length(radicals), 5);
radicalSignatures := List(radicals, entry ->
  [Size(entry.Q), IdGroup(entry.Q), Size(entry.N),
   Size(entry.N) / Size(entry.Q)]);;
Sort(radicalSignatures);
RequireEqual("radical subgroups and normaliser quotients", radicalSignatures,
  [[1, [1, 1], 2903040, 2903040],
   [3, [3, 1], 8640, 2880],
   [27, [27, 3], 2592, 96],
   [27, [27, 5], 2592, 96],
   [81, [81, 7], 648, 8]]);

ordinaryTable := CharacterTable("2.S6(2)");;
brauerTable := BrauerTable(ordinaryTable, 3);;
if ordinaryTable = fail or brauerTable = fail then
  Error("The ordinary or Brauer character table is unavailable.");
fi;
RequireEqual("ordinary table identifier", Identifier(ordinaryTable),
             "2.S6(2)");
RequireEqual("ordinary table order", Size(ordinaryTable), Size(G));
RequireEqual("Brauer table identifier", Identifier(brauerTable),
             "2.S6(2)mod3");

primeBlocks := PrimeBlocks(ordinaryTable, 3);;
blockInfo := BlocksInfo(brauerTable);;
RequireEqual("block labels", Set(primeBlocks.block), [1, 2, 3, 4, 5]);
RequireEqual("block defects", primeBlocks.defect, [4, 1, 1, 0, 4]);
RequireEqual("Brauer-table block defects",
             List(blockInfo, info -> info.defect), primeBlocks.defect);
RequireEqual("ordinary block partitions agree",
  List([1 .. Length(blockInfo)], b -> blockInfo[b].ordchars),
  List([1 .. Length(blockInfo)], b -> Positions(primeBlocks.block, b)));

# The restrictions of the ordinary characters to the 3-regular classes span
# the Brauer-character spaces block by block.  Computing these ranks does not
# use the installed 3-Brauer table.
regularPositions := Filtered(
  [1 .. NrConjugacyClasses(ordinaryTable)],
  i -> OrdersClassRepresentatives(ordinaryTable)[i] mod 3 <> 0);;
restrictionRanks := List([1 .. Length(blockInfo)], b ->
  RankMat(List(Positions(primeBlocks.block, b), i ->
    Irr(ordinaryTable)[i]{regularPositions})));;
RequireEqual("ordinary restriction ranks in table block order",
             restrictionRanks, [10, 2, 2, 1, 6]);
brauerRanks := List(blockInfo, info -> Length(info.modchars));;
RequireEqual("Brauer ranks in table block order", brauerRanks,
             [10, 2, 2, 1, 6]);
RequireEqual("restriction ranks and installed Brauer ranks",
             restrictionRanks, brauerRanks);
RequireEqual("Brauer characters occur in exactly one block",
             Set(Concatenation(List(blockInfo, info -> info.modchars))),
             [1 .. Length(Irr(brauerTable))]);

centrePositions := ClassPositionsOfCentre(ordinaryTable);;
RequireEqual("ordinary-table centre orders",
             OrdersClassRepresentatives(ordinaryTable){centrePositions},
             [1, 2]);
zPosition := centrePositions[2];;
ordinaryBlockSignSets := List([1 .. Length(blockInfo)], b ->
  Set(List(Positions(primeBlocks.block, b), i ->
    Irr(ordinaryTable)[i][zPosition] / Irr(ordinaryTable)[i][1])));;
RequireEqual("ordinary block central-sign sets", ordinaryBlockSignSets,
             [[1], [1], [1], [1], [-1]]);
blockSigns := List(ordinaryBlockSignSets, signs -> signs[1]);;

brauerFusion := GetFusionMap(brauerTable, ordinaryTable);;
if brauerFusion = fail then
  Error("The fusion from the Brauer table to the ordinary table is unavailable.");
fi;
brauerZPositions := Positions(brauerFusion, zPosition);;
RequireEqual("Brauer-table central-class preimage count",
             Length(brauerZPositions), 1);
brauerZPosition := brauerZPositions[1];;
brauerBlockSignSets := List(blockInfo, info ->
  Set(List(info.modchars, i ->
    Irr(brauerTable)[i][brauerZPosition] / Irr(brauerTable)[i][1])));;
RequireEqual("Brauer block central-sign sets", brauerBlockSignSets,
             ordinaryBlockSignSets);

localSpecs := [
  rec(name := "2.S6(2)",
      radicalOrder := 1, normalizerOrder := 2903040,
      quotientOrder := 2903040,
      positions := [28], degrees := [405], signs := [1], blocks := [4]),
  rec(name := "2.(S3xS6)",
      radicalOrder := 3, normalizerOrder := 8640,
      quotientOrder := 2880,
      positions := [21, 22, 23, 24], degrees := [9, 9, 9, 9],
      signs := [1, 1, 1, 1], blocks := [2, 3, 3, 2]),
  rec(name := "2x3^(1+2)_+:2S4",
      radicalOrder := 27, normalizerOrder := 2592,
      quotientOrder := 96,
      positions := [6, 7, 24, 25], degrees := [3, 3, 3, 3],
      signs := [1, 1, -1, -1], blocks := [1, 1, 5, 5]),
  rec(name := "2.(3^3:(S4x2))",
      radicalOrder := 27, normalizerOrder := 2592,
      quotientOrder := 96,
      positions := [11, 12, 13, 14], degrees := [3, 3, 3, 3],
      signs := [1, 1, 1, 1], blocks := [1, 1, 1, 1]),
  rec(name := "2x3^3:(S3x2)",
      radicalOrder := 81, normalizerOrder := 648,
      quotientOrder := 8,
      positions := [1, 2, 3, 4, 5, 6, 7, 8],
      degrees := [1, 1, 1, 1, 1, 1, 1, 1],
      signs := [1, -1, 1, -1, 1, -1, 1, -1],
      blocks := [1, 5, 1, 5, 1, 5, 1, 5])
];

fusionSources := NamesOfFusionSources(ordinaryTable);;
for spec in localSpecs{[2 .. Length(localSpecs)]} do
  RequireTrue(Concatenation("missing stored fusion for ", spec.name),
              spec.name in fusionSources);
od;

weightCounts := List([1 .. Length(blockInfo)], b -> 0);;
localWeightCounts := [];;
for spec in localSpecs do
  assignedBlocks := CheckLocalTable(spec, ordinaryTable, primeBlocks,
                                    zPosition, blockSigns);;
  Add(localWeightCounts, Length(assignedBlocks));
  for b in assignedBlocks do
    weightCounts[b] := weightCounts[b] + 1;
  od;
od;
RequireEqual("weight counts by radical class", localWeightCounts,
             [1, 4, 4, 4, 8]);
RequireEqual("weight counts in table block order", weightCounts,
             [10, 2, 2, 1, 6]);
RequireEqual("blockwise weight and restriction ranks",
             weightCounts, restrictionRanks);
RequireEqual("blockwise weight and Brauer counts", weightCounts, brauerRanks);

Print("GAP_VERSION=", GAPInfo.Version, "\n");
Print("CTBLLIB_VERSION=", PackageInfo("ctbllib")[1].Version, "\n");
Print("ATLASREP_VERSION=", PackageInfo("atlasrep")[1].Version, "\n");
Print("COVER_ORDER=", Size(G), " CENTRE_ORDER=", Size(Centre(G)),
      " QUOTIENT_ORDER=", Size(G) / Size(Centre(G)), "\n");
Print("RADICAL_SIGNATURES=", radicalSignatures, "\n");
Print("BLOCK_DEFECTS=", primeBlocks.defect, "\n");
Print("BLOCK_CENTRAL_SIGNS=", blockSigns, "\n");
Print("ORDINARY_RESTRICTION_RANKS=", restrictionRanks, "\n");
Print("BRAUER_RANKS=", brauerRanks, "\n");
Print("WEIGHT_COUNTS_BY_RADICAL=", localWeightCounts, "\n");
Print("WEIGHT_COUNTS_BY_BLOCK=", weightCounts, "\n");
Print("Each local character induces to a unique block.\n");
Print("The blockwise counts for 2.Sp6(2) at 3 have the stated values.\n");
QUIT_GAP(0);
