# Blocks, central characters, and outer actions for Fi'24 and 3.Fi'24.

if LoadPackage("ctbllib") <> true then
  Error("The CTblLib package is required.");
fi;
SizeScreen([4096,4096]);;

RequireEqual := function(tag, got, expected)
  if got <> expected then
    Error(Concatenation(tag, ": got ", String(got), ", expected ", String(expected)));
  fi;
end;

PermutationFromOuterFusion := function(fusion)
  local permutation, i, fibre;
  permutation := [];
  for i in [1..Length(fusion)] do
    fibre := Positions(fusion, fusion[i]);
    if Length(fibre) = 1 then
      permutation[i] := i;
    elif Length(fibre) = 2 then
      permutation[i] := First(fibre, j -> j <> i);
    else
      Error("An outer fusion fibre has neither one nor two elements.");
    fi;
  od;
  RequireEqual("outer permutation involutory", permutation{permutation},
               [1..Length(permutation)]);
  return permutation;
end;

OuterPermutation := function(inner, outer)
  local fusions, permutations;
  fusions := PossibleClassFusions(inner, outer);
  if IsEmpty(fusions) then
    Error("No possible fusion into the outer extension was found.");
  fi;
  permutations := List(fusions, PermutationFromOuterFusion);
  RequireEqual("outer action independent of fusion",
               Length(Set(permutations)), 1);
  Print("OUTER_FUSIONS pair=", Identifier(inner), " -> ", Identifier(outer),
        " possible=", Length(fusions), " distinct_actions=1\n");
  return permutations[1];
end;

DefectZeroAboveCore := function(tbl, p)
  local order, quotientPPart, coreClasses, coreOrder;
  order := Size(tbl);
  quotientPPart := 1;
  while order mod p = 0 do
    quotientPPart := quotientPPart*p;
    order := order/p;
  od;
  coreClasses := ClassPositionsOfPCore(tbl, p);
  coreOrder := Sum(SizesConjugacyClasses(tbl){coreClasses});
  quotientPPart := quotientPPart/coreOrder;
  return Filtered([1..Length(Irr(tbl))], i ->
    IsSubset(ClassPositionsOfKernel(Irr(tbl)[i]), coreClasses) and
    Irr(tbl)[i][1] mod quotientPPart = 0);
end;

MatchingBlocks := function(localTable, globalTable, p, chi, fusion)
  local omega, blocks, relevant, matches, b;
  omega := CentralCharacter(globalTable,
                            Induced(localTable, globalTable, [chi], fusion)[1]);
  blocks := PrimeBlocks(globalTable, p);
  relevant := ShallowCopy(blocks.relevant);
  matches := [];
  for b in [1..Length(blocks.defect)] do
    if SameBlock(p, omega,
       CentralCharacter(Irr(globalTable)[Position(blocks.block, b)]), relevant) then
      Add(matches, b);
    fi;
  od;
  return matches;
end;

BlockAssignments := function(localTable, globalTable, p, positions, fusion)
  local matches;
  matches := List(positions, i ->
    MatchingBlocks(localTable, globalTable, p, Irr(localTable)[i], fusion));
  if ForAny(matches, x -> Length(x) <> 1) then
    Error("An induced central character does not determine a unique block.");
  fi;
  return List(matches, x -> x[1]);
end;

CheckBlocks := function(label, innerName, outerName, p, expectedDefects,
                        expectedSelected)
  local t, tout, classperm, orders, preg, pregperm, blocks, irr, irrperm,
        ids, imageBlocks, rows, basis, n, plusRows, plusRank, fixed,
        freeOrbits, b, ratios, c, selected, expected;
  t := CharacterTable(innerName);
  tout := CharacterTable(outerName);
  classperm := OuterPermutation(t, tout);
  orders := OrdersClassRepresentatives(t);
  preg := Filtered([1..Length(orders)], i -> orders[i] mod p <> 0);
  pregperm := List(preg, i -> Position(preg, classperm[i]));
  if fail in pregperm then
    Error("The set of p-regular conjugacy classes is not invariant.");
  fi;
  blocks := PrimeBlocks(t, p);
  irr := Irr(t);
  irrperm := List(irr, chi -> Position(irr, chi{classperm}));
  if fail in irrperm then
    Error("An ordinary character has no image in the stored table.");
  fi;
  RequireEqual(Concatenation(label, " block count"), Length(blocks.defect),
               Sum(expectedDefects, row -> row[2]));
  RequireEqual(Concatenation(label, " defect distribution"),
               Collected(blocks.defect), expectedDefects);
  selected := List(expectedSelected, row -> row[1]);
  Print("BLOCK_DATA label=", label, " p=", p, " carrier=", innerName,
        " blocks=", Length(blocks.defect), " defects=", Collected(blocks.defect), "\n");
  for b in selected do
    expected := First(expectedSelected, row -> row[1] = b);
    ids := Positions(blocks.block, b);
    if Length(ids) = 0 then Error("The selected block is empty."); fi;
    imageBlocks := Set(List(ids, i -> blocks.block[irrperm[i]]));
    RequireEqual("unique outer block image", Length(imageBlocks), 1);
    rows := List(ids, i -> irr[i]{preg});
    basis := BaseMat(rows);
    n := Length(basis);
    if imageBlocks[1] = b then
      plusRows := List(basis, row -> row + row{pregperm});
      plusRank := RankMat(plusRows);
      fixed := 2*plusRank-n;
      freeOrbits := (n-fixed)/2;
    else
      fixed := "NA_SWAPPED";
      freeOrbits := "NA_SWAPPED";
    fi;
    ratios := List(ClassPositionsOfCentre(t), c -> irr[ids[1]][c]/irr[ids[1]][1]);
    RequireEqual(Concatenation(label, " block ", String(b), " defect"),
                 blocks.defect[b], expected[2]);
    RequireEqual(Concatenation(label, " block ", String(b), " outer image"),
                 imageBlocks[1], expected[3]);
    RequireEqual(Concatenation(label, " block ", String(b), " Brauer rank"),
                 n, expected[4]);
    RequireEqual(Concatenation(label, " block ", String(b), " fixed count"),
                 fixed, expected[5]);
    RequireEqual(Concatenation(label, " block ", String(b), " free orbit count"),
                 freeOrbits, expected[6]);
    RequireEqual(Concatenation(label, " block ", String(b), " central signature"),
                 ratios, expected[7]);
    Print("BLOCK label=", label, " p=", p, " id=", b, " defect=", blocks.defect[b],
          " outer=", imageBlocks[1], " l=", n, " fixed=", fixed,
          " free2=", freeOrbits, " centre=", ratios, "\n");
  od;
end;

s := CharacterTable("F3+");;
cover := CharacterTable("3.F3+");;
RequireEqual("cover degree", Size(cover), 3*Size(s));
primes := Set(FactorsInt(Size(s)));
RequireEqual("prime support", primes, [2,3,5,7,11,13,17,23,29]);
RequireEqual("GAP version", GAPInfo.Version, "4.16.0");
RequireEqual("CTblLib version", PackageInfo("ctbllib")[1].Version, "1.3.11");

Print("GAP_VERSION=", GAPInfo.Version, "\n");
Print("CTBLLIB_VERSION=", PackageInfo("ctbllib")[1].Version, "\n");
Print("ORDER_SIMPLE=", Size(s), "\n");
Print("ORDER_COVER=", Size(cover), "\n");
Print("PRIME_SUPPORT=", primes, "\n");
for p in primes do
  if p = 3 then carrier := "F3+"; centre := 1;
  else carrier := "3.F3+"; centre := 3; fi;
  Print("CARRIER p=", p, " table=", carrier, " centre=", centre, "\n");
od;

trivialCentre := [1,1,1];;
faithfulCentre := [1,E(3),E(3)^2];;
conjugateCentre := [1,E(3)^2,E(3)];;
swapped := "NA_SWAPPED";;

CheckBlocks("P2", "3.F3+", "3.F3+.2", 2,
  [[0,2],[2,1],[3,3],[21,3]],
  [[1,21,1,33,25,4,trivialCentre],
   [2,2,2,3,1,1,trivialCentre],
   [3,3,3,3,3,0,trivialCentre],
   [4,0,4,1,1,0,trivialCentre],
   [5,0,5,1,1,0,trivialCentre],
   [6,21,7,23,swapped,swapped,faithfulCentre],
   [7,21,6,23,swapped,swapped,conjugateCentre],
   [8,3,9,2,swapped,swapped,faithfulCentre],
   [9,3,8,2,swapped,swapped,conjugateCentre]]);
CheckBlocks("P3", "F3+", "F3+.2", 3,
  [[0,1],[2,1],[16,1]],
  [[1,16,1,25,25,0,[1]],
   [2,2,2,4,2,1,[1]],
   [3,0,3,1,1,0,[1]]]);

# CTblLib maximal-table metadata only; this does not construct an inclusion.
p3maximalSubgroupNames := Maxes(s);;
p3maximalSubgroupPositions := Positions(
  p3maximalSubgroupNames, "(3^2:2xG2(3)).2");;
RequireEqual("p3 maximal-subgroup expected identifier positions",
  p3maximalSubgroupPositions, [17]);
p3maximalSubgroupPosition := p3maximalSubgroupPositions[1];;
p3maximalSubgroupIdentifier :=
  p3maximalSubgroupNames[p3maximalSubgroupPosition];;
RequireEqual("p3 maximal-subgroup entry identifier",
  p3maximalSubgroupIdentifier, "(3^2:2xG2(3)).2");
p3local := CharacterTable(p3maximalSubgroupIdentifier);;
RequireEqual("p3 loaded maximal-subgroup table identifier",
  Identifier(p3local), p3maximalSubgroupIdentifier);
Print("P3_LOCAL_MAXIMAL_SUBGROUP_POSITION=",
      p3maximalSubgroupPosition, "\n");
p3core := ClassPositionsOfPCore(p3local, 3);;
p3quotient := CharacterTableFactorGroup(p3local, p3core);;
p3fusion := GetFusionMap(p3local, p3quotient);;
p3quotientBlocks := PrimeBlocks(p3quotient, 3);;
p3rows := Filtered([1..Length(Irr(p3quotient))],
  i -> p3quotientBlocks.defect[p3quotientBlocks.block[i]] = 0);;
p3degrees := List(p3rows, i -> Irr(p3quotient)[i][1]);;
p3localRows := List(p3rows,
  i -> Position(Irr(p3local), Irr(p3quotient)[i]{p3fusion}));;
p3localBlocks := PrimeBlocks(p3local, 3);;
p3brauer := BrauerTable(p3local, 3);;
p3decomposition := DecompositionMatrix(p3brauer);;
p3brauerRows := List(p3localRows,
  i -> Position(p3decomposition[i], 1));;
p3decompositionSupports := List(p3localRows, i ->
  Filtered([1..Length(p3decomposition[i])],
    j -> p3decomposition[i][j] <> 0));;
p3decompositionCoefficients := List(p3localRows, i ->
  Filtered(p3decomposition[i], x -> x <> 0));;
p3certificate := List([1..Length(p3rows)], i ->
  [p3rows[i], p3degrees[i], p3quotientBlocks.block[p3rows[i]],
   p3localRows[i], p3localBlocks.block[p3localRows[i]],
   p3brauerRows[i]]);;
RequireEqual("p3 local normalizer order", Size(p3local), 152845056);
RequireEqual("p3 radical core classes", p3core, [1,18,41]);
RequireEqual("p3 radical core class sizes",
  SizesConjugacyClasses(p3local){p3core}, [1,4,4]);
RequireEqual("p3 normalizer quotient order", Size(p3quotient), 16982784);
RequireEqual("p3 quotient block defects",
  p3quotientBlocks.defect, [6,0,0,6,0,0]);
RequireEqual("p3 quotient defect-zero rows", p3rows, [23,24,51,52]);
RequireEqual("p3 quotient defect-zero degrees",
  p3degrees, [729,729,729,729]);
RequireEqual("p3 quotient block identifiers",
  List(p3rows, i -> p3quotientBlocks.block[i]), [2,3,5,6]);
RequireEqual("p3 local block defects", p3localBlocks.defect, [8,2]);
RequireEqual("p3 inflated local rows", p3localRows, [23,24,51,52]);
RequireEqual("p3 inflated local block identifiers",
  List(p3localRows, i -> p3localBlocks.block[i]), [2,2,2,2]);
RequireEqual("p3 local block two ordinary rows",
  Positions(p3localBlocks.block, 2), [23,24,51,52,65,76]);
RequireEqual("p3 local block two Brauer rows",
  BlocksInfo(p3brauer)[2].modchars, [8,9,17,18]);
RequireEqual("p3 local Brauer reductions", p3brauerRows, [8,9,18,17]);
RequireEqual("p3 local decomposition singleton supports",
  p3decompositionSupports, [[8],[9],[18],[17]]);
RequireEqual("p3 local decomposition singleton coefficients",
  p3decompositionCoefficients, [[1],[1],[1],[1]]);
RequireEqual("p3 local Brauer reductions pairwise distinct",
  Length(Set(p3brauerRows)), 4);
RequireEqual("p3 local Brauer reductions exhaust block two",
  Set(p3brauerRows), Set(BlocksInfo(p3brauer)[2].modchars));
RequireEqual("p3 local certificate", p3certificate,
  [[23,729,2,23,2,8], [24,729,3,24,2,9],
   [51,729,5,51,2,18], [52,729,6,52,2,17]]);
Print("P3_LOCAL table=", Identifier(p3local), " core=", p3core,
      " quotient_order=", Size(p3quotient), " rows=", p3rows, "\n");
Print("P3_LOCAL_CERTIFICATE=", p3certificate, "\n");
Print("P3_LOCAL_DECOMPOSITION_SUPPORTS=",
      p3decompositionSupports, "\n");
Print("P3_LOCAL_DECOMPOSITION_COEFFICIENTS=",
      p3decompositionCoefficients, "\n");
Print("P3_LOCAL_BLOCK_TWO_BRAUER_ROWS=",
      BlocksInfo(p3brauer)[2].modchars, "\n");

p3ambientBlocks := PrimeBlocks(s, 3);;
p3localBlockTwoRows := Positions(p3localBlocks.block, 2);;
p3possibleFusions := PossibleClassFusions(p3local, s);;
p3storedFusion := GetFusionMap(p3local, s);;
p3storedFusionCandidatePosition :=
  Position(p3possibleFusions, p3storedFusion);;
p3centralCharacterAssignments := List(p3possibleFusions,
  fusion -> BlockAssignments(p3local, s, 3,
    p3localBlockTwoRows, fusion));;

RequireEqual("p3 central-character local table",
  Identifier(p3local), "(3^2:2xG2(3)).2");
RequireEqual("p3 central-character ambient table", Identifier(s), "F3+");
RequireEqual("p3 central-character ambient defects",
  p3ambientBlocks.defect, [16,2,0]);
RequireEqual("p3 central-character principal position",
  p3ambientBlocks.block[1], 1);
RequireEqual("p3 central-character local block two rows",
  p3localBlockTwoRows, [23,24,51,52,65,76]);
RequireEqual("p3 central-character possible fusion count",
  Length(p3possibleFusions), 32);
RequireEqual("p3 stored fusion occurs among possible fusions",
  p3storedFusion in p3possibleFusions, true);
RequireEqual("p3 stored fusion candidate position",
  p3storedFusionCandidatePosition, 1);
RequireEqual("p3 central-character assignments independent of fusion",
  Set(p3centralCharacterAssignments), [[2,2,2,2,2,2]]);

Print("P3_INDUCED_CENTRAL_CHARACTER_LOCAL_TABLE=",
      Identifier(p3local), "\n");
Print("P3_INDUCED_CENTRAL_CHARACTER_AMBIENT_TABLE=",
      Identifier(s), "\n");
Print("P3_INDUCED_CENTRAL_CHARACTER_AMBIENT_DEFECTS=",
      p3ambientBlocks.defect, "\n");
Print("P3_INDUCED_CENTRAL_CHARACTER_LOCAL_BLOCK=2 rows=",
      p3localBlockTwoRows, "\n");
Print("P3_INDUCED_CENTRAL_CHARACTER_POSSIBLE_FUSIONS=",
      Length(p3possibleFusions), "\n");
Print("P3_STORED_FUSION_CANDIDATE_POSITION=",
      p3storedFusionCandidatePosition, "\n");
Print("P3_INDUCED_CENTRAL_CHARACTER_ASSIGNMENT_PATTERNS=",
      Set(p3centralCharacterAssignments), "\n");

CheckBlocks("P5", "3.F3+", "3.F3+.2", 5,
  [[0,78],[1,9],[2,7]],
  [[1,2,1,16,16,0,trivialCentre],
   [2,2,2,14,6,4,trivialCentre],
   [3,2,3,16,16,0,trivialCentre],
   [45,2,46,16,swapped,swapped,faithfulCentre],
   [46,2,45,16,swapped,swapped,conjugateCentre],
   [47,2,48,14,swapped,swapped,faithfulCentre],
   [48,2,47,14,swapped,swapped,conjugateCentre]]);
CheckBlocks("P7", "3.F3+", "3.F3+.2", 7,
  [[0,107],[1,8],[3,3]],
  [[1,3,1,22,12,5,trivialCentre],
   [55,3,56,22,swapped,swapped,faithfulCentre],
   [56,3,55,22,swapped,swapped,conjugateCentre]]);

p2v4a := CharacterTable("2^2.U6(2).3.2");;
p2v4b := CharacterTable("(A4xO8+(2).3).2");;
p2v4aPositions := DefectZeroAboveCore(p2v4a, 2);;
p2v4bPositions := DefectZeroAboveCore(p2v4b, 2);;
RequireEqual("p2 first Klein four weight positions", p2v4aPositions, [93]);
RequireEqual("p2 second Klein four weight positions", p2v4bPositions,
             [62,93,186,187]);
p2v4aFusions := PossibleClassFusions(p2v4a, s);;
p2v4bFusions := PossibleClassFusions(p2v4b, s);;
RequireEqual("number of first Klein four fusions", Length(p2v4aFusions), 2);
RequireEqual("number of second Klein four fusions", Length(p2v4bFusions), 4);
p2v4aAssignments := List(p2v4aFusions,
  fusion -> BlockAssignments(p2v4a, s, 2, p2v4aPositions, fusion));;
p2v4bAssignments := List(p2v4bFusions,
  fusion -> BlockAssignments(p2v4b, s, 2, p2v4bPositions, fusion));;
RequireEqual("first Klein four block distribution independent of fusion",
  Set(List(p2v4aAssignments, Collected)), [[[3,1]]]);
RequireEqual("second Klein four block distribution independent of fusion",
  Set(List(p2v4bAssignments, Collected)), [[[2,3],[3,1]]]);
Print("KLEIN_FOUR_FUSIONS first=", Length(p2v4aFusions),
      " second=", Length(p2v4bFusions),
      " distributions=", Collected(p2v4aAssignments[1]), ",",
      Collected(p2v4bAssignments[1]), "\n");

expectedBlockData :=
  [[5,94,[[0,78],[1,9],[2,7]],[1,2,3,45,46,47,48]],
   [7,118,[[0,107],[1,8],[3,3]],[1,55,56]],
   [11,178,[[0,169],[1,9]],[]],
   [13,170,[[0,162],[1,8]],[]],
   [17,208,[[0,205],[1,3]],[]],
   [23,220,[[0,217],[1,3]],[]],
   [29,211,[[0,208],[1,3]],[]]];;
for expected in expectedBlockData do
  p := expected[1];
  blocks := PrimeBlocks(cover, p);
  noncyclic := PositionsProperty(blocks.defect, d -> d >= 2);
  RequireEqual(Concatenation("p", String(p), " block count"),
               Length(blocks.defect), expected[2]);
  RequireEqual(Concatenation("p", String(p), " defect distribution"),
               Collected(blocks.defect), expected[3]);
  RequireEqual(Concatenation("p", String(p), " noncyclic block positions"),
               noncyclic, expected[4]);
  Print("BLOCK_DATA p=", p, " blocks=", Length(blocks.defect),
        " defects=", Collected(blocks.defect), " noncyclic=", noncyclic, "\n");
od;

Print("The Fi'24 block and automorphism calculations have the stated values.\n");
QUIT_GAP(0);
