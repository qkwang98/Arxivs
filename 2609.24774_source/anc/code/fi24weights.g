# Weights with radical subgroup of order 5 or 25 in Fi'24 and 3.Fi'24.

if LoadPackage("ctbllib") <> true then
  Error("The CTblLib package is required.");
fi;
SizeScreen([4096,4096]);;

RequireEqual := function(tag, got, expected)
  if got <> expected then
    Error(Concatenation(tag, ": got ", String(got), ", expected ", String(expected)));
  fi;
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
  local omega, blocks, matches, b;
  omega := CentralCharacter(globalTable,
                            Induced(localTable, globalTable, [chi], fusion)[1]);
  blocks := PrimeBlocks(globalTable, p);
  matches := [];
  for b in [1..Length(blocks.defect)] do
    if SameBlock(p, omega,
       CentralCharacter(Irr(globalTable)[Position(blocks.block, b)]),
       ShallowCopy(blocks.relevant)) then
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

OuterPermutation := function(fusion)
  local perm, i, fibre;
  perm := [];
  for i in [1..Length(fusion)] do
    fibre := Positions(fusion, fusion[i]);
    if Length(fibre) = 1 then perm[i] := i;
    elif Length(fibre) = 2 then perm[i] := First(fibre, j -> j <> i);
    else Error("An outer fusion fibre has unexpected size."); fi;
  od;
  RequireEqual("local outer permutation involutory", perm{perm},
               [1..Length(perm)]);
  return perm;
end;

CharacterPermutation := function(tbl, classperm)
  return List(Irr(tbl), chi -> Position(Irr(tbl), chi{classperm}));
end;

ImagesOfPositions := function(positions, perm)
  return Set(List(positions, i -> perm[i]));
end;

n := CharacterTable("F3+N5");;
g := CharacterTable("F3+");;
nout := CharacterTable("S4x5^2:4S4");;
positions := DefectZeroAboveCore(n, 5);;
fusions := PossibleClassFusions(n, g);;
RequireEqual("number of possible simple fusions", Length(fusions), 4);
allBlocks := List(fusions,
  fusion -> BlockAssignments(n, g, 5, positions, fusion));;
allDistributions := List(allBlocks, Collected);;
RequireEqual("simple block distribution independent of fusion",
             Set(allDistributions), [[[1,16],[2,14],[3,16]]]);
blocks := allBlocks[1];;
RequireEqual("simple p5 weight count", Length(positions), 46);
simpleBlockIds := Set(blocks);;
RequireEqual("simple block ids", simpleBlockIds, [1,2,3]);
outerFusions := PossibleClassFusions(n, nout);;
RequireEqual("number of possible local outer fusions", Length(outerFusions), 2);
outerPermutations := [];;
for fusion in outerFusions do
  classperm := OuterPermutation(fusion);;
  irrperm := CharacterPermutation(n, classperm);
  if fail in irrperm then
    Error("A local ordinary character has no image under an outer fusion.");
  fi;
  RequireEqual("local ordinary-character action involutory", irrperm{irrperm},
               [1..Length(irrperm)]);
  RequireEqual("simple weight positions invariant",
               ImagesOfPositions(positions, irrperm), Set(positions));
  Add(outerPermutations, irrperm);
od;
allSimpleSignatures := [];;
for assignments in allBlocks do
  for irrperm in outerPermutations do
    for j in [1..Length(positions)] do
      imagePosition := Position(positions, irrperm[positions[j]]);
      if imagePosition = fail or
         assignments[imagePosition] <> assignments[j] then
        Error("A possible outer fusion does not preserve the assigned block.");
      fi;
    od;
    simpleSignatures := [];;
    for b in simpleBlockIds do
      members := Positions(assignments, b);
      fixed := Number(members, j -> irrperm[positions[j]] = positions[j]);
      RequireEqual("simple orbit parity", (Length(members)-fixed) mod 2, 0);
      Add(simpleSignatures,
          [b,Length(members),fixed,(Length(members)-fixed)/2]);
    od;
    Add(allSimpleSignatures, simpleSignatures);
  od;
od;
RequireEqual("simple signatures independent of outer fusion",
             Length(Set(allSimpleSignatures)), 1);
simpleSignatures := allSimpleSignatures[1];;
RequireEqual("simple block signatures", simpleSignatures,
             [[1,16,16,0],[2,14,6,4],[3,16,16,0]]);
Print("SIMPLE_FUSIONS=", Length(fusions),
      " OUTER_FUSIONS=", Length(outerFusions), "\n");
Print("SIMPLE_WEIGHTS=", Length(positions), "\n");
for signature in simpleSignatures do
  Print("SIMPLE_BLOCK id=", signature[1], " total=", signature[2],
        " fixed=", signature[3], " free2=", signature[4], "\n");
od;

cn := CharacterTable("3.F3+N5");;
cg := CharacterTable("3.F3+");;
cpositions := DefectZeroAboveCore(cn, 5);;
cfusions := PossibleClassFusions(cn, cg);;
RequireEqual("number of possible covering fusions", Length(cfusions), 8);
allCBlocks := List(cfusions,
  fusion -> BlockAssignments(cn, cg, 5, cpositions, fusion));;
RequireEqual("cover block distribution independent of fusion",
             Set(List(allCBlocks, Collected)),
             [[[1,16],[2,14],[3,16],[45,16],[46,16],[47,14],[48,14]]]);
cblocks := allCBlocks[1];;
RequireEqual("cover p5 weight count", Length(cpositions), 106);
coverBlockIds := Set(cblocks);;
RequireEqual("cover block ids", coverBlockIds, [1,2,3,45,46,47,48]);
coverSignatures := List(coverBlockIds,
                        b -> [b,Number(cblocks, x -> x = b)]);;
RequireEqual("cover block signatures", coverSignatures,
             [[1,16],[2,14],[3,16],[45,16],[46,16],[47,14],[48,14]]);
Print("COVER_WEIGHTS=", Length(cpositions), "\n");
Print("COVER_FUSIONS=", Length(cfusions), "\n");
for signature in coverSignatures do
  Print("COVER_BLOCK id=", signature[1], " total=", signature[2], "\n");
od;
RequireEqual("simple distribution", List([1,2,3], b -> Number(blocks, x -> x = b)),
             [16,14,16]);
RequireEqual("cover distribution",
             List([1,2,3,45,46,47,48], b -> Number(cblocks, x -> x = b)),
             [16,14,16,16,16,14,14]);

cyclicn := CharacterTable("(D10xA9).2");;
cyclicpositions := DefectZeroAboveCore(cyclicn, 5);;
cyclicfusions := PossibleClassFusions(cyclicn, g);;
RequireEqual("number of possible simple order-five fusions",
             Length(cyclicfusions), 2);
allCyclicBlocks := List(cyclicfusions,
  fusion -> BlockAssignments(cyclicn, g, 5, cyclicpositions, fusion));;
RequireEqual("simple order-five distribution independent of fusion",
             Length(Set(List(allCyclicBlocks, Collected))), 1);
RequireEqual("simple order-five block defects independent of fusion",
             Set(List(allCyclicBlocks, assignments ->
               Set(List(assignments, b -> PrimeBlocks(g, 5).defect[b])))),
             [[1]]);
cyclicblocks := allCyclicBlocks[1];;
RequireEqual("simple order-five weight count", Length(cyclicpositions), 10);
RequireEqual("simple order-five block defects",
             Set(List(cyclicblocks, b -> PrimeBlocks(g, 5).defect[b])), [1]);

ccyclicn := CharacterTable("3x(D10xA9).2");;
ccyclicpositions := DefectZeroAboveCore(ccyclicn, 5);;
ccyclicfusions := PossibleClassFusions(ccyclicn, cg);;
RequireEqual("number of possible covering order-five fusions",
             Length(ccyclicfusions), 8);
allCCyclicBlocks := List(ccyclicfusions,
  fusion -> BlockAssignments(ccyclicn, cg, 5, ccyclicpositions, fusion));;
RequireEqual("cover order-five distribution independent of fusion",
             Length(Set(List(allCCyclicBlocks, Collected))), 1);
RequireEqual("cover order-five block defects independent of fusion",
             Set(List(allCCyclicBlocks, assignments ->
               Set(List(assignments, b -> PrimeBlocks(cg, 5).defect[b])))),
             [[1]]);
ccyclicblocks := allCCyclicBlocks[1];;
RequireEqual("cover order-five weight count", Length(ccyclicpositions), 30);
RequireEqual("cover order-five block defects",
             Set(List(ccyclicblocks, b -> PrimeBlocks(cg, 5).defect[b])), [1]);
Print("ORDER_FIVE_FUSIONS=", Length(cyclicfusions), ",",
      Length(ccyclicfusions), "\n");
Print("The weights arising from radical subgroups of order 5 lie in blocks of cyclic defect.\n");
Print("The 5-weight calculations have the stated block distribution.\n");
QUIT_GAP(0);
