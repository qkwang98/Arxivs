# Local 3-block table calculation used for Fi'24.

if LoadPackage("ctbllib") <> true then
  Error("The CTblLib package is required.");
fi;
SizeScreen([4096,4096]);;

RequireEqual := function(tag, got, expected)
  if got <> expected then
    Error(Concatenation(tag, ": got ", String(got),
                        ", expected ", String(expected)));
  fi;
end;

localTable := CharacterTable("(3^2:2xG2(3)).2");;
coreClasses := ClassPositionsOfPCore(localTable, 3);;
quotientTable := CharacterTableFactorGroup(localTable, coreClasses);;
inflationFusion := GetFusionMap(localTable, quotientTable);;
quotientBlocks := PrimeBlocks(quotientTable, 3);;
quotientRows := Filtered([1..Length(Irr(quotientTable))],
  i -> quotientBlocks.defect[quotientBlocks.block[i]] = 0);;
quotientDegrees := List(quotientRows,
  i -> Irr(quotientTable)[i][1]);;
localRows := List(quotientRows,
  i -> Position(Irr(localTable),
    Irr(quotientTable)[i]{inflationFusion}));;
localBlocks := PrimeBlocks(localTable, 3);;
brauerTable := BrauerTable(localTable, 3);;
blockInfo := BlocksInfo(brauerTable);;
decomposition := DecompositionMatrix(brauerTable);;
supports := List(localRows, i ->
  Filtered([1..Length(decomposition[i])],
    j -> decomposition[i][j] <> 0));;
coefficients := List([1..Length(localRows)], r ->
  List(supports[r], j -> decomposition[localRows[r]][j]));;
brauerRows := List(supports, support -> support[1]);;
blockTwoBrauerRows := blockInfo[2].modchars;;
certificate := List([1..Length(quotientRows)], i ->
  [quotientRows[i], quotientDegrees[i],
   quotientBlocks.block[quotientRows[i]], localRows[i],
   localBlocks.block[localRows[i]], brauerRows[i]]);;

RequireEqual("local table order", Size(localTable), 152845056);
RequireEqual("radical core classes", coreClasses, [1,18,41]);
RequireEqual("radical core class sizes",
  SizesConjugacyClasses(localTable){coreClasses}, [1,4,4]);
RequireEqual("quotient table order", Size(quotientTable), 16982784);
RequireEqual("quotient block defects",
  quotientBlocks.defect, [6,0,0,6,0,0]);
RequireEqual("quotient defect-zero rows",
  quotientRows, [23,24,51,52]);
RequireEqual("quotient defect-zero degrees",
  quotientDegrees, [729,729,729,729]);
RequireEqual("quotient block identifiers",
  List(quotientRows, i -> quotientBlocks.block[i]), [2,3,5,6]);
RequireEqual("local block defects", localBlocks.defect, [8,2]);
RequireEqual("Brauer-table block defects",
  List(blockInfo, info -> info.defect), localBlocks.defect);
RequireEqual("ordinary block partitions agree",
  List([1..Length(blockInfo)], b -> blockInfo[b].ordchars),
  List([1..Length(localBlocks.defect)],
    b -> Positions(localBlocks.block, b)));
RequireEqual("inflated local rows", localRows, [23,24,51,52]);
RequireEqual("inflated local block identifiers",
  List(localRows, i -> localBlocks.block[i]), [2,2,2,2]);
RequireEqual("local block two ordinary rows",
  Positions(localBlocks.block, 2), [23,24,51,52,65,76]);
RequireEqual("local block two Brauer rows",
  blockTwoBrauerRows, [8,9,17,18]);
RequireEqual("singleton decomposition supports",
  supports, [[8],[9],[18],[17]]);
RequireEqual("singleton decomposition coefficients",
  coefficients, [[1],[1],[1],[1]]);
RequireEqual("Brauer reductions pairwise distinct",
  Length(Set(brauerRows)), 4);
RequireEqual("Brauer reductions exhaust block two",
  Set(brauerRows), Set(blockTwoBrauerRows));
RequireEqual("local certificate", certificate,
  [[23,729,2,23,2,8], [24,729,3,24,2,9],
   [51,729,5,51,2,18], [52,729,6,52,2,17]]);

Print("GAP_VERSION=", GAPInfo.Version, "\n");
Print("CTBLLIB_VERSION=", PackageInfo("ctbllib")[1].Version, "\n");
Print("P3_LOCAL_TABLE=", Identifier(localTable), "\n");
Print("P3_LOCAL_CERTIFICATE=", certificate, "\n");
Print("P3_LOCAL_DECOMPOSITION_SUPPORTS=", supports, "\n");
Print("P3_LOCAL_DECOMPOSITION_COEFFICIENTS=", coefficients, "\n");
Print("P3_LOCAL_BLOCK_TWO_BRAUER_ROWS=", blockTwoBrauerRows, "\n");
Print("The Fi'24 local 3-block table calculation has the stated values.\n");
QUIT_GAP(0);
