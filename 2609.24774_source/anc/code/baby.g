# Derive the two Baby Monster 2-block Brauer counts from exact ordinary
# restrictions, independently of any installed 2-Brauer table.  The final
# assertions also check the aggregate 7-regular class count and the ranks of
# the four 7-blocks of defect 2 in 2.B.
if LoadPackage("ctbllib") <> true then
  Error("The CTblLib package is required.");
fi;
SizeScreen([80,2000]);

t := CharacterTable("B");;
if t = fail then
  Error("The ordinary character table of the Baby Monster is unavailable.");
fi;
irr := Irr(t);;
blocks := PrimeBlocks(t, 2);;
classOrders := OrdersClassRepresentatives(t);;
regularPositions := Filtered([1 .. Length(classOrders)],
    i -> IsOddInt(classOrders[i]));;
labels := Set(blocks.block);;

Print("GAP_VERSION=", GAPInfo.Version, "\n");
Print("CTBLLIB_VERSION=", PackageInfo("ctbllib")[1].Version, "\n");
Print("IDENTIFIER=", Identifier(t), "\n");
Print("ORDINARY_COUNT=", Length(irr), "\n");
Print("REGULAR_POSITIONS_COUNT=", Length(regularPositions), "\n");
Print("BLOCK_LABELS=", labels, "\n");
Print("BLOCK_DEFECTS=", blocks.defect, "\n");
Print("PRINCIPAL_LABEL=", blocks.block[1], "\n");

blockBases := [];;
for label in labels do
  indices := Positions(blocks.block, label);;
  restrictions := List(indices, i -> irr[i]{regularPositions});;
  rankByRankMat := RankMat(restrictions);;
  base := BaseMat(restrictions);;
  sem := SemiEchelonMatTransformation(restrictions);;
  pivots := [];;
  for position in [1 .. Length(sem.heads)] do
    if sem.heads[position] <> 0 then Add(pivots, position); fi;
  od;
  pivotMinor := [];;
  for basisRow in sem.vectors do Add(pivotMinor, basisRow{pivots}); od;
  pivotDeterminant := DeterminantMat(pivotMinor);;
  Add(blockBases, base);
  Print("BLOCK_", label, "_K=", Length(indices), "\n");
  Print("BLOCK_", label, "_RANK_RANKMAT=", rankByRankMat, "\n");
  Print("BLOCK_", label, "_RANK_BASEMAT=", Length(base), "\n");
  Print("BLOCK_", label, "_LEFT_NULLITY=", Length(sem.relations), "\n");
  Print("BLOCK_", label, "_PIVOT_COLUMNS=", pivots, "\n");
  Print("BLOCK_", label, "_PIVOT_MINOR_DET=", pivotDeterminant, "\n");
  Print("BLOCK_", label, "_TRANSFORMATION_IDENTITY=",
        sem.coeffs * restrictions = sem.vectors, "\n");
  if Length(indices) <= 10 then
    Print("BLOCK_", label, "_INDICES=", indices, "\n");
    Print("BLOCK_", label, "_DEGREES=", List(indices, i -> irr[i][1]), "\n");
  fi;
od;

allRestrictions := List([1 .. Length(irr)],
    i -> irr[i]{regularPositions});;
combinedBases := Concatenation(blockBases);;
twoPartExponent := PValuation(Size(t), 2);;
defectZeroIndices := Filtered([1 .. Length(irr)],
    i -> PValuation(irr[i][1], 2) = twoPartExponent);;

Print("ALL_RESTRICTIONS_RANK=", RankMat(allRestrictions), "\n");
Print("COMBINED_BLOCK_BASES_RANK=", RankMat(combinedBases), "\n");
Print("GROUP_TWO_PART_EXPONENT=", twoPartExponent, "\n");
Print("DEFECT_ZERO_INDICES=", defectZeroIndices, "\n");

if labels <> [1, 2] then
  Error("The Baby Monster block labels should be [1,2].");
fi;
if blocks.defect <> [41, 3] then
  Error("The Baby Monster 2-block defects should be [41,3].");
fi;
if blocks.block[1] <> 1 then
  Error("The principal block should have label 1.");
fi;
if Length(irr) <> 184 then
  Error("The Baby Monster should have 184 ordinary irreducible characters.");
fi;
if Length(regularPositions) <> 27 then
  Error("The Baby Monster should have 27 two-regular conjugacy classes.");
fi;
if List(labels, label -> Length(Positions(blocks.block, label))) <> [179, 5] then
  Error("The ordinary character counts of the two blocks should be [179,5].");
fi;
if Positions(blocks.block, 2) <> [119, 165, 166, 176, 177] then
  Error("The nonprincipal block has unexpected ordinary character positions.");
fi;
if List(blockBases, Length) <> [25, 2] then
  Error("The restriction bases should have ranks [25,2].");
fi;
if List(labels, label -> RankMat(List(Positions(blocks.block, label),
      i -> irr[i]{regularPositions}))) <> [25, 2] then
  Error("The direct restriction ranks should be [25,2].");
fi;
if RankMat(combinedBases) <> 27 then
  Error("The combined block bases should have rank 27.");
fi;
if RankMat(allRestrictions) <> 27 then
  Error("The ordinary character restrictions should have rank 27.");
fi;
if twoPartExponent <> 41 or defectZeroIndices <> [] then
  Error("The 2-part exponent or the defect-zero character list is unexpected.");
fi;

# The proof of An--Wilson, Lemma 5.2, prints the aggregate value 220 at
# p=7.  The verified ordinary table of 2.B has 222 7-regular classes.  The
# four blocks of defect 2 have the ranks used in the blockwise theorem.
t7 := CharacterTable("2.B");;
if t7 = fail then
  Error("The ordinary character table of 2.B is unavailable.");
fi;
irr7 := Irr(t7);;
blocks7 := PrimeBlocks(t7, 7);;
orders7 := OrdersClassRepresentatives(t7);;
regular7 := Filtered([1 .. Length(orders7)], i -> orders7[i] mod 7 <> 0);;
labels7 := Set(blocks7.block);;
defectTwo7 := Filtered(labels7, label -> blocks7.defect[label] = 2);;
ranks7 := List(defectTwo7, label -> RankMat(List(
    Positions(blocks7.block, label), i -> irr7[i]{regular7})));;

Print("DOUBLE_COVER_7_REGULAR_CLASS_COUNT=", Length(regular7), "\n");
Print("DOUBLE_COVER_DEFECT_2_SEVEN_BLOCK_LABELS=", defectTwo7, "\n");
Print("DOUBLE_COVER_DEFECT_2_SEVEN_BLOCK_RANKS=", ranks7, "\n");

if Length(regular7) <> 222 then
  Error("The group 2.B should have 222 seven-regular conjugacy classes.");
fi;
if defectTwo7 <> [1, 2, 4, 73] then
  Error("The labels of the 7-blocks of defect two in 2.B are unexpected.");
fi;
if ranks7 <> [24, 24, 21, 24] then
  Error("The ranks of the 7-blocks of defect two in 2.B should be [24,24,21,24].");
fi;

Print("The Baby Monster calculations have the stated ranks and class counts.\n");
QUIT_GAP(0);
