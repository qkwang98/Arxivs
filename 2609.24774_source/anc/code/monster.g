# The ordinary 2-blocks of the Monster.

if LoadPackage("ctbllib") <> true then
  Error("The CTblLib package is required.");
fi;
SizeScreen([80,2000]);

t := CharacterTable("M");;
if t = fail then
  Error("The ordinary character table of the Monster is unavailable.");
fi;

irr := Irr(t);;
pb := PrimeBlocks(t, 2);;
n := Length(irr);;
labels := Set(pb.block);;
parts := List(labels, b -> Positions(pb.block, b));;
defects := List(labels, b -> pb.defect[b]);;
ordinaryCounts := List(parts, Length);;
positive := Filtered(labels, b -> pb.defect[b] > 0);;
zero := Filtered(labels, b -> pb.defect[b] = 0);;
principal := pb.block[1];;
groupTwoValuation := PValuation(Size(t), 2);;
manualHeights := List([1..n], i ->
  pb.defect[pb.block[i]] -
  (groupTwoValuation - PValuation(irr[i][1], 2)));
zeroIndices := List(zero, b -> Positions(pb.block, b)[1]);;
zeroCharacterDefects := List(zeroIndices, i ->
  groupTwoValuation - PValuation(irr[i][1], 2));;
defectFourIndices := Positions(pb.block, 4);;
defectFourHeights := manualHeights{defectFourIndices};;
twoRegularClasses := Number(OrdersClassRepresentatives(t), IsOddInt);;

if Identifier(t) <> "M" then
  Error("The character table should have identifier M.");
fi;
if n <> 194 then
  Error("The Monster should have 194 ordinary irreducible characters.");
fi;
if Length(pb.block) <> n then
  Error("The block list should have one entry for each ordinary character.");
fi;
if Sum(ordinaryCounts) <> n then
  Error("The ordinary block counts should sum to 194.");
fi;
if Set(Concatenation(parts)) <> [1..n] then
  Error("The blocks do not partition the ordinary characters.");
fi;
if labels <> [1,2,3,4,5] then
  Error("The Monster 2-block labels should be [1,2,3,4,5].");
fi;
if defects <> [46,0,0,4,0] then
  Error("The Monster 2-block defects should be [46,0,0,4,0].");
fi;
if ordinaryCounts <> [183,1,1,8,1] then
  Error("The ordinary block counts should be [183,1,1,8,1].");
fi;
if positive <> [1,4] then
  Error("The blocks of positive defect should have labels [1,4].");
fi;
if zero <> [2,3,5] then
  Error("The blocks of defect zero should have labels [2,3,5].");
fi;
if irr[1][1] <> 1 or principal <> 1 then
  Error("The first ordinary character should be trivial and should lie in block 1.");
fi;
if groupTwoValuation <> 46 then
  Error("The 2-adic valuation of the group order should be 46.");
fi;
if pb.height <> manualHeights then
  Error("The reconstructed character heights disagree with the table data.");
fi;
if zeroCharacterDefects <> [0,0,0] then
  Error("The characters in the blocks of defect zero should have defect zero.");
fi;
if defectFourIndices <> [123,124,125,133,140,172,175,181] then
  Error("The block of defect four has unexpected character positions.");
fi;
if defectFourHeights <> [1,1,1,0,0,0,0,2] then
  Error("The character heights in the block of defect four are unexpected.");
fi;
if twoRegularClasses <> 61 then
  Error("The Monster should have 61 two-regular conjugacy classes.");
fi;

Print("GAP_VERSION=", GAPInfo.Version, "\n");
Print("CTBLLIB_VERSION=", InstalledPackageVersion("ctbllib"), "\n");
Print("TABLE_IDENTIFIER=", Identifier(t), "\n");
Print("ORDINARY_CHARACTER_COUNT=", n, "\n");
Print("BLOCK_LABELS=", labels, "\n");
Print("BLOCK_DEFECT_EXPONENTS=", defects, "\n");
Print("ORDINARY_kB_COUNTS=", ordinaryCounts, "\n");
Print("PRINCIPAL_BLOCK_LABEL=", principal, "\n");
Print("POSITIVE_DEFECT_LABELS=", positive, "\n");
Print("DEFECT_ZERO_LABELS=", zero, "\n");
Print("DEFECT_ZERO_CHARACTER_INDICES=", zeroIndices, "\n");
Print("DEFECT_ZERO_CHARACTER_DEFECTS=", zeroCharacterDefects, "\n");
Print("DEFECT_FOUR_CHARACTER_INDICES=", defectFourIndices, "\n");
Print("DEFECT_FOUR_HEIGHTS=", defectFourHeights, "\n");
Print("TWO_REGULAR_CLASS_COUNT=", twoRegularClasses, "\n");
Print("The ordinary block counts are not the Brauer character counts.\n");
Print("The Monster calculation has the stated block data and 61 two-regular classes.\n");
QUIT_GAP(0);
