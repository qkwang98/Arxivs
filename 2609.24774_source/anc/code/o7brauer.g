# Principal Brauer-character restrictions from SO7(3) to Omega7(3).

if LoadPackage("ctbllib") <> true then
  Error("The CTblLib package is required.");
fi;

Check := function(condition, message)
  if not condition then
    Error(message);
  fi;
end;;

s := CharacterTable("O7(3)");;
h := CharacterTable("O7(3).2");;
bs := BrauerTable(s, 2);;
bh := BrauerTable(h, 2);;

Check(Identifier(s) = "O7(3)", "The simple group table should have identifier O7(3).");;
Check(Identifier(h) = "O7(3).2", "The outer group table should have identifier O7(3).2.");;
Check(Size(s) = 4585351680, "The simple group table has unexpected order.");;
Check(Size(h) = 9170703360, "The outer group table has unexpected order.");;
Check(Size(h) / Size(s) = 2, "The order of H should be twice the order of S.");;

b0s := First(BlocksInfo(bs), b -> Position(b.modchars, 1) <> fail);;
b0h := First(BlocksInfo(bh), b -> Position(b.modchars, 1) <> fail);;
Check(b0s.modchars = [1..12],
      "The principal block of S has unexpected Brauer character positions.");;
Check(b0h.modchars = [1..10],
      "The principal block of H has unexpected Brauer character positions.");;

fusion := GetFusionMap(bs, bh);;
Check(fusion <> fail,
      "The stored fusion from the Brauer table of S to that of H is unavailable.");;

expected := [ [1], [2], [3], [4], [5,6], [7], [8], [9], [10], [11,12] ];;
fibres := [];;
for i in [1..10] do
  r := RestrictedClassFunction(Irr(bh)[i], bs);;
  singles := [];;
  pairs := [];;
  for j in [1..Length(Irr(bs))] do
    if r = Irr(bs)[j] then
      Add(singles, j);
    fi;
  od;
  for j in [1..Length(Irr(bs))] do
    for k in [j+1..Length(Irr(bs))] do
      if r = Irr(bs)[j] + Irr(bs)[k] then
        Add(pairs, [j,k]);
      fi;
    od;
  od;
  Check(Length(singles) + Length(pairs) = 1,
         Concatenation("The restriction of H character ", String(i),
                       " does not have a unique decomposition."));
  if Length(singles) = 1 then
    fibre := [singles[1]];
  else
    fibre := pairs[1];
  fi;
  Check(fibre = expected[i],
         Concatenation("The restriction fibre of H character ", String(i),
                       " is unexpected."));
  Add(fibres, fibre);
  Print("H_B0_RESTRICTION_H", i, "=", fibre, "\n");;
od;

Check(Number(fibres, x -> Length(x) = 1) = 8,
      "There should be eight singleton restriction fibres.");;
Check(Number(fibres, x -> Length(x) = 2) = 2,
      "There should be two restriction fibres with two constituents.");;
Check(Set(Concatenation(fibres)) = [1..12],
      "The restriction fibres do not partition the principal block of S.");;

Print("GAP_VERSION=", GAPInfo.Version, "\n");;
Print("CTBLLIB_VERSION=", PackageInfo("ctbllib")[1].Version, "\n");;
Print("S_TABLE=", Identifier(s), "\n");;
Print("H_TABLE=", Identifier(h), "\n");;
Print("S_ORDER=", Size(s), "\n");;
Print("H_ORDER=", Size(h), "\n");;
Print("H_OVER_S=", Size(h) / Size(s), "\n");;
Print("TABLE_FUSION_LENGTH=", Length(fusion), "\n");;
Print("S_B0_BRAUER_COUNT=", Length(b0s.modchars), "\n");;
Print("H_B0_BRAUER_COUNT=", Length(b0h.modchars), "\n");;
Print("TABLE_DECOMPOSITION_FIXED_SINGLETONS=8\n");;
Print("TABLE_DECOMPOSITION_TWO_CONSTITUENT_ROWS=2\n");;
Print("The principal Brauer characters restrict as eight singletons and two pairs.\n");;
QUIT_GAP(0);
