# The six exceptional one-dimensional semilinear groups.
#
# For K acting on V, n_reg(K,V^2) is the number of regular K-orbits on V x V.
# The calculation finds this number by a complete orbit decomposition.  It also
# enumerates every subgroup class of GammaL(1,q) for each exceptional q and
# verifies that every proper faithful irreducible primitive solvable subgroup
# has at least five regular orbits on V x V.

if LoadPackage("irredsol") <> true then
    Error("The GAP package IrredSol is required.");
fi;

RequireEqual := function(description, found, expected)
    if found <> expected then
        Error(description, "\nexpected: ", expected, "\nfound: ", found);
    fi;
end;;

GammaL1 := function(q)
    local p, F, basis, w, singer, frobenius;
    p := Factors(q)[1];
    F := GF(q);
    basis := Basis(F);
    w := Z(q);
    singer := List(BasisVectors(basis),
                   b -> Coefficients(basis, w * b));
    frobenius := List(BasisVectors(basis),
                      b -> Coefficients(basis, b ^ p));
    return Group(singer, frobenius);
end;;

NumberRegularPairOrbits := function(K)
    local V, action, orbits;
    V := FieldOfMatrixGroup(K) ^ DimensionOfMatrixGroup(K);
    action := function(pair, g)
        return [pair[1] * g, pair[2] * g];
    end;
    orbits := Orbits(K, Cartesian(Elements(V), Elements(V)), action);
    return Number(orbits, orbit -> Length(orbit) = Size(K));
end;;

SemilinearCases := [
    rec(q := 2,  numberRegularPairOrbits := 4, classes := 1, proper := 0),
    rec(q := 3,  numberRegularPairOrbits := 4, classes := 2, proper := 1),
    rec(q := 4,  numberRegularPairOrbits := 1, classes := 2, proper := 1),
    rec(q := 8,  numberRegularPairOrbits := 2, classes := 2, proper := 1),
    rec(q := 9,  numberRegularPairOrbits := 3, classes := 3, proper := 2),
    rec(q := 16, numberRegularPairOrbits := 3, classes := 6, proper := 5)
];;

for specification in SemilinearCases do
    G := GammaL1(specification.q);
    primeField := GF(Factors(specification.q)[1]);
    qualifyingClasses := 0;
    properClasses := 0;
    fullValue := fail;
    smallProperValues := [];

    for class in ConjugacyClassesSubgroups(G) do
        K := Representative(class);
        if IsSolvableGroup(K)
           and IsIrreducibleMatrixGroup(K, primeField)
           and IsPrimitiveMatrixGroup(K, primeField) then
            qualifyingClasses := qualifyingClasses + 1;
            value := NumberRegularPairOrbits(K);
            if Size(K) = Size(G) then
                fullValue := value;
            else
                properClasses := properClasses + 1;
                if value < 5 then
                    Add(smallProperValues,
                        rec(order := Size(K), numberOfOrbits := value));
                fi;
            fi;
        fi;
    od;

    RequireEqual(Concatenation("qualifying subgroup classes for q = ",
                               String(specification.q)),
                 qualifyingClasses, specification.classes);
    RequireEqual(Concatenation("proper qualifying subgroup classes for q = ",
                               String(specification.q)),
                 properClasses, specification.proper);
    RequireEqual(Concatenation("regular orbits on V x V for GammaL(1,",
                               String(specification.q), ")"),
                 fullValue, specification.numberRegularPairOrbits);
    RequireEqual(Concatenation("proper classes with fewer than five regular ",
                               "orbits on V x V for q = ",
                               String(specification.q)),
                 smallProperValues, []);

    Print("q = ", specification.q, ": ", qualifyingClasses,
          " qualifying subgroup classes, ", properClasses,
          " proper; the number of regular orbits on V x V for GammaL(1,q) ",
          "is ", fullValue, ", and every proper qualifying class has at ",
          "least 5 such orbits.\n");
od;

Print("For q = 2, 3, 4, 8, 9 and 16 the numbers of regular orbits on ",
      "V x V for GammaL(1,q) are 4, 4, 1, 2, 3 and 3, respectively; ",
      "every proper qualifying subgroup class has at least 5 such orbits.\n");
QUIT_GAP(0);
