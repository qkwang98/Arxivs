# Certificates for the 411 primitive residual linear actions.
#
# The data are grouped by residual row.  For each action they give matrix
# generators, an abundant vector, and either a source of a balanced pair or
# the indication that the cubic condition is to be checked.

if LoadPackage("irredsol") <> true then
    Error("The GAP package IrredSol is required.");
fi;

RequireEqual := function(description, found, expected)
    if found <> expected then
        Error(description, "\nexpected: ", expected, "\nfound: ", found);
    fi;
end;;

ReadRequiredFile := function(path)
    if not IsReadableFile(path) then
        Error("The required data file is missing or unreadable: ", path);
    fi;
    Read(path);
end;;

MatrixFromList := function(entries, q, d)
    local one, rows, i, j;
    RequireEqual("the number of entries in a stored matrix",
                 Length(entries), d ^ 2);
    if not ForAll(entries, entry -> IsInt(entry)
        and entry >= 0 and entry < q) then
        Error("A stored matrix entry is outside its prime field.");
    fi;
    one := One(GF(q));
    rows := [];
    for i in [0 .. d - 1] do
        Add(rows, List([1 .. d], j -> entries[i * d + j] * one));
    od;
    return ImmutableMatrix(GF(q), rows);
end;;

MatrixGroupFromLists := function(q, d, storedGenerators)
    local matrices;
    if Length(storedGenerators) = 0 then
        Error("A stored group has no generators.");
    fi;
    matrices := List(storedGenerators,
                     entries -> MatrixFromList(entries, q, d));
    return Group(matrices);
end;;

VectorFromList := function(entries, q, d)
    local one;
    RequireEqual("the number of entries in a stored vector",
                 Length(entries), d);
    if not ForAll(entries, entry -> IsInt(entry)
        and entry >= 0 and entry < q) then
        Error("A stored vector entry is outside its prime field.");
    fi;
    one := One(GF(q));
    return List(entries, entry -> entry * one);
end;;

LargestNilpotentOrder := function(K)
    local largest, class, R;
    if IsNilpotentGroup(K) then
        return Size(K);
    fi;
    largest := 1;
    for class in ConjugacyClassesSubgroups(K) do
        R := Representative(class);
        if IsNilpotentGroup(R) then
            largest := Maximum(largest, Size(R));
        fi;
    od;
    return largest;
end;;

# The orbit is grown only until it closes or contains more than cap vectors.
# In the latter case the returned lower bound proves the required inequality.
BoundedOrbitRight := function(J, v, cap)
    local generators, queue, seen, position, g, w;
    generators := GeneratorsOfGroup(J);
    queue := [v];
    seen := [v];
    position := 1;
    while position <= Length(queue) do
        for g in generators do
            w := queue[position] * g;
            if not w in seen then
                Add(queue, w);
                AddSet(seen, w);
                if Length(queue) > cap then
                    return rec(exceeded := true, size := Length(queue));
                fi;
            fi;
        od;
        position := position + 1;
    od;
    return rec(exceeded := false, size := Length(queue));
end;;

AbundanceCertificate := function(J, v)
    local order, orbit, index, stabiliserOrder, stabiliser, nu;
    order := Size(J);
    orbit := BoundedOrbitRight(J, v, RootInt(order) + 1);
    if orbit.exceeded then
        return rec(kind := "order-bound");
    fi;
    index := orbit.size;
    stabiliserOrder := order / index;
    if stabiliserOrder = 1 then
        return rec(kind := "regular");
    fi;
    if index >= stabiliserOrder then
        return rec(kind := "order-bound");
    fi;
    stabiliser := Stabilizer(J, v, OnRight);
    nu := LargestNilpotentOrder(stabiliser);
    if index >= nu then
        return rec(kind := "exact");
    fi;
    return fail;
end;;

NormalSections := function(J)
    local sections, K, L;
    sections := [];
    for K in NormalSubgroups(J) do
        for L in NormalSubgroups(K) do
            if not L in sections then
                Add(sections, L);
            fi;
        od;
    od;
    return sections;
end;;

IsChainAbundantOrbit := function(J, a)
    local orbit, L, isAbundantForL;
    orbit := Orbit(J, a, OnRight);
    for L in NormalSections(J) do
        isAbundantForL := function(v)
            local stabiliser;
            stabiliser := Stabilizer(L, v, OnRight);
            return Index(L, stabiliser) >=
                   LargestNilpotentOrder(stabiliser);
        end;
        if not ForAny(orbit, isAbundantForL) then
            return false;
        fi;
    od;
    return true;
end;;

RegularPairCertificate := function(J, a, b)
    local stabiliserA;
    if RepresentativeAction(J, a, b, OnRight) <> fail then
        return false;
    fi;
    stabiliserA := Stabilizer(J, a, OnRight);
    return Size(Stabilizer(stabiliserA, b, OnRight)) = 1;
end;;

TwoOrbitCertificate := function(J, a, b)
    return RepresentativeAction(J, a, b, OnRight) = fail
       and IsChainAbundantOrbit(J, a)
       and IsChainAbundantOrbit(J, b);
end;;

# This is the exact minimum of z_L n_L^3 over all L normal in K normal in J.
# Every nonzero vector is included.  The calculation is used only for the nine
# small actions carrying a cubic-condition certificate.
CubicConditionMinimum := function(J, q, d)
    local vectors, nonzeroOrbits, sections, L, orbit, v, stabiliser, ratio,
          largestRatio, value, minimum;
    vectors := Elements(GF(q) ^ d);
    nonzeroOrbits := Filtered(Orbits(J, vectors, OnRight),
                              orbit -> not IsZero(orbit[1]));
    RequireEqual("nonzero vector orbits for a cubic-condition group",
                 Length(nonzeroOrbits), 1);
    sections := NormalSections(J);
    minimum := infinity;
    for L in sections do
        largestRatio := 0;
        for orbit in nonzeroOrbits do
            for v in orbit do
                stabiliser := Stabilizer(L, v, OnRight);
                ratio := Index(L, stabiliser)
                         / LargestNilpotentOrder(stabiliser);
                largestRatio := Maximum(largestRatio, ratio);
            od;
        od;
        value := largestRatio ^ 3 / LargestNilpotentOrder(L);
        minimum := Minimum(minimum, value);
    od;
    return minimum;
end;;

MatrixHypothesesHold := function(G, q, d)
    return DimensionOfMatrixGroup(G) = d
       and ForAll(GeneratorsOfGroup(G),
                  matrix -> ForAll(Flat(matrix), x -> x in GF(q)))
       and IsSolvableGroup(G)
       and IsIrreducibleMatrixGroup(G, GF(q));
end;;

ReadRequiredFile("residual_action_data.g");

ExpectedRows := [
    ["1E+",  3, 16, 12],
    ["3",    2, 18, 40],
    ["9E+",  3,  8, 27],
    ["9E-",  3,  8, 71],
    ["10",   5,  8, 22],
    ["19E+", 3,  4, 14],
    ["19E-", 3,  4,  9],
    ["20",   5,  4, 22],
    ["21E+", 7,  4, 16],
    ["22",   3,  8, 74],
    ["23E+",11,  4,  4],
    ["24",  13,  4,  5],
    ["25",  17,  4,  4],
    ["28",   5,  8,  3],
    ["48",   2,  6,  7],
    ["49",   7,  3,  4],
    ["50",  13,  3,  2],
    ["51",   2, 12,  8],
    ["52",  19,  3,  1],
    ["53",   5,  6,  3],
    ["62",   3,  2,  2],
    ["63",   5,  2,  2],
    ["64",   7,  2,  2],
    ["65",   3,  4, 11],
    ["66",  11,  2,  2],
    ["67",  13,  2,  2],
    ["68",  17,  2,  3],
    ["69",  19,  2,  2],
    ["71",   5,  4, 16],
    ["72",   3,  6,  2],
    ["74",   7,  4,  7],
    ["75",   3,  8, 10],
    ["117",  3,  8,  2]
];;

RequireEqual("the number of residual rows", Length(ResidualActionData), 33);
RequireEqual("the row specification count", Length(ExpectedRows), 33);
RequireEqual("the number of residual actions",
             Sum(ResidualActionData, rowData -> Length(rowData.actions)),
             411);

WitnessCounts := rec(regular := 0, orderBound := 0, exact := 0);;
LocalCertificateCounts := rec(
    regularPair := 0,
    twoOrbits := 0,
    cubicCondition := 0);;
CubicCases := [];;
actionCount := 0;;

for rowNumber in [1 .. Length(ResidualActionData)] do
    rowData := ResidualActionData[rowNumber];
    expected := ExpectedRows[rowNumber];
    RequireEqual(Concatenation("the description of residual row ",
                               String(rowNumber)),
                 [rowData.row, rowData.q, rowData.d,
                  Length(rowData.actions)],
                 expected);

    for actionNumber in [1 .. Length(rowData.actions)] do
        action := rowData.actions[actionNumber];
        G := MatrixGroupFromLists(rowData.q, rowData.d, action.generators);
        description := Concatenation("row ", rowData.row, ", action ",
                                     String(actionNumber));
        actionCount := actionCount + 1;

        RequireEqual(Concatenation("matrix hypotheses for ", description),
                     MatrixHypothesesHold(G, rowData.q, rowData.d), true);
        RequireEqual(Concatenation("linear primitivity for ", description),
                     IsPrimitiveMatrixGroup(G, GF(rowData.q)), true);

        if rowData.row = "62" and actionNumber = 2 then
            row62Action2 := G;
        fi;

        abundantVector := VectorFromList(action.abundant,
                                         rowData.q, rowData.d);
        abundance := AbundanceCertificate(G, abundantVector);
        if abundance = fail then
            Error("The stated abundant vector fails for ", description, ".");
        fi;
        if abundance.kind = "regular" then
            WitnessCounts.regular := WitnessCounts.regular + 1;
        elif abundance.kind = "order-bound" then
            WitnessCounts.orderBound := WitnessCounts.orderBound + 1;
        elif abundance.kind = "exact" then
            WitnessCounts.exact := WitnessCounts.exact + 1;
        else
            Error("An unknown abundance certificate occurs in ",
                  description, ".");
        fi;

        if action.balance = "regular-pair" then
            first := VectorFromList(action.first, rowData.q, rowData.d);
            second := VectorFromList(action.second, rowData.q, rowData.d);
            RequireEqual(Concatenation("regular pair for ", description),
                         RegularPairCertificate(G, first, second), true);
            LocalCertificateCounts.regularPair :=
                LocalCertificateCounts.regularPair + 1;
        elif action.balance = "two-orbits" then
            first := VectorFromList(action.first, rowData.q, rowData.d);
            second := VectorFromList(action.second, rowData.q, rowData.d);
            RequireEqual(Concatenation("two chain-abundant orbits for ",
                                       description),
                         TwoOrbitCertificate(G, first, second), true);
            LocalCertificateCounts.twoOrbits :=
                LocalCertificateCounts.twoOrbits + 1;
        elif action.balance = "cubic-condition" then
            Add(CubicCases,
                [rowData.row, actionNumber, rowData.q,
                 rowData.d, Size(G)]);
            profileMinimum := CubicConditionMinimum(
                G, rowData.q, rowData.d);
            if profileMinimum < 1 then
                Error("The cubic-condition inequality fails for ",
                      description, ": the minimum is ",
                      profileMinimum, ".");
            fi;
            LocalCertificateCounts.cubicCondition :=
                LocalCertificateCounts.cubicCondition + 1;
        else
            Error("An unknown local certificate occurs in ",
                  description, ".");
        fi;
    od;
    Print("Row ", rowData.row, ": ", Length(rowData.actions),
          " primitive actions.\n");
od;

RequireEqual("the residual-action count", actionCount, 411);
RequireEqual("actions requiring the cubic condition",
    CubicCases,
    [["19E-", 2, 3, 4, 640],
     ["19E-", 5, 3, 4, 320],
     ["19E-", 6, 3, 4, 160],
     ["62", 1, 3, 2, 48],
     ["62", 2, 3, 2, 24],
     ["63", 1, 5, 2, 96],
     ["63", 2, 5, 2, 48],
     ["64", 1, 7, 2, 144],
     ["66", 1, 11, 2, 240]]);
RequireEqual("row 62 action 2 is isomorphic to SL(2,3)",
             IsomorphismGroups(row62Action2, SL(2, 3)) <> fail, true);
RequireEqual("regular abundance certificates",
             WitnessCounts.regular, 0);
RequireEqual("order-bound abundance certificates",
             WitnessCounts.orderBound, 401);
RequireEqual("exact abundance certificates",
             WitnessCounts.exact, 10);
RequireEqual("regular-pair certificates",
             LocalCertificateCounts.regularPair, 394);
RequireEqual("two-orbit certificates",
             LocalCertificateCounts.twoOrbits, 8);
RequireEqual("balanced-pair certificates",
             LocalCertificateCounts.regularPair
             + LocalCertificateCounts.twoOrbits, 402);
RequireEqual("cubic-condition certificates",
             LocalCertificateCounts.cubicCondition, 9);

Print("All 411 residual actions are linearly primitive.\n");
Print("Every one has an abundant vector.\n");
Print("Balanced-pair certificates: 402 (394 from a regular pair and 8 from\n");
Print("two distinct chain-abundant orbits).\n");
Print("The remaining 9 satisfy the cubic condition.\n");
QUIT_GAP(0);
