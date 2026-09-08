# Chain-abundant subset orbits for small solvable permutation groups.
#
# For a subgroup S, nu(S) denotes the largest order of a nilpotent subgroup
# of S.  The first computation considers every solvable primitive group of
# degree at most 9 and every chain L normal in K normal in J.  The second
# considers every solvable transitive group of degree at most 15.

RequireEqual := function(description, found, expected)
    if found <> expected then
        Error(description, "\nexpected: ", expected, "\nfound: ", found);
    fi;
end;;

LargestNilpotentOrder := function(S)
    local largest, class, R;
    if IsNilpotentGroup(S) then
        return Size(S);
    fi;
    largest := 1;
    for class in ConjugacyClassesSubgroups(S) do
        R := Representative(class);
        if IsNilpotentGroup(R) then
            largest := Maximum(largest, Size(R));
        fi;
    od;
    return largest;
end;;

SomeMemberIsAbundantFor := function(orbit, L)
    local A, stabiliser, index;
    for A in orbit do
        stabiliser := Stabilizer(L, A, OnSets);
        index := Index(L, stabiliser);
        if index >= Size(stabiliser)
           or index >= LargestNilpotentOrder(stabiliser) then
            return true;
        fi;
    od;
    return false;
end;;

SectionAbundantOrbits := function(J, degree)
    local subsetOrbits, sections, K, L, orbit, sizes, number;
    subsetOrbits := Orbits(J, Combinations([1 .. degree]), OnSets);
    sections := [];
    for K in NormalSubgroups(J) do
        for L in NormalSubgroups(K) do
            if not L in sections then
                Add(sections, L);
            fi;
        od;
    od;

    sizes := [];
    number := 0;
    for orbit in subsetOrbits do
        if ForAll(sections, L -> SomeMemberIsAbundantFor(orbit, L)) then
            number := number + 1;
            AddSet(sizes, Length(orbit[1]));
        fi;
    od;
    return rec(number := number, sizes := sizes);
end;;

# The ratio |J:J_A|/nu(J_A) is constant on a J-orbit of subsets.  It is also
# unchanged on replacing A by its complement.  Thus one representative from
# each J-orbit on k-subsets, for 1 <= k <= degree/2, is sufficient.
HasAbundantSubset := function(J, degree)
    local size, orbit, A, stabiliser, index;
    for size in [1 .. QuoInt(degree, 2)] do
        for orbit in Orbits(J, Combinations([1 .. degree], size), OnSets) do
            A := orbit[1];
            stabiliser := Stabilizer(J, A, OnSets);
            index := Index(J, stabiliser);
            if index >= Size(stabiliser)
               or index >= LargestNilpotentOrder(stabiliser) then
                return true;
            fi;
        od;
    od;
    return false;
end;;

primitiveCount := 0;;
singletonExceptions := [];;

for degree in [2 .. 9] do
    for number in [1 .. NrPrimitiveGroups(degree)] do
        J := PrimitiveGroup(degree, number);
        if IsSolvableGroup(J) then
            primitiveCount := primitiveCount + 1;
            abundant := SectionAbundantOrbits(J, degree);

            if degree = 2 then
                RequireEqual("chain-abundant orbits for PrimitiveGroup(2,1)",
                             [abundant.number, abundant.sizes], [1, [1]]);
            else
                pointStabiliserNu := LargestNilpotentOrder(Stabilizer(J, 1));
                if pointStabiliserNu > degree then
                    Add(singletonExceptions, [degree, number]);
                    requiredSizes := [2, 3];
                else
                    requiredSizes := [1, 2];
                fi;
                if not IsSubset(abundant.sizes, requiredSizes) then
                    Error("Missing chain-abundant subset size for ",
                          "PrimitiveGroup(", degree, ",", number, "): ",
                          requiredSizes, " are required, whereas ",
                          abundant.sizes, " occur.");
                fi;
            fi;
        fi;
    od;
od;

RequireEqual("the number of solvable primitive groups of degrees 2 to 9",
             primitiveCount, 21);
RequireEqual("the degree-nine singleton exceptions",
             singletonExceptions, [[9, 5], [9, 7]]);

Print("All 21 solvable primitive groups of degrees 2 to 9 have the required ",
      "chain-abundant subset sizes.  The singleton exceptions are ",
      "PrimitiveGroup(9,5), (C3 x C3):QD16 = AGammaL(1,9), and ",
      "PrimitiveGroup(9,7), the affine group AGL(2,3).\n");

transitiveCount := 0;;
withoutAbundantSubset := [];;

for degree in [2 .. 15] do
    for number in [1 .. NrTransitiveGroups(degree)] do
        J := TransitiveGroup(degree, number);
        if IsSolvableGroup(J) then
            transitiveCount := transitiveCount + 1;
            if not HasAbundantSubset(J, degree) then
                Add(withoutAbundantSubset, [degree, number]);
            fi;
        fi;
    od;
od;

RequireEqual("the number of solvable transitive groups of degrees 2 to 15",
             transitiveCount, 501);
RequireEqual("solvable transitive groups without an abundant subset",
             withoutAbundantSubset, []);

Print("Each of the 501 solvable transitive groups of degrees 2 to 15 has an ",
      "abundant subset.\n");
QUIT_GAP(0);
