# One-dimensional semilinear subgroups below 2^18.
#
# Let q=p^d be a proper prime power and put n=q-1.  On writing every nonzero
# element of GF(q) as zeta^t, the group GammaL(1,q) has the presentation
#
#     <s,f | s^n=f^d=1, s^f=s^p>,
#
# where s sends t to t+1 and f sends t to pt modulo n.  Every subgroup L has
# a unique description
#
#     L=<s^u, f^r s^j>,
#
# in which u divides n, r divides d, 0<=j<u, c=d/r, and
#
#     u divides j(1+p^r+...+p^((c-1)r)).                    (1)
#
# To see this, <s^u> is L intersect <s>, and <f^r<s>> is the image of L in
# the cyclic quotient by <s>.  A lift of f^r is unique modulo <s^u>, giving j
# modulo u.  Its c-th power is
#
#     (f^r s^j)^c=s^(j(1+p^r+...+p^((c-1)r))),
#
# so (1) is necessary.  Conversely, (1) makes the displayed generators a
# subgroup with the stated intersection and quotient.  Its order is (n/u)c.
#
# The <s^u>-orbits on the exponents are the residue classes modulo u and have
# length n/u.  The second generator permutes these classes by
#
#     t -> p^r t+j  (mod u).
#
# Hence the largest L-orbit has length n/u times the largest cycle of this
# affine permutation.  Its c-th power is the identity.  For k dividing c, its
# k-th power fixes t precisely when
#
#     (p^(rk)-1)t = -j(1+p^r+...+p^((k-1)r))  (mod u).      (2)
#
# The number of solutions of (2) is either zero or gcd(p^(rk)-1,u).
# Subtracting the points of smaller least period determines every cycle length
# exactly, without constructing field vectors or their orbits.
#
# Every point stabiliser in GammaL(1,q) is cyclic.  Thus, if m_L is the largest
# L-orbit length, then
#
#     n_L=m_L^2/|L|.
#
# Put tau_L=n_L^3.  Since nu(L)<=|L|, tau_L>|L| proves
# tau_L/nu(L)>1 immediately.  If tau_L=|L|, equality holds exactly when L is
# nilpotent.  Only when tau_L<|L| is nu(L) computed from the subgroup lattice
# of L.  This occurs for three small groups.

RequireEqual := function(description, found, expected)
    if found<>expected then
        Error(description, "\nexpected: ", expected, "\nfound: ", found);
    fi;
end;;

LargestNilpotentOrder := function(L)
    local largest, class, T;
    if IsNilpotentGroup(L) then
        return Size(L);
    fi;
    largest := 1;
    for class in ConjugacyClassesSubgroups(L) do
        T := Representative(class);
        if IsNilpotentGroup(T) then
            largest := Maximum(largest, Size(T));
        fi;
    od;
    return largest;
end;;

GeometricSum := function(a, k)
    return QuoInt(a^k-1, a-1);
end;;

# Return the largest cycle length of t -> at+j on the residues modulo u,
# under the assumption that its c-th power is the identity.
LargestAffineCycle := function(u, a, j, c)
    local divisors, leastPeriodCounts, k, common, fixed, exact, position,
          smaller, largest;
    divisors := DivisorsInt(c);
    leastPeriodCounts := [];
    largest := 0;
    for k in divisors do
        common := GcdInt(a^k-1, u);
        if (j*GeometricSum(a, k)) mod common=0 then
            fixed := common;
        else
            fixed := 0;
        fi;
        exact := fixed;
        for position in [1..Length(leastPeriodCounts)] do
            smaller := divisors[position];
            if k mod smaller=0 then
                exact := exact-leastPeriodCounts[position];
            fi;
        od;
        if exact<0 or exact mod k<>0 then
            Error("The least-period count is inconsistent for u = ", u,
                  ", a = ", a, ", j = ", j, ", c = ", c, ".");
        fi;
        Add(leastPeriodCounts, exact);
        if exact>0 then
            largest := k;
        fi;
    od;
    RequireEqual("the affine cycles account for every residue",
                 Sum(leastPeriodCounts), u);
    if largest=0 then
        Error("No affine cycle was found.");
    fi;
    return largest;
end;;

# For fixed u and r, let T=1+p^r+...+p^((c-1)r) and g=gcd(u,T).
# The solutions of (1) are j=k(u/g), with k modulo g.  Conjugation by s and f
# sends k respectively to
#
#     k+(1-p^r)/(u/g)   and   pk  (mod g).
#
# Their orbits are therefore precisely the GammaL(1,q)-conjugacy classes of
# subgroups having these fixed values of u and r.
JParameterData := function(q, u, r)
    local p, d, c, a, sum, g, step, delta, seen, representatives, k,
          orbit, cursor, next, image;
    p := Factors(q)[1];
    d := LogInt(q, p);
    c := QuoInt(d, r);
    a := p^r;
    sum := GeometricSum(a, c);
    g := GcdInt(u, sum);
    step := QuoInt(u, g);
    if (1-a) mod step<>0 then
        Error("The conjugation translation is not a valid j-parameter.");
    fi;
    delta := QuoInt(1-a, step) mod g;

    seen := BlistList([1..g], []);
    representatives := [];
    for k in [0..g-1] do
        if not seen[k+1] then
            Add(representatives, k);
            orbit := [k];
            seen[k+1] := true;
            cursor := 1;
            while cursor<=Length(orbit) do
                next := orbit[cursor];
                for image in [(next+delta) mod g, (p*next) mod g] do
                    if not seen[image+1] then
                        seen[image+1] := true;
                        Add(orbit, image);
                    fi;
                od;
                cursor := cursor+1;
            od;
        fi;
    od;
    return rec(c := c, a := a, sum := sum, g := g, step := step,
               classRepresentatives := representatives);
end;;

# Construct GammaL(1,q) as a polycyclic group.  This is called only when
# tau_L<=|L|; it is not used to enumerate the subgroups.
PcSemilinearModel := function(q)
    local p, d, n, cyclicNormal, automorphism, cyclicGalois, action, P,
          frobenius, singer;
    p := Factors(q)[1];
    d := LogInt(q, p);
    n := q-1;
    cyclicNormal := CyclicGroup(IsPcGroup, n);
    automorphism := GroupHomomorphismByImages(cyclicNormal, cyclicNormal,
        [cyclicNormal.1], [cyclicNormal.1^p]);
    if automorphism=fail then
        Error("The action on the Singer cycle is not defined for q = ", q,
              ".");
    fi;
    cyclicGalois := CyclicGroup(IsPcGroup, d);
    action := GroupHomomorphismByImages(cyclicGalois, Group(automorphism),
        [cyclicGalois.1], [automorphism]);
    if action=fail then
        Error("The semidirect-product action is not defined for q = ", q,
              ".");
    fi;
    P := SemidirectProduct(cyclicGalois, action, cyclicNormal);
    frobenius := Image(Embedding(P, 1), cyclicGalois.1);
    singer := Image(Embedding(P, 2), cyclicNormal.1);
    RequireEqual(Concatenation("order of GammaL(1,", String(q), ")"),
                 Size(P), d*n);
    RequireEqual(Concatenation("Singer generator order for q = ", String(q)),
                 Order(singer), n);
    RequireEqual(Concatenation("Frobenius generator order for q = ", String(q)),
                 Order(frobenius), d);
    RequireEqual(Concatenation("semilinear relation for q = ", String(q)),
                 singer^frobenius, singer^p);
    return rec(group := P, singer := singer, frobenius := frobenius);
end;;

GroupFromParameters := function(model, u, r, j)
    return Group([model.singer^u, model.frobenius^r*model.singer^j]);
end;;

VerifyOneField := function(q)
    local p, d, n, subgroupCount, classCount, belowOrderSubgroups,
          belowOrderClasses, equalOrderNilpotentSubgroups,
          equalOrderNilpotentClasses, belowOrderEqualitySubgroups,
          belowOrderEqualityClasses, hasEquality, model, u, r, data, k, j,
          orderL, largestCycle, largestOrbit, nL, tauL,
          isClassRepresentative, L, nuL, value, belowOrderRecords,
          equalityRecords;
    p := Factors(q)[1];
    d := LogInt(q, p);
    n := q-1;
    subgroupCount := 0;
    classCount := 0;
    belowOrderSubgroups := 0;
    belowOrderClasses := 0;
    equalOrderNilpotentSubgroups := 0;
    equalOrderNilpotentClasses := 0;
    belowOrderEqualitySubgroups := 0;
    belowOrderEqualityClasses := 0;
    belowOrderRecords := [];
    equalityRecords := [];
    hasEquality := false;
    model := fail;

    for u in DivisorsInt(n) do
        for r in DivisorsInt(d) do
            data := JParameterData(q, u, r);
            for k in [0..data.g-1] do
                j := k*data.step;
                RequireEqual("the subgroup closing condition",
                             (j*data.sum) mod u, 0);
                orderL := QuoInt(n, u)*data.c;
                if orderL>1 then
                    subgroupCount := subgroupCount+1;
                    isClassRepresentative := k in data.classRepresentatives;
                    if isClassRepresentative then
                        classCount := classCount+1;
                    fi;

                    largestCycle := LargestAffineCycle(u, data.a, j, data.c);
                    largestOrbit := QuoInt(n, u)*largestCycle;
                    nL := largestOrbit^2/orderL;
                    tauL := nL^3;

                    if tauL<=orderL then
                        if model=fail then
                            model := PcSemilinearModel(q);
                        fi;
                        L := GroupFromParameters(model, u, r, j);
                        RequireEqual("the order given by the subgroup parameters",
                                     Size(L), orderL);
                        if tauL=orderL then
                            if IsNilpotentGroup(L) then
                                hasEquality := true;
                                Add(equalityRecords,
                                    [q, [u, r, j], orderL, largestOrbit, nL,
                                     orderL, tauL/orderL]);
                                equalOrderNilpotentSubgroups :=
                                    equalOrderNilpotentSubgroups+1;
                                if isClassRepresentative then
                                    equalOrderNilpotentClasses :=
                                        equalOrderNilpotentClasses+1;
                                fi;
                            fi;
                        else
                            belowOrderSubgroups := belowOrderSubgroups+1;
                            if isClassRepresentative then
                                belowOrderClasses := belowOrderClasses+1;
                            fi;
                            nuL := LargestNilpotentOrder(L);
                            value := tauL/nuL;
                            Add(belowOrderRecords,
                                [q, [u, r, j], orderL, largestOrbit, nL,
                                 nuL, value]);
                            if value<1 then
                                Error("For q = ", q,
                                      " the subgroup [u,r,j] = ", [u, r, j],
                                      " gives z_L n_L^3 = ", value, ".");
                            elif value=1 then
                                hasEquality := true;
                                belowOrderEqualitySubgroups :=
                                    belowOrderEqualitySubgroups+1;
                                if isClassRepresentative then
                                    belowOrderEqualityClasses :=
                                        belowOrderEqualityClasses+1;
                                fi;
                            fi;
                        fi;
                    fi;
                fi;
            od;
        od;
    od;
    return rec(
        subgroupCount := subgroupCount,
        classCount := classCount,
        belowOrderSubgroups := belowOrderSubgroups,
        belowOrderClasses := belowOrderClasses,
        equalOrderNilpotentSubgroups := equalOrderNilpotentSubgroups,
        equalOrderNilpotentClasses := equalOrderNilpotentClasses,
        belowOrderEqualitySubgroups := belowOrderEqualitySubgroups,
        belowOrderEqualityClasses := belowOrderEqualityClasses,
        belowOrderRecords := belowOrderRecords,
        equalityRecords := equalityRecords,
        hasEquality := hasEquality);
end;;

ProperPrimePowers := Filtered([2..2^18-1],
    q -> IsPrimePowerInt(q) and not IsPrimeInt(q));;
RequireEqual("the number of proper prime powers below 2^18",
             Length(ProperPrimePowers), 149);

totalSubgroups := 0;;
totalSubgroupClasses := 0;;
belowOrderSubgroups := 0;;
belowOrderClasses := 0;;
equalOrderNilpotentSubgroups := 0;;
equalOrderNilpotentClasses := 0;;
belowOrderEqualitySubgroups := 0;;
belowOrderEqualityClasses := 0;;
belowOrderRecords := [];;
equalityRecords := [];;
equalityFields := [];;

for q in ProperPrimePowers do
    result := VerifyOneField(q);
    totalSubgroups := totalSubgroups+result.subgroupCount;
    totalSubgroupClasses := totalSubgroupClasses+result.classCount;
    belowOrderSubgroups := belowOrderSubgroups+result.belowOrderSubgroups;
    belowOrderClasses := belowOrderClasses+result.belowOrderClasses;
    equalOrderNilpotentSubgroups := equalOrderNilpotentSubgroups+
        result.equalOrderNilpotentSubgroups;
    equalOrderNilpotentClasses := equalOrderNilpotentClasses+
        result.equalOrderNilpotentClasses;
    belowOrderEqualitySubgroups := belowOrderEqualitySubgroups+
        result.belowOrderEqualitySubgroups;
    belowOrderEqualityClasses := belowOrderEqualityClasses+
        result.belowOrderEqualityClasses;
    Append(belowOrderRecords, result.belowOrderRecords);
    Append(equalityRecords, result.equalityRecords);
    if result.hasEquality then
        Add(equalityFields, q);
    fi;
    Print("q = ", q, ": ", result.subgroupCount,
          " nontrivial subgroups in ", result.classCount,
          " conjugacy classes.\n");
od;

RequireEqual("the total number of nontrivial subgroups",
             totalSubgroups, 1896985);
RequireEqual("the total number of nontrivial subgroup classes",
             totalSubgroupClasses, 17603);
RequireEqual("subgroups with n_L^3 below |L|", belowOrderSubgroups, 3);
RequireEqual("subgroup classes with n_L^3 below |L|", belowOrderClasses, 3);
RequireEqual("nilpotent subgroup equality cases with n_L^3 = |L|",
             equalOrderNilpotentSubgroups, 1);
RequireEqual("nilpotent class equality cases with n_L^3 = |L|",
             equalOrderNilpotentClasses, 1);
RequireEqual("subgroup equality cases with n_L^3 below |L|",
             belowOrderEqualitySubgroups, 0);
RequireEqual("class equality cases with n_L^3 below |L|",
             belowOrderEqualityClasses, 0);
RequireEqual("the fields attaining equality", equalityFields, [9]);
RequireEqual("the three subgroups with n_L^3 below |L|",
    belowOrderRecords,
    [[4, [1, 1, 0], 6, 3, 3/2, 3, 9/8],
     [8, [1, 1, 0], 21, 7, 7/3, 7, 49/27],
     [16, [1, 1, 0], 60, 15, 15/4, 15, 225/64]]);
RequireEqual("the nontrivial equality case",
    equalityRecords, [[9, [2, 1, 0], 8, 4, 2, 8, 1]]);

Print("All 1,896,985 nontrivial subgroups belonging to the 149 proper prime ",
      "powers q < 2^18 satisfy z_L n_L^3 >= 1.  They form 17,603 conjugacy ",
      "classes, and equality occurs precisely for q = 9.  Exactly three ",
      "subgroups have n_L^3 < |L|; exactly one has n_L^3 = |L| with L ",
      "nilpotent; and none of the first three attains equality.\n");
QUIT_GAP(0);
