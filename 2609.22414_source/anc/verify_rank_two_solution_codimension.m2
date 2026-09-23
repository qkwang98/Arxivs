-- Independent computation of the fake indicial scheme in the rank 2 example.

verifyCheck = (label, condition) -> (
	if not condition then error("FAILED: " | label);
	print("PASS: " | label);
	);

R = QQ[d1,d2,d3,d4,d5,MonomialOrder => GRevLex];
f1 = d3^3*d5^3-d1^3*d2^2*d4;
f2 = d2^3*d4-d3^3*d5;
f3 = d2*d5^2-d1^3;
toricGenerators = ideal(f2,f3);
verifyCheck("third Groebner binomial follows from the complete intersection generators",
	f1 == d2^2*d4*f3-d5^2*f2);
verifyCheck("toric complete intersection has dimension three", dim(R/toricGenerators) == 3);
verifyCheck("toric complete intersection has degree twelve", degree(R/toricGenerators) == 12);
initialIdeal = monomialIdeal(d3^3*d5^3,d2^3*d4,d2*d5^2);
standardPairList = standardPairs initialIdeal;
verifyCheck("twelve standard pairs", #standardPairList == 12);
verifyCheck("initial ideal has degree twelve", degree(R/initialIdeal) == 12);

S = QQ[s1,s2,MonomialOrder => GRevLex];
falling = (value, exponent) -> product(0..exponent-1, k -> value-k);
theta2 = 2*s1+3*s2;
theta3 = -1-3*s1-3*s2;
theta4 = s1+s2;
theta5 = -3*s1-s2;
fakeIndicial = trim ideal(
	falling(theta3,3)*falling(theta5,3),
	falling(theta2,3)*theta4,
	theta2*falling(theta5,2)
	);
verifyCheck("fake indicial scheme has length twelve", degree(S/fakeIndicial) == 12);

targetComponent = trim ideal(3*s1+s2,(s1+s2)^2);
points = {
	{-1,2/3},
	{-2,4/3},
	{-3,2},
	{-1/7,3/7},
	{-2/7,6/7},
	{-5/7,8/7},
	{-4/7,5/7},
	{-3/7,2/7},
	{-6/7,4/7},
	{-1/2,1/2}
	};
decomposition = targetComponent;
for point in points do (
	pointIdeal := trim ideal(s1-point#0,s2-point#1);
	verifyCheck("listed point is reduced", degree(S/pointIdeal) == 1);
	decomposition = trim intersect(decomposition,pointIdeal);
	);
verifyCheck("target component has length two", degree(S/targetComponent) == 2);
verifyCheck("displayed primary decomposition", decomposition == fakeIndicial);

intrinsicTarget = ideal(s1,s2);
verifyCheck("intrinsic target space has dimension one", degree(S/intrinsicTarget) == 1);
verifyCheck("target coefficient defect has dimension one",
	degree(S/targetComponent)-degree(S/intrinsicTarget) == 1);

print "VERIFIED: the fake indicial scheme has eleven points and total length twelve.";
print "VERIFIED: only the fake exponent represented by (s1,s2)=(0,0) has multiplicity two, and its intrinsic coefficient image has codimension one.";
