-- Independent Macaulay2 audit for the fixed-rank obstruction family.
--
-- It checks q=2 and q=3 by direct polynomial colon computations, and it
-- also checks the all-family local codimension from the three linear forms.

verifyCheck = (label, condition) -> (
    if not condition then error("FAILED: " | label);
    print("PASS: " | label);
    );

print "=== Fixed-rank boundary verification ===";

R2 = QQ[a1,b1,c1,d1,e1,a2,b2,c2,d2,e2,
        MonomialOrder => GRevLex];
U2 = ideal(
    a1+b1+c1+d1+e1,
    2*a1+3*d1+3*e1,
    3*a1+3*b1+2*c1+3*e1,
    a2+b2+c2+d2+e2,
    2*a2+3*d2+3*e2,
    3*a2+3*b2+2*c2+3*e2,
    a2-a1,d2-d1
    );
cprod2 = c1*c2;
dprod2 = d1*d2;
bprod2 = b1*b2;
eprod2 = e1*e2;
M2 = ideal(cprod2,dprod2);
P2 = ideal(bprod2*dprod2,cprod2*eprod2);
left2 = trim((U2*M2+P2) : ideal(cprod2));
right2 = trim((U2+P2) : ideal(cprod2));

S2 = QQ[x,y,MonomialOrder => GRevLex];
lambda2 = 2*x+3*y;
mu2 = 3*x+y;
z2 = x+y;
phi2 = map(S2,R2,{
    3*x,lambda2,-3*z2,z2,-mu2,
    3*x,lambda2,-3*z2,z2,-mu2
    });
leftImage2 = trim phi2 left2;
rightImage2 = trim phi2 right2;
expectedLeft2 = trim ideal(mu2^2,lambda2^2*z2^2);
expectedRight2 = trim ideal(lambda2^2,mu2^2);
singleton2 = trim ideal(z2^2,mu2^2);
allIntrinsic2 = trim intersect(expectedRight2,singleton2);
threePowers2 = trim ideal(lambda2^2,z2^2,mu2^2);

verifyCheck("q=2 left image under the Gale map",
    leftImage2 == expectedLeft2);
verifyCheck("q=2 right image under the Gale map",
    rightImage2 == expectedRight2);
verifyCheck("q=2 colengths are 8 and 4",
    degree(S2/leftImage2) == 8 and degree(S2/rightImage2) == 4);
verifyCheck("q=2 all-family local codimension is 3",
    degree(S2/threePowers2) == 3 and
    degree(S2/expectedLeft2)-degree(S2/allIntrinsic2) == 3);
verifyCheck("q=2 defect Hilbert series is u^2+2u^3+u^4",
    hilbertFunction(0,S2/leftImage2)-hilbertFunction(0,S2/rightImage2) == 0 and
    hilbertFunction(1,S2/leftImage2)-hilbertFunction(1,S2/rightImage2) == 0 and
    hilbertFunction(2,S2/leftImage2)-hilbertFunction(2,S2/rightImage2) == 1 and
    hilbertFunction(3,S2/leftImage2)-hilbertFunction(3,S2/rightImage2) == 2 and
    hilbertFunction(4,S2/leftImage2)-hilbertFunction(4,S2/rightImage2) == 1 and
    hilbertFunction(5,S2/leftImage2)-hilbertFunction(5,S2/rightImage2) == 0);

R3 = QQ[A1,B1,C1,D1,E1,A2,B2,C2,D2,E2,
        A3,B3,C3,D3,E3,MonomialOrder => GRevLex];
U3 = ideal(
    A1+B1+C1+D1+E1,
    2*A1+3*D1+3*E1,
    3*A1+3*B1+2*C1+3*E1,
    A2+B2+C2+D2+E2,
    2*A2+3*D2+3*E2,
    3*A2+3*B2+2*C2+3*E2,
    A3+B3+C3+D3+E3,
    2*A3+3*D3+3*E3,
    3*A3+3*B3+2*C3+3*E3,
    A2-A1,D2-D1,A3-A1,D3-D1
    );
Cprod3 = C1*C2*C3;
Dprod3 = D1*D2*D3;
Bprod3 = B1*B2*B3;
Eprod3 = E1*E2*E3;
M3 = ideal(Cprod3,Dprod3);
P3 = ideal(Bprod3*Dprod3,Cprod3*Eprod3);
left3 = trim((U3*M3+P3) : ideal(Cprod3));
right3 = trim((U3+P3) : ideal(Cprod3));

S3 = QQ[X,Y,MonomialOrder => GRevLex];
lambda3 = 2*X+3*Y;
mu3 = 3*X+Y;
z3 = X+Y;
phi3 = map(S3,R3,{
    3*X,lambda3,-3*z3,z3,-mu3,
    3*X,lambda3,-3*z3,z3,-mu3,
    3*X,lambda3,-3*z3,z3,-mu3
    });
leftImage3 = trim phi3 left3;
rightImage3 = trim phi3 right3;
expectedLeft3 = trim ideal(mu3^3,lambda3^3*z3^3);
expectedRight3 = trim ideal(lambda3^3,mu3^3);
singleton3 = trim ideal(z3^3,mu3^3);
allIntrinsic3 = trim intersect(expectedRight3,singleton3);
threePowers3 = trim ideal(lambda3^3,z3^3,mu3^3);

verifyCheck("q=3 left image under the Gale map",
    leftImage3 == expectedLeft3);
verifyCheck("q=3 right image under the Gale map",
    rightImage3 == expectedRight3);
verifyCheck("q=3 colengths are 18 and 9",
    degree(S3/leftImage3) == 18 and degree(S3/rightImage3) == 9);
verifyCheck("q=3 all-family local codimension is 7",
    degree(S3/threePowers3) == 7 and
    degree(S3/expectedLeft3)-degree(S3/allIntrinsic3) == 7);
verifyCheck("q=3 defect Hilbert series is u^3(1+u+u^2)^2",
    hilbertFunction(0,S3/leftImage3)-hilbertFunction(0,S3/rightImage3) == 0 and
    hilbertFunction(1,S3/leftImage3)-hilbertFunction(1,S3/rightImage3) == 0 and
    hilbertFunction(2,S3/leftImage3)-hilbertFunction(2,S3/rightImage3) == 0 and
    hilbertFunction(3,S3/leftImage3)-hilbertFunction(3,S3/rightImage3) == 1 and
    hilbertFunction(4,S3/leftImage3)-hilbertFunction(4,S3/rightImage3) == 2 and
    hilbertFunction(5,S3/leftImage3)-hilbertFunction(5,S3/rightImage3) == 3 and
    hilbertFunction(6,S3/leftImage3)-hilbertFunction(6,S3/rightImage3) == 2 and
    hilbertFunction(7,S3/leftImage3)-hilbertFunction(7,S3/rightImage3) == 1 and
    hilbertFunction(8,S3/leftImage3)-hilbertFunction(8,S3/rightImage3) == 0);

print "VERIFIED: fixed-rank defect lengths are 4 for q=2 and 9 for q=3,";
print "          and all-family local codimensions are 3 and 7.";
