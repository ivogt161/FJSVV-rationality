//Example 1.5 - Section 5.2

R<u,v,w> := PolynomialRing(Rationals(), 3);

Q1 := -31*u^2 + 12*u*v + 4*u*w - 6*v^2 + 8*v*w + 25*w^2;
Q2 := -25*u^2 + 120*u*v + 9*u*w + 30*v^2 - v*w;
Q3 := -8047*u^2 + 1092*u*v + 4*u*w - 1446*v^2 + 7*v*w - 25*w^2;

M1 := SymmetricMatrix(Q1);
M2 := SymmetricMatrix(Q2);
M3 := SymmetricMatrix(Q3);

AA<T> := PolynomialRing(Rationals());


MT := M1 + 2*T*M2 + T^2*M3;
GammaBranch:=Determinant(MT);
// -1133336585/4*T^6 + 27137987/2*T^5 + 1128363667/4*T^4 - 13441289*T^3 + 1875527*T^2 - 72144*T + 4366
4*GammaBranch;
// -1133336585*T^6 + 54275974*T^5 + 1128363667*T^4 - 53765156*T^3 + 7502108*T^2 - 288576*T + 17464
 


/*****************************************/
//Claims about Y(RR)
/*****************************************/
Roots(GammaBranch, RealField());
// [ <-1.00097187430029595946348180493, 1>, 
// <1.00127345061927853993335232327, 1> ]

for s in [0,2] do
    Qs := Evaluate(MT, s);
    D := Diagonalization(Qs);
    print s, [Sign(D[j][j]) : j in [1..3]] cat [-1];
end for;

// 0 [ -1, -1, 1, -1 ] semi-definite - points in fibers
// 2 [ -1, -1, -1, -1 ] negative definite - no points in fibers

MT;

Mi1 := -8047*T^2 - 50*T - 31;
Mi1;
Roots(Mi1, RealField());
Mi2 := Minor(MT, 3, 3);
Mi2;
Roots(Mi2, RealField());
Mi3 := Determinant(MT);
Mi3;
Roots(Mi3, RealField());
Evaluate(Mi3, 0);
Evaluate(Mi3, 2);

/*****************************************/
//Claims about Ptilde
/*****************************************/
F<i> := QuadraticField(-1);
Delta := Q3*Q1 - Q2^2;
// 248832*u^4 - 124416*u^3*v - 31862*u^3*w + 93312*u^2*v^2 - 62387*u^2*v*w - 200465*u^2*w^2 - 31104*u*v^3 + 2712*u*v^2*w +
//    27078*u*v*w^2 + 7776*v^4 - 11550*v^3*w - 35945*v^2*w^2 - 25*v*w^3 - 625*w^4

DeltaRestToLine := Evaluate(Delta, [T,1,0]);
// DeltaRestToLine for this Delta is equal to that for the Delta in Theorem 1.3(1), 
// so the rest of the code goes through exactly as there. 

points := Roots(DeltaRestToLine, F);
points;
// [ <-1/2*i, 1>, <1/4*(-i + 1), 1>, <1/4*(i + 1), 1>, <1/2*i, 1> ]

Deltatildevals := [];
for pp in points do
    junk, r := IsSquare(Evaluate(Q1, [pp[1], 1, 0]));
    junk, s := IsSquare(Evaluate(Q3, [pp[1], 1, 0]));
    if r*s ne Evaluate(Q2, [pp[1],1,0]) then
        s := -s;
    end if;
    Append(~Deltatildevals, [pp[1], 1, 0, r,s]);
    Append(~Deltatildevals, [pp[1], 1, 0, -r,-s]);
end for;
print Deltatildevals;
// [
//     [ -1/2*i, 1, 0, 1/2*(3*i - 4), 1/2*(21*i - 52) ],
//     [ -1/2*i, 1, 0, 1/2*(-3*i + 4), 1/2*(-21*i + 52) ],
//     [ 1/4*(-i + 1), 1, 0, 1/4*(7*i + 1), 1/4*(-143*i - 41) ],
//     [ 1/4*(-i + 1), 1, 0, 1/4*(-7*i - 1), 1/4*(143*i + 41) ],
//     [ 1/4*(i + 1), 1, 0, 1/4*(-7*i + 1), 1/4*(143*i - 41) ],
//     [ 1/4*(i + 1), 1, 0, 1/4*(7*i - 1), 1/4*(-143*i + 41) ],
//     [ 1/2*i, 1, 0, 1/2*(-3*i - 4), 1/2*(-21*i - 52) ],
//     [ 1/2*i, 1, 0, 1/2*(3*i + 4), 1/2*(21*i + 52) ]
// ]

M := Matrix([
  [  -i, 2, 4 - 3*i,  52 -  21*i ],
  [   i, 2, 4 + 3*i,  52 +  21*i ],
  [ 1-i, 4, 1 + 7*i, -41 - 143*i ],
  [ 1+i, 4, 1 - 7*i, -41 + 143*i ]
]);
M;
// [         -i           2    -3*i + 4  -21*i + 52]
// [          i           2     3*i + 4   21*i + 52]
// [     -i + 1           4     7*i + 1 -143*i - 41]
// [      i + 1           4    -7*i + 1  143*i - 41]
Determinant(M);
// -23040
Factorization(Integers()!Determinant(M));
// [ <2, 9>, <3, 2>, <5, 1> ]

/*****************************************/
//Claim about Gamma
/*****************************************/

Gamma := HyperellipticCurve(-GammaBranch);

print "Does Gamma have Q3 points?", IsLocallySoluble(Gamma, 3);

/******************************************************************************/
//Check that Delta and Deltatilde are smooth
//
/******************************************************************************/

DeltaCurve := Proj(quo<R | Delta>);

T<u,v,w,r,s> := PolynomialRing(Rationals(), 5);

Q1tilde := -31*u^2 + 12*u*v + 4*u*w - 6*v^2 + 8*v*w + 25*w^2 - r^2;
Q2tilde :=  -25*u^2 + 120*u*v + 9*u*w + 30*v^2 - v*w - r*s;
Q3tilde :=  -8047*u^2 + 1092*u*v + 4*u*w - 1446*v^2 + 7*v*w - 25*w^2 - s^2;

I := ideal<T | Q1tilde, Q2tilde, Q3tilde>;
DeltatildeCurve := Curve(Proj(T),I);

print "Is Delta smooth?", IsNonsingular(DeltaCurve);
print "Is Deltatilde smooth?", IsNonsingular(DeltatildeCurve);

