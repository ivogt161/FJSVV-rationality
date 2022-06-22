//Example in paper.

R<u,v,w> := PolynomialRing(Rationals(), 3);

Q1 := -31*u^2 + 12*u*v + 9*u*w - 6*v^2 + 531*v*w + 25*w^2;
Q2 := -25*u^2 + 120*u*v - 31*u*w + 30*v^2 + 37*v*w;
Q3 := -8047*u^2 + 1092*u*v - 423*u*w - 1446*v^2 - 375*v*w - 25*w^2;

Q1;
// -31*u^2 + 12*u*v + 9*u*w - 6*v^2 + 531*v*w + 25*w^2
Q2;
// -25*u^2 + 120*u*v - 31*u*w + 30*v^2 + 37*v*w
Q3;
// -8047*u^2 + 1092*u*v - 423*u*w - 1446*v^2 - 375*v*w - 25*w^2


AA<T> := PolynomialRing(Rationals());

M1 := SymmetricMatrix(Q1);
M2 := SymmetricMatrix(Q2);
M3 := SymmetricMatrix(Q3);

MT := T^2*M1 + 2*T*M2 + M3;

GammaBranch := Determinant(MT); 

4*GammaBranch;
// 8813625*T^6 + 16982610*T^5 + 2262441955*T^4 + 464971196*T^3 - 
//     2293725941*T^2 - 291034182*T + 429774609



/*****************************************/
//Claims about Y(RR)
/*****************************************/
Roots(GammaBranch, RealField());
// [ <-0.915196746319255767689848888094, 1>, 
// <-0.572198419145318231218169168273, 1>, 
// <0.426221405237461987917606601050, 1>, 
// <0.848932732855715630715427359145, 1> ]

for s in [-3/4,0,1/2,1] do
    Qs := Evaluate(MT, s);
    D := Diagonalization(Qs);
    print s, [Sign(D[j][j]) : j in [1..3]] cat [-1];
end for;
// -3/4 [ -1, -1, -1, -1 ]
// 0    [ -1, -1,  1, -1 ]
// 1/2  [ -1, -1, -1, -1 ]
// 1    [ -1, -1,  1, -1 ]

/*****************************************/
//Claims about Ptilde
/*****************************************/
F<i> := QuadraticField(-1);
Delta := Q3*Q1 - Q2^2;
DeltaRestToLine := Evaluate(Delta, [T,1,0]);

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
//     [ -1/2*i, 1, 0, 1/2*(-3*i + 4), 1/2*(-21*i + 52) ],
//     [ -1/2*i, 1, 0, 1/2*(3*i - 4), 1/2*(21*i - 52) ],
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

/******************************************************************************/
//Check that Delta and Deltatilde are smooth
//
/******************************************************************************/

DeltaCurve := Proj(quo<R | Delta>);

T<u,v,w,r,s> := PolynomialRing(Rationals(), 5);

Q1tilde := -31*u^2 + 12*u*v + 9*u*w - 6*v^2 + 531*v*w + 25*w^2 - r^2;
Q2tilde :=  -25*u^2 + 120*u*v - 31*u*w + 30*v^2 + 37*v*w - r*s;
Q3tilde :=  -8047*u^2 + 1092*u*v - 423*u*w - 1446*v^2 - 375*v*w - 25*w^2 - s^2;

I := ideal<T | Q1tilde, Q2tilde, Q3tilde>;
DeltatildeCurve := Curve(Proj(T),I);

print "Is Delta smooth?", IsNonsingular(DeltaCurve);
print "Is Deltatilde smooth?", IsNonsingular(DeltatildeCurve);
