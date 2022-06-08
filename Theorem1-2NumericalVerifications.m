//Theorem 1.2 \label{thm:IrratlConicBundle}


F2<sqrt2> := QuadraticField(2);

At<t> := PolynomialRing(Rationals(): Global := false);

f1 := 2- (t - 3)^2; // has roots 3\pm sqrt2
f2  := 2 - (t - 5)^2; // has roots 5 \pm sqrt 2
f3 := 3*(-t^2 - 4); //has no real roots

//By construction Qt has real lines when t in [5 - Sqrt(2), 3 + Sqrt(2)]


R<u,v,w> := PolynomialRing(Rationals(), 3);

Q1 :=  -u^2 - v^2 - 3*w^2;
Q2 :=  3*u^2 + 5*v^2;
Q3 :=  -7*u^2 - 23*v^2 - 12*w^2;

print "Q1 = ", Q1;
print "Q2 = ", Q2;
print "Q3 = ", Q3;



M1 := SymmetricMatrix(Q1);
M2 := SymmetricMatrix(Q2);
M3 := SymmetricMatrix(Q3);

F := Determinant(t^2*M1 + 2*t*M2 + M3);
assert F eq f1*f2*f3;

Delta := Q1*Q3 - Q2^2;

print "\nDelta = ", Delta;

Gamma := HyperellipticCurve(-F);

print "Does Gamma have Q3 points?", IsLocallySoluble(Gamma, 3);



/******************************************************************************/
//Delta is an quadric equation in u^2, v^2, w^2
//Diagonalize this equation
/******************************************************************************/
Ftilde := R!0;
for m in Generators(ideal<R | u, v, w>^2) do
    Ftilde := Ftilde + MonomialCoefficient(Delta, m^2)*m;
end for;

print "Discriminant of Delta restricted to w=0 is", Discriminant(Evaluate(Ftilde, [u,v,0]),v);
print "Since the discriminant is negative, there are no real points of Delta with w = 0.\n";



assert Evaluate(Ftilde, [u^2,v^2,w^2]) eq Delta; //Delta = Ftilde(u^2,v^2,w^2)
Mtilde := SymmetricMatrix(Ftilde);

D, B := Diagonalization(Mtilde); //Diagonalize Ftilde
assert B*Mtilde*Transpose(B) eq D;
Binvuvw := ChangeRing(Transpose(B)^(-1),R)*Matrix([[u],[v],[w]]);

utilde := Binvuvw[1][1];
vtilde := Binvuvw[2][1];
wtilde := Binvuvw[3][1];

assert D[1][1]*utilde^2 + D[2][2]*vtilde^2 + D[3][3]*wtilde^2 eq Ftilde; //Diagonalization of Ftilde


Eutilde := Evaluate(utilde, [u^2, v^2, w^2]);
Evtilde := Evaluate(vtilde, [u^2, v^2, w^2]);
Ewtilde := Evaluate(wtilde, [u^2, v^2, w^2]);

assert D[1][1]*Eutilde^2 + D[2][2]*Evtilde^2 + D[3][3]*Ewtilde^2 eq Delta;
printf "Delta = %o(%o)^2 + %o(%o)^2 +%o(%o)^2\n",D[1][1], Eutilde, D[2][2], Evtilde, D[3][3], Ewtilde;
print "This realizes Delta as a 4-1 cover of the conic", [D[1][1], D[2][2], D[3][3]], "which has a point";


/******************************************************************************/


/******************************************************************************/
//Parametrize conic given by Ftilde, using s as coordinate on P^1
/******************************************************************************/
As<s> := PolynomialRing(Rationals(): Global := false);
K<s> := FieldOfFractions(As);
S := ChangeRing(R, K);

C := Proj(quo<R | Ftilde>);

p := (PointSearch(C, 15))[1];
p := [p[1], p[2], p[3]];
assert Evaluate(Ftilde, p) eq 0; //basepoint for parametrization

IdealDefp := ideal<R | Minors(Matrix([[u,v,w],p]), 2)>;
gens := Generators(IdealDefp);
l0 := gens[1];
l1 := gens[2];

//intersect l0 - s*l1 with Ftilde
J := ideal<S | S!l0 - s*(S!l1), S!Ftilde>;
J := Saturation(J, ideal<S | gens>); //remove p from intersection
J := J + ideal<S | w - 1>;

wsq := 1;
usq := K!NormalForm(S!u, J); //parametrization of u
vsq := K!NormalForm(S!v, J); //parametrization of v

if Denominator(usq) eq Denominator(vsq) then //clear denominators
    wsq := As!(Denominator(usq)*wsq);
    vsq := As!(Denominator(usq)*vsq);
    usq := As!(Denominator(usq)*usq);
end if;


print "After parametrizing this conic, we obtain the following equations expressing k(Delta) as a degree 4 extension of k(s)";
print "u^2 = ", usq;
print "v^2 = ", vsq;
print "w^2 = ", wsq;
assert Evaluate(Ftilde, [usq,vsq,wsq]) eq 0; //parametrization works


M := Matrix([[S!usq,S!vsq,S!wsq],[S!u^2, S!v^2, S!w^2]]);
I := ideal<S | Minors(M, 2)>; //relations for u,v,w, given parametrization
I := I + ideal<S | w - 1>; //Delta has no real points when w =0, so we may work in affine where w = 1.
// print "GB of I";
// print GroebnerBasis(I);

assert S!Delta in I; //Equations indeed realize Delta as a 4-1 cover of P^1

/******************************************************************************/
//Find locus of P^1(R) that is the image of real points on Delta
/******************************************************************************/

//Finding conditions to be able to solve for u, v, and w

//Studying wsq
assert #Roots(wsq, RealField()) eq 0 and Evaluate(wsq, 0) gt 0;//wsq is always positive
print "\nNow we determine the image of real points of Delta on P1";
printf "w^2 = %o is always positive, so we can always solve for w\n", wsq;

//Studying usq
discu := Discriminant(usq);
discu := Numerator(discu)*Denominator(discu);
discu := SquarefreeFactorization(discu);
assert discu gt 0; //usq has real roots
cu,bu,au := Explode(Coefficients(usq));

_<sqrtdiscu> := QuadraticField(discu);
junk, factoru := IsSquare((bu^2 - 4*au*cu)/discu);
Roots_usq := [1/(2*au)*(-bu - factoru*sqrtdiscu), 1/(2*au)*(-bu + factoru*sqrtdiscu)];
if au lt 0 then
    printf "u^2 = = %o is nonnegative on interval %o, where sqrtdiscu^2=%o\n", usq, Roots_usq, discu;
else
    print "u^2 = = %o is nonpositive on interval %o, where sqrtdiscu^2=%o\n", usq, Roots_usq, discu;
end if;

assert [Evaluate(usq, rr) : rr in Roots_usq] eq [0,0]; //found roots of usq
RealRoots_usq := Sort([1/(2*au)*(-bu - factoru*Sqrt(discu)), 1/(2*au)*(-bu + factoru*Sqrt(discu))]);
assert RealRoots_usq[1] lt RealRoots_usq[2];

//Studying vsq
discv := Discriminant(vsq);
discv := Numerator(discv)*Denominator(discv);
discv := SquarefreeFactorization(discv);
assert discv gt 0; //vsq has real roots
cv,bv,av := Explode(Coefficients(vsq));

_<sqrtdiscv> := QuadraticField(discv);
junk, factorv := IsSquare((bv^2 - 4*av*cv)/discv);
Roots_vsq := [1/(2*av)*(-bv - factorv*sqrtdiscv), 1/(2*av)*(-bv + factorv*sqrtdiscv)];
assert [Evaluate(vsq, rr) : rr in Roots_vsq] eq [0,0]; //found roots of vsq
RealRootsvsq := Sort([1/(2*av)*(-bv - factorv*Sqrt(discv)), 1/(2*av)*(-bv + factorv*Sqrt(discv))]);
assert RealRootsvsq[1] lt RealRootsvsq[2];
if av lt 0 then
    printf "v^2 = = %o is nonnegative on interval %o, where sqrtdiscv^2=%o\n", vsq, Roots_vsq,discv;
else
    printf "v^2 = = %o is nonpositive on interval %o, where sqrtdiscv^2=%o\n", vsq, Roots_vsq,discv;
end if;
print "\n";


RealRoots := RealRootsvsq cat RealRoots_usq;
RealRoots := Sort(RealRoots);

intervals := [];
i := 0;
while i lt 4 do
    test := Floor(RealRoots[1] - 1);
    while (Evaluate(usq, test) lt 0 or Evaluate(vsq, test) lt 0 ) and i lt 4 do
        i := i + 1;
        if i ne 4 then
            test := 1/2*(RealRoots[i] + RealRoots[i + 1]);
        else 
            test := Ceiling(RealRoots[4] + 1);
        end if;
    end while;
    if i ne 4 then
        Append(~intervals, [RealRoots[i], RealRoots[i + 1]]);
    else
        test := Ceiling(RealRoots[4] + 1);
        if (Evaluate(usq, test) gt 0 and Evaluate(vsq, test) gt 0 ) then
            Append(~intervals, [RealRoots[4]]);
        end if;
    end if;
end while;

assert #intervals eq 1;//one interval where we can take square roots of usq and vsq

assert #(intervals[1]) eq 2; //interval is compact
leftbound := intervals[1][1];
rightbound := intervals[1][2];

print "v^2 is ", Evaluate(vsq, leftbound),  "at", leftbound, "and", 
        Evaluate(vsq, rightbound), "at", rightbound;
print "u^2 is ", Evaluate(usq, leftbound),  "at", leftbound, "and", 
        Evaluate(usq, rightbound), "at", rightbound;
print "So ", [leftbound, rightbound], "is the image of the real points on Delta\n\n";

minu := 0;
minu_achieved := rightbound;
minv := 0;
minv_achieved := leftbound;


//Now we have parametrized all real points of Delta.  Since there is one real interval of P^1 that is the image of the real points on Delta, Delta(R) has one connected component.  



/******************************************************************************/
//Find tangent lines to Delta contained in \Sigma.
/******************************************************************************/

//Delta(R) is a single connected component that is symmetric about [0,0,1]

print "Now we will compute tangent lines at real points of Delta where the tangent line does not intersect any real point transversely.";

//Find maximum absolute values of u/w, v/w
deriv_usqoverwsq := Numerator(Derivative(usq/wsq));
ExactRootsDeriv_usq := Roots(deriv_usqoverwsq, F2); 
// [ <-sqrt2 - 1, 1>, <sqrt2 - 1, 1> ]
RootsDeriv_usq := Sort(Roots(deriv_usqoverwsq, RealField()));
CriticalPoints_usq := intervals[1];
for r in RootsDeriv_usq do
    if r[1] ge leftbound and r[1] le rightbound then
        Append(~CriticalPoints_usq, r[1]);
    end if;
end for;

CriticalPoints_usq := Sort(CriticalPoints_usq);
CriticalValues_usq := [Evaluate(usq, cc)/Evaluate(wsq, cc): cc in CriticalPoints_usq];
maxu, indu := Maximum(CriticalValues_usq);
maxu_achieved := CriticalPoints_usq[indu];

deriv_vsqoverwsq := Derivative(vsq)*wsq - vsq*Derivative(wsq);
ExactRootsDeriv_vsq := Roots(deriv_vsqoverwsq, F2);
RootsDeriv_vsq := Sort(Roots(deriv_vsqoverwsq, RealField()));
CriticalPoints_vsq := intervals[1];
for r in RootsDeriv_vsq do
    if r[1] ge leftbound and r[1] le rightbound then
        Append(~CriticalPoints_vsq, r[1]);
    end if;
end for;

CriticalPoints_vsq := Sort(CriticalPoints_vsq);
CriticalValues_vsq := [Evaluate(vsq, cc)/Evaluate(wsq, cc): cc in CriticalPoints_vsq];
maxv, indv := Maximum(CriticalValues_vsq);
maxv_achieved := CriticalPoints_vsq[indv];

newinterval := Sort([maxv_achieved, maxu_achieved]);

assert not newinterval[1] in intervals[1];
assert not newinterval[2] in intervals[1];

assert newinterval[1] - (Sqrt(2) - 1) lt 10^(-Precision(newinterval[1]));
assert newinterval[2] - (Sqrt(2) + 1) lt 10^(-Precision(newinterval[2]));
exactnewinterval := [-1 - sqrt2, 1 + sqrt2];
exactmaxv_achieved := 1 + sqrt2;
exactmaxu_achieved := -1 - sqrt2;
assert Evaluate(deriv_vsqoverwsq, exactmaxv_achieved) eq 0;
assert Evaluate(deriv_usqoverwsq, exactmaxu_achieved) eq 0;

printf "u achieves its maximum at %o = %o\n", exactmaxu_achieved, maxu_achieved;
printf "v achieves its maximum at %o = %o\n", exactmaxv_achieved, maxv_achieved;
printf "Thus, as s runs along the interval %o = %o the tangent line to Delta does not intersect any real points\n\n", exactnewinterval, newinterval;
/******************************************************************************/



/******************************************************************************/
//look at lines tangent to Delta at point with s in interval [leftbound, umax]
/******************************************************************************/
Delu := Derivative(Delta, u);
Delv := Derivative(Delta, v);
Delw := Derivative(Delta, w);

musq := K!NormalForm(S!Delu^2, I)/K!NormalForm(S!Delw^2, I);
nusq := K!NormalForm(S!Delv^2, I)/K!NormalForm(S!Delw^2, I);

// mu*u + nu*v = w is equation of line tangent to Delta at a real point in the parametrization 
// mu = -(Delu/Delw)(pt), nu = -(Delv/Delw)(pt)
//want to consider this line for s in newinterval, because then the line does not meet Delta transversely in any realpoints

assert Evaluate(musq, exactmaxv_achieved) eq 0;
assert Evaluate(nusq, exactmaxu_achieved) eq 0;

//More generally we can consider the line mu*u + nu*v = lambda*w, for lamba-> infinity (and always >= 1), which moves away from Delta(RR) as lambda increases.

/********************************************************************/
//MAIN QUESTION:
//Is this line is tangent to QT for T in [5 - sqrt2, 3 + sqrt2]
//this line is tangent to Qt if and only if [mu, nu, -lambda] lies on the 
//dual conic of QT
/********************************************************************/

Bst<T>:= ChangeRing(At, K);
CC<lambda0> := PolynomialRing(As: Global := false);
C<lambda> := PolynomialRing(Bst: Global := false);

dualQToverK := [f2*f3, f1*f3, f1*f2];
dualQT := [ //Qt is diagonal so dual quadric equation is straightforward
    //Qt = f1u^2 + f2v^2 + f3w^2
    Evaluate(cc, T) : cc in dualQToverK];

assert Denominator(musq) eq Denominator(nusq);
num_musq := Numerator(musq);
num_nusq := Numerator(nusq);
denom := Denominator(musq);

tEqn := num_musq*dualQT[1] + num_nusq*dualQT[2] + lambda^2*denom*dualQT[3]; //the line is tangent to QT if and only if tEqn vanishes.
//So whenever s is in newinterval, we want 
//tEqn to have a root in [5-sqrt2, 3 + sqrt2]

function Eval_tEqn(c)
    Ac<s> := ChangeRing(As, Parent(c));
    CCc<lambda0c> := ChangeRing(CC,Ac);
    return Ac!num_musq*Evaluate(dualQToverK[1], c) + Ac!num_nusq*Evaluate(dualQToverK[2], c) + lambda0c^2*Ac!denom*Evaluate(dualQToverK[3], c);
end function;

print "The line is tangent to QT if and only if the following equation has a root in the interval", [5 - sqrt2, 3 + sqrt2];
print tEqn;


tangentLine := Evaluate(tEqn, 1);//this is line tangent to Delta at [us,vs,ws]
//want to consider this line for s in newinterval, because then the line does not meet Delta transversely in any realpoints

varylambda := denom*Evaluate(f2*f1, T);
assert tangentLine + (lambda^2 - 1)*varylambda eq tEqn; //The equation in T can be split into a part that corresponds to lambda = 1 (i.e., when the line is tangent to Delta) and the part where lambda is > 1.

assert Evaluate(f1, 3 + sqrt2) eq 0;
//Therefore Evaluate(tEqn, 3 + sqrt2) = musq*Evaluate(f2*f3, 3 + sqrt2) = musq*(-108*sqrt2 + 36)
assert Evaluate(f2*f3, 3 + Sqrt(2)) lt 0;
//Therefore tEqn evaluated at the endpoint 3 + sqrt2 is nonpositive


assert Evaluate(f2, 5 - sqrt2) eq 0;
//Therefore Evaluate(tEqn, 5 - sqrt2) = nusq*Evaluate(f1*f3, 5 - sqrt2) = musq*(-492*sqrt2 + 612)
assert Evaluate(f1*f3, 5- Sqrt(2)) lt 0;
//Therefore tEqn evaluated at the endpoint 5 - sqrt2 is nonpositive


/***************************************************************/
//Find point in [5 - sqrt2, 3 + sqrt2] where tEqn takes a positive value
/***************************************************************/


assert not IsSeparable(tangentLine);//tangentLine has double root
rr := Explode([r[1] : r in Roots(tangentLine) | r[2] eq 2]);
//CLAIM: for s in exactnewinterval, rr is contained in interval [5 - sqrt2, 3 + sqrt2] and tEqn(rr) > 0

print "We check that the above equation is nonpositive at the endpoints 5 - sqrt2, and 3 + sqrt2, and that the equation is nonnegative at ", rr;
print "(See the code for more details on the verification)";


//Find any local maxima and minima in exactnewinterval
Deriv_rr := Derivative(Numerator(rr))*Denominator(rr) - Derivative(Denominator(rr))*Numerator(rr);
critvals_rr := Sort([Evaluate(rr, newinterval[1]), Evaluate(rr, newinterval[2])] cat [Evaluate(rr, root) : root in Roots(Deriv_rr, RealField())]);

assert Minimum(critvals_rr) ge 5 - Sqrt(2);
assert Maximum(critvals_rr) le 3 + Sqrt(2);
//So rr is contained in the desired interval.


//Now to check that tEqn(rr) > 0 when s in exactnewinterval 
cofactor := As!((-1)*(s^2 - 2*s - 1)*(s^2 + 2*s - 1)*(s^2 + 1));
assert IsSquare(Evaluate(varylambda, rr)*cofactor);

//check cofactor has no roots within newinterval, so that cofactor does not change sign on newinterval
sorted_roots := Sort([r[1] : r in Roots(cofactor, RealField()) ]);
i := 1;
while sorted_roots[i] - newinterval[1] lt 0 and newinterval[1] - sorted_roots[i]gt 10^(1-Precision(newinterval[1])) do
    i := i + 1;
end while;
if i lt #sorted_roots then //sorted_roots[i] is left endpoint of newinterval
    assert sorted_roots[i+1] ge newinterval[2] or newinterval[2] - sorted_roots[i+1] le 10^(1-Precision(newinterval[1])); //next element of sorted_roots is greater than or equal to right endpoint of newinterval.
    assert Evaluate(cofactor, exactnewinterval[1]) eq 0;//verify with exact values
    assert Evaluate(cofactor, exactnewinterval[2]) eq 0;//verify with exact values
end if;

assert 1 ge newinterval[1] and 1 le newinterval[2]; //1 in newinterval
// print "tEqn has sign", Sign(Evaluate(cofactor, 1)), "at rr";

    
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

IsNonsingular(DeltaCurve);
IsNonsingular(DeltatildeCurve);




