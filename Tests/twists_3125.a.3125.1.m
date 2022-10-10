printf "Checking that we compute the same twists of 3125.a.3125.1 in 3 different ways...";

R<x> := PolynomialRing(Rationals());
C0 := HyperellipticCurve(R![0, 0, 0, 0, 0, 1], R![1]);
A0, phi0 := GeometricAutomorphismGroupViaPeriods(C0);
L := BaseRing(Domain(phi0(A0.1)));
T1 := AllTwists(C0, L : AutGrp := <A0, phi0>);
assert #T1 eq 2;


R<x> := PolynomialRing(Rationals());
C0 := HyperellipticCurve(R![0, 0, 0, 0, 0, 1], R![1]);
L := ext<K0|Polynomial(K0, [1, -1, 1, -1, 1])> where K0 is RationalField();
T2 := AllTwists(C0, L);
assert #T2 eq 2;

R<x> := PolynomialRing(Rationals());
C0 := HyperellipticCurve(R![0, 0, 0, 0, 0, 1], R![1]);
L := ext<K0|Polynomial(K0, [1, -1, 1, -1, 1])> where K0 is RationalField();
A0, phi0 := AutomorphismGroup(ChangeRing(C0, L));
T3 := AllTwists(C0, L : AutGrp := <A0, phi0>);
assert #T3 eq 2;


Texpected := [ PowerStructure(CrvHyp) |
HyperellipticCurve([Polynomial([RationalField() | 0, 0, 0, 0, 0, -1]), Polynomial([RationalField() | 1])]),
HyperellipticCurve([Polynomial([RationalField() | 0, -5, 0, 0, 0, 0, 1]), Polynomial([RationalField() | 0, 0, 0, 1])])
];

for Torig in [T1, T2, T3] do
  T := Torig; // so is mutable
  assert {Discriminant(elt) : elt in T} eq {3125, 30517578125};
  if Discriminant(T[1]) ne 3125 then
    T[2], T[1] := Explode(T);
  end if;
  for i in [1..2] do
    assert IsIsomorphic(T[i], Texpected[i]);
  end for;
end for;

