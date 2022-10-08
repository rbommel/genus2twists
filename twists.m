
declare verbose Twists, 1;

function ApplyGalois(f, rho)
	if Type(f) in {Map, MapAutSch} then
		// Given a morphism of curves, apply a Galois action to its coefficients.
		C := Domain(f);
		D := Codomain(f);
		E := DefiningEquations(f);
		Erho := [];
		for g in E do
			gC := Coefficients(g);
			mC := Monomials(g);
			Append(~Erho, &+[rho(gC[i])*mC[i] : i in [1..#gC]]);
		end for;
		return hom<C->D | Erho>;
	elif Type(f) eq AlgMatElt then
		// Given a matrix, apply a Galois action on its coefficients.
		return Matrix([ [rho(f[j][i]) : i in [1..NumberOfRows(f)]] : j in [1..NumberOfColumns(f)]]);
	end if;
end function;

function MapToAssociativeArray(M)
	// Turn a map (recursively) into an associative array in order to not recompute the map the whole time.
	A := AssociativeArray();
	for x in Domain(M) do
		N := M(x);
		if Type(N) eq Map then
			A[x] := MapToAssociativeArray(N);
		else
			A[x] := N;
		end if;
	end for;
	return A;
end function;

function H1(G, A, M)
	// Find all crossed morphisms modulo equivalence
	S := [g : g in Generators(G)];
	CM := [];
	for rho in CartesianPower(A, #S) do
		for a in A do
			for rho2 in CM do
				if {rho[i] eq a^(-1) * rho2(S[i]) * M[S[i]][a] : i in [1..#S]} eq {true} then
					continue rho;	// Crossed morphism is equivalent to earlier found one.
				end if;
			end for;
		end for;
		h := AssociativeArray();
		for i in [1..#S] do
			h[S[i]] := rho[i];
		end for;
		AddedNewOne := true;
		while #Keys(h) ne #G or AddedNewOne do
			AddedNewOne := false;
			for g1, g2 in Keys(h) do
				if not(g1*g2) in Keys(h) then
					h[g1*g2] := h[g1] * M[g1][h[g2]];
					AddedNewOne := true;
				elif h[g1*g2] ne h[g1] * M[g1][h[g2]] then
					continue rho;	// Cocycle condition has not been satisfied.
				end if;
			end for;
		end while;
		Append(~CM, map<G->A | g:->h[g]>);
	end for;
	return CM;
end function;

function HilbertNinety(nu, K, rho)
	repeat
		repeat
			M0 := Matrix([[ &+[Random([-10..10])*K.1^e : e in [0..Degree(K)-1]] : i in [1,2]]: j in [1,2]]);
			M := &+[ ApplyGalois(M0, rho(g^(-1))) * nu(g) : g in Domain(nu) ];
		until Determinant(M) ne 0;
	until {ApplyGalois(M, rho(g^(-1)))^(-1)*M eq nu(g) : g in Domain(nu)} eq {true};
	return M;
end function;

function GetCoefficients(f, M)
	c, m := CoefficientsAndMonomials(f);
	assert(Set(m) subset M);
	C := AssociativeArray();
	for m in M do
		C[m] := 0;
	end for;
	for i in [1..#c] do
		C[m[i]] := c[i];
	end for;
	return C;
end function;

function ExtendToGL2(nu)
	A := AssociativeArray();
	for g in Domain(nu) do
		f := DefiningEquations(nu(g));
		R<x,y,z> := Parent(f[1]);
		cx := GetCoefficients(f[1], [x,z]);
		cy := GetCoefficients(f[2], [y]);
		cz := GetCoefficients(f[3], [x,z]);
		a := cx[x];
		b := cx[z];
		c := cz[x];
		d := cz[z];
		e := cy[y];
		lambda := e * (a*d - b*c)^(-1);
		a /:= lambda;
		b /:= lambda;
		c /:= lambda;
		d /:= lambda;
		A[g] := Matrix([ [a,b], [c,d] ]);
	end for;
	return map< Domain(nu)->Parent(A[Random(Domain(nu))]) | x :-> A[x] >;
end function;

function ParticularTwist(C, K, G, phi, rho, nu)
	// C is a curve over a Galois number field K
	// G is the (abstract) Galois group of K over Q
	// rho maps elements of G to automorphisms of K
	// nu is a cocycle from G to the group of automorphisms A of C
	// phi maps elements of A to actual automorphisms of C

	// First some basic assertions, surely the method could be generalised
	assert(Type(C) eq CrvHyp);
	assert(IsSimplifiedModel(C));
	assert(Genus(C) eq 2);

	// Lift nu to GL2 and apply Hilbert 90
	nuLift := ExtendToGL2(nu*phi);
	M := HilbertNinety(nuLift, K, rho)^(-1);

	// Find curve
	R<x> := PolynomialRing(K);
	a := M[1][1]; b := M[1][2]; c := M[2][1]; d := M[2][2];
	f := Determinant(M)^(-2) * (c*x + d)^6 * Evaluate(HyperellipticPolynomials(C), (a*x+b)/(c*x+d));
	assert Denominator(f) eq 1;
	assert {c in Rationals() : c in Coefficients(Numerator(f))} eq {true};
	H := HyperellipticCurve(ChangeRing(Numerator(f), Rationals()));
	Hs := ReducedMinimalWeierstrassModel(H);

	return Hs;
end function;

intrinsic BaseChangeAutomorphismGroup(G::Grp, phi::Map, L::FldNum) -> Gpr, Map
	{ Base change automorphism group of a curve to a bigger field. }
	CK := Domain(phi(Identity(G)));
	K := BaseRing(CK);
	require K subset L: "Field of definiting not contained inside L";
	CL := BaseChange(CK, L);
	A := AssociativeArray();
	for g in G do
		rhoG := map< CL->CL | [CoordinateRing(Ambient(CL))!f : f in DefiningEquations(phi(g))] >;
		_, rhoG := IsAutomorphism(rhoG);
		A[g] := rhoG;
	end for;
	rho := map< G->Aut(CL) | [ car< G, Aut(CL) > | <g, A[g]> : g in G]>;
	return G, rho;
end intrinsic;

intrinsic PushforwardAutomorphismGroup(G::Grp, phi::Map, m::Map) -> Gpr, Map
	{ Base change automorphism group of a curve to a different model. }
	C0 := Domain(m);
	C1 := Codomain(m);
	m1 := Inverse(m);
	require C0 eq Domain(phi(Identity(G))): "The domain of the map and the automorphism group do not match";
	rho := map< G -> Aut(C1) |
          [ car< G, Aut(C1) > |
					<g, newphi>  where _, newphi := IsAutomorphism(m1*phi(g)*m): g in G] >;
	return G, rho;
end intrinsic;

intrinsic AllTwists(C::CrvHyp, K::FldNum : CheckAutomorphisms:=true) -> SeqEnum[CrvHyp]
	{ compute all the twists of C over K }
	vprint Twists: Sprintf("AllTwists(C, K), where C:=%o, K:=%o", C, K);
	require Degree(K) gt 1 : "second argument cannot be the rationals";
	// First compute the Galois group of K to check that K is Galois.
	vprintf Twists: "Computing GaloisGroup(K)...";
	vtime Twists:
	G := GaloisGroup(K);
	require #G eq AbsoluteDegree(K): "K is not Galois";
	vprintf Twists: "Computing AutomorphismGroup(K)...";
	vtime Twists:
	G, _, rho := AutomorphismGroup(K);

	// Now compute the automorphisms of C_K and check that these are all geometric automorphisms.
	C := SimplifiedModel(C);
	vprint Twists: "New model for C = ", C;
	vprintf Twists: "Computing automorphism of C over K...";
	vtime Twists:
	A, phi := AutomorphismGroup(ChangeRing(C, K));
	if CheckAutomorphisms then
		vprintf Twists: "Computing automorphism of C over Qbar...";
		vtime Twists:
		Abar := GeometricAutomorphismGroup(C);
		assert #A eq #Abar;
		vprint Twists : "Automorphism group checked";
	end if;

	// Find H1
	vprintf Twists: "Computing action on hom-set...";
	vtime Twists:
	M := map< G->Maps(A,A) | g:-> map<A->A | a:->[b : b in A | ApplyGalois(phi(a),rho(g)) eq phi(b)][1] > >;
	vprintf Twists: "Caching action on hom-set...";
	vtime Twists:
	M := MapToAssociativeArray(M);
	vprint Twists : "Galois action on hom-set defined";
	vprintf Twists: "Computing H1...";
	vtime Twists:
	H1CK := H1(G, A, M);
	vprint Twists : "H1 found";

	// Find all twists
	L := [];
	for i->nu in H1CK do
		vprintf Twists : "Computing %o twist of %o...", i, #H1CK;
		vtime Twists:
		T := ParticularTwist(C, K, G, phi, rho, nu);
		Append(~L, T);
	end for;
	vprint Twists : "AllTwists(C, K) done";
	return L;
end intrinsic;
