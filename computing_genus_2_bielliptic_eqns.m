// genus_2_bielliptic_eqn : suppose X is a bielliptic genus two curve over Q
// with bielliptic quotients over Q
// 		E_1 : y^2 = x^3 + A_1x + B_1
//		E_2 : y^2 = x^3 + A_2x + B_2.
// Given the Short--Weierstrass coefficients for E_1 and E_2, we 
// return a list of models containing one model over Q for X. This uses the method outlined in Proposition 2.1
// of the 2024 paper "Equations of Shimura curves of genus two" by González--Rotger. 

genus_2_bielliptic_eqns := function(A1,B1,A2,B2);

	A<a,b> := AffineSpace(Rationals(),2);

	f1 := 27*a^3*B2 - (2*A1^3+27*B1^2+9*A1*B1*b + 2*A1^2*b^2-B1*b^3);
	f2 := 9*a^2*A2 - (-3*A1^2 + 9*B1*b + A1*b^2); 

	S := Scheme(A,[f1,f2]);

	Pts := Setseq(RationalPoints(S));

	hypell_eqns := [];

	for pt in Pts do 

		a1 := pt[1]; 
		b1 := pt[2];
		c1 := (3*A1+b1^2)/(3*a1);
		d1 := (27*B1+9*A1*b1+b1^3)/(27*(a1^2));

		P<x> := PolynomialRing(Rationals());
		f := a1*x^6+b1*x^4+c1*x^2+d1;

		if IsEmpty({g : g in hypell_eqns | IsIsomorphic(HyperellipticCurve(f),HyperellipticCurve(g))}) then 
			Append(~hypell_eqns,f);
		end if; 

	end for; 

	return hypell_eqns;

end function;


load "genus_2_bielliptics_one_AL.m";
load "genus_2_bielliptics_two_AL.m";
load "genus_1_AL_quotient_jacobian_isomorphism_classes.m";
load "ribet_isog.m";

// SetOutputFile("genus_2_bielliptics_eqn_determined_initial.m");
// print "genus_2_bielliptics_eqn_determined_initial := [";
// UnsetOutputFile();

// SetOutputFile("genus_2_bielliptics_eqn_not_determined_initial.m");
// print "genus_2_bielliptics_eqn_not_determined_initial := [";
// UnsetOutputFile();

// function for sorting elements of genus_2_bielliptic_one_AL cat genus_2_bielliptics_two_AL
sort_bielliptics := function(x,y)
	x := x[1];
	y := y[1];
    D_diff := x[1]-y[1];
    if D_diff ne 0 then 
        return D_diff;
    else
        N_diff := x[2]-y[2];
        if N_diff ne 0 then 
            return N_diff;
        else 
            x_gens := Sort(Setseq(x[3]));
            y_gens := Sort(Setseq(y[3]));
            subgroup_size_diff := #x_gens - #y_gens;
            if subgroup_size_diff ne 0 then 
                return subgroup_size_diff;
            else 
                distinguishing_index := Min([i : i in [1..#x_gens] | x_gens[i] ne y_gens[i]]);
                return x_gens[distinguishing_index] - y_gens[distinguishing_index];
            end if;
        end if;
    end if;
end function;

// concatenating and sorting genus 2 bielliptics lists
genus_2_bielliptics := Sort(genus_2_bielliptics_one_AL cat genus_2_bielliptics_two_AL,sort_bielliptics);

// currently skipped, Ribet brute force runtime is long
skipped_indices := [519,573,581];
	// [* [* 390, 11,
	//     { 2, 5, 13, 33 }
	// *], [* 390, 11,
	//     { 2, 3, 5, 11, 13 }
	// *] *]
	// [* [* 714, 5,
	//     { 2, 5, 17, 21 }
	// *], [* 714, 5,
	//     { 2, 3, 5, 7, 17 }
	// *] *]
	// [* [* 798, 5,
	//     { 2, 3, 19, 35 }
	// *], [* 798, 5,
	//     { 2, 3, 5, 7, 19 }
	// *] *]

// step counter
start_index := 1;
c := start_index-1;
start := Cputime();

_<x> := PolynomialRing(Rationals());

for X in [X : X in genus_2_bielliptics | (Index(genus_2_bielliptics,X) ge start_index) and (not (Index(genus_2_bielliptics,X) in skipped_indices) )] do
	 
	print X;
	c := c+1;
	print "step out of 639: ", c;
	step_start := Cputime();

	D := X[1][1];
	N := X[1][2];
	gens := X[1][3];

	// this checks that we know the isomorphism class of the elliptic curve X[2]
	if IsSquarefree(N) then 
		gensE1 := X[2][3];
		ref1 := Explode([J[4] : J in genus_1_AL_quotient_jacobian_isomorphism_classes | [*D,N,gensE1*] eq [*J[1],J[2],J[3]*]]);
		E1_list := [WeierstrassModel(EllipticCurve(ref1))];

		// The second Jacobian factor either corresponds to a bielliptic AL quotient, in which
		// case we know its isomorphism class, or a bielliptic non-AL quotient, in which case
		// we just know its isogeny class. 
		if #X eq 3 then
			gensE2 := X[3][3];
			ref2 := Explode([J[4] : J in genus_1_AL_quotient_jacobian_isomorphism_classes | [*D,N,gensE2*] eq [*J[1],J[2],J[3]*]]);
			E2_list := [WeierstrassModel(EllipticCurve(ref2))];
		else 
			// we try to compute the isogeny factors of the Jacobian using modular symbols
			// computations the determine the isogeny class of the second Jacobian factor
			print "trying symbols...";
			Jac_factors := isogeny_factors_from_symbols_and_dim(D,N,gens,2);

			// if the Jacobian factors were not found in level D*N, we perform the
			// ribet isogeny computation to get isogeny class of second Jacobian factor
			if #Jac_factors ne 2 then 
				print "trying brute force decomp...";
				Jac_factors := IsogClassALQuotient(D,N,gens);
			end if; 

			if IsIsogenous(EllipticCurve(Jac_factors[1]),E1_list[1]) then 
				E2 := EllipticCurve(Jac_factors[2]);
			else 
				E2 := EllipticCurve(Jac_factors[1]);
			end if; 

			E2_list := [WeierstrassModel(E) : E in IsogenousCurves(E2)];
		end if; 

	else 
		// we try to compute the isogeny factors of the Jacobian using modular symbols
		print "trying symbols...";
		Jac_factors := isogeny_factors_from_symbols_and_dim(D,N,gens,2);

		// if the Jacobian factors were not both found in level D*N, we perform the
		// ribet isogeny computation to get them 
		if #Jac_factors ne 2 then 
			print "trying brute force decomp...";
			Jac_factors := IsogClassALQuotient(D,N,gens);
		end if; 

		E1 := EllipticCurve(Jac_factors[1]);
		E2 := EllipticCurve(Jac_factors[2]);
		E1_list := [WeierstrassModel(E) : E in IsogenousCurves(E1)];
		E2_list := [WeierstrassModel(E) : E in IsogenousCurves(E2)];

	end if; 

	// initializing candidate hyperelliptic equations
	hypell_eqns := [];

	for E1 in E1_list do 
		coeffsE1 := Coefficients(E1);
		A1 := coeffsE1[4];
		B1 := coeffsE1[5];

		for E2 in E2_list do 
			coeffsE2 := Coefficients(E2);
			A2 := coeffsE2[4];
			B2 := coeffsE2[5];

			hypell_eqns := hypell_eqns cat genus_2_bielliptic_eqns(A1,B1,A2,B2); 
		end for;
	end for;

	if #hypell_eqns eq 1 then 
		SetOutputFile("genus_2_bielliptics_eqn_determined.m");
		print [* D,N,gens,hypell_eqns[1] *], ",";
		UnsetOutputFile();
	else
		SetOutputFile("genus_2_bielliptics_eqn_not_determined.m");
		print [* D,N,gens,hypell_eqns *], ",";
		UnsetOutputFile();
	end if;

	step_end := Cputime();
	print "step time: ", step_end - step_start;
end for;

end := Cputime();
"total time taken: ", end - start;









