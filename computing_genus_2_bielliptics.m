// In this file, we determine all genus 2 bielliptic curves which have at least
// one bielliptic Atkin--Lehner involution. For genus 2 curves which have no bielliptic
// Atkin--Lehner involutions, we then try to use results on automorphism groups
// and Jacobian decompositions to prove that they are not bielliptic. 

load "genus_2_AL_quotients.m";
load "genus_1_AL_quotients.m";
load "AL_identifiers.m";


// initializing genus_2_bielliptics: list of triples [C, E1, E2], where each of 
// C, E1, and E2 gives an Atkin--Lehner quotient X_0^D(N) (of genera 2, 1, and 1), 
// respectively, as a triple [* D, N, gens *] with W = <gens> <= W_0(D,N), such that 
// C is bielliptic with bielliptic AL quotient maps to E1 and E2. 
genus_2_bielliptics_one_AL := [];
genus_2_bielliptics_two_AL := [];

count := 0;

for C in genus_2_AL_quotients do 
	print "C: ", C;
	count := count + 1;
	print "Step out of 1580: ", count;
	D := C[1];
	N := C[2];
	Cgens := C[3];
	Cidentifier := gens_to_identifier(D*N,Cgens);
	H := HallDivisors(D*N);

	C_bielliptic_quotients := [];

	for m in [m : m in H | not (m in Cidentifier)] do
		C2gens := identifier_to_min_gens(D*N,gens_to_identifier(D*N,Cgens join {m}));
		C2 := [* D, N, C2gens *];
		if (C2 in genus_1_AL_quotients) and (not (C2 in C_bielliptic_quotients)) then 
			Append(~C_bielliptic_quotients,C2);
			if #C_bielliptic_quotients eq 2 then // found all bielliptic quotients
				break;
			end if;
		end if; 
	end for;

	if #C_bielliptic_quotients eq 1 then 
		Append(~genus_2_bielliptics_one_AL,[*C,C_bielliptic_quotients[1]*]);
	elif #C_bielliptic_quotients eq 2 then 
		Append(~genus_2_bielliptics_two_AL,[*C,C_bielliptic_quotients[1],C_bielliptic_quotients[2]*]);
	end if; 

end for; 

// SetOutputFile("genus_2_bielliptics_one_AL.m");
// print "genus_2_bielliptics_one_AL := ", genus_2_bielliptics_one_AL, ";";
// UnsetOutputFile();

// SetOutputFile("genus_2_bielliptics_two_AL.m");
// print "genus_2_bielliptics_two_AL := ", genus_2_bielliptics_two_AL, ";";
// UnsetOutputFile();



// for pairs for which we find no bielliptic AL involutions, we need to ensure
// there are no non-AL involutions. We first try using known results on automorphism
// groups to exclude this possibility

genus_2_remaining_bielliptic_candidates := [C : C in genus_2_AL_quotients | IsEmpty([L : L in (genus_2_bielliptics_one_AL cat genus_2_bielliptics_two_AL) | L[1] eq C])];

load "all_atkin_lehner_10k.m";
load "aut_checks.m";

for C in genus_2_remaining_bielliptic_candidates do
	D := C[1];
	N := C[2];

	if IsSquarefree(N) then 
		if IsOdd(D*N) then 
			if [D,N] in all_atkin_lehner_10k then 
				Exclude(~genus_2_remaining_bielliptic_candidates,C);
			end if;
		else 
			if all_atkin_lehner_KR_no_point_counts(D,N) eq true then
				Exclude(~genus_2_remaining_bielliptic_candidates,C);
			end if;
		end if;
	end if;
end for; 


// For remaining genus 2 curves, we check for simplicity of Jacobians to 
// ensure curves are not bielliptic. 
// If N is not squarefree, we don't necessarily know that all automorphisms of
// X_0^D(N)/W are defined over Q (by Kontogeorgis--Rotger Prop 1.5),
// so this only will tell us that this curve
// is not bielliptic over Q (but perhaps it is geometrically bielliptic). 

load "ribet_isog.m";

// SetOutputFile("ribet_excluded.m");
// print "ribet_excluded := [";
// UnsetOutputFile();

start_index := 1;
c := start_index - 1;

for X in [X : X in genus_2_remaining_bielliptic_candidates | Index(genus_2_remaining_bielliptic_candidates,X) ge start_index] do 
	
	print X;
	c := c+1;
	start_time := Cputime();

	print "step out of 173: ", c;
	
	D := X[1];
	N := X[2];
	gens := X[3];


	// we first try to compute the isogeny factors of the Jacobian of X using modular symbols
	// in level D*N
	M := ModularSymbols(D*N,2,-1); // modular symbols of level D*N, weight 2
                               // trivial character, and sign -1 over \Q
                               // -1 as sign picks out just 
                               // cusp forms with mult 1
    Snew := NewSubspace(CuspidalSubspace(M));
    ALdecomp := AtkinLehnerDecomposition(Snew);

    compatible_symbols_list := [];

    for V in ALdecomp do
        d := Dimension(V);  
        if d le 2 then  
	        print V;
	        if IsCompatible(D,signpattern(V),gens) then 
	            print "above V is compatible, dimension ", d;
	            Append(~compatible_symbols_list,V);
	            // since we know the Jacobian has dimension 2, finding
	            // just one isogeny factor is sufficient
	            break;
	        end if;
        end if;
    end for;

	if not IsEmpty(compatible_symbols_list) then 
		M := compatible_symbols_list[1];
		if Dimension(M) eq 2 then 
			if IsIrreducible(M) then 
				print "excluded X";
				SetOutputFile("ribet_excluded.m");
				print X, ",";
				UnsetOutputFile();
			end if;
		end if;

	// if a Jacobian factor was not found in level D*N, we perform a brute
	// force Ribet isogeny decomposition computation to get the isogeny factors 
	else 
		print "trying brute force check";
		X_isog_factors := IsogClassALQuotient(D,N,gens);

		// if Jac(X) is simple, we know X is not bielliptic
		if Dimension(X_isog_factors[1]) eq 2 then 
			print "excluded X";
			SetOutputFile("ribet_excluded.m");
			print X, ",";
			UnsetOutputFile();
		end if; 
	end if; 

	end_time := Cputime();

	print "step time: ", end_time-start_time;

end for; 


load "ribet_excluded.m";
genus_2_remaining_non_AL_bielliptic_candidates_final := [X : X in genus_2_remaining_bielliptic_candidates | not (X in ribet_excluded)];

SetOutputFile("genus_2_remaining_non_AL_bielliptic_candidates_final.m");
print "genus_2_remaining_non_AL_bielliptic_candidates_final := [";
print genus_2_remaining_non_AL_bielliptic_candidates_final;
print ";";
UnsetOutputFile();


