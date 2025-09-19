// Here, we work to determine candidate non-elliptic equations for genus 1 quotients
// X = X_0^D(N)/W, with W non-trivial and N squarefree, for which we remain unsure of whether 
// X has a rational point. If we can exclude all such candidate equations, then we know X must 
// be an elliptic curve over \Q. 

load "genus_1_AL_quotients_unknown_rat_pts.m";
load "genus_0_AL_quotients_rat_pts.m";
load "genus_1_AL_quotient_jacobian_isomorphism_classes.m";
load "AL_identifiers.m";


// function for sorting elements of genus_1_AL_quotients_rat_pts_by_non_elliptic_test
// after each check
sort_non_elliptics := function(x,y)
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

// Given an elliptic curve E, returns a sequence
// of representatives in E(K) of generators for
// the Weak Mordell--Weil group E(K)/2E(K)
WeakMWreps := function(E)
    // SetClassGroupBounds("GRH"); // required to make MW group computation reasonable for (at least)
                                // the curve [210,1,{3,10}]
    generators := Generators(E);
    S := [Identity(E)];
    for P in Generators(E) do
        S := S cat [P+Q : Q in S];
    end for;
    return S;
end function;


// Given jac_ref the Cremona reference for the isomorphism class of the Jacobian 
// of a genus 1 curve C over Q and an integer d such that C has a point over Q(sqrt(d)) 
// whose image on a genus 0 quotient by an involution is rational, compute candidate
// equations for C using the first method outlined in section 2.1 of 
// González--Rotger 2006
non_elliptic_eqn_candidates := function(jac_ref,d);
    E := WeierstrassModel(EllipticCurve(jac_ref));
    Coeffs := Coefficients(E);

    A<x> := PolynomialRing(Rationals());

    A := Coeffs[4];
    B := Coeffs[5]; 

    Ed := EllipticCurve([A*d^2,B*d^3]);

    // We get one candidate equation from a representative for each non-trivial 
    // element of E(K)/[2]E(K)
    C_Candidates := [];

    for P in WeakMWreps(Ed) do 
        if not (IsIdentity(P)) then 
            P1 := P[1];
            P2 := P[2];
            f := x^4 - 6*P1*x^2 + 8*P2*x - 3*P1^2 - 4*A*d^2;
            Append(~C_Candidates,d*f);
        end if;
    end for; 

    return C_Candidates; 

end function; 


// initializing lists for genus one quotients X_0^D(N)/W
// for which we do and do not exclude all candidate non-elliptic equations
genus_1_AL_quotients_rat_pts_by_non_elliptic_test := [];
unknown_rat_pts_genus_1_equation_not_determined_initial := [];

// initializing list for those non-elliptic genus one quotients X_0^D(N)/W
// for which we are not able to find the setup needed to apply Gonzalez--Rotger's method
// in section 2.1 of their paper using CM point information on depth 1 quotients. 
unknown_rat_pts_genus_1_lacking_CM := [];

// quotients for which Magma has difficulty computing (generators for) the 
// Mordell--Weil group of the relevant twist that comes up in our method. 
trouble_quotients := [[*210,1,{3,10}*]];
// trouble? [* 1722, 1,{ 6, 14, 41 }*

load "cond_disc_list_allO.m";
load "depth_1_CM_residue_field.m";
print "running initial candidates checks...";

for T in [T : T in genus_1_AL_quotients_unknown_rat_pts | (IsSquarefree(T[2])) and (not (T in trouble_quotients))] do 
    print T;
    D := T[1];
    N := T[2];
    gens := T[3];
    W := gens_to_identifier(D*N,gens);

    genus_0_quotient_m0s := [m0 : m0 in HallDivisors(D*N) | (not (m0 in W)) and (quot_genus(D,N,gens_to_identifier(D*N,gens join {m0})) eq 0)];
    genus_0_quotient_with_rat_pts_m0s := [m0 : m0 in genus_0_quotient_m0s | [*D,N,identifier_to_min_gens(D*N,gens_to_identifier(D*N,gens join {m0}))*] in genus_0_AL_quotients_rat_pts];

    // initialize pair to be hopefully found 
    m0_disc_pair := []; 

    // checking if E satisfies the equivalent properties of GR06 Lemma 2.1 via 
    // a genus 0 Atkin--Lehner involution
    if not (IsEmpty(genus_0_quotient_with_rat_pts_m0s)) then 
        for m0 in genus_0_quotient_with_rat_pts_m0s do 
            rat_pt_info := depth_1_has_rational_CM_pt(D,N,m0);
            if Type(rat_pt_info) eq RngIntElt then 
                m0_disc_pair := [m0,rat_pt_info];
                break;
            end if;
        end for;
    end if;


    if not (IsEmpty(m0_disc_pair)) then 
        m0 := m0_disc_pair[1];
        d := m0_disc_pair[2];

        // iso class of the quotient elliptic curve
        Jac_ref := Explode([J[4] : J in genus_1_AL_quotient_jacobian_isomorphism_classes | [*D,N,W*] eq [*J[1],J[2],gens_to_identifier(J[1]*J[2],J[3])*]]);

        H := non_elliptic_eqn_candidates(Jac_ref,d);
        
        if #H eq 0 then 
            Append(~genus_1_AL_quotients_rat_pts_by_non_elliptic_test,[*D,N,gens*]);
        else
            Append(~unknown_rat_pts_genus_1_equation_not_determined_initial,[*D,N,gens,H*]);
        end if; 

    else
        Append(~unknown_rat_pts_genus_1_lacking_CM,[*D,N,gens*]);
    end if; 

end for; 


SetOutputFile("genus_1_AL_quotients_rat_pts_by_non_elliptic_test_initial.m");
print "genus_1_AL_quotients_rat_pts_by_non_elliptic_test_initial := ";
print genus_1_AL_quotients_rat_pts_by_non_elliptic_test;
print ";";
UnsetOutputFile();

SetOutputFile("unknown_rat_pts_genus_1_equation_not_determined_initial.m");
print "_<x> := PolynomialRing(Rationals());";
print "unknown_rat_pts_genus_1_equation_not_determined_initial := ";
print unknown_rat_pts_genus_1_equation_not_determined_initial;
print ";";
UnsetOutputFile();

SetOutputFile("unknown_rat_pts_genus_1_lacking_CM.m");
print "unknown_rat_pts_genus_1_lacking_CM := ";
print unknown_rat_pts_genus_1_lacking_CM;
print ";";
UnsetOutputFile();


// trying to use local obstruction checks at primes p | D to further exclude candidate equations 
// in the cases where they were not uniquely determined

load "dual_graphs.m";
unknown_rat_pts_genus_1_equation_not_determined_local_pts := [];
print "checking local obstructions...";

for X in unknown_rat_pts_genus_1_equation_not_determined_initial do 
    print X;
    D := X[1];
    N := X[2];
    gens := X[3];
    H := X[4];
    D_primes := PrimeDivisors(D);

    local_points_info := [];
    for p in D_primes do 
        Append(~local_points_info,[*p,quotient_has_Qp_points(D,N,gens,p)*]);
    end for; 

    for h in H do 
        C := HyperellipticCurve(h);
        for i in [1..#D_primes] do 
            if IsLocallySolvable(C,D_primes[i]) ne local_points_info[i][2] then 
                Exclude(~H,h);
                break;
            end if;
        end for;
    end for; 

    if #H eq 0 then 
        Append(~genus_1_AL_quotients_rat_pts_by_non_elliptic_test,[*D,N,gens*]);
    else 
        Append(~unknown_rat_pts_genus_1_equation_not_determined_local_pts,[*D,N,gens,H*]);
    end if;
end for;

Sort(~genus_1_AL_quotients_rat_pts_by_non_elliptic_test,sort_non_elliptics);

SetOutputFile("genus_1_AL_quotients_rat_pts_by_non_elliptic_test_local_pts.m");
print "genus_1_AL_quotients_rat_pts_by_non_elliptic_test_local_pts := ";
print genus_1_AL_quotients_rat_pts_by_non_elliptic_test;
print ";";
UnsetOutputFile();

SetOutputFile("unknown_rat_pts_genus_1_equation_not_determined_local_pts.m");
print "_<x> := PolynomialRing(Rationals());";
print "unknown_rat_pts_genus_1_equation_not_determined_local_pts := ";
print unknown_rat_pts_genus_1_equation_not_determined_local_pts;
print ";";
UnsetOutputFile();



// beginning code for real point checks on depth 1 quotients 

// psi_p 
// Given natural N, prime p, computes psi_p(N) as in Ogg83 Thm 2

psi_p := function(N,p)
    k := Valuation(N,p);
    if k eq 0 then 
        return 1;
    else 
        return p^k + p^(k-1); 
    end if;
end function; 

// count_local_embeddings
// Counts number of local embeddings of order R of discriminant f^2*delta_K into Eichler
// order of level N in the quaternion algebra over \Q of discriminant D, via Ogg83 Theorem 2 
count_local_embeddings := function(D,N,p,delta_K,f)

    assert IsDivisibleBy(D*N,p);
    
    if (f mod p eq 0) then 
        symbol_R_p := 1;
    else
        symbol_R_p := KroneckerSymbol(delta_K,p);
    end if; 

    if (D mod p) eq 0 then // case i
        return 1 - symbol_R_p;

    elif (N mod p) eq 0 then 

        k := Valuation(N,p);
        l := Valuation(f,p);

        if k eq 1 then // case ii
            return 1 + symbol_R_p;

        elif k ge (2+2*l) then  // case iii a
            if KroneckerSymbol(delta_K,p) eq 1 then
                return 2*psi_p(f,p); 
            else
                return 0;
            end if; 

        elif k eq (1+2*l) then  // case iii b
            if KroneckerSymbol(delta_K,p) eq 1 then
                return 2*psi_p(f,p);
            elif KroneckerSymbol(delta_K,p) eq 0 then
                return p^l;
            else 
                return 0;
            end if;

        elif k eq 2*l then  // case iii c
            return p^(l-1)*(p+1+KroneckerSymbol(delta_K,p));

        elif (f^2 mod p*N) eq 0 then // case iii d
            if (k mod 2) eq 0 then
                return p^k+p^(k-1);
            else
                return 2*p^k;
            end if;

        end if;
    end if;
end function; 

// sqfree_part
// given positive integer m, returns the sqfree part of m
sqfree_part := function(m)
    S := 1;
    for pair in Factorization(m) do
        v := Valuation(m,pair[1]);
        if (v mod 2) eq 1 then 
            S := S*pair[1];
        end if;
    end for;

    return S;
end function; 

// depth_1_has_real_points: given D, N, and m dividing DN, returns true if
// X_0^D(N)/<w_m> has a real point and false otherwise. This check uses Ogg83 Theorem 3
// (or really, just Proposition 1 there, since we don't care to count the number of componenets
// over \R here)
depth_1_has_real_points := function(D,N,m)
    assert IsDivisibleBy(D*N,m);
    assert m gt 1;

    real_points_check := true;

    if IsSquare(m) then 
        real_points_check := false;
    else 
        places_to_check := PrimeDivisors(ExactQuotient(D*N,m));
        m_sqfree_part := sqfree_part(m);
        _,f := IsSquare(Integers()!(m/m_sqfree_part));
        if (m mod 4) eq 1 then
            disc_K := m_sqfree_part;
        else 
            disc_K := 4*m_sqfree_part;
        end if; 

        for p in places_to_check do 
            // check local embedding of Z[sqrt(m)]
            if count_local_embeddings(D,N,p,disc_K,f) eq 0 then 

                if (m mod 4) eq 1 then 
                    for p in places_to_check do 
                        // check local embedding of Z[(1+sqrt(m))/2]
                        if count_local_embeddings(D,N,p,disc_K,2*f) eq 0 then 
                            real_points_check := false;
                            break;
                        end if;
                    end for;

                else 
                    real_points_check := false;
                    break;
                end if; 
            end if; 

            // in case we are in the m = 1 (mod 4) case and found no local embeddings at p
            if real_points_check eq false then 
                break;
            end if; 
        end for; 
    end if; 

    return real_points_check;
end function; 

_<x> := PolynomialRing(Rationals());
// hypell_has_real_pts : given a polynomial f over Q corresponding to the curve H: y^2 = f(x), 
// returns true if H has real points and false otherwise 
// this is based on the function TestRealSolvability implemented in local solvability checks in Magma.
hypell_has_real_pts := function(f)
    rts := [r[1] : r in Roots(Polynomial([ RealField()! c : c in Coefficients(f)] ))];
    if #rts eq 0 then
        return Evaluate(f,0) ge 0;
    else
        return true;
    end if;
end function; 


print "checking over reals...";
unknown_rat_pts_genus_1_equation_not_determined_real_pts := [];

// Each of the remaining curves in the v2 list has exactly 2 candidate equations remaining. 
// If one of these has real points and the other does not, then we use real point checks to try to
// determine which is correct. 
for X in unknown_rat_pts_genus_1_equation_not_determined_local_pts do
    D := X[1];
    N := X[2];
    gens := X[3];
    H := X[4];

    if #gens eq 1 then 
        // in this case, Ogg's criterion tells us whether X has real points
        has_real_pts := depth_1_has_real_points(D,N,Setseq(gens)[1]);
        for h in H do 
            if hypell_has_real_pts(h) ne has_real_pts then 
                Exclude(~H,h);
            end if; 
        end for; 
    else 
        W := gens_to_identifier(D*N,gens);
        // we check if there is some w_m in W so that X_0^D(N)/<w_m> has real points by Ogg's
        // criterion, which implies X has real points 
        for m in [m : m in W | m gt 1] do 
            if depth_1_has_real_points(D,N,m) then 
                for h in H do 
                    if not (hypell_has_real_pts(h)) then 
                        Exclude(~H,h); 
                    end if;  
                end for; 
                break;
            end if; 
        end for;
    end if;

    if #H eq 0 then 
        Append(~genus_1_AL_quotients_rat_pts_by_non_elliptic_test,[*D,N,gens*]);
    else 
        Append(~unknown_rat_pts_genus_1_equation_not_determined_real_pts,[*D,N,gens,H*]);
    end if;

end for;

Sort(~genus_1_AL_quotients_rat_pts_by_non_elliptic_test,sort_non_elliptics);

SetOutputFile("genus_1_AL_quotients_rat_pts_by_non_elliptic_test_real_pts.m");
print "genus_1_AL_quotients_rat_pts_by_non_elliptic_test_real_pts := ";
print genus_1_AL_quotients_rat_pts_by_non_elliptic_test;
print ";";
UnsetOutputFile();

SetOutputFile("unknown_rat_pts_genus_1_equation_not_determined_real_pts.m");
print "unknown_rat_pts_genus_1_equation_not_determined_real_pts := ";
print unknown_rat_pts_genus_1_equation_not_determined_real_pts;
print ";";
UnsetOutputFile();






