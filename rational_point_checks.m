// list of all triples (D,N,W) with X_0^D(N)/W having genus 0
load "genus_0_AL_quotients.m";

// list of all triples (D,N,W) with X_0^D(N)/W having genus 1
load "genus_1_AL_quotients.m";

// loading in functions for working with AL subgroups and their generating sets, as well as
// genus function for AL quotients
load "AL_identifiers.m";

// For triples (D,N,W) with X_0^D(N)/W having genus 0 or 1,
// we work to show X_0^D(N)/W has a rational point by showing there is W' <= W of order 2
// so that X_0^D(N)/W' has a rational CM point. 

genus_0_AL_quotients_rat_pts := [];
genus_0_AL_quotients_no_rat_pts := [];
genus_1_AL_quotients_rat_pts := [];
genus_1_AL_quotients_no_rat_pts := [];


load "depth_1_CM_residue_field.m";


"checking CM points when N is squarefree...";

for triple in [triple : triple in genus_1_AL_quotients cat genus_0_AL_quotients | IsSquarefree(triple[2])] do 
    D := triple[1];
    N := triple[2];
    W_gens := triple[3];

    rat_pts_m_values := [];
    m_values_W := [m : m in gens_to_identifier(D*N,W_gens) | m ne 1];

    // storing info of rational CM points on quotients X_0^D(N)/<w_m>
    for m in m_values_W do
        if Type(depth_1_has_rational_CM_pt(D,N,m)) eq RngIntElt then;
            Append(~rat_pts_m_values,m);
            break;
        end if; 
    end for;

    // If at least one quotient X_0^D(N)/<w_m> with w_m in W has a rational point,
    // then X_0^D(N)/W has a rational point 
    if rat_pts_m_values ne [] then 
        if triple in genus_1_AL_quotients then
            Append(~genus_1_AL_quotients_rat_pts,triple);
        elif triple in genus_0_AL_quotients then 
            Append(~genus_0_AL_quotients_rat_pts,triple);
        end if; 
    end if;
end for; 


// given D, N, W_gens a minimal generating set for W <= W_0(D,N), 
// provide a sequence of identifiers of index 2 subgroups W0 <= W.
index_2_subgroups := function(D,N,W_gens)

    index_2_subgroups := [];

    assert #W_gens ge 1;
    W := gens_to_identifier(D*N,W_gens); 
    W_min_gens_size := #W_gens; 

    for S in Subsets(Seqset(W),W_min_gens_size-1) do
        W0 := gens_to_identifier(D*N,S);
        if ((#W0 eq 2^(W_min_gens_size-1) and (not (W0 in index_2_subgroups)))) then
            Append(~index_2_subgroups,W0);
        end if;
    end for;

    return index_2_subgroups;
end function; 


// given D, N, W_gens a minimal generating set for W <= W_0(D,N), 
// provide a sequence of identifiers of all proper non-trivial subgroups W0 <= W.
AL_subgroups := function(D,N,W_gens)

    W_subgroups := [];

    assert #W_gens ge 1;
    W := gens_to_identifier(D*N,W_gens); 
    W_min_gens_size := #W_gens; 

    for i in [1..(#W_gens-1)] do // minimal number of generators

        for S in Subsets(Seqset(W),i) do
            W0 := gens_to_identifier(D*N,S);
            if ((#W0 eq 2^(i) and (not (W0 in W_subgroups)))) then
                Append(~W_subgroups,W0);
            end if;
        end for;
    end for; 

    return W_subgroups;
end function; 


"checking genus 2 covers...";
// for triples (D,N,W) of genus 1 for which we have not yet found a rational point, 
// we check for genus 2 double covers

for triple in [triple : triple in genus_1_AL_quotients | not (triple in genus_1_AL_quotients_rat_pts)] do 
    D := triple[1];
    N := triple[2];
    W_gens := triple[3];

    for W0 in index_2_subgroups(D,N,W_gens) do
        if quot_genus(D,N,W0) eq 2 then 
            Append(~genus_1_AL_quotients_rat_pts,triple);
            break;
        end if;
    end for;

end for;


// It could be the case that a genus 1 is covered by another genus 1 curve which has a genus 2 double cover

for triple in [triple : triple in genus_1_AL_quotients | not (triple in genus_1_AL_quotients_rat_pts)] do 
    D := triple[1];
    N := triple[2];
    W_gens := triple[3];

    for W0 in AL_subgroups(D,N,W_gens) do
        if [*D, N, identifier_to_min_gens(D*N,W0)*] in genus_1_AL_quotients_rat_pts then 
            Append(~genus_1_AL_quotients_rat_pts,triple);
            break;
        end if;
    end for;

end for;


// for triple (D,N,W) of genus 0, we check whether there is an elliptic curve cover found
// in the previous check

for triple in [triple : triple in genus_0_AL_quotients | not (triple in genus_0_AL_quotients_rat_pts)] do 
    D := triple[1];
    N := triple[2];
    W_gens := triple[3];

    for W0 in AL_subgroups(D,N,W_gens) do

        if [* D, N, identifier_to_min_gens(D*N,W0) *] in genus_1_AL_quotients_rat_pts then 
            Append(~genus_0_AL_quotients_rat_pts,triple);
            break;
        end if; 

    end for;
end for;


"checking local obstructions at primes dividing D...";
// Checking for local obstructions to rational points
load "dual_graphs.m";

"genus 0 checks: ";
// for triple in [triple : triple in genus_0_AL_quotients | IsSquarefree(triple[2])] do 
//     D := triple[1];
//     N := triple[2];
//     gens := triple[3];
//     print triple;

//     for p in PrimeDivisors(D) do 
//         if quotient_has_Qp_points(D,N,gens,p) eq false then 
//             Append(~genus_0_AL_quotients_no_rat_pts,triple);
//             break;
//         end if;
//     end for;
// end for;

// The local obstruction checks take at least 15 hours or so to complete, 
// so if reloading this file it's best to load in that information
load "genus_0_AL_quotients_no_rat_pts_Qp.m";


"genus 1 checks: ";
// for triple in [triple : triple in genus_1_AL_quotients | IsSquarefree(triple[2])] do 
//     D := triple[1];
//     N := triple[2];
//     gens := triple[3];
//     print triple;

//     for p in PrimeDivisors(D) do 
//         if quotient_has_Qp_points(D,N,gens,p) eq false then 
//             Append(~genus_1_AL_quotients_no_rat_pts,triple);
//             break;
//         end if;
//     end for;
// end for;

// The local obstruction checks take at least 15 hours or so to complete, 
// so if re-running this file it's best to load in that pre-computed information
load "genus_1_AL_quotients_no_rat_pts_Qp.m";



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


"checking local obstructions over reals for depth 1 quotients...";

for triple in [triple : triple in genus_0_AL_quotients | (#triple[3] eq 1) and (not (triple in genus_0_AL_quotients_no_rat_pts))] do 
    if not (depth_1_has_real_points(triple[1],triple[2],Setseq(triple[3])[1])) then 
        Append(~genus_0_AL_quotients_no_rat_pts,triple);
    end if; 
end for; 

for triple in [triple : triple in genus_1_AL_quotients | (#triple[3] eq 1) and (not (triple in genus_1_AL_quotients_no_rat_pts))] do 
    if not (depth_1_has_real_points(triple[1],triple[2],Setseq(triple[3])[1])) then 
        Append(~genus_1_AL_quotients_no_rat_pts,triple);
    end if; 
end for; 

// sanity checks
errors_0 := [triple : triple in genus_0_AL_quotients | (triple in genus_0_AL_quotients_rat_pts) and (triple in genus_0_AL_quotients_no_rat_pts)];
errors_1 := [triple : triple in genus_1_AL_quotients | (triple in genus_1_AL_quotients_rat_pts) and (triple in genus_1_AL_quotients_no_rat_pts)];


// creating lists of genus 0 and 1 quotients for which the (non)-existence of rational points
// has not yet been determined
genus_1_AL_quotients_unknown_rat_pts := [triple : triple in genus_1_AL_quotients | not (triple in genus_1_AL_quotients_rat_pts cat genus_1_AL_quotients_no_rat_pts)];
genus_0_AL_quotients_unknown_rat_pts := [triple : triple in genus_0_AL_quotients | not (triple in genus_0_AL_quotients_rat_pts cat genus_0_AL_quotients_no_rat_pts)];


// Hasse Minkowski check in genus 0:
// If g(X_0^D(N)/W) = 0, N = 1, and 2 divides D, then if we can find a w_m in W so that 
// X_0^D(N)/w_m has real points (by Ogg's criterion) then we know that X_0^D(N)/W has points
// everywhere locally (because the reduction over F_p is a smooth conic for all p not dividing D, and then
// we use Hensel), and hence by Hasse--Minkowski X_0^D(N)/W has a rational point
genus_0_AL_quotients_rat_pts_by_HM := [];

for triple in [triple : triple in genus_0_AL_quotients_unknown_rat_pts | (triple[2] eq 1) and (triple[1] mod 2 eq 0)] do
    D := triple[1];
    N := triple[2];
    gens := triple[3];
    W := gens_to_identifier(D*N,gens);

    real_points_check := false;
    for m in [m : m in W | m gt 1] do
        if depth_1_has_real_points(D,N,m) then 
            real_points_check := true;
            break;
        end if;
    end for; 

    if real_points_check then 
        Append(~genus_0_AL_quotients_rat_pts_by_HM,triple);
    end if; 
end for; 

for triple in genus_0_AL_quotients_rat_pts_by_HM do
    Append(~genus_0_AL_quotients_rat_pts,triple);
    Exclude(~genus_0_AL_quotients_unknown_rat_pts,triple);
end for;


// function for sorting two triples of the form [D,N,W_gens] where W_gens is a minimal generating set for 
// an Atkin--Lehner subgroup W of W_0(D,N)
sort_triples := function(x,y)
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


// By the thesis of Nualart--Riera, all genus 0 star quotients have rational points
// (we use this last simply to try establish as much as we can independently)
genus_0_rat_pts_by_NR := [triple : triple in genus_0_AL_quotients_unknown_rat_pts | #triple[3] eq #PrimeDivisors(triple[1]*triple[2])];

for triple in genus_0_rat_pts_by_NR do 
    Append(~genus_0_AL_quotients_rat_pts,triple);
    Exclude(~genus_0_AL_quotients_unknown_rat_pts,triple);
end for;


// Next we remove from unknowns quotients for which we have equations via work of Guo--Yang followed 
// by Padurariu--Schembri (for X_0^D(N) hyperelliptic) and of others including Gonzalez--Rotger and Kurihara 
// (for X_0^D(N) having genus 0 or 1).
// (we use this last simply to try establish as much as we can independently)
load "known_gonalities.m";

genus_0_in_PS_GY := [triple : triple in genus_0_AL_quotients_unknown_rat_pts | [triple[1],triple[2]] in ((genus_0 cat genus_1) cat (Q_gon_2 cat Qbar_gon_2))];
genus_1_in_PS_GY := [triple : triple in genus_1_AL_quotients_unknown_rat_pts | [triple[1],triple[2]] in ((genus_0 cat genus_1) cat (Q_gon_2 cat Qbar_gon_2))];


// quotients with top curves in GR06 remaining to check: 
// genus 0:
    [ [* 6, 5,
        { 6 }
    *], [* 6, 5,
        { 2, 3 }
    *], [* 6, 5,
        { 2, 5 }
    *], [* 6, 7,
        { 2, 3 }
    *], [* 6, 7,
        { 3, 7 }
    *], [* 6, 13,
        { 3 }
    *], [* 10, 3,
        { 2, 3 }
    *], [* 10, 7,
        { 2, 5 }
    *], [* 10, 7,
        { 5, 7 }
    *], [* 10, 7,
        { 10, 14 } ]
// genus 1:
    // [ [* 10, 7,
    //     { 2, 7 }
    // *] ]

// X_0^D(N) is given in GR06 (has genus 1) and X has a rational point
    // genus 0
for triple in [ [*6, 13, {2,3} *] ] do
    Append(~genus_0_AL_quotients_rat_pts,triple);
    Exclude(~genus_0_AL_quotients_unknown_rat_pts,triple);
end for;
    // genus 1  

// X is given in Padurariu--Schembri and has a rational point 
    // genus 0 
for triple in [
    [* 6, 17, {2,17}*],
    [* 10, 13, {5,13}*],
    [* 10,13, {10,26}*],
    [* 10, 19, {2,19}*], 
    [* 14, 3, {2,7}*],
    [* 14, 5, {14}*],
    [* 14, 5, {2,7}*],
    [* 15, 2, { 15 }*],
    [* 15, 2, { 3,5 }*],
    [* 15, 2, { 6,10 }*],
    [* 15, 4, {3, 5}*],
    [* 15, 4, {4,15}*],
    [* 15, 4, {12,15}*],
    [* 21, 2, {2,7}*],
    [* 26, 3, {2,13}*],
    [* 39, 2, {39}*],
    [* 39, 2, {3,13}*],
    [* 39, 2, {6,26}*]] do
    Append(~genus_0_AL_quotients_rat_pts,triple);
    Exclude(~genus_0_AL_quotients_unknown_rat_pts,triple);
end for; 
    // genus 1
for triple in [[*15,2,{3}*]] do
    Append(~genus_1_AL_quotients_rat_pts,triple);
    Exclude(~genus_1_AL_quotients_unknown_rat_pts,triple);
end for; 



Sort(~genus_0_AL_quotients_rat_pts,sort_triples);
Sort(~genus_0_AL_quotients_no_rat_pts,sort_triples);
Sort(~genus_0_AL_quotients_unknown_rat_pts,sort_triples);
Sort(~genus_1_AL_quotients_rat_pts,sort_triples);
Sort(~genus_1_AL_quotients_no_rat_pts,sort_triples);
Sort(~genus_1_AL_quotients_unknown_rat_pts,sort_triples);


SetOutputFile("genus_0_AL_quotients_rat_pts.m");
print "genus_0_AL_quotients_rat_pts := ", genus_0_AL_quotients_rat_pts,";";
UnsetOutputFile();

SetOutputFile("genus_0_AL_quotients_no_rat_pts.m");
print "genus_0_AL_quotients_no_rat_pts := ", genus_0_AL_quotients_no_rat_pts, ";"; 
UnsetOutputFile();

SetOutputFile("genus_0_AL_quotients_unknown_rat_pts.m");
print "genus_0_AL_quotients_unknown_rat_pts := ", genus_0_AL_quotients_unknown_rat_pts, ";"; 
UnsetOutputFile();

SetOutputFile("genus_1_AL_quotients_rat_pts.m");
print "genus_1_AL_quotients_rat_pts := ", genus_1_AL_quotients_rat_pts,";";
UnsetOutputFile();

SetOutputFile("genus_1_AL_quotients_no_rat_pts.m");
print "genus_1_AL_quotients_no_rat_pts := ", genus_1_AL_quotients_no_rat_pts, ";"; 
UnsetOutputFile();

SetOutputFile("genus_1_AL_quotients_unknown_rat_pts.m");
print "genus_1_AL_quotients_unknown_rat_pts := ", genus_1_AL_quotients_unknown_rat_pts, ";"; 
UnsetOutputFile();

SetOutputFile("genus_0_unknowns_in_PS_GY.m");
print "genus_0_unknowns_in_PS_GY := ", genus_0_in_PS_GY, ";";
UnsetOutputFile();

SetOutputFile("genus_1_unknowns_in_PS_GY.m");
print "genus_1_unknowns_in_PS_GY := ", genus_1_in_PS_GY, ";";
UnsetOutputFile();


load "genus_1_jacobian_isog_classes.m";

print "checking positivity of ranks for elliptic curve quotients...";

genus_1_AL_quotients_rat_pts_pos_rank := [];

for triple in genus_1_AL_quotients_rat_pts do 
    D := triple[1];
    N := triple[2];
    gens := triple[3];

    J := Explode([Jac : Jac in genus_1_jacobian_isog_classes | [*D,N,gens*] eq [*Jac[1],Jac[2],Jac[3]*]]);

    isog_class_member := EllipticCurve(J[4]);

    if Rank(isog_class_member) ge 1 then 
        Append(~genus_1_AL_quotients_rat_pts_pos_rank,triple);
    end if; 
end for;

SetOutputFile("genus_1_AL_quotients_rat_pts_pos_rank.m");
print "genus_1_AL_quotients_rat_pts_pos_rank := ";
print genus_1_AL_quotients_rat_pts_pos_rank, ";";
UnsetOutputFile();


print "Lastly, checking positivity of ranks for unknown genus 1 quotients...";

genus_1_AL_quotients_unknown_rat_pts_pos_rank := [];

for triple in genus_1_AL_quotients_unknown_rat_pts do 
    D := triple[1];
    N := triple[2];
    gens := triple[3];

    J := Explode([Jac : Jac in genus_1_jacobian_isog_classes | [*D,N,gens*] eq [*Jac[1],Jac[2],Jac[3]*]]);

    isog_class_member := EllipticCurve(J[4]);

    if Rank(isog_class_member) ge 1 then 
        Append(~genus_1_AL_quotients_unknown_rat_pts_pos_rank,triple);
    end if; 
end for;

SetOutputFile("genus_1_AL_quotients_unknown_rat_pts_pos_rank.m");
print "genus_1_AL_quotients_unknown_rat_pts_pos_rank := ";
print genus_1_AL_quotients_unknown_rat_pts_pos_rank, ";";
UnsetOutputFile();





