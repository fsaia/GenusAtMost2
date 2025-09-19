// Code for determing the Atkin--Lehner quotients $X_0^D(N)/W$, with $W \leq W_0(D,N)$ 
// not trivial, of genus at most $2$.

// load genus 0 star pairs
load "genus_0_stars.m";

// load genus 1 star pairs
load "genus_1_stars.m";

// load genus 2 star pairs
load "genus_2_stars.m";

// loading AL_identifiers.m, which contains code for going between
// lists of all elements and lists of generators for any subgroup 
// of the full Atkin--Lehner group W_0(D,N) of X_0^D(N). 
// This also loads file quot_genus.m, with function for computing the genus
// of an Atkin--Lehner quotient X_0^D(N)/W. 
load "AL_identifiers.m";


// initialize lists of quotients of genus zero and genus one

genus_0_AL_quotients_omegale4 := [];
genus_1_AL_quotients_omegale4 := [];
genus_2_AL_quotients_omegale4 := [];
genus_le2_stars_omega5 := [];

genus_le2_stars := (genus_0_stars cat genus_1_stars) cat genus_2_stars;
Sort(~genus_le2_stars);

// handling the omega(DN) <= 4 pairs and separating the omega(DN)=5 pairs
for pair in genus_le2_stars do 
    D := pair[1];
    N := pair[2]; 
    PDiv := PrimeDivisors(D*N);
    omega := #PDiv; 
    if omega le 4 then 

        for W in [W : W in AL_subgroups(D*N) | W ne {1} ] do // not considering top curves
            order_W := 2^#W; 

            g := quot_genus(D,N,gens_to_identifier(D*N,W));

            if g eq 0 then 
                Append(~genus_0_AL_quotients_omegale4,[*D, N, W*]); 

            elif g eq 1 then  
                Append(~genus_1_AL_quotients_omegale4,[*D, N, W*]); 

            elif g eq 2 then
                Append(~genus_2_AL_quotients_omegale4,[*D, N, W*]);

            end if; 

        end for;

    else
        Append(~genus_le2_stars_omega5,pair); // Note: omega(DN) = 5 is the highest 
                                            // number of distinct prime divisors for pairs in genus_le2_stars
    end if; 
end for;


// handling the omega(DN) = 5 pairs
genus_0_omega5 := [];
genus_1_omega5 := [];
genus_2_omega5 := [];

for pair in genus_le2_stars_omega5 do
    D := pair[1];
    N := pair[2];
    H := Seqset(HallDivisors(D*N)); 

    // dealing with quotients of depths 2, 3, and 4
    for genset in Subsets(H,4) do 

        W := gens_to_identifier(D*N,genset); // Atkin--Lehner subgroup of size up to 2^4. EVERY AL subgroup
                                           // of size 2^2 to 2^4 is realized in this way, as omega(DN)=5. 

        g := quot_genus(D,N,W); 

        gens := identifier_to_min_gens(D*N,W);

        if not ( ([* D, N, gens *] in ((genus_0_omega5 cat genus_1_omega5) cat genus_2_omega5))) then 
            if g eq 0 then 
                Append(~genus_0_omega5,[* D,N,gens *]);
            elif g eq 1 then 
                Append(~genus_1_omega5,[* D,N,gens *]);
            elif g eq 2 then 
                Append(~genus_2_omega5,[* D,N,gens *]);
            end if;
        end if;

    end for;

    // dealing with quotients of depth 1
    for m in [m : m in H | m ne 1] do

        g := quot_genus(D,N,[1,m]);

        if g eq 0 then 
            Append(~genus_0_omega5,[* D,N,{m} *]);
        elif g eq 1 then
            Append(~genus_1_omega5,[* D,N,{m} *]);
        elif g eq 2 then
            Append(~genus_2_omega5,[* D,N,{m} *]);
        end if;
    end for; 

    // dealing with star quotients 
    H := HallDivisors(D*N);
    gens := identifier_to_min_gens(D*N,H);
    g := quot_genus(D,N,H);

    if g eq 0 then 
        Append(~genus_0_omega5,[* D,N,gens *]);
    elif g eq 1 then
        Append(~genus_1_omega5,[* D,N,gens *]);
    elif g eq 2 then
        Append(~genus_2_omega5,[* D,N,gens *]);
    end if;

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


genus_0_AL_quotients := genus_0_AL_quotients_omegale4 cat genus_0_omega5;
Sort(~genus_0_AL_quotients,sort_triples);

genus_1_AL_quotients := genus_1_AL_quotients_omegale4 cat genus_1_omega5;
Sort(~genus_1_AL_quotients,sort_triples);

genus_2_AL_quotients := genus_2_AL_quotients_omegale4 cat genus_2_omega5;
Sort(~genus_2_AL_quotients,sort_triples);



SetOutputFile("genus_0_AL_quotients.m");
print "genus_0_AL_quotients := ";
genus_0_AL_quotients;
print ";";
UnsetOutputFile(); 

SetOutputFile("genus_1_AL_quotients.m");
print "genus_1_AL_quotients := ";
genus_1_AL_quotients;
print ";";
UnsetOutputFile(); 

SetOutputFile("genus_2_AL_quotients.m");
print "genus_2_AL_quotients := ";
genus_2_AL_quotients;
print ";";
UnsetOutputFile(); 


