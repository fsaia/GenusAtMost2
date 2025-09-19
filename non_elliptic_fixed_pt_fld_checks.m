load "non_elliptic_genus_1_equation_not_determined_real_points.m";
load "genus_0_AL_quotients_rat_pts.m";
load "AL_identifiers.m";
load "depth_1_CM_residue_field.m";

non_elliptic_genus_1_equation_determined_fixed_pt_fields := [];
non_elliptic_genus_1_equation_not_determined_v4 := [];

// SetOutputFile("non_elliptic_genus_1_equation_determined_fixed_pt_fields.m");
// print "non_elliptic_genus_1_equation_determined_fixed_pt_fields := [";
// UnsetOutputFile();

// SetOutputFile("non_elliptic_genus_1_equation_not_determined_fixed_pt_fields.m");
// print "non_elliptic_genus_1_equation_not_determined_fixed_pt_fields := [";
// UnsetOutputFile();

skipped_indices := [51,52];
start_index := 54; 
c := start_index-1;

for X in [X : X in non_elliptic_genus_1_equation_not_determined_real_points | Index(non_elliptic_genus_1_equation_not_determined_real_points,X) eq 52] do  
    step_start_time := Cputime();
    c := c+1;
    print "step out of 54: ", c;
    print X;

    D := X[1];
    N := X[2];
    gens := X[3];
    W := gens_to_identifier(D*N,gens);
    h1 := X[4][1];
    K1 := SplittingField(h1);
    h2 := X[4][2];
    K2 := SplittingField(h2);

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

    if not IsEmpty(m0_disc_pair) then 
        m0 := m0_disc_pair[1];
        d := m0_disc_pair[2];

        involutions_to_check := [m : m in gens_to_identifier(D*N, gens join {m0}) | not (m in W)];
        disc_cond_pairs := [];

        // creating list of CM orders that could correspond to fixed points
        // of elements in <W, w_m0> not in W
        for m in involutions_to_check do 
            if m eq 2 then 
                Append(~disc_cond_pairs,[-4,1]);
                Append(~disc_cond_pairs,[-8,1]); 

            elif (m mod 4) eq 3 then 
                disc_K := -1*sqfree_part(m); // K = Q(sqrt(-m))
                _,f := IsSquare(Integers()!(m/sqfree_part(m)));
                Append(~disc_cond_pairs,[disc_K,f]);
                Append(~disc_cond_pairs,[disc_K,2*f]); 

            else
                disc_K := -4*(sqfree_part(m)); // K = Q(sqrt(-m))
                _,f := IsSquare(Integers()!(m/sqfree_part(m)));
                Append(~disc_cond_pairs,[disc_K,f]);

            end if; 
        end for; 

        // creating list of CM orders corresponding to fixed points under the map X -> X/<w_m0>
        orders_with_fixed_pts := [];

        for order in disc_cond_pairs do
            if has_R_CM_points(D,N,order[1],order[2]) then 
                Append(~orders_with_fixed_pts,order);
            end if;
        end for; 

        print "orders_with_fixed_pts: ", orders_with_fixed_pts;
        L := Rationals(); 
        for order in orders_with_fixed_pts do 
            // For each specified order with a fixed point, we take a field K containing the residue
            // field of each o-CM point on X. We do this by choosing a minimal degree field
            // among the residue fields of covers of X of the form X_0^D(N)/<w_m> with 
            // m>1 in W. 
            d_K := order[1];
            f := order[2];

            // K is initialized as the ring class field corresponding to the order,
            // which certainly contains the residue field
            K := Compositum(NumberField(HilbertClassPolynomial(f^2*d_K)),NumberField(x^2-d_K));
            Kdeg := Degree(K);

            if D_R(D,d_K,f)*Nstar_R(N,d_K,f) ne 1 then 
                least_possible_Kdeg := ExactQuotient(Kdeg,2);
            else
                least_possible_Kdeg := ExactQuotient(Kdeg,4);
            end if;

            if ClassNumber(f^2*d_K) lt 16 then 
                print "checking order: ", order;
                for m in [m : m in W | m gt 1] do 
                    // we try using the function depth_1_CM_residue_field
                    // based on Corollary 5.14 of GR06. The reason this might return
                    // an error is due to lack of implementation of complex conjugation
                    // for ring class fields of 
                    print "trying res fld comp for m = ", m; 
                    try 
                        Km := depth_1_CM_residue_field(D,N,m,d_K,f);
                        Kmdeg := Degree(Km);

                        if Kmdeg lt Kdeg then 
                            K := Km;
                            Kdeg := Kmdeg;

                            if Kdeg eq least_possible_Kdeg then 
                                print "lowered degree of Km";
                                break;
                            end if;
                        end if; 
                    catch e
                        continue;
                    end try;

                end for; 
            end if;

            // compositing L with a field containing the residue field of each CM point by the 
            // specified order
            L := Compositum(L,K);
        end for; 

        print "Degree of compositum of fields containing fixed point res fields: ", Degree(L);

        // Unless the quotient X is depth 1, we don't have a result to tell us the residue field of the 
        // fixed points on X (rather than on X_0^D(N)). We do a coarse check here, checking
        // if one of the splitting fields K1 or K2 is not contained in L, which is certainly necessary. 
        if not IsSubfield(K1,L) then 
            Append(~non_elliptic_genus_1_equation_determined_fixed_pt_fields,[*D,N,gens,h2*]);
            print "h2 was correct model";
            step_end_time := Cputime();
            print "step time: ", step_end_time - step_start_time;

            SetOutputFile("non_elliptic_genus_1_equation_determined_fixed_pt_fields.m");
            Sprint([*D,N,gens,h2*]);
            print ",";
            UnsetOutputFile();

        elif not IsSubfield(K2,L) then 
            Append(~non_elliptic_genus_1_equation_determined_fixed_pt_fields,[*D,N,gens,h1*]);
            print "h1 was correct model";

            step_end_time := Cputime();
            print "step time: ", step_end_time - step_start_time;

            SetOutputFile("non_elliptic_genus_1_equation_determined_fixed_pt_fields.m");
            Sprint([*D,N,gens,h1*]);
            print ",";
            UnsetOutputFile();
        
        else 
            print "fixed pt field check didn't succeed :(";

            step_end_time := Cputime();
            print "step time: ", step_end_time - step_start_time;

            SetOutputFile("non_elliptic_genus_1_equation_not_determined_fixed_pt_fields.m");
            Sprint([*D,N,gens,[h1,h2]*]);
            print ",";
            UnsetOutputFile();

        end if;
    end if; 
end for; 


// first session: 68 hours





