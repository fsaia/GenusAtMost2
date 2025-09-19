// For every genus 1 Atkin--Lehner quotients X = X_0^D(N)/W with W non-trivial and N squarefree, 
// we attempt to compute the isomorphism class of Jac(X) using the isogeny class and pre-computed 
// Kodaira symbols (this is where the N squarefree hypothesis is needed). 

// loading pre-computed information on isogeny classes and Kodaira symbols of genus 1 Jacobians
load "genus_1_jacobian_isog_classes.m";
load "genus_1_AL_quotient_symbols.m";

genus_1_AL_quotient_jacobian_isomorphism_classes := [];
genus_1_AL_quotient_jacobian_isomorphism_class_not_determined := [];

for J in [J : J in genus_1_jacobian_isog_classes | IsSquarefree(J[2])] do 
    D := J[1];
    N := J[2];
    gens := J[3];
    class_ref := J[4];

    // creating list of Kodaira symbols for the Jacobian
    J_symbols_int := Explode([J[4] : J in genus_1_AL_quotient_symbols | [* J[1], J[2], J[3] *] eq [* D, N, gens *]]);

    J_symbols := [];

    // Just making the J_symbols_int list into strings of the form "In" rather than an integer n for the length
    for p in PrimeDivisors(D) do 
        p_sym := KodairaSymbol(("I" cat IntegerToString(Explode([pair[2] : pair in J_symbols_int | pair[1] eq p]))));
        Append(~J_symbols, [* p, p_sym *]);
    end for;

    isogeny_class_candidates := IsogenousCurves(EllipticCurve(class_ref));

    // If the correct isogeny class over Q for the jacobian has exactly 1 element, 
    // then we know that is the right isomorphism class (should be rare; could only happen
    // if [W_0(D,N) : W] = 2 and the hyperelliptic involution is Atkin--Lehner)
    if #isogeny_class_candidates eq 1 then 
        Append(~genus_1_AL_quotient_jacobian_isomorphism_classes,[*D,N,gens,("\"" cat CremonaReference(isogeny_class_candidates[1])) cat "\""*]);
    
    // Otherwise, we exclude isogeny class members not matching Kodaira symbols at
    // primes dividing D
    else 
        for E in isogeny_class_candidates do
            for q in PrimeDivisors(D) do
                if KodairaSymbol(E,q) ne Explode([pair[2] : pair in J_symbols | pair[1] eq q]) then 
                    Exclude(~isogeny_class_candidates,E);
                    break;
                end if;
            end for;
        end for;

        if #isogeny_class_candidates eq 1 then 
            Append(~genus_1_AL_quotient_jacobian_isomorphism_classes,[*D,N,gens,("\"" cat CremonaReference(isogeny_class_candidates[1])) cat "\"" *]);
        else
            Append(~genus_1_AL_quotient_jacobian_isomorphism_class_not_determined, [*D,N,gens,[("\"" cat CremonaReference(E)) cat "\"" : E in isogeny_class_candidates] *]);
        end if;

    end if; 
end for;

SetOutputFile("genus_1_AL_quotient_jacobian_isomorphism_classes.m");
print "genus_1_AL_quotient_jacobian_isomorphism_classes := ", genus_1_AL_quotient_jacobian_isomorphism_classes, ";";
UnsetOutputFile();

SetOutputFile("genus_1_AL_quotient_jacobian_isomorphism_class_not_determined.m");
print "genus_1_AL_quotient_jacobian_isomorphism_class_not_determined := ", genus_1_AL_quotient_jacobian_isomorphism_class_not_determined, ";";
UnsetOutputFile();


genus_1_AL_quotient_not_sqfree_jacobian_isomorphism_classes := [];
genus_1_AL_quotient_not_sqfree_jacobian_not_determined := [];

for J in [J : J in genus_1_jacobian_isog_classes | not (IsSquarefree(J[2]))] do
    D := J[1];
    N := J[2];
    gens := J[3];
    class_ref := J[4];

    isogeny_class_candidates := IsogenousCurves(EllipticCurve(class_ref));

    // If the correct isogeny class over Q for the jacobian has exactly 1 element, 
    // then we know that is the right isomorphism class
    if #isogeny_class_candidates eq 1 then 
        Append(~genus_1_AL_quotient_not_sqfree_jacobian_isomorphism_classes,[*D,N,gens,("\"" cat CremonaReference(isogeny_class_candidates[1])) cat "\""*]);
    else 
        Append(~genus_1_AL_quotient_not_sqfree_jacobian_not_determined,[*D,N,gens,[("\"" cat CremonaReference(E)) cat "\"" : E in isogeny_class_candidates]*]);
    end if;
end for;

SetOutputFile("genus_1_AL_quotient_not_sqfree_jacobian_isomorphism_classes.m");
print "genus_1_AL_quotient_not_sqfree_jacobian_isomorphism_classes := ", genus_1_AL_quotient_not_sqfree_jacobian_isomorphism_classes, ";";
UnsetOutputFile();

SetOutputFile("genus_1_AL_quotient_not_sqfree_jacobian_not_determined.m");
print "genus_1_AL_quotient_not_sqfree_jacobian_not_determined := ", genus_1_AL_quotient_not_sqfree_jacobian_not_determined, ";";
UnsetOutputFile();


