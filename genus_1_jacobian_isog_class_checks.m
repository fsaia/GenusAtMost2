// Code for computing the isogeny class of $\text{Jac}(X)$ for each curve listed in 
// `genus_1_AL_quotients.m`.


// loading AL_identifiers.m, which contains code for going between
// lists of all elements and lists of generators for any subgroup 
// of the full Atkin--Lehner group W_0(D,N) of X_0^D(N). 
// This also loads file quot_genus.m, with function for computing the genus
// of an Atkin--Lehner quotient X_0^D(N)/W. 
load "AL_identifiers.m";


// loading dual_graphs.m, containing code used here for computing Kodaira symbols
// of Jacobians of genus 1 Atkin--Lehner quotients of X_0^D(N) at primes dividing D. 
load "dual_graphs.m";


// signpattern: given a space of modular symbols, returns the corresponding sign pattern
// corresponding to the action of Hecke operators for primes dividing the level
signpattern := function(V);
    signs := [];
    for pe in Factorization(Level(V)) do
        ALpe := AtkinLehnerOperator(V,pe[1]^pe[2]);
        lam := ALpe[1,1];
        assert ALpe eq Parent(ALpe)!lam;
        Append(~signs, <pe[1],pe[2],lam>);
    end for;
    
    return signs;

end function;


// Is Compatible: given a sign pattern of a modular symbol and 
// a set {m_1,...,m_r} of generators of an AL subgroup W,
// we check whether signpattern corresponds to a form fixed
// by the action of W on X_0^D(N)

IsCompatible := function(D,pattern,gens)

    compat_check := true;

    for m in gens do 

        m_sign := &*([1] cat [triple[3] : triple in pattern | triple[1] in PrimeDivisors(m)]);

        if m_sign ne (-1)^(#PrimeDivisors(GCD(D,m))) then
            compat_check := false;
            break;
        end if;
    end for;

    return compat_check;
end function;


// Given D, N, and gens so that W = <gens> is an Atkin--Lehner subgroup so that 
// X_0^D(N)/W has genus 1, looks in the space of modular symbols which are new of level
// D*N and of weight 2 and sign -1 to find a one-dimensional space which is compatible
// with the Atkin--Lehner action on Jac(X_0^D(N)/W) given by Ribet's isogeny. 
Genus1IsogenyClass := function(D,N,gens)
    M := ModularSymbols(D*N,2,-1); // modular symbols of level D*N, weight 2
                               // trivial character, and sign -1 over \Q
                               // -1 as sign picks out just 
                               // cusp forms with mult 1
    Snew := NewSubspace(CuspidalSubspace(M));
    ALdecomp := AtkinLehnerDecomposition(Snew);

    compatible_symbols_list := [];

    for V in ALdecomp do    
        if IsCompatible(D,signpattern(V),gens) then 
            Append(~compatible_symbols_list,V);
        end if;
    end for;

    // If no compatible space is found, it means it is not new of level D*N
    // (hence there is some conductor change between X_0^D(N) and X_0^D(N)/W).
    // It shouldn't happen that there is more than one compatible space of 
    // symbols, but we check for it as a sanity check. 
    if (#compatible_symbols_list ne 1) then 
        return "zero or more than one compatible symbol.";

    // This should not happen, and is just a sanity check
    else 
        M := compatible_symbols_list[1];
        if Dimension(M) ne 1 then 
            return "one compatible symbol, but not dimension 1.";
        else  
            E := EllipticCurve(M);
            return CremonaReference(E);
        end if; 
    end if;

end function;


// load genus 1 Atkin--Lehner quotients in form [D,N,gens] where W = <gens> is an Atkin--Lehner subgroup
load "genus_1_AL_quotients.m";

// Pre-computed Kodaira symbols for J = Jac(X_0^D(N)/W) with N squarefree
load "genus_1_AL_quotient_symbols.m";

SetOutputFile("genus_1_jacobian_isog_classes.m");
"genus_1_jacobian_isog_classes := [";
UnsetOutputFile();


Dcurrent := 1;
Ncurrent := 1;

start_index := 1;
count := start_index-1;

start_time := Cputime();

for triple in [quotient : quotient in genus_1_AL_quotients | Index(genus_1_AL_quotients,quotient) ge start_index] do 
    
    step_start_time := Cputime();

    D := triple[1];
    N := triple[2];
    gens := triple[3];

    count := count+1;
    print "step out of 1352: ", count;
    print "D, N, W_gens, g(X_0(DN)):", D, N, gens, GenusX0N(D*N);

    ref := Genus1IsogenyClass(D,N,gens);

    // If there is a level change in the associated space of symbols upon quotienting by W = <gens>,
    // then we proceed in another way
    if ref eq "zero or more than one compatible symbol." then 

        // in this case, by Kodaira symbol computations we know the conductor change is 
        // by a factor of N and we determine the isogeny class within the right level
        // using these Kodaira symbols at primes dividing D
        if (IsPrime(N)) and (IsEmpty([m : m in gens | m mod N eq 0])) then 

            // Getting pre-computed Kodaira symbols for J = Jac(X_0^D(N)/W)
            J_symbols_int := Explode([J[4] : J in genus_1_AL_quotient_symbols | [* J[1], J[2], identifier_to_min_gens(J[1]*J[2],gens_to_identifier(J[1]*J[2],J[3])) *] eq [* D, N, identifier_to_min_gens(D*N,gens_to_identifier(D*N,gens)) *]]);

            J_symbols := [];

            for p in PrimeDivisors(D) do 
                p_sym := KodairaSymbol(("I" cat IntegerToString(Explode([pair[2] : pair in J_symbols_int | pair[1] eq p]))));
                Append(~J_symbols, [* p, p_sym *]);
            end for;

            M := ModularSymbols(D,2,-1); // modular symbols of level D*N, weight 2
                               // trivial character, and sign -1 over \Q
                               // -1 as sign picks out just 
                               // cusp forms with mult 1
            Snew := NewSubspace(CuspidalSubspace(M));
            ALdecomp := AtkinLehnerDecomposition(Snew);

            dim_1_symbols := [space : space in ALdecomp | Dimension(space) eq 1];

            isogeny_class_candidates := &cat([IsogenousCurves(EllipticCurve(space)) : space in dim_1_symbols]);

            for E in isogeny_class_candidates do

                for q in PrimeDivisors(D) do
                    if KodairaSymbol(E,q) ne Explode([pair[2] : pair in J_symbols | pair[1] eq q]) then 
                        Exclude(~isogeny_class_candidates,E);
                        break;
                    end if;
                end for;
            end for;

            // These are sanity checks which should not occur
            if #isogeny_class_candidates gt 1 then
                print "more than one candidate was found";
            elif #isogeny_class_candidates eq 0 then 
                print "no candidates were found";
            else 
                ref := CremonaReference(Explode(isogeny_class_candidates));
            end if;

        else 
            // If N is not prime and there is a level change, then we use Ribet's isogeny and 
            // explicit decomposition of Jacobians to determine the isogeny class
            if (D ne Dcurrent) or (N ne Ncurrent) then // we don't want to recompute jacobians
                Dcurrent := D;
                Ncurrent := N;
                J0 := JZero(D*N);
            end if; 

            m_vars := &meet[ Kernel((-1)^((1+#PrimeDivisors(GCD(D,m))))*Matrix(AtkinLehnerOperator(J0,m))+1) : m in gens];

            _,JW := DefinesAbelianSubvariety(J0,m_vars);

            J := [A : A in Decomposition(JW) | IsDivisibleBy(Conductor(A),D)]; // isogeny factors of J(X_0^D(N)/W)
            E := EllipticCurve(Explode(J)); 
            ref := CremonaReference(E);
        end if; 

    end if; 

    step_end_time := Cputime();
    print "time taken for step: ", step_end_time - step_start_time; 

    SetOutputFile("genus_1_jacobian_isog_classes.m");
    print [* D, N, gens, ("\"" cat ref) cat "\"" *] , ",";
    UnsetOutputFile(); 

end for; 

end_time := Cputime();


SetOutputFile("genus_1_jacobian_isog_classes.m");
print "];";
print "Total time taken: ", end_time-start_time;
UnsetOutputFile();







