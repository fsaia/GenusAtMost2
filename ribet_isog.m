// Code for computing isogeny factors of the Jacobian of an Atkin-Lehner 
// quotient $X_0^D(N)/W$ using Ribet's isogeny.

//``plus" space of the Jacobian of X0(N) wrt w_m

Jplus := function(N,m)
    assert IsDivisibleBy(N,m);

    J0 := JZero(N);
    wm := AtkinLehnerOperator(J0,m);
    Wm := Kernel(-Matrix(wm)+1);
    try
     _,jquotient :=DefinesAbelianSubvariety(J0,Wm);
     catch e
     jquotient :=DefinesAbelianSubvariety(J0,Wm);
     end try;
 return jquotient;
end function;


//``minus" space of the Jacobian of X0(N) wrt w_m

Jminus := function(N,m)
    assert IsDivisibleBy(N,m);

    J0 := JZero(N);
    wm := AtkinLehnerOperator(J0,m);
    Wm := Kernel(Matrix(wm)+1);
    try
     _,jquotient :=DefinesAbelianSubvariety(J0,Wm);
     catch e
     jquotient :=DefinesAbelianSubvariety(J0,Wm);
     end try;
 return jquotient;
end function;


// list of Hall Divisors of a given positive integer N
// (not needed right now, but maybe helpful later)

HallDivisors := function(N)
    return [d : d in Divisors(N) | GCD(d,Integers()!(N/d)) eq 1 and d ne 1];
end function;


// Given an indefinite rational quaternion discriminant D, a positive integer N coprime to D, 
// and a Hall divisor m of D*N, returns the abelian subvariety of Jac(X_0(D*N)) which is 
// the image of Ribet's isogeny on X_0^D(N)/<w_m>

IsogClassSimpleALQuotient := function(D,N,m)
    assert GCD(D,N) eq 1;

	if IsEven(#PrimeFactors(GCD(D,m))) then
        V1 := Jplus(D*N,m);
    else 
    	V1 := Jminus(D*N,m);
    end if;

    V := [a : a in  Decomposition(V1) | IsDivisibleBy(Conductor(a),D)];

    return V;
end function;


// Given an indefinite rational quaternion discriminant D, a positive integer N coprime to D, 
// and a subgroup W of W_0(D,N) given via a set m_gen_set of Hall divisors m>1 of D*N so that 
// {w_m : m in m_gen_set} generates W, returns the list of isogeny factors of the abelian subvariety 
// of Jac(X_0(D*N)) which is the image of Ribet's isogeny on X_0^D(N)/W. This function
// computes the factors directly using Ribet's isogeny and a decomposition of the Jacobian
// of X_0^D(N). The function isogeny_factors_from_symbols below is more efficient, but
// will not determine isogeny factors which appear in level properly dividing D*N. 

IsogClassALQuotient := function(D,N,m_gen_set)
    assert GCD(D,N) eq 1;

    J0 := JZero(D*N);

    m_vars := &meet[ Kernel((-1)^((1+#PrimeDivisors(GCD(D,m))))*Matrix(AtkinLehnerOperator(J0,m))+1) : m in m_gen_set];

    _,JW := DefinesAbelianSubvariety(J0,m_vars);

    return [A : A in Decomposition(JW) | IsDivisibleBy(Conductor(A),D)]; // isogeny factors of J(X_0^D(N)/W)

end function;


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

// isogeny_factors_from_symbols: given D, N, and gens so that W = <gens> is an Atkin--Lehner subgroup
// looks in the space of modular symbols which are new of level
// D*N and of weight 2 and sign -1 to find spaces which are compatible
// with the Atkin--Lehner action on Jac(X_0^D(N)/W) given by Ribet's isogeny. Returns
// a list of compatible isogeny factors. Since we only look in level D*N, 
// this may not obtain all isogeny factors of the Jacobian.
isogeny_factors_from_symbols := function(D,N,gens)
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

    isog_factors := [];
    for symbol in compatible_symbols_list do 
        if Dimension(symbol) eq 1 then 
            Append(~isog_factors,symbol);
        else 
            isog_factors := isog_factors cat Decomposition(ModularAbelianVariety(symbol));
        end if;
    end for;

    return isog_factors;

end function; 

// isogeny_factors_from_symbols_and_dim: this function works the same as isogeny_factors_from_symbols, 
// but also takes as input the dimension of the total space of compatible symbols expected
// and uses this information both to look at fewer symbols in ALDecomp and to break once
// the total expected dimension has been found
isogeny_factors_from_symbols_and_dim := function(D,N,gens,dim)
    M := ModularSymbols(D*N,2,-1); // modular symbols of level D*N, weight 2
                               // trivial character, and sign -1 over \Q
                               // -1 as sign picks out just 
                               // cusp forms with mult 1
    Snew := NewSubspace(CuspidalSubspace(M));
    ALdecomp := AtkinLehnerDecomposition(Snew);

    compatible_symbols_list := [];
    compatible_dim_found := 0;

    for V in ALdecomp do
        d := Dimension(V);
        if d le (dim-compatible_dim_found) then     
            print V;
            if IsCompatible(D,signpattern(V),gens) then 
                print "above V is compatible, dimension ", d;
                compatible_dim_found := compatible_dim_found + d;
                Append(~compatible_symbols_list,V);
                if compatible_dim_found eq dim then 
                    break;
                end if;
            end if;
        end if;
    end for;

    isog_factors := [];
    for symbol in compatible_symbols_list do 
        if Dimension(symbol) eq 1 then 
            Append(~isog_factors,symbol);
        else 
            isog_factors := isog_factors cat Decomposition(ModularAbelianVariety(symbol));
        end if;
    end for; 

    return isog_factors;

end function; 

