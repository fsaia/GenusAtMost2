// The main function in this file is for computing
// the residue field of a given CM point on an Atkin--Lehner quotient
// of the form X_0^D(N)/<w_m> with N squarefree, D>1, and m>1 a Hall Divisor
// of D*N. This is done using Corollary 5.14 of Gonzalez--Rotger 2006. 

// Part of our code in the main function, in particular the functionality
// for taking the correct fixed fields, and the function ExtendAutomorphism
// is borrowed from the file CMfunctions.m in the repository 
// for Padurariu--Schembri 2023 linked here: 
// https://github.com/ciaran-schembri/Shimura/blob/main/CMfunctions.m


// D_R: given an indefinite quaternion discriminant D, 
// the fundamental imaginary quadratic discriminant d_K of a field K, 
// and a positive integer f, returns the integer D(R) corresponding to the 
// order R of discriminant f^2*d_K as defined in Gonzalez--Rotger 2006 p. 942
D_R := function(D,d_K,f)
    return &*([1] cat [p : p in PrimeDivisors(D) | (f mod p ne 0) and (KroneckerSymbol(d_K,p) eq -1)]);
end function;

// N_R: given an indefinite quaternion discriminant D, 
// the fundamental imaginary quadratic discriminant d_K of a field K, 
// and a positive integer f, returns the integer N(R) corresponding to the 
// order R of discriminant f^2*d_K as defined in Gonzalez--Rotger 2006 p. 942
N_R := function(N,d_K,f)
    return &*([1] cat [p : p in PrimeDivisors(N) | (f mod p eq 0) or (KroneckerSymbol(d_K,p) eq 1)]);
end function;

// N_R: given an indefinite quaternion discriminant D, 
// the fundamental imaginary quadratic discriminant d_K of a field K, 
// and a positive integer f, returns the integer N^*(R) corresponding to the 
// order R of discriminant f^2*d_K as defined in Gonzalez--Rotger 2006 p. 942
Nstar_R := function(N,d_K,f)
  return &*([1] cat [p : p in PrimeDivisors(N) | (f mod p ne 0) and (KroneckerSymbol(d_K,p) eq 1)]);
end function;

// has R_CM_points: given an indefinite quaternion discriminant D,
// a squarefree positive integer N, the fundamental imaginary quadratic 
// discriminant d_K of a field K, and a positive integer f, returns true if 
// X_0^D(N) has at least one CM point x with residue field K(x) over K
// equal to the ring class field corresponding to the order of discriminant
// f^2*d_K. See Gonzalez--Rotger 2006 Proposition 5.6
has_R_CM_points := function(D,N,d_K,f)
    assert IsSquarefree(N);
    
    if IsDivisibleBy(f^2*d_K,ExactQuotient(D*N,D_R(D,d_K,f)*Nstar_R(N,d_K,f))) then 
        return true;
    else 
        return false;
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

// ExtendAutomorphism: Given a tower of fields L/K/F and an an element
// a in Aut(L|K), coerce a in Aut(L|F).
ExtendAutomorphism := function(sig,LF)
    return map< LF -> LF | a :-> LF!sig(Domain(sig)!a), a :-> LF!Inverse(sig)(Domain(sig)!a)  >;
end function;

// depth_1_CM_residue_field: given an indefinite quaternion discriminant D,
// a squarefree positive integer N, the fundamental imaginary quadratic 
// discriminant d_K of a field K, a positive integer f, and a Hall
// Divisor m>1 of D*N, determines the residue field of the image on X_0^D(N)/<w_m>
// of each f^2*d_K-CM point on X_0^D(N) (by which in this context we mean a point
// x on X_0^D(N) with residue field K(x) over K equal to the ring class field 
// corresponding to the order of discriminant f^2*d_K). This is
// using Corollary 5.14 of Gonzalez--Rotger 2006. 
depth_1_CM_residue_field := function(D,N,m,d_K,f)
    assert IsSquarefree(N);
    assert m gt 1;
    assert D*N mod m eq 0;

    disc_R := f^2*d_K;
    m_r := GCD(IntegerRing()!m,IntegerRing()!(disc_R/GCD(N,f)));
    Q := m/m_r;

    _<x> := PolynomialRing(Rationals());
    K := NumberField(x^2+sqfree_part(d_K));
    R_K := MaximalOrder(K);
    B := Basis(R_K);
    assert B[1] eq 1;
    R:=sub< R_K | B[1], f*B[2] >;

    // bb: invertible ideal in R of norm m_r
    if m_r eq 1 then
        bb:=1*R;
    else
        fac:=Factorization(MaximalOrder(R)*m_r);
        bb_init:=&*[ pp[1] : pp in fac ];
        bb:=bb_init meet R;
    end if;
    assert Norm(bb) eq m_r;

    // initializing correct ring class field and 
    // automorphisms thereof
    Cl,m1:=RingClassGroup(R);
    ray:=RingClassField(R);
    // ring class field corresponding to order of disc f^2*d_K, as extension of K = \Q(\sqrt{d_K})
    HK:=NumberField(ray);
    // ring class field corresponding to order of disc f^2*d_K, as extension of \Q
    HKabs:=AbsoluteField(HK);
    ag1,ag2,ag3:=AutomorphismGroup(ray);

    idm:=map< HK -> HK | a :-> a, a:->a >;
    // Use of this cc may cause an error,
    // as the map is only well-defined in Magma if 
    // HasComplexConjugate(HK) is true. It should be
    // implemented if f=1, but not always for ring class fields
    // of non-maximal orders. 
    cc:=map< HK -> HK | a :-> ComplexConjugate(a), a :-> ComplexConjugate(a) >;

    if HK eq K then
        A:=map< Codomain(m1) -> ag2 | pp :-> ag2!idm >;
    else
        A:=ArtinMap(ray);
    end if;

    D_R_Nstar_R := D_R(D,d_K,f)*Nstar_R(N,d_K,f);

    // Case (1): D(R)*N^*(R) \ne 1 (residue field of an R-CM point on X_0^D(N) is
    // the ring class field corresponding to R)
    if D_R_Nstar_R ne 1 then 
        if Q eq 1 then 
            auts:=[ExtendAutomorphism(A(bb),HKabs)];
            Hfix:=FixedField(HKabs,auts);

        elif Q eq D_R_Nstar_R then 
            if #Cl eq 1 then
                aa := ideal< R | 1 >;
                assert Discriminant(QuaternionAlgebra<Rationals()| d_K , D_R_Nstar_R*Norm(aa)>) eq D;
            else
                aa:=[ m1(idl) : idl in Set(Cl) | Discriminant(QuaternionAlgebra<Rationals()|d_K,D_R_Nstar_R*Norm(m1(idl))>) eq D ];
                assert #aa ne 0;
                aa:=aa[1];
            end if;

            auts:=[ ExtendAutomorphism(A(bb*aa),HKabs)*cc ];
            Hfix:=FixedField(HKabs,auts);

        else
            Hfix := HKabs;
        end if;

    // Case (2): D(R)*N^*(R) = 1 (residue field of an R-CM point on X_0^D(N) is
    // an index 2 subfield of the ring class field corresponding to R)
    else 
        if Q eq 1 then
            if #Cl eq 1 then
                aa := ideal< R | 1 >;
                assert Discriminant(QuaternionAlgebra<Rationals()|d_K,D_R_Nstar_R*Norm(aa)>) eq D;
            else
                aa:=[ m1(idl) : idl in Set(Cl) | Discriminant(QuaternionAlgebra<Rationals()|d_K,Norm(m1(idl))>) eq D ];
                assert #aa ne 0;
                aa:=aa[1];
            end if;

            auts := [ cc*ExtendAutomorphism(A(aa),HKabs), ExtendAutomorphism(A(bb),HKabs) ];
            Hfix:=FixedField(HKabs,auts);

        else
            if #Cl eq 1 then
                aa := ideal< R | 1 >;
                assert Discriminant(QuaternionAlgebra<Rationals()| d_K ,D_R_Nstar_R*Norm(aa)>) eq D;
            else
                aa:=[ m1(idl) : idl in Set(Cl) | Discriminant(QuaternionAlgebra<Rationals()| d_K,Norm(m1(idl))>) eq D ];
                assert #aa ne 0;
                aa:=aa[1];
            end if;

            auts:= [ cc*ExtendAutomorphism(A(aa),HKabs) ];
            Hfix:=FixedField(HKabs,auts);
        end if;
    end if;

    return Hfix; 

end function; 


load "cond_disc_list_allO.m";
class_num_1 := cond_disc_list_allO[1]; // class number 1 im quad orders
class_num_2 := cond_disc_list_allO[2]; // class number 2 im quad orders

// depth_1_has_rational_CM_pt: given an indefinite quaternion discriminant
// D>1, a squarefree positive integer N, and a Hall Divisor m>1 of 
// D*N, returns false if X_0^D(N)/<w_m> has no rational CM point
// and otherwise returns the discriminant of a quadratic order R
// for which this curve has a rational R-CM point 
depth_1_has_rational_CM_pt := function(D,N,m)
    rat_pt_found := false;

    // checking over class number 1 orders (with f=1; those with f=2
    // are not orders of CM points in the framework of Gonzalez--Rotger 2006)
    for order in [order : order in class_num_1 | order[1] eq 1] do 
        d_K := order[2];
        f := order[1];
        if has_R_CM_points(D,N,d_K,f) then 
            if depth_1_CM_residue_field(D,N,m,d_K,f) eq Rationals() then 
                rat_pt_found := true;
                rat_pt_disc := f^2*d_K;
                break;
            end if;
        end if;
    end for;

    // checking over class number 2 orders (except for discriminant -60,
    // which is not the order of a CM point in the framework of Gonzalez--Rotger 2006 
    // because discriminant -15 has the same ring class field)
    if rat_pt_found eq false then 
        for order in [order : order in class_num_2 | order[1] eq 1] do 
            d_K := order[2];
            f := order[1];
            if has_R_CM_points(D,N,d_K,f) then 
                if depth_1_CM_residue_field(D,N,m,d_K,f) eq Rationals() then 
                    rat_pt_found := true;
                    rat_pt_disc := f^2*d_K;
                    break;
                end if;
            end if;
        end for;
    end if;

    if rat_pt_found eq false then
        return false;
    else 
        return rat_pt_disc;
    end if; 

end function;

