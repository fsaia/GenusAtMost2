// This file contains a function which uses results from Kontogeorgis--Rotger 2008 to prove 
// certain curves $X_0^D(N)$ have no non-Atkin--Lehner automorphisms. 

load "quot_genus.m";

start_time := Cputime();

// HallDivisors : given positive integer N, returns sequence of all Hall Divisors d || N. 
HallDivisors := function(N)
    assert N ge 1;
    return [d : d in Divisors(N) | GCD(d,Integers()!(N/d)) eq 1];
end function;

// all_atkin_lehner_KR_no_point_counts : uses results from Kontogeorgis--Rotger Theorems 1.6, 1.7
// to prove that Aut(X_0^D(N)) = W_0(D,N) in the case of N squarefree.
all_atkin_lehner_KR_no_point_counts := function(D,N)

    assert IsSquarefree(N); 

    F_D := Factorization(D);
    F_N := Factorization(N);
    g := Integers()!genus(D,N);
    r := #F_D + #F_N; // r = omega(DN)
    e_1 := e1_from_facts(F_D,F_N,N);
    e_3 := e3_from_facts(F_D,F_N,N);

    if (D*N mod 3) eq 0 then // using KR Thm 1.7 (i) with m=3
        
        check_3 := true; // check on prime divisors of N

        for factor in F_N do
            p := factor[1];
            if (KroneckerSymbol(-3,p) eq -1) then
                check_3 := false;
                break;
            end if;
        end for;

        if check_3 eq true then // then we check factors of D
            c := 0;
            for factor in F_D do
                p := factor[1];
                if (KroneckerSymbol(-3,p) eq 1) then
                    c := c+1;
                    if c gt 1 then 
                        break;
                    end if;
                end if; 
            end for; 

            if (c le 1) then 
                return true;
            end if;
        end if;
    end if; 


    // if previous check didn't succeed, try KR Thm 1.6 i and 1.6 ii and Lemma arguments
    if (((e_1 eq 0) and (e_3 eq 0))) or (r eq Valuation(g-1,2)+2)  then
        return true;
    end if; 

    // If none of the above methods succeeded, we return false
    return false;
end function; 

