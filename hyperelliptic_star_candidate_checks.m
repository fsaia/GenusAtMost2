// Code for determining the star quotients $X_0^D(N)^*$ of genus at most $2$. 


// We know that the full Atkin--Lehner quotient X_0^D(N)^* has geometric gonality stictly larger than 2 if 
// DN > 19226700$

initial_DN_bound := 19226700; 

// loading quot_genus.m, which contains the genus(D,N) function for the genus of X_0^D(N)
load "quot_genus.m";


// check_for_candidates_brute: given naturals low <= high, lists all pairs (D,N) with product D*N between
// low and high such that D is an indefinite quaternion discriminant, N is a positive integer relatively
// prime to D, and the pair (D,N) is a "hyperelliptic candidate pair" in the sense that

    // (975/8192)*(g(X_0^D(N)))-1) <= 2^{1+\omega(DN)}.

// We use this to run multiple checks simultaneously for larger values of DN.

check_for_candidates_brute := function(low,high)

    start_time := Cputime();
    D := IntegerRing()!high;

    while D ge low do

        omega_D := #Factorization(D);
        if IsSquarefree(D) and IsEven(omega_D) then 

            for N in [Ceiling(low/D)..Floor(high/D)] do
                if GCD(D,N) eq 1 then
                    omega_N := #Factorization(N); 
                    if ( (975/8192)*(genus(D,N)-1) le 2^(1+omega_D + omega_N) ) then  

                        end_time := Cputime();
                        print "Done. Time taken", end_time - start_time;
                        return "candidate pair found: D,N = ", D, N;
                        break;

                    end if; 
                end if;
            end for;
        end if; 
        D := D-1;
    end while;

    end_time := Cputime();
    print "Done. Time taken", end_time - start_time;
    return "no bads found in the given range";
end function;


// check_for_candidates_brute(initial_DN_bound-5*10^6,initial_DN_bound);
// none found in this range 

// check_for_candidates_brute(initial_DN_bound-10^7,initial_DN_bound-5*10^6);
// none found in this range 

// check_for_candidates_brute(initial_DN_bound-15*10^6,initial_DN_bound-10^7);
// none found in this range 


// Compare_DN_pairs
// Input: two pairs x, y
// Output: integer which is x[1]-y[1] if this quantity is non-zero, and is x[2]-y[2] otherwise,
// as comparision function for sorting dcm_list in next function
compare_DN_pairs := function(x,y)
    c := x[1] - y[1];
    if c ne 0 then
        return c;
    else
        return x[2]-y[2];
    end if;
end function;


// list_candidates_brute: given naturals low <= high, lists all pairs (D,N) with product D*N between
// low and high such that D is an indefinite quaternion discriminant, N is a positive integer relatively
// prime to D, and the pair (D,N) is a "candidate pair" in the sense that 
//  (21/200)*(genus(X_0^D(N))-1) le 2^(2+omega(DN)) = 2^(2+ omega(D) + omega(N)). 

list_candidates_brute := function(low,high)

    start_time := Cputime();
    candidates_list := [];
    D := IntegerRing()!high;

    while D ge low do

        omega_D := #Factorization(D);
        if IsSquarefree(D) and IsEven(omega_D) then 

            for N in [Ceiling(low/D)..Floor(high/D)] do
                if GCD(D,N) eq 1 then

                    omega_N := #Factorization(N); 

                    if ( (975/8192)*(genus(D,N)-1) le 2^(2+omega_D + omega_N) ) then  
                        Append(~candidates_list,[D,N]); 
                    end if; 

                end if;
            end for;
        end if; 
        D := D-1;
    end while;

    end_time := Cputime();
    print "Done. Time taken", end_time - start_time;
    // print "Candidate pairs [D,N] with D*N from ", low, " to ", high, ":";
    Sort(~candidates_list,compare_DN_pairs);
    return candidates_list; 
end function;
    

hyperelliptic_star_candidates := list_candidates_brute(6,initial_DN_bound-15*10^6); 

// SetOutputFile("hyperelliptic_star_candidates.m");
// print "hyperelliptic_star_candidates := ", hyperelliptic_star_candidates, ";";
// UnsetOutputFile(); 


// loading quot_genus.m, which contains the genus(D,N) function for the genus of X_0^D(N)
load "quot_genus.m";


// given a positive integer n, returns the sequence of divisors d | n such that GCD(d,n/d) = 1.
HallDivisors := function(n) 
    assert n ge 1;
    return {d : d in Divisors(n) | GCD(d,Integers()!(n/d)) eq 1};
end function;


// Making lists of all star quotients of genus <= 2. 

// Initializing lists. Since any genus 2 star quotient is geometrically hyperelliptic, 
// we also separate these cases
genus_0_stars := [];
genus_1_stars := []; 
genus_2_stars := [];
hyperelliptic_star_candidates_genus_ge3 := [];

for pair in hyperelliptic_star_candidates do

    D := pair[1];
    N := pair[2]; 
    H := HallDivisors(D*N); 

    g := quot_genus(D,N,H); // genus of star quotient X_0^D(N)^*

    if g eq 0 then
        Append(~genus_0_stars,pair);

    elif g eq 1 then
        Append(~genus_1_stars,pair);

    elif g eq 2 then
        Append(~genus_2_stars,pair);

    else 
        Append(~hyperelliptic_star_candidates_genus_ge3,pair);

    end if;  

end for;

end_time := Cputime();


// SetOutputFile("genus_0_stars.m");
// print "genus_0_stars := ";
// genus_0_stars;
// print ";";
// UnsetOutputFile();  

// SetOutputFile("genus_1_stars.m");
// print "genus_1_stars := ";
// genus_1_stars;
// print ";";
// UnsetOutputFile();  

// SetOutputFile("genus_2_stars.m");
// print "genus_2_stars := ";
// genus_2_stars;
// print ";";
// UnsetOutputFile();    

// SetOutputFile("hyperelliptic_star_candidates_genus_ge3.m");
// print "hyperelliptic_star_candidates_genus_ge3 := ";
// hyperelliptic_star_candidates_genus_ge3;
// print ";";
// UnsetOutputFile();
   





 
