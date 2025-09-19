// Using dual graphs of minimal models of X_0^D(N)/W over Z_p for primes p | D
// to compute Kodaira symbols for genus 1 curves X_0^D(N)/W

// loading list of all genus 1 AL quotients and code for computing dual graphs and Kodaira symbols
load "dual_graphs.m";
load "genus_1_AL_quotients.m"; 


comp_start_time := Cputime(); 
step := 0;
SetOutputFile("genus_1_AL_quotient_symbols.m");
"genus_1_AL_quotient_symbols := [";
UnsetOutputFile();

for quotient in [quotient : quotient in genus_1_AL_quotients | IsSquarefree(quotient[2])] do 

	start_time := Cputime(); 
	step := step + 1;
	print "Current step out of 1484: ", step;
	print "Current quotient: ", quotient; 
	D := quotient[1];
	N := quotient[2];
	Wgens := quotient[3];

	SetOutputFile("genus_1_AL_quotient_symbols.m");
	print [* D, N, Wgens, Kodaira_from_dual(D,N,Wgens) *];
	UnsetOutputFile();

	end_time := Cputime();
	print "Time taken for step: ", end_time - start_time;

end for; 

SetOutputFile("genus_1_AL_quotient_symbols.m");
print "];";
UnsetOutputFile();

comp_end_time := Cputime();

print "Total time for all genus 1 curves: ", comp_end_time - comp_start_time; 

	


