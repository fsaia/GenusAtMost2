// The first two functions are heavily based on code by Jim Stankewicz for computing 
// the dual graph of the special fiber at $p$ of the Shimura curve 
// $X_0^{D}(N)/\langle w_p \rangle# over $\mathbb{Q}$, where $p \mid D$, $\gcd(D,N) = 1$, 
// $N$ is squarefree, and $D$ is an indefinite quaternion discriminant 
// (hence $D/p$ is a definite quaternion discriminant) over $\mathbb{Q}$. 

// The remainder of the code in this file is dedicated to computing information about the 
// dual graphs of general Atkin--Lehner quotients of $X_0^{D}(N)$ (including the trivial one) 
// at $p \mid D$, including functions for computing Kodaira symbols in the $g=1$ case and for 
// determining the existence of local points at primes $p \mid D$.

function LocalDualGram(L,q)
	Mat := MatrixAlgebra(ResidueClassRing(q), Rank(L));
	U := Kernel(Mat!GramMatrix(L));
	B := [ L!v : v in Basis(U) ] cat [ q*v : v in Basis(L) ];
	return MinkowskiGramReduction((1/q)*GramMatrix(sub< L | B >):
	Canonical := true);
end function;

function fiber(D,N,p)
	assert D mod p eq 0;
	assert IsSquarefree(D*N);
	Dprime := ExactQuotient(D,p);
	Q := QuaternionAlgebra(Dprime);
	O := QuaternionOrder(Q,N);
	L := LeftIdealClasses(O);
	OO := Order(O,p);
	LL := LeftIdealClasses(OO);
	OriginList := [ Explode([Index(L,I): I in L | IsIsomorphic(I,lideal<O | Basis(II)>)]) : II in LL];
	ALList := [0 : II in LL];
	OrderGrams := [ ReducedGramMatrix(RightOrder(II)) : II in LL];

	for A in SequenceToSet(OrderGrams) do
		Lat := LatticeWithGram(A);
		K := [ j : j in [1..#OrderGrams] | OrderGrams[j] eq A ];
		B := LocalDualGram(Lat,p);

		for i in K do
			ALList[i] := Explode([ j : j in K | IsIsometric(LatticeWithGram(1/(Norm(I)*Norm(J)) * GramMatrix(Conjugate(J)*I)),LatticeWithGram(B)) where I := LL[i] where J := LL[j] ]);
		end for;
	end for;

	W := ZeroMatrix(Integers(),#LL,#LL);

	for i in [1..#LL] do
		W[i,ALList[i]] := 1;
	end for;

	TerminusList := RowSequence(Transpose(W*Matrix(Integers(),#LL,1,OriginList)))[1];
	ALOperators := AssociativeArray();

	for l in PrimeDivisors(D*N) do
		ALList := [0 : II in LL];

		for A in SequenceToSet(OrderGrams) do
			Lat := LatticeWithGram(A);
			K := [ j : j in [1..#OrderGrams] | OrderGrams[j] eq A ];
			B := LocalDualGram(Lat,l);

			for i in K do
				ALList[i] := Explode([ j : j in K | IsIsometric(LatticeWithGram(1/(Norm(I)*Norm(J)) * GramMatrix(Conjugate(J)*I)),LatticeWithGram(B)) where I := LL[i] where J := LL[j] ]);
			end for;
		end for;

		ALOperators[l] := [[i,ALList[i]] : i in [1..#ALList]];
	end for;

	EdgeInfo := [];

	for i in [1..#OriginList] do 
		Append(~EdgeInfo,[OriginList[i],TerminusList[i],ExactQuotient(#Units(RightOrder(LL[i])),2)]);
	end for; 

	return EdgeInfo, ALOperators;
end function;



// Prints out the info from fiber(D,N,p) in a nice way suitable to human reading. The information
// of the action of w_d is printed for each prime-power divisor d||m (so, you can take m=D*N if
// you want all Atkin--Lehner info printed out nicely).

dual_graph_info := procedure(D,N,m,p)
	edge_info, AL := fiber(D,N,p);
	print "Oriented Edge Info in Form [origin, terminus, stab_order]: ", edge_info;

	print "p = ", p;
	print "Action of w_p on edges: ", AL[p];

	for q in [q : q in PrimeDivisors(m) | q ne p] do
		print "q = ", q;
		print "action of w_q on edges: ", AL[q];
	end for;
end procedure; 



// Analogous function to fiber(D,N,p) for the bipartite cover G of G_p. That is, G is the graph which, 
// upon normalization and minimization, is the dual graph for the special fiber at p of X_0^D(N). 

bipartite_cover_fiber := function(D,N,p)

	// info for graph corresponding to G/<w_p> from Jim's code
	// the sets {[e,"plus"] | e edge in G/<w_p>} and {[e,"minus"] | e edge in G/<w_p>} are preserved by 
	// w_m for p not dividing m, and mapped to one-another by w_m if p divides m. 
	Gp_edge_info, Gp_AL := fiber(D,N,p);

	// creating edge set info for bipartite cover G 
	// element of G_edge_info is of form [origin_vertex_label, terminal_vertex_label, stab_order]
	// The vertex set of G is a disjoint union of two copies of the vertex set of Gp, and
	// the "plus" and "minus" identifiers denote each piece of this bipartite cover's vertex set.
	Gp_edge_set_size := #Gp_edge_info;
	G_edge_info := [ [* [* Gp_edge_info[i][1],"plus" *],[* Gp_edge_info[i][2],"minus" *], Gp_edge_info[i][3] *]  : i in [1..Gp_edge_set_size] ];
	for i in [1..Gp_edge_set_size] do 
		Append(~G_edge_info,[* [* Gp_edge_info[i][1],"minus" *],[* Gp_edge_info[i][2],"plus" *], Gp_edge_info[i][3] *]);
	end for; 

	// initializing Atkin--Lehner info array for bipartite cover G
	G_ALOperators := AssociativeArray();

	// creating Atkin--Lehner info for w_l, l not equal to p
	for l in PrimeDivisors(ExactQuotient(D,p)*N) do
		ALList := [* 0 : edge in G_edge_info *]; // initializing size of ALList to be size of edge set of G

		// constructing ALList at prime l. Each entry is a pair [j,k] denoting that the 
		// jth edge in G_edge_info is sent to the kth by w_l
		for i in [1..Gp_edge_set_size] do
			ALList[i] := [i, Gp_AL[l][i][2] ];
			ALList[i+Gp_edge_set_size] := [i+Gp_edge_set_size,Gp_AL[l][i][2]+Gp_edge_set_size];
		end for;
		G_ALOperators[l] := ALList; 
	end for; 

	// creating Atkin--Lehner info for w_p, p|DN prime
	ALList := [* 0 : edge in G_edge_info *]; // initializing size of ALList to be size of edge set of G
	for i in [1..Gp_edge_set_size] do
		ALList[i] := [i, Gp_AL[p][i][2]+Gp_edge_set_size ];
		ALList[i+Gp_edge_set_size] := [i+Gp_edge_set_size,Gp_AL[p][i][2]];
	end for;
	G_ALOperators[p] := ALList; 

	// creating Atkin--Lehner info for w_1 (trivial action)
	ALList := [* 0 : edge in G_edge_info *]; // initializing size of ALList to be size of edge set of G
	for i in [1..2*Gp_edge_set_size] do
		ALList[i] := [i, i ];
	end for;
	G_ALOperators[1] := ALList; 

	// creating Atkin--Lehner info for w_m, m|DN composite
	for m in Divisors(D*N) do
		m_primes := PrimeDivisors(m);
		if #m_primes gt 1 then // already handled prime and m=1 cases
			ALList := [* 0 : edge in G_edge_info *]; // initializing size of ALList to be size of edge set of G

			for i in [1..#ALList] do 
				e_index := i; // initializing edge index we keep track of
				for l in m_primes do
					e_index := G_ALOperators[l][e_index][2]; // update edge index as image of current index under w_l
				end for;

				ALList[i] := [i,e_index];
			end for;

			G_ALOperators[m] := ALList; 
		end if; 
	end for;

	return G_edge_info, G_ALOperators; 

end function;



// Prints out the info from bipartite_cover(D,N,p) in a nice way suitable to human reading. The input m
// should be for the Atkin--Lehner operator w_m you are interested in considering (or, you can take m=D*N if
// you want all Atkin--Lehner info printed out nicely)

bipartite_cover_info := procedure(D,N,m,p)
	edge_info, AL := bipartite_cover_fiber(D,N,p);
	print "Edge Info in form [origin, terminus, stab_order]: ";
	for edge in edge_info do
		print edge;
	end for;

	print "p = ", p;
	print "Action of w_p on edges: ", AL[p];

	for q in [q : q in PrimeDivisors(m) | q ne p] do
		print "q = ", q;
		print "action of w_q on edges: ", AL[q];
	end for;
end procedure; 


// AL_quotient_edges : given D, N, p, W so that X_0^D(N)/W has genus 1 and p | D,
// give list of orbits of edges in G under the action of W (via indices in edge set for G)
AL_quotient_edges := function(D,N,p,W,edge_info,AL) 
	edge_index_set := {i : i in [1..#edge_info]};
	orbits_seq := [];
	already_met := []; // don't want to redo orbit computations
	for i in edge_index_set do
		if not (i in already_met) then 
			orbit := {AL[m][i][2] : m in W};
			already_met := Setseq(Seqset(already_met cat Setseq(orbit)));
			stab_order := edge_info[i][3]*Integers()!(#W/#orbit); // orbit stabilizer to get stab order on quotient by W
			Append(~orbits_seq,[* orbit, stab_order *]);
		end if;
	end for; 

	return orbits_seq;
end function;


// remove_half_edges: given input orbits_seq as in the output of AL_quotient_edges and edge_info for the dual graph
// of the top Shimura curve X_0^D(N), remove half-edges in orbits_seq. 
remove_half_edges := function(orbits_seq,edge_info)

	// vertices of G, which serve as representatives for vertices in G_W
	vertices := [];
	for edge in edge_info do
		w := edge[1];
		if not (w in vertices) then
			Append(~vertices,w);
		end if; 
	end for;

	// prune half-edges
	E := Integers()!(#edge_info/2);
	for orbit in orbits_seq do 
		edge := Sort(Setseq(orbit[1]))[1]; // representative of the orbit
		if edge+E in orbit[1] then // check that edge is self-inverse
			Exclude(~orbits_seq,orbit);
		end if; 
	end for;

	return orbits_seq;

end function; 



// Prune: given input orbits_seq as in the output of AL_quotient_edges and edge_info for the dual graph
// of the top Shimura curve X_0^D(N), prune half-edges and any edge which is the unique edge
// incident to a given vertex. Repeated pruning until the graph stabilizes results in the minimization
// of the graph. 
prune := function(orbits_seq,edge_info)

	// vertices of G, which serve as representatives for vertices in G_W
	vertices := [];
	for edge in edge_info do
		w := edge[1];
		if not (w in vertices) then
			Append(~vertices,w);
		end if; 
	end for;

	// prune half-edges
	E := Integers()!(#edge_info/2);
	for orbit in orbits_seq do 
		edge := Sort(Setseq(orbit[1]))[1]; // representative of the orbit
		if edge+E in orbit[1] then // check that edge is self-inverse
			Exclude(~orbits_seq,orbit);
		end if; 
	end for;

	// prune any edge which is the unique edge incident to a given vertex
	for v in vertices do
		v_origin_edges := [orbit : orbit in orbits_seq | v in [edge_info[k][1] : k in orbit[1]]];
		v_terminus_edges := [orbit : orbit in orbits_seq | v in [edge_info[k][2] : k in orbit[1]]];

		if #v_origin_edges eq 1 then 
			Exclude(~orbits_seq,v_origin_edges[1]);
		end if; 

		if #v_terminus_edges eq 1 then 
			Exclude(~orbits_seq,v_terminus_edges[1]);
		end if; 
	end for;

	return orbits_seq;

end function; 


// loading in functions for working with AL subgroups and their generating sets
load "AL_identifiers.m";


// Kodaira_from_dual : take D, N, Wgens set of generators for W with X_0^D(N)/W genus 1, 
// return Kodaira symbols of X_0^D(N)/W at all primes p|D. 
// Note: if X_0^D(N)/W does not have genus 1, then this returns for each prime p|D
// the number of edges in the dual graph of the minimal regular model X_0^D(N)/W at p. 

Kodaira_from_dual := function(D,N,Wgens) 
	
	symbols := []; // initializing list of symbols

	for p in PrimeDivisors(D) do 

		// get AL info at p for top graph G
		edge_info, AL := bipartite_cover_fiber(D,N,p);

		// identify edges via W
		orbits_seq := AL_quotient_edges(D,N,p,gens_to_identifier(D*N,Wgens),edge_info,AL);

		// minimize
		minimal_check := false; 
		while minimal_check eq false do 
			pruned_orbits_seq := prune(orbits_seq,edge_info);
			if pruned_orbits_seq eq orbits_seq then 
				minimal_check := true;
			else 
				orbits_seq := pruned_orbits_seq;
			end if; 
		end while; 

		// n = count of edges with multiplicity after pruning

		n := Integers()!(&+[orbit[2] : orbit in orbits_seq]/2);

		Append(~symbols, [p, n]); 

	end for; 

	return symbols;

end function; 



// quotient_has_Qp_points: given D, N, Wgens, and p | D, determines whether the quotient
// X_0^D(N)/W is locally solvable at p. This is done by computing information for the
// dual graph of the special fiber over Zp and checking for a vertex in the
// resolution of its minimization which is fixed by the action of w_p (frobenius) and 
// is the origin of less than p+1 half-edges 
// (i.e., such a vertex corresponds to a component of the minimal regular 
// model which is defined over Fp and has a smooth point)

quotient_has_Qp_points := function(D,N,Wgens,p)
	
	// get AL info at p for top graph G
	edge_info, AL := bipartite_cover_fiber(D,N,p);
	E := Integers()!(#edge_info/2); // half-total number of edges in top graph

	// identify edges via W
	orbits_seq := AL_quotient_edges(D,N,p,gens_to_identifier(D*N,Wgens),edge_info,AL);
	// print "pre prune: ", orbits_seq;

	// remove half-edges from sequence of edge orbits
	orbits_seq := remove_half_edges(orbits_seq,edge_info);
	// print "post prune: ", orbits_seq;

	// We are keeping track of vertices via their edges. If the model over Z_p is smooth
	// of genus 0, all edges are pruned away. This check handles that case.
	if IsEmpty(orbits_seq) then 
		return true; 
	end if; 

	// making list of w_p fixed vertices 
	wp_fixed_vertices := [];
	for orbit in orbits_seq do
		edge_index := Sort(Setseq(orbit[1]))[1]; // index in edge_info of a representative edge of the orbit
		edge := edge_info[edge_index];
		w := edge[1]; // representative vertex for origin of orbit
		if not (w in wp_fixed_vertices) then
			wp_hit_edge_index := Explode([pair[2] : pair in AL[p] | pair[1] eq edge_index]);
			wp_hit_orbit := Explode([orbit2 : orbit2 in orbits_seq | wp_hit_edge_index in orbit2[1]]); // image of orbit under wp

			for image_edge_index in wp_hit_orbit[1] do
				wp_hit_edge := edge_info[image_edge_index];
				if wp_hit_edge[1] eq w then 
					Append(~wp_fixed_vertices,w);
				end if;
			end for; 
		end if; 
	end for;

	// initializing a check for a found fixed vertex which is origin to less than p+1 half-edges
	found_check := false;

	// checking vertices introduced by resolutions of edges with non-trivial
	// stabilizer 
	for orbit in [orbit : orbit in orbits_seq | orbit[2] gt 1] do 
		edge_index := Sort(Setseq(orbit[1]))[1]; // index in edge_info of a representative edge of the orbit

		// To have a fixed vertex be introduced by the resolution of edge,
		// it must be the case that at least one of the orbit of its origin vertex and 
		// the orbit of its terminal vertex vt is fixed by wp. In other words,
		// it must be the case that the orbit is either fixed by wp or is sent to its
		// inverse by wp. 
		wp_hit_edge_index := Explode([pair[2] : pair in AL[p] | pair[1] eq edge_index]);
		wp_hit_orbit := Explode([orbit2 : orbit2 in orbits_seq | wp_hit_edge_index in orbit2[1]]); // image of orbit under wp

		// case that orbit is fixed by w_p
		if edge_index in wp_hit_orbit[1] then 
			found_check := true;
			break; 
		// case that orbit is sent to its inverse under w_p
		elif (edge_index+E in wp_hit_orbit[1]) or (edge_index-E in wp_hit_orbit[1]) then 
			if orbit[2] mod 2 eq 0 then 
				found_check := true;
				break;
			end if;
		end if;
	end for; 

	// If we did not find a fixed vertex among those introduced by resolving, 
	// then we check the rest of the vertices
	if found_check eq false then 

		for v in wp_fixed_vertices do 
			v_origin_edges := [orbit : orbit in orbits_seq | v in [edge_info[k][1] : k in orbit[1]]];

			if #v_origin_edges lt p+1 then 
				found_check := true;
				break;	
			else 
				// count number of half-edges originating at w
				v_fixed_edge_count := 0;
				

				for orbit in v_origin_edges do 
					edge_index := Sort(Setseq(orbit[1]))[1]; // index in edge_info of a representative edge of the orbit
					wp_hit_edge_index := Explode([pair[2] : pair in AL[p] | pair[1] eq edge_index]);
					if wp_hit_edge_index in orbit[1] then 
						v_fixed_edge_count := v_fixed_edge_count + 1;
					end if; 
				end for;

				if v_fixed_edge_count lt p+1 then 
					found_check := true; 
					break;
				end if;
			end if; 
		end for; 
	end if; 

	return found_check;
end function;





