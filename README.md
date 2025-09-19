# GenusAtMost2
This is a repository for Magma code related to the paper "Shimura curve Atkin--Lehner quotients of genus at most two" by Oana Padurariu and Frederick Saia.


## Main Files

- `dual_graphs.m`: The first two functions are heavily based on code by Jim Stankewicz for computing the dual graph of the special fiber at $p$ of the Shimura curve $X_0^{D}(N)/\langle w_p \rangle$ over $\mathbb{Q}$, where $p \mid D$, $\gcd(D,N) = 1$, $N$ is squarefree, and $D$ is an indefinite quaternion discriminant (hence $D/p$ is a definite quaternion discriminant) over $\mathbb{Q}$. The remainder of the code in this file is dedicated to computing information about the dual graphs of general Atkin--Lehner quotients of $X_0^{D}(N)$ (including the trivial one) at $p \mid D$, including functions for computing Kodaira symbols in the $g=1$ case and for determining the existence of local points at primes $p \mid D$. 

- `hyperelliptic_star_candidate_checks.m`: Code for determining the star quotients $X_0^D(N)^*$ of genus at most $2$.

- `genus_le2_quotient_checks.m`: Code for determing the Atkin--Lehner quotients $X_0^D(N)/W$, with $W \leq W_0(D,N)$ not trivial, of genus at most $2$.

- `rational_point_checks.m`: In this file we run tests of genus $0$ and genus $1$ Atkin--Lehner quotients for rational points. In particular, we conclude we do have rational points when we find rational CM points, when have genus $2$ double covers of genus $1$ curves, or when an Hasse--Minkowski argument succeeds in the genus $0$ case, and we conclude we lack rational points if we lack local points at some prime or over the reals. We then also handle some quotients for which we have equations from past work.

- `Kodaira_computations.m`: In this code, we compute Kodaira symbols for each genus $1$ curve $X_0^D(N)/W$ with $N$ squarefree at all primes $p \mid D$ using the relevant function in `dual_graphs.m`.

- `genus_1_jacobian_isog_class_checks.m`: Code for computing the isogeny class of $\text{Jac}(X)$ for each curve listed in `genus_1_AL_quotients.m`.

- `genus_1_jacobian_isomorphism_class_checks.m`: Code for computing the isomorphism class of $\text{Jac}(X)$ for each curve listed in `genus_1_AL_quotients.m` with $N$ squarefree.

- `non_elliptic_genus_1_eqn_computations.m`: Code used for obtaining models for non-elliptic genus $1$ Atkin--Lehner quotients $X_0^D(N)/W$.

- `non_elliptic_fixed_pt_fld_checks.m`: Code for excluding candidate models of non-elliptic genus $1$ curves via a check on the splitting field of the hyperelliptic polynomial.

- `computing_genus_2_bielliptics.m`: In this file, we compute Atkin--Lehner quotients $X_0^D(N)$ which are genus $2$ and have at least one bielliptic Atkin--Lehner quotient. We also prove that many other genus $2$ quotients are not bielliptic.

- `computing_genus_2_bielliptic_eqns.m`: Code for computing models of genus $2$ Atkin--Lehner quotients which have at least one bielliptic Atkin--Lehner involution.

- `unknown_non_elliptic_eqn_computations.m`: In this file, we take Atkin--Lehner quotients $X_0^D(N)/W$ of genus $1$ for which we are otherwise unable to prove whether $X$ has a rational point and we attempt to use the same methods from `non_elliptic_genus_1_eqn_computations.m` to generate a finite list of candidate equations for $X$ assuming it is non-elliptic. We then use information about the existence of local points to exclude candidate equations. This is in the hopes of showing $X$ cannot be non-elliptic, i.e., must have a rational point. 

- `unknown_non_elliptic_fixed_pt_fld_checks.m`: The work in this file continues the work done in `unknown_non_elliptic_eqn_computations.m`, performing the checks done in `non_elliptic_fixed_pt_fld_checks.m` for non-elliptic candidate models in hopes of excluding all candidates and thus proving that a given genus $1$ quotient $X_0^D(N)/W$ has a rational point. 



## Required Files

- `quot_genus.m`: Code for computing genera of Atkin--Lehner quotients of $X_0^D(N)$ assuming $D>1$. The calculation uses Riemann--Hurwitz along with counts of fixed points of Atkin--Lehner involutions from work of Ogg.

- `AL_identifiers.m`: Code for working with Atkin--Lehner subgroups of the automorphisms group of $X_0^D(N)$. In particular, this file contains code for going between lists of all elements of a subgroup and minimal length lists of generators, and for listing all subgroups of the Atkin--Lehner group $W_0(D,N)$.

- `known_gonalities.m`: Known lists of coprime pairs $(D,N)$ with $D>1$ so that the curve $X_0^D(N)$ has genus $0$ or $1$ or has gonality over $\mathbb{Q}$ or geometric gonality at most 3.

- `cond_disc_list_allO.m`: list of all (not just maximal) imaginary quadratic orders of class number up to $100$. The $i^\text{th}$ element is the complete list of sequences $[f,d_K] = [\text{conductor}, \text{fundamental disc}]$ for imaginary quadratic orders of class number $i$. Generated using list of maximal orders by M. Watkins. In this work, we only really use the first two elements of this list, giving the orders of class numbers $1$ and $2$, in the file `depth_1_CM_residue_field.m`.

- `depth_1_CM_residue_field.m`: The main function in this file is for computing the residue field of a given CM point on an Atkin--Lehner quotient of the form $X_0^D(N)/<w_m>$ with $N$ squarefree, $D>1$, and $m>1$ a Hall Divisor of $DN$. This is done using Corollary 5.14 of Gonzalez--Rotger 2006. Part of our code in the main function, in particular the functionality for taking the correct fixed fields, and the function `ExtendAutomorphism` is borrowed from the file `CMfunctions.m` in the repository for Padurariu--Schembri 2023 [linked here](https://github.com/ciaran-schembri/Shimura/blob/main/CMfunctions.m).

- `ribet_isog.m`: Code for computing isogeny factors of the Jacobian of an Atkin-Lehner quotient $X_0^D(N)/W$ using Ribet's isogeny.

- `aut_checks.m`: This file contains a function which uses results from Kontogeorgis--Rotger 2008 to prove certain curves $X_0^D(N)$ have no non-Atkin--Lehner automorphisms.

- `all_atkin_lehner_10k.m`: List of $4718$ pairs $(D,N)$, all with $DN < 10000$$ for which it is proven that all automorphisms of $X_0^D(N)/W$ are Atkin--Lehner for each $W \leq W_0(D,N)$ in work of Mercuri--Padurariu--Saia--Stirpe 2025. 



## Computed Lists

- `genus_0_stars.m`: The list of all $271$ pairs $(D,N)$ with $\gcd(D,N) = 1$ so that $X_0^D(N)^*$ has genus $0$.

- `genus_1_stars.m`: The list of all $276$ pairs $(D,N)$ with $\gcd(D,N) = 1$ so that $X_0^D(N)^*$ has genus $1$.

- `genus_2_stars.m`: The list of all $289$ pairs $(D,N)$ with $\gcd(D,N) = 1$ so that $X_0^D(N)^*$ has genus $2$.

- `genus_0_AL_quotients.m`: The list of all $779$ triples $[D,N,\text{gens}]$ such that, with $W \leq W_0(D,N)$ being generated by the $w_m$ for $m$ in gens, we have that $X_0^D(N)/W$ is a non-trivial quotient having genus $0$.

- `genus_1_AL_quotients.m`: The list of all $1352$ triples $[D,N,\text{gens}]$ such that, with $W \leq W_0(D,N)$ being generated by the $w_m$ for $m$ in gens, we have that $X_0^D(N)/W$ is a non-trivial quotient having genus $1$

- `genus_2_AL_quotients.m`: The list of all $1580$ triples $[D,N,\text{gens}]$ such that, with $W \leq W_0(D,N)$ being generated by the $w_m$ for $m$ in gens, we have that $X_0^D(N)/W$ is a non-trivial quotient having genus $2$

- `genus_0_AL_quotients_no_rat_pts.m`: The list of all $81$ triples $[D,N,\text{gens}]$ in `genus_0_AL_quotients.m` for which we prove $X_0^D(N)/W$ has no rational points.

- `genus_0_AL_quotients_rat_pts.m`: The list of all $643$ triples $[D,N,\text{gens}]$ in `genus_0_AL_quotients.m` for which we prove $X_0^D(N)/W$ has a rational point.

- `genus_0_AL_quotients_unknown_rat_pts.m`: The list of all $55$ triples $[D,N,\text{gens}]$ in `genus_0_AL_quotients.m` for which we do not prove whether $X_0^D(N)/W$ has a rational point.

- `genus_1_AL_quotients_no_rat_pts.m`: The list of all $154$ triples $[D,N,\text{gens}]$ in `genus_1_AL_quotients.m` for which we prove $X_0^D(N)/W$ has no rational points.

- `genus_1_AL_quotients_rat_pts.m`: The list of all $1040$ triples $[D,N,\text{gens}]$ in `genus_1_AL_quotients.m` for which we prove $X_0^D(N)/W$ has a rational point.

- `genus_1_AL_quotients_unknown_rat_pts.m`: The list of all $158$ triples $[D,N,\text{gens}]$ in `genus_1_AL_quotients.m` for which we do not prove whether $X_0^D(N)/W$ has a rational point.

- `genus_1_AL_quotients_rat_pts_pos_rank.m`: The list of all $537$ triples $[D,N,\text{gens}]$ in `genus_1_AL_quotients_rat_pts.m` for which $\text{Jac}(X_0^D(N)/W)$ has positive rank over $\mathbb{Q}$. 

- `genus_1_AL_quotients_unknown_rat_pts_pos_rank.m`: The list of all $54$ triples $[D,N,\text{gens}]$ in `genus_1_AL_quotients_unknown_rat_pts.m` for which $\text{Jac}(X_0^D(N)/W)$ has positive rank over $\mathbb{Q}$.

- `genus_1_AL_quotient_symbols.m`: For each triple $(D,N,\text{gens})$ in `genus_1_AL_quotients.m` with $N$ squarefree, we list the Kodaira symbols of $Jac(X_0^D(N)/W)$ at all primes $p \mid D$. This is output from `Kodaira_computations.m`.

- `genus_1_jacobian_isog_classes.m`: For each triple $(D,N,\text{gens})$ in `genus_1_AL_quotients.m`, we list a member of the isogeny class of the elliptic curve $\text{Jac}(X_0^D(N))$.

- `genus_1_AL_quotient_jacobian_isomorphism_classes.m`: For each triple $(D,N,\text{gens})$ in `genus_1_AL_quotients.m` with $N$ squarefree, we list the Cremona reference of the elliptic curve $\text{Jac}(X_0^D(N))$.

- `non_elliptic_genus_one_equation_determined_final.m`: For $146$ triples $(D,N,\text{gens})$ in `genus_1_AL_quotients.m` for which $X = X_0^D(N)/W$ is non-elliptic, we provide a polynomial $f(x)$ so that $y^2=f(x)$ is a model over $\mathbb{Q}$ for $X$.

- `non_elliptic_genus_one_equation_not_determined_final.m`: For $4$ triples $(D,N,\text{gens})$ in `genus_1_AL_quotients.m` for which $X = X_0^D(N)/W$ is non-elliptic, we provide polynomial $f_1(x)$ and $f_2(x)$ so that exactly one of $y^2=f_1(x)$ or $y^2=f_2(x)$ is a model over $\mathbb{Q}$ for $X$.

- `genus_two_bielliptics_one_AL.m`: The list of all $251$ triples $[D,N,\text{gens}]$ in `genus_2_AL_quotients.m` so that the corresponding curve $X_0^D(N)$ has exactly one bielliptic involution which is Atkin--Lehner.

- `genus_two_bielliptics_two_AL.m`: The list of all $388$ triples $[D,N,\text{gens}]$ in `genus_2_AL_quotients.m` so that the corresponding curve $X_0^D(N)$ has exactly two bielliptic involutions which are Atkin--Lehner.

- `genus_2_remaining_non_AL_bielliptic_candidates_final.m`: The list of all $76$ triples $[D,N,\text{gens}]$ in `genus_2_AL_quotients.m` so that the corresponding curve $X_0^D(N)$ has no bielliptic involutions which are Atkin--Lehner and we do not prove whether $X_0^D(N)/W$ is bielliptic.

- `genus_2_bielliptics_eqn_determined.m`: The list of all $405$ triples $[D,N,\text{gens}]$ appearing in either `genus_two_bielliptics_one_AL.m` or in `genus_two_bielliptics_two_AL.m` for which we determine a model for the corresponding curve $X_0^D(N)/W$ over $\mathbb{Q}$. 

- `genus_2_bielliptics_eqn_not_determined.m`: The list of all $231$ triples $[D,N,\text{gens}]$ appearing in either `genus_two_bielliptics_one_AL.m` or in `genus_two_bielliptics_two_AL.m` for which we compute candidate models for $X_0^D(N)/W$ over $\mathbb{Q}$ but are not able to determine which candidate model is correct.

- `genus_1_AL_quotients_rat_pts_by_non_elliptic_test_final.m`: The list of all $17$ triples $(D,N,\text{gens})$ in `genus_1_AL_quotients.m` for which we prove that the corresponding curve $X_0^D(N)/W$ has a rational point in the files `unknown_non_elliptic_eqn_computations.m` and `unknown_non_elliptic_fixed_pt_fld_checks.m`.
