# GenusAtMost2
This is a repository for Magma code related to the paper "Shimura curve Atkin--Lehner quotients of genus at most two" by Oana Padurariu and Frederick Saia.


## Main Files

## Required Files

- `quot_genus.m`: Code for computing genera of Atkin--Lehner quotients of $X_0^D(N)$ assuming $D>1$. The calculation uses Riemann--Hurwitz along with counts of fixed points of Atkin--Lehner involutions from work of Ogg.

- `AL_identifiers.m`: Code for working with Atkin--Lehner subgroups of the automorphisms group of $X_0^D(N)$. In particular, this file contains code for going between lists of all elements of a subgroup and minimal length lists of generators, and for listing all subgroups of the Atkin--Lehner group $W_0(D,N)$.

- `known_gonalities.m`: Known lists of coprime pairs $(D,N)$ with $D>1$ so that the curve $X_0^D(N)$ has genus $0$ or $1$ or has gonality over $\mathbb{Q}$ or geometric gonality at most 3.

- `cond_disc_list_allO.m`: list of all (not just maximal) imaginary quadratic orders of class number up to $100$. The $i^\text{th}$ element is the complete list of sequences $[f,d_K] = [\text{conductor}, \text{fundamental disc}]$ for imaginary quadratic orders of class number $i$. Generated using list of maximal orders by M. Watkins.


## Computed Lists
