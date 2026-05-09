# Centralizer Restriction to the Kernel of a Nilpotent Element

## Problem

Let \(F\) be a field of characteristic not equal to \(2\). Let \(V\) be a
finite-dimensional \(F\)-vector space equipped with a non-degenerate
\(\epsilon\)-symmetric bilinear form
\[
\langle\,,\,\rangle:V\times V\to F,
\qquad
\langle v,w\rangle=\epsilon\langle w,v\rangle,
\qquad
\epsilon\in\{+1,-1\}.
\]
Let
\[
G=\operatorname{Isom}(V,\langle\,,\,\rangle)
\]
be the corresponding classical group. Thus \(G\) is an orthogonal group if
\(\epsilon=+1\), and a symplectic group if \(\epsilon=-1\). Let
\[
\mathfrak g=\operatorname{Lie}(G)
=
\{X\in\operatorname{End}_F(V):
\langle Xv,w\rangle+\langle v,Xw\rangle=0
\text{ for all }v,w\in V\}.
\]

Let \(X\in\mathfrak g\) be nilpotent, and set
\[
K:=\ker X.
\]
The restricted form
\[
\langle\,,\,\rangle_K:=\langle\,,\,\rangle|_{K\times K}
\]
may be degenerate. Nevertheless define
\[
H:=\operatorname{Isom}(K,\langle\,,\,\rangle_K)
=
\{h\in\operatorname{GL}(K):
\langle hu,hv\rangle_K=\langle u,v\rangle_K
\text{ for all }u,v\in K\}.
\]

Let
\[
Z_G(X):=\{g\in G:gX=Xg\}
\]
be the centralizer of \(X\) in \(G\). Since \(gX=Xg\) implies
\(g(\ker X)=\ker X\), restriction to \(K\) defines a group homomorphism
\[
\rho_X:Z_G(X)\longrightarrow H,
\qquad
\rho_X(g)=g|_K.
\]

Decide whether the following assertion is true.

> **Naive assertion.** For every nilpotent \(X\in\mathfrak g\), the restriction
> homomorphism
> \[
> \rho_X:Z_G(X)\to H
> \]
> is surjective.

If the assertion is true, give a proof. If it is false, give an explicit
counterexample and explain precisely which part of the naive intuition fails.

## Required output

Produce a verified markdown blueprint. The final result should be one of:

1. a proof of the naive assertion, or
2. a counterexample showing that the naive assertion is false.

If the naive assertion is false, also record a corrected lesson: what extra
structure on \(K=\ker X\), beyond the degenerate restricted form
\(\langle\,,\,\rangle_K\), is visibly remembered by the centralizer
\(Z_G(X)\)?
