# lemma lem:centralizer-preserves-kernel-image-flag

## statement
Let \(V\) be a finite-dimensional vector space over a field \(F\), let
\(X \in \operatorname{End}_F(V)\), and let
\[
K := \ker X.
\]
If \(g \in \operatorname{GL}(V)\) satisfies \(gX = Xg\), then for every
integer \(r \ge 0\) one has
\[
g(\operatorname{Im} X^r) = \operatorname{Im} X^r
\]
and therefore
\[
g\bigl(K \cap \operatorname{Im} X^r\bigr) = K \cap \operatorname{Im} X^r.
\]

## proof
If \(gX = Xg\), then \(gX^r = X^r g\) for every \(r \ge 0\). Hence
\[
g(\operatorname{Im} X^r)
=
g(X^r V)
=
X^r(gV)
=
X^r V
=
\operatorname{Im} X^r.
\]
Also,
\[
X(gv)=g(Xv),
\]
so if \(v \in \ker X\), then \(X(gv)=0\), and therefore \(g(\ker X)=\ker X\).
Intersecting the two preserved subspaces gives
\[
g\bigl(K \cap \operatorname{Im} X^r\bigr)=K \cap \operatorname{Im} X^r.
\]

# lemma lem:explicit-symplectic-42-example

## statement
Assume \(\operatorname{char} F \ne 2\). Let
\[
V
=
Fe_1 \oplus Fe_2 \oplus Fe_3 \oplus Fe_4 \oplus Ff_1 \oplus Ff_2.
\]
Define an alternating bilinear form on \(V\) by
\[
\langle e_1,e_4\rangle = 1,\qquad
\langle e_4,e_1\rangle = -1,
\]
\[
\langle e_2,e_3\rangle = -1,\qquad
\langle e_3,e_2\rangle = 1,
\]
\[
\langle f_1,f_2\rangle = 1,\qquad
\langle f_2,f_1\rangle = -1,
\]
and all other pairings between basis vectors equal to \(0\).

Define \(X \in \operatorname{End}_F(V)\) by
\[
Xe_4=e_3,\qquad Xe_3=e_2,\qquad Xe_2=e_1,\qquad Xe_1=0,
\]
\[
Xf_2=f_1,\qquad Xf_1=0.
\]
Then:

1. \(\langle\,,\,\rangle\) is a non-degenerate alternating form on \(V\).
2. \(X\) is nilpotent.
3. \(X \in \mathfrak{sp}(V,\langle\,,\,\rangle)\).
4. One has
   \[
   K:=\ker X = Fe_1 \oplus Ff_1.
   \]
5. The restricted form on \(K\) is identically zero. Hence
   \[
   H=\operatorname{Isom}(K,\langle\,,\,\rangle_K)=\operatorname{GL}(K).
   \]
6. One has
   \[
   K \cap \operatorname{Im} X = Fe_1 \oplus Ff_1,
   \qquad
   K \cap \operatorname{Im} X^2 = Fe_1,
   \qquad
   K \cap \operatorname{Im} X^3 = Fe_1.
   \]

## proof
The Gram matrix of the form in the ordered basis
\[
(e_1,e_2,e_3,e_4,f_1,f_2)
\]
is block diagonal with \(2 \times 2\) symplectic blocks on the pairs
\((e_1,e_4)\), \((e_2,e_3)\), and \((f_1,f_2)\). Hence the form is alternating
and non-degenerate.

The formulas for \(X\) show immediately that \(X^4=0\), so \(X\) is nilpotent.

To check that \(X \in \mathfrak{sp}(V)\), we must verify
\[
\langle Xv,w\rangle+\langle v,Xw\rangle=0
\qquad
(v,w \in V).
\]
By bilinearity it suffices to check basis pairs. Since the only nonzero values
of \(X\) on basis vectors are
\[
Xe_4=e_3,\quad Xe_3=e_2,\quad Xe_2=e_1,\quad Xf_2=f_1,
\]
the only possibly nontrivial checks are when one of the displayed vectors is
paired with the unique basis vector to which it has nonzero pairing. These are:
\[
\langle Xe_4,e_2\rangle+\langle e_4,Xe_2\rangle

=
\langle e_3,e_2\rangle+\langle e_4,e_1\rangle
=
1+(-1)=0,
\]
\[
\langle Xe_3,e_3\rangle+\langle e_3,Xe_3\rangle

=
\langle e_2,e_3\rangle+\langle e_3,e_2\rangle
=
(-1)+1=0,
\]
\[
\langle Xf_2,f_1\rangle+\langle f_2,Xf_1\rangle

=
\langle f_1,f_1\rangle+\langle f_2,0\rangle
=
0.
\]
All other basis-pair checks are zero for trivial reasons. Thus \(X\) is
skew-adjoint for the alternating form, so \(X \in \mathfrak{sp}(V)\).

Now let
\[
v=a_1e_1+a_2e_2+a_3e_3+a_4e_4+b_1f_1+b_2f_2.
\]
Then
\[
Xv=a_2e_1+a_3e_2+a_4e_3+b_2f_1.
\]
Hence \(Xv=0\) if and only if
\[
a_2=a_3=a_4=b_2=0,
\]
which proves
\[
K=\ker X=Fe_1 \oplus Ff_1.
\]

The restricted form on \(K\) is zero because \(e_1\) only pairs with \(e_4\),
and \(f_1\) only pairs with \(f_2\), neither of which lies in \(K\). Therefore
\[
\langle e_1,e_1\rangle
=
\langle e_1,f_1\rangle
=
\langle f_1,f_1\rangle
=
0,
\]
so \(\langle\,,\,\rangle_K\) is identically zero. An automorphism of \(K\)
automatically preserves the zero form, hence
\[
H=\operatorname{GL}(K).
\]

Finally,
\[
\operatorname{Im} X
=
\operatorname{span}\{e_1,e_2,e_3,f_1\},
\]
\[
\operatorname{Im} X^2
=
\operatorname{span}\{e_1,e_2\},
\]
\[
\operatorname{Im} X^3
=
\operatorname{span}\{e_1\}.
\]
Intersecting with \(K=Fe_1 \oplus Ff_1\) gives
\[
K \cap \operatorname{Im} X
=
Fe_1 \oplus Ff_1,
\]
\[
K \cap \operatorname{Im} X^2
=
Fe_1,
\]
\[
K \cap \operatorname{Im} X^3
=
Fe_1.
\]

# proposition prop:counterexample-to-surjectivity

## statement
For the symplectic space and nilpotent element \(X\) of
Lemma `lem:explicit-symplectic-42-example`, the restriction map
\[
\rho_X: Z_G(X) \to H
\]
is not surjective.

More precisely, if
\[
h \in H=\operatorname{GL}(K)
\]
is defined on the basis \((e_1,f_1)\) of \(K\) by
\[
h(e_1)=f_1,\qquad h(f_1)=e_1,
\]
then \(h\) does not lie in the image of \(\rho_X\).

## proof
By Lemma `lem:explicit-symplectic-42-example`, the restriction of the ambient
form to \(K\) is zero, so
\[
H=\operatorname{GL}(K),
\]
and the swap map
\[
h(e_1)=f_1,\qquad h(f_1)=e_1
\]
is certainly an element of \(H\).

Assume for contradiction that \(h=\rho_X(g)\) for some
\[
g \in Z_G(X).
\]
Then \(gX=Xg\), so Lemma `lem:centralizer-preserves-kernel-image-flag` applies.
In particular, \(g\) preserves
\[
K \cap \operatorname{Im} X^3.
\]
But Lemma `lem:explicit-symplectic-42-example` gives
\[
K \cap \operatorname{Im} X^3 = Fe_1.
\]
Therefore
\[
g(e_1) \in Fe_1.
\]
After restricting to \(K\), this says
\[
\rho_X(g)(e_1) \in Fe_1.
\]
However,
\[
h(e_1)=f_1 \notin Fe_1.
\]
This contradiction shows that no such \(g\) exists. Hence
\[
h \notin \operatorname{Im}(\rho_X),
\]
so \(\rho_X\) is not surjective.

# theorem thm:main

## statement
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

## proof
The naive assertion is false.

Indeed, Lemma `lem:explicit-symplectic-42-example` constructs a symplectic
space \((V,\langle\,,\,\rangle)\) of dimension \(6\) together with a nilpotent
element \(X \in \mathfrak{sp}(V)\) such that
\[
K=\ker X=Fe_1 \oplus Ff_1
\]
and the restricted form on \(K\) is identically zero. Therefore
\[
H=\operatorname{Isom}(K,\langle\,,\,\rangle_K)=\operatorname{GL}(K).
\]
So the transposition
\[
h(e_1)=f_1,\qquad h(f_1)=e_1
\]
is an element of \(H\).

However, Proposition `prop:counterexample-to-surjectivity` shows that this
element \(h\) cannot be the restriction of any element of \(Z_G(X)\). The
reason is elementary and conceptual: every element \(g\) centralizing \(X\)
preserves not only \(K\), but the entire descending family of subspaces
\[
K \cap \operatorname{Im} X^r
\qquad (r \ge 0),
\]
by Lemma `lem:centralizer-preserves-kernel-image-flag`.

In the explicit example one has
\[
K \cap \operatorname{Im} X^3 = Fe_1,
\]
so every element in the image of \(\rho_X\) must preserve the line \(Fe_1\).
The swap \(h\) does not preserve that line, because \(h(e_1)=f_1\). Hence
\[
h \notin \operatorname{Im}(\rho_X),
\]
and \(\rho_X\) is not surjective.

This gives the requested corrected lesson. The centralizer \(Z_G(X)\) visibly
remembers more than the degenerate form on \(K=\ker X\). At a minimum it
remembers the filtration
\[
K \supseteq K \cap \operatorname{Im} X \supseteq K \cap \operatorname{Im} X^2
\supseteq \cdots,
\]
which records how vectors of \(K\) sit at different depths in the Jordan chains
of \(X\). The degenerate form \(\langle\,,\,\rangle_K\) does not in general
determine this filtration. Therefore \(\operatorname{Im}(\rho_X)\) can be a
proper subgroup of \(H\), namely the subgroup of isometries of \(K\) that also
respect the extra filtration coming from the nilpotent operator \(X\).
