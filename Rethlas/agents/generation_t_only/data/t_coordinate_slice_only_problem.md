# T-Coordinate Slice Orbit Classification

Let \(F=\mathbb R\) or \(F=\mathbb C\), and let
\(\epsilon\in\{\pm1\}\). Let
\[
V=E\oplus V_0\oplus E'
\]
be equipped with a non-degenerate \(\epsilon\)-symmetric bilinear form
\(\langle\ ,\ \rangle\), where \(V_0\) is non-degenerate and \(E,E'\) are
totally isotropic and paired perfectly.

Let \(G_0=\operatorname{Isom}(V_0)\), let \(X_0\in\mathfrak g_0\) be
nilpotent, and put
\[
K=\ker X_0,\qquad \operatorname{Im}X_0=K^\perp .
\]
For \(S:E'\to V_0\), define \(S^*:V_0\to E\) by
\[
\langle S^*v,u\rangle=\langle v,Su\rangle.
\]
For a \((-\epsilon)\)-symmetric bilinear form \(T\) on \(E'\), also write
\(T:E'\to E\) for the corresponding map. Define
\[
Y_{S,T}=
\begin{bmatrix}
0&-S^*&T\\
0&0&S\\
0&0&0
\end{bmatrix}
\in\mathfrak u .
\]
Let
\[
H=(\operatorname{GL}(E')\times Z_{G_0}(X_0))\ltimes U
\]
act on \(X_0+\mathfrak u\) by the adjoint action.

Fix \(S:E'\to V_0\) satisfying the normal form condition
\[
S^{-1}(\operatorname{Im}X_0)=\ker S.
\tag{NF}
\]
Put \(L=\ker S\). Assume moreover that the map
\[
K\to (E'/L)^*,\qquad k\mapsto (u+L\mapsto \langle k,Su\rangle)
\]
is surjective. This is the only property of the maximal-rank condition needed
below.

A \((-\epsilon)\)-symmetric bilinear form \(b\) on a finite-dimensional
vector space \(W\) is called maximally non-degenerate if its radical is
one-dimensional when \(-\epsilon=-1\) and \(\dim W\) is odd, and is
non-degenerate otherwise.

Define
\[
\mathcal B_{-\epsilon}^{\max}(E',S)
=
\{T\in\mathcal B_{-\epsilon}(E'): T|_L\text{ is maximally non-degenerate}\}.
\]

## Problem

Prove that for \(T_1,T_2\in\mathcal B_{-\epsilon}^{\max}(E',S)\),
\[
H\cdot (X_0+Y_{S,T_1})=H\cdot (X_0+Y_{S,T_2})
\]
if and only if the restricted forms
\[
T_1|_L,\qquad T_2|_L
\]
are congruent under \(\operatorname{GL}(L)\).

The proof should explicitly derive the unipotent conjugation formula and prove
that the stabilizer of the \(S\)-coordinate acts on \(L\) through the full group
\(\operatorname{GL}(L)\).
