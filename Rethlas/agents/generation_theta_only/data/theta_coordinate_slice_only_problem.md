# Theta-Corrected T-Coordinate Slice Orbit Classification

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

Fix \(S:E'\to V_0\). Let
\[
\overline S:E'\to V_0/\operatorname{Im}X_0
\]
be the composition of \(S\) with the quotient map, and put
\[
N=\ker\overline S.
\]
Since \(S(N)\subset\operatorname{Im}X_0\), choose a linear map
\[
P:N\to V_0
\]
such that
\[
X_0P=S|_N.
\]
For \(T\in\mathcal B_{-\epsilon}(E')\), define a bilinear form on \(N\) by
\[
\Theta^P_{S,T}(u,v)
:=
T(u,v)+\langle Pu,Sv\rangle-\langle Su,Pv\rangle+\langle X_0Pu,Pv\rangle
\qquad(u,v\in N).
\]

First prove that \(\Theta^P_{S,T}\) is independent of the choice of \(P\);
write the resulting form as \(\Theta_{S,T}\).

A \((-\epsilon)\)-symmetric bilinear form \(b\) on a finite-dimensional
vector space \(W\) is called maximally non-degenerate if its radical is
one-dimensional when \(-\epsilon=-1\) and \(\dim W\) is odd, and is
non-degenerate otherwise.

Define
\[
\mathcal B_{-\epsilon}^{\max}(E',S)
=
\{T\in\mathcal B_{-\epsilon}(E'):\Theta_{S,T}
\text{ is maximally non-degenerate on }N\}.
\]

## Problem

Prove that for \(T_1,T_2\in\mathcal B_{-\epsilon}^{\max}(E',S)\),
\[
H\cdot (X_0+Y_{S,T_1})=H\cdot (X_0+Y_{S,T_2})
\]
if and only if the forms
\[
\Theta_{S,T_1},\qquad \Theta_{S,T_2}
\]
are congruent under \(\operatorname{GL}(N)\).

The proof should explicitly derive the unipotent conjugation formula. It should
also explain why this statement reduces to the normal form case
\(\ker S=\ker\overline S\), where the invariant is the ordinary restriction
\(T|_{\ker S}\).
