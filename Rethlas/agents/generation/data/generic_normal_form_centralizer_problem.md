# Lie Algebra Centralizer for the Generic Normal Form

## Setup
Let \(F=\mathbb R\). Let \((V_0,\langle\,,\,\rangle_0)\) be a non-degenerate
\(\epsilon\)-symmetric space, where \(\epsilon=1\) is the symmetric case and
\(\epsilon=-1\) is the alternating case. Let
\[
X_0\in\mathfrak g_0:=\operatorname{Lie}\operatorname{Isom}(V_0)
\]
be nilpotent. Set
\[
c_1:=\dim\ker X_0,\qquad
c_2:=\dim(\ker X_0\cap\operatorname{Im}X_0).
\]
Let \(E,E'\) be real vector spaces of dimension \(\kappa\), with perfect pairing
\[
\lambda:E\times E'\to\mathbb R,
\]
and assume
\[
c_2\le \kappa<c_1,\qquad d:=c_1-\kappa.
\]
Let
\[
V=E\oplus V_0\oplus E',
\qquad
G=\operatorname{Isom}(V),
\qquad
P=\operatorname{Stab}_G(E),
\qquad
\mathfrak p=\operatorname{Lie}(P),
\]
where the form on \(V\) is the orthogonal sum of \((V_0,\langle\,,\,\rangle_0)\)
and the hyperbolic pairing between \(E\) and \(E'\).

Put
\[
R:=\ker X_0\cap\operatorname{Im}X_0.
\]
Choose \(V_1\subset\ker X_0\) such that
\[
\ker X_0=V_1\oplus R.
\]
Choose an adapted complement
\[
V_0=V_+\oplus\operatorname{Im}X_0
\]
such that
\[
V_+\cap\ker X_0=V_1.
\]
Then
\[
\dim V_1=c_1-c_2,\qquad
\dim\bigl(V_+/V_1\bigr)=c_2.
\]

For \(S:E'\to V_+\), assume
\[
S \text{ is injective},\qquad
\bar S:E'\to V_+/(V_+\cap\ker X_0) \text{ is surjective}.
\]
Set
\[
K_{X_0}:=\ker X_0/R,
\]
and let \(q:\ker X_0\to K_{X_0}\) be the quotient map. The form on
\(\ker X_0\) induces a non-degenerate \(\epsilon\)-symmetric form
\(\langle\,,\,\rangle_K\) on \(K_{X_0}\).

Define
\[
\phi_S:=S^\vee|_{\ker X_0},\qquad
L:=\ker\phi_S,\qquad
A:=q(L)\subset K_{X_0}.
\]
The assumptions on \(S\) imply
\[
\dim L=d,\qquad L\cap R=0,\qquad \dim A=d.
\]
Set
\[
n:=\dim K_{X_0}=c_1-c_2,\qquad
r:=\dim\operatorname{rad}(\langle\,,\,\rangle_K|_A).
\]

Define
\[
x_S:=X_{S,0}
=
\begin{pmatrix}
0&S^\vee&0\\
0&X_0&S\\
0&0&0
\end{pmatrix}
\in\mathfrak p
\]
relative to \(V=E\oplus V_0\oplus E'\).

## Problem
Compute the Lie algebra centralizer
\[
\mathfrak z_{\mathfrak p}(x_S):=\{Y\in\mathfrak p:[Y,x_S]=0\}.
\]

More precisely:

1. Write a general element \(Y\in\mathfrak p\) in block form relative to
   \[
   V=E\oplus V_0\oplus E'
   \]
   and compute \([Y,x_S]\) explicitly.

2. Solve the resulting block equations completely enough to describe
   \(\mathfrak z_{\mathfrak p}(x_S)\).

3. Show that the \(B\)- and \(T\)-block freedoms contribute only a
   constant-dimensional linear space, independent of the rank of
   \(\langle\,,\,\rangle_K|_A\).

4. Let
   \[
   \mathfrak z:=\mathfrak z_{\mathfrak g_0}(X_0),\qquad
   \mathfrak h:=\operatorname{Lie}\operatorname{Isom}(K_{X_0}),
   \]
   and let
   \[
   \rho:\mathfrak z\to\mathfrak h
   \]
   be the map induced by the action of \(\mathfrak z\) on
   \(K_{X_0}=\ker X_0/R\). Define
   \[
   \mathfrak c_L
   :=
   \{D\in\mathfrak z_{\mathfrak g_0}(X_0):DL\subset L\},
   \qquad
   \mathfrak h_A
   :=
   \{u\in\mathfrak h:uA\subset A\}.
   \]
   Prove that \(\rho\) is surjective and that the induced map
   \[
   \mathfrak c_L\to\mathfrak h_A
   \]
   is surjective.

5. Prove the constant-fiber calculation for
   \(\mathfrak c_L\to\mathfrak h_A\). If
   \[
   \mathfrak n:=\ker\rho,
   \]
   then the restriction map
   \[
   \mathfrak n\to\operatorname{Hom}(L,R),\qquad N\mapsto N|_L
   \]
   is surjective, and hence
   \[
   \dim\ker(\mathfrak c_L\to\mathfrak h_A)
   =
   \dim\mathfrak n-dc_2.
   \]
   In particular the fiber dimension of
   \[
   \mathfrak c_L\to\mathfrak h_A
   \]
   is independent of the rank of \(\langle\,,\,\rangle_K|_A\).

   A useful way to prove the required surjectivity is to use rank-two
   operators: for \(r_0\in R\) and \(v\in\ker X_0\), set
   \[
   T_{r_0,v}(w)
   =
   r_0\langle v,w\rangle_0-\epsilon v\langle r_0,w\rangle_0.
   \]
   Show that \(T_{r_0,v}\in\ker\rho\), and that these operators realize all
   maps \(K_{X_0}\to R\), hence all maps \(L\to R\) because \(L\cap R=0\).

6. Deduce the dimension formula
   \[
   \dim\mathfrak c_L
   =
   \dim\mathfrak z_{\mathfrak g_0}(X_0)
   -dc_2-d(n-d)+\frac{r(r+\epsilon)}2.
   \]

   For this, compute
   \[
   \dim\mathfrak h_A
   =
   \frac{n(n-\epsilon)}2-d(n-d)+\frac{r(r+\epsilon)}2.
   \]
   One direct route is to compute the dimension of the \(H\)-orbit of \(A\),
   where \(H=\operatorname{Isom}(K_{X_0})\). The stratum of \(d\)-planes in
   \(K_{X_0}\) whose restricted form has radical dimension \(r\) has dimension
   \[
   d(n-d)-\frac{r(r+\epsilon)}2.
   \]

7. Deduce that \(\dim\mathfrak z_{\mathfrak p}(x_S)\) is minimal exactly when
   \(\langle\,,\,\rangle_K|_A\) has maximal possible rank. Equivalently, the
   radical dimension \(r\) is minimal: \(r=0\) in the symmetric case, and in
   the alternating case \(r=0\) for even \(d\) and \(r=1\) for odd \(d\).

## Exclusions
Do not use signed Young diagrams, component groups, multiplicities, or
defect-space language.

Do not use SymPy, Sage, Mathematica, computer algebra, or any machine algebra
check in the proof. In particular, do not use Python or any other programming
language to verify dimension identities, ranks, or linear-algebra formulas.
All dimension identities and linear algebra calculations must be proved by
hand in the Rethlas proof. Rethlas infrastructure tools for memory, search, and
verification may still be used when required by AGENTS.md, but they must not
serve as mathematical evidence.
