# Maximal-Rank Slice Orbits for a Classical Parabolic

Let \(F=\mathbb R\) or \(F=\mathbb C\), and let \(\epsilon\in\{\pm1\}\).
Let \(V\) be a finite-dimensional \(F\)-vector space equipped with a
non-degenerate \(\epsilon\)-symmetric bilinear form
\[
\langle u,v\rangle=\epsilon\langle v,u\rangle .
\]
Let
\[
G=\operatorname{Isom}(V,\langle\ ,\ \rangle).
\]

Fix a Witt decomposition
\[
V=E\oplus V_0\oplus E',
\]
where \(V_0\) is non-degenerate, while \(E\) and \(E'\) are totally
isotropic and paired perfectly by \(\langle\ ,\ \rangle\). Let
\[
P=M\ltimes U
\]
be the parabolic subgroup stabilizing \(E\). Its Levi factor is identified
with
\[
M\simeq G_0\times \operatorname{GL}(E'),
\qquad
G_0:=\operatorname{Isom}(V_0).
\]
Let \(\mathfrak u=\operatorname{Lie}(U)\) and
\(\mathfrak g_0=\operatorname{Lie}(G_0)\).

Fix a nilpotent element \(X_0\in\mathfrak g_0\). Put
\[
K:=\ker X_0,
\qquad
R:=\operatorname{rad}\bigl(\langle\ ,\ \rangle|_K\bigr).
\]
Equivalently,
\[
R=K\cap \operatorname{Im}X_0,
\qquad
\dim R=\dim(\ker X_0^2/\ker X_0).
\]
Assume
\[
\dim E\ge \dim R.
\]
If \(\epsilon=-1\) and \(\dim K>\dim E\), assume moreover that
\[
\dim K-\dim E
\]
is even.

For \(S\in\operatorname{Hom}(E',V_0)\), define \(S^*:V_0\to E\) by
\[
\langle S^*v,u\rangle=\langle v,Su\rangle
\qquad(v\in V_0,\ u\in E').
\]
Let \(\mathcal B_{-\epsilon}(E')\) denote the space of
\((-\epsilon)\)-symmetric bilinear forms on \(E'\). Using the perfect
pairing between \(E\) and \(E'\), we also regard an element
\(T\in\mathcal B_{-\epsilon}(E')\) as a map \(T:E'\to E\) satisfying
\[
\langle Tu,v\rangle=-\epsilon\langle Tv,u\rangle
\qquad(u,v\in E').
\]
With respect to \(V=E\oplus V_0\oplus E'\), there is an identification
\[
\operatorname{Hom}(E',V_0)\oplus\mathcal B_{-\epsilon}(E')
\xrightarrow{\sim}
\mathfrak u,
\qquad
(S,T)\mapsto
Y_{S,T}:=
\begin{bmatrix}
0&-S^*&T\\
0&0&S\\
0&0&0
\end{bmatrix}.
\]

Define
\[
\operatorname{Hom}^{\max}(E',V_0):=
\begin{cases}
\{S\in\operatorname{Hom}(E',V_0): S^*|_K\text{ is injective}\},
& \dim E\ge \dim K,\\[4pt]
\{S\in\operatorname{Hom}(E',V_0): S^*|_K\text{ is surjective and }
\ker(S^*|_K)\text{ is non-degenerate}\},
& \dim K>\dim E.
\end{cases}
\]
Here "non-degenerate" in the second case means non-degenerate for the
restriction of \(\langle\ ,\ \rangle\) to the subspace
\(\ker(S^*|_K)\subset K\).

Let
\[
\Gamma:=(\operatorname{GL}(E')\times Z_{G_0}(X_0))\ltimes U.
\]
The adjoint action of \(\Gamma\) on \(X_0+\mathfrak u\) descends, via the
projection
\[
X_0+\mathfrak u
\simeq
X_0+\operatorname{Hom}(E',V_0)\oplus\mathcal B_{-\epsilon}(E')
\longrightarrow
X_0+\operatorname{Hom}(E',V_0),
\]
to an action on the affine space \(X_0+\operatorname{Hom}(E',V_0)\). Thus
we view
\[
X_0+\operatorname{Hom}^{\max}(E',V_0)
\]
as a \(\Gamma\)-stable subset of this quotient affine space.

In the case \(\dim K>\dim E\), for each
\(S\in\operatorname{Hom}^{\max}(E',V_0)\), define
\[
V_S
:=
\text{the image of }\ker(S^*|_K)\text{ under }K\to K/R.
\]
The form \(\langle\ ,\ \rangle\) induces a non-degenerate
\(\epsilon\)-symmetric bilinear form on \(K/R\), and we write
\[
G(K/R):=\operatorname{Isom}(K/R).
\]

Prove the following statements.

For the proof of the openness and density assertion in (1), use the following
topological route. In the case where the relevant maps have maximal rank, the
kernel construction should be treated as a smooth map from the maximal-rank
locus in a Hom-space to the appropriate Grassmannian. Non-degeneracy of the
restricted bilinear form is an open condition on the Grassmannian. For density,
show that the desired maximal condition defines a nonempty Zariski open subset
of the Hom-space, and use the fact that a nonempty Zariski open subset of a
finite-dimensional real or complex affine space is dense in the usual topology.

1. Under the Euclidean topology, viewed as the usual real topology on the
   finite-dimensional real vector space underlying
   \(\operatorname{Hom}(E',V_0)\), the subset
   \[
   \operatorname{Hom}^{\max}(E',V_0)
   \]
   is open dense in \(\operatorname{Hom}(E',V_0)\).

2. If \(\dim E\ge \dim K\), then \(\Gamma\) acts transitively on
   \[
   X_0+\operatorname{Hom}^{\max}(E',V_0).
   \]

3. If \(\dim K>\dim E\), then for every
   \(S\in\operatorname{Hom}^{\max}(E',V_0)\), the space \(V_S\) is a
   non-degenerate subspace of \(K/R\) of dimension
   \[
   \dim V_S=\dim K-\dim E.
   \]
   Moreover, the map
   \[
   S\mapsto V_S
   \]
   induces a bijection between the set of \(\Gamma\)-orbits on
   \[
   X_0+\operatorname{Hom}^{\max}(E',V_0)
   \]
   and the set of \(G(K/R)\)-orbits on non-degenerate subspaces of \(K/R\)
   of dimension \(\dim K-\dim E\).
