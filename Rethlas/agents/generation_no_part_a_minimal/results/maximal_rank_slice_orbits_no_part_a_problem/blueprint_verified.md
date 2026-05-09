# Maximal-Rank Slice Orbit Classification

## statement

Let \(F=\mathbb R\) or \(F=\mathbb C\), and let
\(\epsilon\in\{\pm1\}\). Let \(V\) be a finite-dimensional \(F\)-vector
space equipped with a non-degenerate \(\epsilon\)-symmetric bilinear form
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
With respect to \(V=E\oplus V_0\oplus E'\), identify
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

Define the maximal-rank subset
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
Here non-degenerate means non-degenerate for the restriction of
\(\langle\ ,\ \rangle\) to the subspace \(\ker(S^*|_K)\subset K\).

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
\[
X_0+\operatorname{Hom}^{\max}(E',V_0)
\]
is viewed as a \(\Gamma\)-stable subset of this quotient affine space.

In the case \(\dim K>\dim E\), for
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

Prove the following two orbit statements.

1. If \(\dim E\ge \dim K\), then \(\Gamma\) acts transitively on
   \[
   X_0+\operatorname{Hom}^{\max}(E',V_0).
   \]

2. If \(\dim K>\dim E\), then for every
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

## proof

We first isolate the elementary linear algebra used in the orbit
calculation.

### 1. Two basic facts about \(X_0\)

Because \(X_0\in\mathfrak g_0\), it is skew-adjoint:
\[
\langle X_0v,w\rangle+\langle v,X_0w\rangle=0
\qquad(v,w\in V_0).
\]
Hence
\[
K^\perp=(\ker X_0)^\perp=\operatorname{Im}X_0.
\]
Indeed, for a linear map on a finite-dimensional non-degenerate bilinear
space one has \((\ker A)^\perp=\operatorname{Im}A^*\), and here
\(X_0^*=-X_0\). Thus the radical of \(\langle\ ,\ \rangle|_K\) is
\[
R=K\cap K^\perp=K\cap\operatorname{Im}X_0.
\]
Consequently the form on \(K\) descends to a non-degenerate
\(\epsilon\)-symmetric form on \(K/R\).

We shall also use the following centralizer lemma.

**Lemma.** Let \(L_1,L_2\subset K\) be non-degenerate subspaces of the
same dimension. Suppose that their images in \(K/R\) satisfy
\[
q(L_2)=a\,q(L_1)
\]
for some \(a\in G(K/R)\), where \(q:K\to K/R\) is the quotient map. Then
there is \(z\in Z_{G_0}(X_0)\) such that the induced isometry of \(K/R\)
is \(a\), and
\[
zL_1=L_2.
\]

**Proof of the lemma.** Choose a non-degenerate complement \(C\) to
\(R\) in \(K\). Then \(q|_C:C\to K/R\) is an isometry. Since \(C\subset K\),
\(X_0|_C=0\). Also \(C^\perp\) is \(X_0\)-stable, because for
\(c\in C\) and \(v\in C^\perp\),
\[
\langle X_0v,c\rangle=-\langle v,X_0c\rangle=0.
\]
Thus \(V_0=C\oplus C^\perp\), with \(X_0=0\) on \(C\). The isometry
\(a\) lifts to an isometry \(a_C\) of \(C\), and
\[
z_0:=a_C\oplus 1_{C^\perp}
\]
lies in \(Z_{G_0}(X_0)\). Replacing \(L_1\) by \(z_0L_1\), it remains to
handle the case \(q(L_1)=q(L_2)\) and to construct an element inducing the
identity on \(K/R\).

Let \(W\subset C\) be the common inverse image of \(q(L_1)=q(L_2)\) under
\(q|_C\). Since \(L_i\cap R=0\), each \(q|_{L_i}\) is injective, and hence
each \(L_i\) is the graph of a unique linear map
\[
\phi_i:W\to R:
\qquad
L_i=\{w+\phi_i(w):w\in W\}.
\]
Extend \(\phi_2-\phi_1:W\to R\) to a linear map \(A:C\to R\). Let
\(A^*:C^\perp\to C\) be the adjoint of \(A\), defined by
\[
\langle A^*v,c\rangle=\langle v,Ac\rangle
\qquad(v\in C^\perp,\ c\in C).
\]
Define \(N:V_0=C\oplus C^\perp\to V_0\) by
\[
N(c+v)=Ac-A^*v .
\]
Then \(N^*=-N\), so \(N\in\mathfrak g_0\). Moreover \(N\) commutes with
\(X_0\). On \(C\) this is clear because \(X_0C=0\) and \(A(C)\subset
R\subset\ker X_0\). On \(C^\perp\), for \(v\in C^\perp\) and \(c\in C\),
\[
\langle A^*X_0v,c\rangle=\langle X_0v,Ac\rangle
=-\langle v,X_0Ac\rangle=0,
\]
so \(A^*X_0v=0\); hence \(NX_0v=0=X_0Nv\), since \(Nv=-A^*v\in C\).
Thus \(\exp N\in Z_{G_0}(X_0)\).

Finally \(A^*R=0\), because \(R\) is the radical of \(K\) and
\(A(C)\subset R\). Therefore \(N^2c=0\) for \(c\in C\), and \(\exp N\)
acts on \(C\) by
\[
\exp(N)c=c+Ac.
\]
It fixes \(R\). Thus for \(w\in W\),
\[
\exp(N)(w+\phi_1(w))
=w+A w+\phi_1(w)
=w+\phi_2(w).
\]
So \(\exp(N)L_1=L_2\), and the lemma follows. \(\square\)

### 2. Reduction from \(S\) to \(\lambda_S=S^*|_K\)

Set
\[
\lambda_S:=S^*|_K:K\to E.
\]
The map
\[
S\longmapsto \lambda_S
\]
from \(\operatorname{Hom}(E',V_0)\) to \(\operatorname{Hom}(K,E)\) is
surjective. To see this, fix a linear map \(\lambda:K\to E\). For each
\(u\in E'\), the rule
\[
v\longmapsto \langle \lambda(v),u\rangle
\qquad(v\in K)
\]
is a linear functional on \(K\). Since \(V_0\) is non-degenerate, every
linear functional on \(K\) is represented by pairing with some vector of
\(V_0\). Choosing these representing vectors linearly in \(u\) gives
\(S:E'\to V_0\) such that \(S^*|_K=\lambda\).

The fibers of \(S\mapsto\lambda_S\) are exactly the \(U\)-orbits in the
quotient by the \(T\)-coordinate. Indeed, for \(A:E'\to V_0\), the
unipotent element \(\exp(Y_{A,B})\) changes the \(S\)-coordinate by
\[
S\longmapsto S-X_0A
\]
after projection to \(X_0+\operatorname{Hom}(E',V_0)\); the value of \(B\)
and the resulting \(T\)-coordinate are irrelevant in this quotient. This
formula follows by computing
\[
[Y_{A,B},X_0]=Y_{-X_0A,0},
\]
while brackets inside \(\mathfrak u\) contribute only to the top-right
\(T\)-coordinate.

Since \((X_0A)^*|_K=-A^*X_0|_K=0\), this \(U\)-action preserves
\(\lambda_S\). Conversely, if \(S_1^*|_K=S_2^*|_K\), then
\(D:=S_2-S_1\) satisfies \(D^*|_K=0\). Equivalently, the image of \(D\)
is contained in \(K^\perp=\operatorname{Im}X_0\). Hence there is
\(A:E'\to V_0\) with \(-X_0A=D\), and the above \(U\)-action carries
\(S_1\) to \(S_2\). Thus, after quotienting by \(U\), the orbit problem is
the orbit problem for the maps \(\lambda_S:K\to E\).

The Levi action has the expected form. If \(h\in\operatorname{GL}(E')\)
and \(g\in Z_{G_0}(X_0)\), then the induced action on
\(\lambda=\lambda_S\) is
\[
\lambda\longmapsto h_E\circ\lambda\circ g^{-1}|_K,
\]
where \(h_E\in\operatorname{GL}(E)\) is the contragredient map determined
by the perfect pairing between \(E\) and \(E'\). Since
\(h\mapsto h_E\) is an isomorphism from \(\operatorname{GL}(E')\) to
\(\operatorname{GL}(E)\), we may equivalently use the natural
\(\operatorname{GL}(E)\)-action on the target of \(\lambda\).

Therefore the original \(\Gamma\)-orbits on
\(X_0+\operatorname{Hom}^{\max}(E',V_0)\) are the same as the
\(\operatorname{GL}(E)\times Z_{G_0}(X_0)\)-orbits on the following
corresponding set of maps \(\lambda:K\to E\):
\[
\begin{cases}
\lambda\text{ injective}, & \dim E\ge \dim K,\\
\lambda\text{ surjective and }\ker\lambda\text{ non-degenerate},
& \dim K>\dim E.
\end{cases}
\]

### 3. The case \(\dim E\ge \dim K\)

Let \(\lambda_1,\lambda_2:K\to E\) be injective. Since their images are
subspaces of \(E\) of the same dimension, there is an element
\(h\in\operatorname{GL}(E)\) carrying \(\lambda_1(K)\) isomorphically to
\(\lambda_2(K)\) and satisfying
\[
h\lambda_1=\lambda_2.
\]
Thus all injective \(\lambda\)'s lie in one \(\operatorname{GL}(E)\)-orbit.
By the reduction above, all \(S\in\operatorname{Hom}^{\max}(E',V_0)\) lie
in one \(\Gamma\)-orbit. This proves transitivity in the first case.

### 4. The case \(\dim K>\dim E\)

Let \(S\in\operatorname{Hom}^{\max}(E',V_0)\), and put
\(\lambda=\lambda_S\), \(L=\ker\lambda\). Since \(\lambda\) is surjective,
\[
\dim L=\dim K-\dim E.
\]
By definition of \(\operatorname{Hom}^{\max}\), the restriction of the
form to \(L\) is non-degenerate. Since \(R\) is the radical of the form on
\(K\), this implies \(L\cap R=0\). Hence \(q|_L:L\to K/R\) is injective
and preserves the form. Its image is exactly \(V_S\), so \(V_S\) is
non-degenerate and
\[
\dim V_S=\dim L=\dim K-\dim E.
\]

Now we classify the orbits. If \(S_1\) and \(S_2\) are in the same
\(\Gamma\)-orbit, then their maps \(\lambda_i=\lambda_{S_i}\) are related
by
\[
\lambda_2=h\lambda_1 g^{-1}
\]
for some \(h\in\operatorname{GL}(E)\) and \(g\in Z_{G_0}(X_0)\). Therefore
\[
\ker\lambda_2=g(\ker\lambda_1).
\]
Passing to \(K/R\), we get
\[
V_{S_2}=\bar g\,V_{S_1},
\]
where \(\bar g\in G(K/R)\) is the isometry induced by \(g\). Thus
\(S\mapsto V_S\) is constant on \(\Gamma\)-orbits after passing to
\(G(K/R)\)-orbits.

Conversely, suppose \(S_1,S_2\in\operatorname{Hom}^{\max}(E',V_0)\) and
that
\[
V_{S_2}=a\,V_{S_1}
\]
for some \(a\in G(K/R)\). Put \(L_i=\ker\lambda_{S_i}\). The centralizer
lemma gives \(g\in Z_{G_0}(X_0)\) whose induced action on \(K/R\) is
\(a\) and such that
\[
gL_1=L_2.
\]
Then \(\lambda_{S_1}g^{-1}\) and \(\lambda_{S_2}\) are both surjective
maps \(K\to E\) with the same kernel \(L_2\). Therefore there is
\(h\in\operatorname{GL}(E)\) such that
\[
h\,\lambda_{S_1}g^{-1}=\lambda_{S_2}.
\]
By the reduction in Step 2, this equality of \(\lambda\)-data implies
that \(S_1\) and \(S_2\) are in the same \(\Gamma\)-orbit.

Finally, every non-degenerate subspace \(W\subset K/R\) of dimension
\(\dim K-\dim E\) occurs. Choose a non-degenerate lift \(L\subset K\) of
\(W\), for instance by choosing a non-degenerate complement \(C\) to \(R\)
in \(K\) and taking the inverse image of \(W\) inside \(C\). Since
\[
\dim K/L=\dim E,
\]
there is a surjective linear map \(\lambda:K\to E\) with kernel \(L\).
By the surjectivity of \(S\mapsto S^*|_K\), choose
\(S:E'\to V_0\) with \(S^*|_K=\lambda\). Then
\(S\in\operatorname{Hom}^{\max}(E',V_0)\) and \(V_S=W\).

Thus \(S\mapsto V_S\) induces a bijection between \(\Gamma\)-orbits on
\[
X_0+\operatorname{Hom}^{\max}(E',V_0)
\]
and \(G(K/R)\)-orbits on non-degenerate subspaces of \(K/R\) of dimension
\(\dim K-\dim E\). This proves the second orbit statement and completes
the proof. \(\square\)
