# lemma lem:adapted-splitting

## statement
There exists a decomposition
\[
K=\ker X_0=L\oplus R
\]
such that:

1. \(L\) is non-degenerate for \(\langle\ ,\ \rangle\);
2. \(X_0|_L=0\);
3. the projection \(K\to K/R\) identifies \(L\) isometrically with \(K/R\).

Moreover one may choose a direct-sum decomposition
\[
V_0=L\oplus R\oplus D\oplus H
\]
such that:

1. \(X_0\) vanishes on \(L\oplus R\);
2. \(R\) pairs perfectly with \(D\);
3. \(L\) is orthogonal to \(R\oplus D\oplus H\);
4. \(X_0(D)\subseteq R\oplus H\);
5. \(X_0(R\oplus H)\subseteq R\oplus H\).

## proof
Choose an orthogonal Jordan decomposition of the nilpotent skew-adjoint operator
\(X_0\): \(V_0\) is an orthogonal direct sum of the usual indecomposable
\(X_0\)-stable non-degenerate blocks for a classical group, namely paired
Jordan chains and self-dual Jordan chains.

Let \(L\) be the orthogonal direct sum of the blocks of size \(1\). On those
blocks \(X_0\) is zero, hence \(L\subseteq K\), and \(L\) is non-degenerate
because it is an orthogonal direct sum of non-degenerate size-\(1\) blocks.

In a size-\(1\) block the whole block lies in \(K\) and contributes to \(L\).
In every indecomposable block of size \(>1\), every kernel vector lies in
\(\operatorname{Im}X_0\): for a self-dual block there is one such kernel
vector, and for a paired \(m\!+\!m\) block there are two, one from each chain.
Therefore the kernel vectors coming from blocks of size \(>1\) span exactly
\[
R=K\cap \operatorname{Im}X_0,
\]
and every element of \(K\) decomposes uniquely as a sum of a kernel vector from
the size-\(1\) blocks and a kernel vector coming from the longer blocks. Thus
\[
K=L\oplus R.
\]
Since \(R\) is the radical of \(\langle\ ,\ \rangle|_K\), the quotient map
\(K\to K/R\) restricts to an isometric isomorphism \(L\xrightarrow{\sim}K/R\).

Now choose, in each longer indecomposable block, basis vectors as follows.
For every kernel basis vector \(r_j\) in that block choose a vector \(d_j\) in
the same block with \(\langle r_j,d_j\rangle\neq 0\). In a self-dual block
there is one such pair \((r_j,d_j)\); in a paired \(m\!+\!m\) block there are
two, one for each chain. After rescaling, the vectors \(r_j\) form a basis of
\(R\), the vectors \(d_j\) span a subspace \(D\) paired perfectly with \(R\),
and \(D\) is orthogonal to \(L\). Let \(H\) be the span of all remaining basis
vectors in the longer blocks. Then
\[
V_0=L\oplus R\oplus D\oplus H,
\]
and by construction \(X_0\) vanishes on \(L\oplus R\), the only nonzero
pairings involving \(R\) are with \(D\), \(L\) is orthogonal to
\(R\oplus D\oplus H\), \(X_0(D)\subseteq R\oplus H\), and also
\(X_0(R\oplus H)\subseteq R\oplus H\): in every Jordan chain,
applying \(X_0\) moves one step downward, so once one removes the top vectors
\(d_j\), the remaining part of the longer block is \(X_0\)-stable up to the
kernel vectors \(r_j\). This is exactly the required decomposition.


# lemma lem:quotient-model

## statement
Let
\[
\rho:\operatorname{Hom}(E',V_0)\longrightarrow \operatorname{Hom}(K,E),
\qquad
\rho(S)=S^*|_K.
\]
Then:

1. \(\rho\) is surjective;
2. \(\ker \rho=X_0\operatorname{Hom}(E',V_0)\);
3. the fibers of \(\rho\) are exactly the \(U\)-orbits in
   \(X_0+\operatorname{Hom}(E',V_0)\);
4. consequently, \(\rho\) induces a bijection between the set of
   \(\Gamma\)-orbits on \(X_0+\operatorname{Hom}(E',V_0)\) and the set of
   \((\operatorname{GL}(E')\times Z_{G_0}(X_0))\)-orbits on
   \(X_0+\operatorname{Hom}(K,E)\);
5. under the induced action on \(\operatorname{Hom}(K,E)\),
   \(\operatorname{GL}(E')\) acts through its contragredient action on \(E\),
   and \(Z_{G_0}(X_0)\) acts by precomposition through its action on \(K\).

## proof
First,
\[
\operatorname{Im}X_0\subseteq K^\perp,
\]
because for \(v\in V_0\) and \(k\in K\),
\[
\langle X_0v,k\rangle=-\langle v,X_0k\rangle=0.
\]
The two subspaces have the same dimension:
\[
\dim K^\perp=\dim V_0-\dim K=\dim \operatorname{Im}X_0.
\]
Hence
\[
K^\perp=\operatorname{Im}X_0.
\]

Now \(\rho(S)=0\) means precisely that \(\langle k,Su\rangle=0\) for every
\(k\in K\) and \(u\in E'\). Equivalently, \(\operatorname{Im}S\subseteq K^\perp\),
so \(\operatorname{Im}S\subseteq \operatorname{Im}X_0\). Thus \(S=X_0A\) for
some \(A\in \operatorname{Hom}(E',V_0)\). Conversely,
\[
\rho(X_0A)=(X_0A)^*|_K=-A^*X_0|_K=0.
\]
Therefore
\[
\ker \rho=X_0\operatorname{Hom}(E',V_0).
\]

For surjectivity, fix \(\lambda\in\operatorname{Hom}(K,E)\). Using the perfect
pairing between \(E\) and \(E'\), \(\lambda\) is the same thing as a bilinear
form \(b_\lambda\) on \(K\times E'\). Because the form on \(V_0\) is
non-degenerate, the linear map
\[
V_0\longrightarrow K^*,\qquad v\longmapsto \langle\,\cdot\,,v\rangle|_K
\]
has kernel \(K^\perp=\operatorname{Im}X_0\), hence is surjective. Therefore,
for each \(u\in E'\), there exists \(Su\in V_0\) such that
\[
\langle k,Su\rangle=b_\lambda(k,u)\qquad(k\in K).
\]
Doing this linearly in \(u\) gives \(S\in \operatorname{Hom}(E',V_0)\) with
\(\rho(S)=\lambda\). So \(\rho\) is surjective.

It remains to describe the action. Write \(A\in\operatorname{Hom}(E',V_0)\),
\(B\in\mathcal B_{-\epsilon}(E')\), and \(Y_{A,B}\in\mathfrak u\). A direct
block-matrix calculation gives
\[
[Y_{A,B},X_0]=Y_{-X_0A,0}.
\]
Since \([\mathfrak u,\mathfrak u]\subseteq \mathcal B_{-\epsilon}(E')\), the
\(\operatorname{Hom}(E',V_0)\)-coordinate of
\(\operatorname{Ad}(\exp Y_{A,B})(X_0+Y_{S,T})\) is \(S-X_0A\). Hence \(U\)
acts by translation by \(X_0\operatorname{Hom}(E',V_0)\). By the kernel
computation above, the fibers of \(\rho\) are exactly the \(U\)-orbits.

For \((g,h)\in \operatorname{GL}(E')\times Z_{G_0}(X_0)\), the
\(\operatorname{Hom}(E',V_0)\)-coordinate is \(hSg^{-1}\), and therefore
\[
\rho(hSg^{-1})=(g^{-1})^*\circ \rho(S)\circ h^{-1}|_K.
\]
Thus \(\rho\) is equivariant for the action of
\(\operatorname{GL}(E')\times Z_{G_0}(X_0)\), and it identifies the
\(\Gamma\)-orbit problem on \(X_0+\operatorname{Hom}(E',V_0)\) with the
\((\operatorname{GL}(E')\times Z_{G_0}(X_0))\)-orbit problem on
\(X_0+\operatorname{Hom}(K,E)\). This proves the lemma.


# proposition prop:openness-density

## statement
The subset \(\operatorname{Hom}^{\max}(E',V_0)\) is open dense in
\(\operatorname{Hom}(E',V_0)\).

## proof
By Lemma \(\mathrm{lem{:}quotient\text{-}model}\), \(\rho\) is a surjective
linear map, and \(\operatorname{Hom}^{\max}(E',V_0)\) is the inverse image
under \(\rho\) of the following subset \(\mathcal M^{\max}\subseteq
\operatorname{Hom}(K,E)\):

- if \(\dim E\ge \dim K\), \(\mathcal M^{\max}\) is the set of injective maps
  \(K\to E\);
- if \(\dim K>\dim E\), \(\mathcal M^{\max}\) is the set of surjective maps
  \(\lambda:K\to E\) whose kernel is non-degenerate.

So it is enough to prove that \(\mathcal M^{\max}\) is open dense.

If \(\dim E\ge \dim K\), injectivity is the nonvanishing of at least one
\(\dim K\times \dim K\) minor, hence is open; it is dense because the
complement is a proper algebraic subset.

Assume now \(\dim K>\dim E\). Put
\[
d:=\dim K-\dim E.
\]
By Lemma \(\mathrm{lem{:}adapted\text{-}splitting}\), choose
\[
K=L\oplus R,\qquad L\simeq K/R
\]
with \(L\) non-degenerate. Because \(\dim E\ge \dim R\), we have
\[
d=\dim K-\dim E\le \dim K-\dim R=\dim L.
\]
If \(\epsilon=-1\), then \(L\) is symplectic; the additional hypothesis says
that \(d\) is even, which is exactly the parity condition for the existence of
non-degenerate \(d\)-dimensional subspaces of a symplectic space.

Let \(\operatorname{Gr}_d(K)\) be the Grassmannian of \(d\)-planes in \(K\),
and let \(\Omega\subseteq \operatorname{Gr}_d(K)\) be the open set of
subspaces transverse to \(R\):
\[
\Omega=\{N\subseteq K:\dim N=d,\ N\cap R=0\}.
\]
For \(N\in\Omega\), the projection \(K=L\oplus R\to L\) restricts to an
isomorphism \(N\xrightarrow{\sim} q(N)\), and \(N\) is the graph of a unique
linear map \(q(N)\to R\). Because \(R\) is the radical of \(\langle\ ,\
\rangle|_K\), the form on \(N\) is exactly the pullback of the form on
\(q(N)\subseteq L\). Therefore
\[
N\text{ is non-degenerate } \Longleftrightarrow q(N)\subseteq L
\text{ is non-degenerate.}
\]
The set of non-degenerate \(d\)-planes in the non-degenerate space \(L\) is
open dense in \(\operatorname{Gr}_d(L)\), so its inverse image in \(\Omega\)
is open dense in \(\operatorname{Gr}_d(K)\). Hence the set
\[
\mathcal U_d:=\{N\in\operatorname{Gr}_d(K):N\text{ is non-degenerate}\}
\]
is open dense.

We now record the two topological facts needed for
\(\mathcal M^{\max}\). First, \(\mathcal M^{\max}\) is Euclidean open.
Surjectivity is an open maximal-rank condition. On a maximal-rank chart, choose
coordinates
\[
K=N_0\oplus E_0
\]
so that the \(E_0\to E\) block of \(\lambda\) is invertible. Then
\(\ker\lambda\) is the graph of a linear map \(N_0\to E_0\) whose matrix entries
are smooth rational functions of the entries of \(\lambda\). Equivalently, on
the surjective locus the map
\[
\kappa:\operatorname{Hom}_{\operatorname{surj}}(K,E)\longrightarrow
\operatorname{Gr}_d(K),\qquad \lambda\longmapsto \ker\lambda
\]
is smooth. Since the set \(\mathcal U_d\) of non-degenerate \(d\)-planes is open
in \(\operatorname{Gr}_d(K)\), we have
\[
\mathcal M^{\max}=\kappa^{-1}(\mathcal U_d),
\]
and therefore \(\mathcal M^{\max}\) is Euclidean open.

Second, \(\mathcal M^{\max}\) is Zariski open. Surjectivity is the nonvanishing
of at least one \(\dim E\times \dim E\) minor. On the same maximal-rank chart,
after multiplying by a power of the chosen minor, the determinant of the Gram
matrix of \(\langle\ ,\ \rangle|_{\ker\lambda}\) becomes a polynomial function.
Hence the condition that \(\ker\lambda\) be non-degenerate is the nonvanishing
of this polynomial on the rank chart. Taking the union over all rank charts,
\(\mathcal M^{\max}\) is a Zariski open subset of \(\operatorname{Hom}(K,E)\).

It is nonempty. Indeed, choose a non-degenerate \(d\)-plane
\(V\subseteq L\), possible by \(d\le \dim L\) and the parity hypothesis in the
symplectic case. Let
\[
N:=V\subseteq K=L\oplus R.
\]
Then \(N\) is non-degenerate in \(K\), and because
\[
\dim K/N=\dim E,
\]
there exists a surjective linear map \(\lambda:K\to E\) with kernel \(N\).
Thus \(\lambda\in\mathcal M^{\max}\).

A nonempty Zariski open subset of a finite-dimensional real or complex affine
space is dense in the usual Euclidean topology: a nonzero polynomial cannot
vanish on a Euclidean open ball. Therefore
\(\mathcal M^{\max}\) is Euclidean dense. Together with the Euclidean openness
proved above, \(\mathcal M^{\max}\) is open dense in \(\operatorname{Hom}(K,E)\).

Since \(\operatorname{Hom}^{\max}(E',V_0)=\rho^{-1}(\mathcal M^{\max})\) and
\(\rho\) is a surjective linear map, \(\operatorname{Hom}^{\max}(E',V_0)\) is
open dense in \(\operatorname{Hom}(E',V_0)\).


# proposition prop:large-E

## statement
If \(\dim E\ge \dim K\), then \(\Gamma\) acts transitively on
\[
X_0+\operatorname{Hom}^{\max}(E',V_0).
\]

## proof
Pass to the quotient model of Lemma \(\mathrm{lem{:}quotient\text{-}model}\).
There the orbit problem is the action of \(\operatorname{GL}(E')\times
Z_{G_0}(X_0)\) on the set of injective maps \(\lambda:K\to E\), and \(U\)
acts trivially.

But \(\operatorname{GL}(E')\) acts on \(E\) through the full linear group of
\(E\) (via the contragredient representation). If \(\lambda_1,\lambda_2:K\to
E\) are injective, choose \(a\in \operatorname{GL}(E)\) carrying
\(\lambda_1(K)\) isomorphically onto \(\lambda_2(K)\) and satisfying
\[
a\circ \lambda_1=\lambda_2.
\]
Then the corresponding element of \(\operatorname{GL}(E')\subseteq \Gamma\)
sends \(\lambda_1\) to \(\lambda_2\).

Thus all injective maps \(K\to E\) lie in a single \(\Gamma\)-orbit, hence so
do all points of \(X_0+\operatorname{Hom}^{\max}(E',V_0)\).


# lemma lem:shears-and-quotient-action

## statement
Keep the decomposition \(V_0=L\oplus R\oplus D\oplus H\) from
Lemma \(\mathrm{lem{:}adapted\text{-}splitting}\).

1. The restriction map
   \[
   Z_{G_0}(X_0)\longrightarrow G(L)\simeq G(K/R)
   \]
   is surjective.
2. For every linear map \(a:L\to R\), there exists
   \(u_a\in Z_{G_0}(X_0)\) such that
   \[
   u_a(\ell+r)=\ell+r+a(\ell)\qquad(\ell\in L,\ r\in R).
   \]
   In particular \(u_a\) acts trivially on \(K/R\).

## proof
Because \(L\) is an \(X_0\)-stable orthogonal direct summand and \(X_0|_L=0\),
any isometry of \(L\) extended by the identity on \(R\oplus D\oplus H\) lies
in \(Z_{G_0}(X_0)\). Hence the restriction map onto \(G(L)\) is surjective.

Now fix \(a:L\to R\). Since \(R\) and \(D\) are in perfect duality, there is a
unique adjoint map \(a^\dagger:D\to L\) characterized by
\[
\langle a\ell,d\rangle=\langle \ell,a^\dagger d\rangle
\qquad(\ell\in L,\ d\in D).
\]
Define a linear endomorphism \(A\) of \(V_0\) by
\[
A|_L=a,\qquad A|_D=-a^\dagger,\qquad A|_{R\oplus H}=0.
\]
We check that \(A\in \mathfrak g_0\) and \(AX_0=X_0A\).

Skew-adjointness is immediate from the definition of \(a^\dagger\), because
the only possibly nonzero terms in
\(\langle Ax,y\rangle+\langle x,Ay\rangle\) occur when one argument lies in
\(L\) and the other in \(D\). For \(\ell\in L\) and \(d\in D\),
\[
\langle A\ell,d\rangle+\langle \ell,Ad\rangle
=\langle a\ell,d\rangle-\langle \ell,a^\dagger d\rangle=0,
\]
and all other pairings vanish by the orthogonality properties from
Lemma \(\mathrm{lem{:}adapted\text{-}splitting}\).

Next, \(X_0\) vanishes on \(L\oplus R\), \(A\) vanishes on \(R\oplus H\), and
by Lemma \(\mathrm{lem{:}adapted\text{-}splitting}\) we have
\(X_0(D)\subseteq R\oplus H\) and \(X_0(R\oplus H)\subseteq R\oplus H\).
Therefore:

- if \(x\in L\), then \(X_0Ax=0=AX_0x\);
- if \(x\in D\), then \(X_0Ax=0\) because \(Ax\in L\), while
  \(AX_0x=0\) because \(X_0x\in R\oplus H\);
- if \(x\in R\oplus H\), then both \(AX_0x\) and \(X_0Ax\) are zero.

So \(AX_0=X_0A\), hence \(u_a:=\exp(A)\) belongs to \(Z_{G_0}(X_0)\).

Finally, on \(K=L\oplus R\) we have \(A(\ell+r)=a(\ell)\in R\) and
\(A(R)=0\), so \(A^2|_K=0\). Therefore
\[
u_a|_K=(1+A)|_K,
\]
and thus
\[
u_a(\ell+r)=\ell+r+a(\ell).
\]
This proves the lemma.


# proposition prop:small-E

## statement
Assume \(\dim K>\dim E\). Then:

1. for every \(S\in \operatorname{Hom}^{\max}(E',V_0)\), the space
   \[
   V_S=\text{image of }\ker(S^*|_K)\text{ in }K/R
   \]
   is non-degenerate of dimension \(\dim K-\dim E\);
2. the map \(S\mapsto V_S\) induces a bijection between the set of
   \(\Gamma\)-orbits on \(X_0+\operatorname{Hom}^{\max}(E',V_0)\) and the set
   of \(G(K/R)\)-orbits on non-degenerate subspaces of \(K/R\) of dimension
   \(\dim K-\dim E\).

## proof
Again pass to the quotient model of Lemma
\(\mathrm{lem{:}quotient\text{-}model}\). Write
\[
\lambda=\rho(S)=S^*|_K,\qquad N=\ker \lambda,\qquad d=\dim K-\dim E.
\]
By definition of \(\operatorname{Hom}^{\max}\), \(\lambda\) is surjective and
\(N\) is non-degenerate.

Using \(K=L\oplus R\) with \(L\simeq K/R\), let \(q:K\to L\) be the
projection. Since \(N\) is non-degenerate, we have \(N\cap R=0\), because
\(R\) is the radical of \(\langle\ ,\ \rangle|_K\). Hence \(q|_N\) is
injective. Its image is exactly \(V_S\) after identifying \(L\) with \(K/R\).
Because \(R\) is orthogonal to \(K\), the form on \(N\) is the pullback of the
form on \(q(N)\). Therefore \(q(N)=V_S\) is non-degenerate, and
\[
\dim V_S=\dim N=d=\dim K-\dim E.
\]
This proves (1).

For the orbit classification, first note that \(U\) acts trivially in the
quotient model, and \(\operatorname{GL}(E')\) acts on the left. In particular,
\(\operatorname{GL}(E')\) does not change the kernel \(N=\ker \lambda\), so the
only way the kernel moves is through \(Z_{G_0}(X_0)\).

If \(h\in Z_{G_0}(X_0)\), then \(h\) preserves \(K\) and \(R\), hence induces
an isometry \(\bar h\in G(K/R)\). For \(\lambda'=\lambda\circ h^{-1}|_K\),
\[
\ker \lambda'=h(N),
\]
so
\[
V_{\lambda'}=\bar h(V_\lambda).
\]
Thus \(S\mapsto V_S\) is constant on \(\Gamma\)-orbits up to the natural
\(G(K/R)\)-action.

We next show surjectivity on orbit sets. Let \(V\subseteq K/R\simeq L\) be a
non-degenerate \(d\)-dimensional subspace. Since \(L\) is non-degenerate,
\[
L=V\oplus W
\]
with \(W\) non-degenerate. Its dimension is
\[
\dim W=\dim L-d=(\dim K-\dim R)-(\dim K-\dim E)=\dim E-\dim R.
\]
Hence
\[
\dim(R\oplus W)=\dim R+\dim W=\dim E.
\]
Choose an isomorphism \(\alpha:R\oplus W\xrightarrow{\sim}E\), and define
\[
\lambda_V:K=L\oplus R=V\oplus W\oplus R\longrightarrow E,
\qquad
\lambda_V(v+w+r)=\alpha(w+r).
\]
Then \(\lambda_V\) is surjective and
\[
\ker \lambda_V=V,
\]
which is non-degenerate. Therefore \(\lambda_V\in \mathcal M^{\max}\), and by
surjectivity of \(\rho\) it comes from some \(S\in
\operatorname{Hom}^{\max}(E',V_0)\). So every non-degenerate
\(d\)-subspace of \(K/R\) occurs as some \(V_S\).

Finally we prove injectivity on orbit sets. Let \(S_1,S_2\) be maximal and put
\[
\lambda_i=\rho(S_i),\qquad N_i=\ker \lambda_i,\qquad V_i=V_{S_i}\subseteq L.
\]
Assume \(V_1\) and \(V_2\) are in the same \(G(L)\)-orbit. By
Lemma \(\mathrm{lem{:}shears\text{-}and\text{-}quotient\text{-}action}\), an
element of \(Z_{G_0}(X_0)\) lifts the corresponding isometry of \(L\), so
after replacing \(S_2\) by a \(\Gamma\)-conjugate we may assume
\[
V_1=V_2=:V.
\]

Now \(N_1\) and \(N_2\) are both lifts of the same subspace \(V\subseteq L\).
Since they are transverse to \(R\), there exist unique linear maps
\(\tau_i:V\to R\) such that
\[
N_i=\{\,v+\tau_i(v):v\in V\,\}\qquad(i=1,2).
\]
Set \(a:L\to R\) to be any extension of \(\tau_2-\tau_1:V\to R\). By
Lemma \(\mathrm{lem{:}shears\text{-}and\text{-}quotient\text{-}action}\),
there is \(u_a\in Z_{G_0}(X_0)\) acting on \(K=L\oplus R\) by
\[
u_a(\ell+r)=\ell+r+a(\ell).
\]
For \(v+\tau_1(v)\in N_1\),
\[
u_a(v+\tau_1(v))
=v+\tau_1(v)+a(v)
=v+\tau_2(v)\in N_2,
\]
so \(u_a(N_1)=N_2\). Replacing \(S_1\) by the corresponding
\(\Gamma\)-conjugate, we may therefore assume
\[
N_1=N_2=:N.
\]

Once the kernel is fixed, \(\operatorname{GL}(E')\) is transitive on the
surjective maps \(K\to E\) with kernel \(N\): indeed such a map is the same
thing as an isomorphism \(K/N\xrightarrow{\sim}E\), and
\(\operatorname{GL}(E')\) acts through the full linear group of \(E\). Hence
\(\lambda_1\) and \(\lambda_2\) are in the same \(\Gamma\)-orbit.

We have shown that two maximal points lie in the same \(\Gamma\)-orbit if and
only if their associated subspaces \(V_S\) lie in the same \(G(K/R)\)-orbit.
This proves (2).


# theorem thm:maximal-rank-slice-orbits

## statement
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

Then:

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

## proof
Part (1) is Proposition \(\mathrm{prop{:}openness\text{-}density}\).

Part (2) is Proposition \(\mathrm{prop{:}large\text{-}E}\).

Part (3) is Proposition \(\mathrm{prop{:}small\text{-}E}\).
