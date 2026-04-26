# Induced Orbit Representatives and Multiplicity — Self-Contained Problem

Let $F$ be either $\mathbb R$ or a non-archimedean local field of characteristic $0$. Let $\epsilon\in\{+1,-1\}$.

## Setup

Let $(V_0,\langle\cdot,\cdot\rangle_0)$ be a finite-dimensional $F$-vector space with a non-degenerate bilinear form satisfying
$$
\langle v,w\rangle_0=\epsilon\langle w,v\rangle_0
\qquad \forall v,w\in V_0.
$$
Set
$$
G_0:=\{g\in \mathrm{GL}(V_0):\langle gv,gw\rangle_0=\langle v,w\rangle_0\},
$$
$$
\mathfrak g_0:=\{Y\in\mathrm{End}_F(V_0):
\langle Yv,w\rangle_0+\langle v,Yw\rangle_0=0\ \forall v,w\in V_0\}.
$$

Let $X_0\in\mathfrak g_0$ be nilpotent, and let
$$
\mathcal O_0:=G_0\cdot X_0,
$$
where $G_0$ acts on $\mathfrak g_0$ by conjugation.
Put
$$
c:=\dim_F\ker X_0.
$$
Fix an integer $r\ge c$ and set $l:=r-c$.

Let $E,E'$ be $r$-dimensional $F$-vector spaces with a non-degenerate pairing
$$
\lambda:E\times E'\to F.
$$
Set
$$
V:=E\oplus V_0\oplus E'
$$
and define a bilinear form on $V$ by
$$
\langle e+v+e',\ f+w+f'\rangle
:=\lambda(e,f')+\epsilon \lambda(f,e')+\langle v,w\rangle_0.
$$
Let
$$
G:=\{g\in\mathrm{GL}(V):\langle gx,gy\rangle=\langle x,y\rangle\},
$$
$$
\mathfrak g:=\{Y\in\mathrm{End}_F(V):
\langle Yx,y\rangle+\langle x,Yy\rangle=0\ \forall x,y\in V\}.
$$

The group $G$ acts on $\mathfrak g$ by conjugation. Let
$$
P:=\{g\in G:g(E)=E\}.
$$
Since $E^\perp=E\oplus V_0$, define
$$
\mathfrak u:=\{Y\in\mathfrak g:
Y(E)=0,
Y(E^\perp)\subseteq E,
Y(V)\subseteq E^\perp
\}.
$$
Regard $\mathcal O_0$ as a subset of $\mathfrak g$ by letting each operator in $\mathcal O_0$ act on the $V_0$-summand and act as $0$ on $E\oplus E'$.

Define the induced set
$$
\operatorname{Ind}_P^G(\mathcal O_0)
:=\overline{G\cdot(\mathcal O_0+\mathfrak u)}\subseteq\mathfrak g.
$$
Here the closure is taken in the $F$-analytic topology on the finite-dimensional $F$-vector space $\mathfrak g$.

A $G$-orbit $\mathcal O\subseteq\operatorname{Ind}_P^G(\mathcal O_0)$ is called induced from $\mathcal O_0$ via $P$ if it is maximal, among the $G$-orbits contained in $\operatorname{Ind}_P^G(\mathcal O_0)$, for the closure order
$$
\mathcal O_1\preceq \mathcal O_2
\iff
\mathcal O_1\subseteq\overline{\mathcal O_2}.
$$

For $x\in\mathfrak g$, write
$$
Z_G(x):=\{g\in G:gxg^{-1}=x\}.
$$
For an algebraic subgroup $H$ of $G$, let $H^\circ$ denote its algebraic identity component, and set
$$
\pi_0(H):=H/H^\circ.
$$
For $x\in\mathcal O_0+\mathfrak u$, define the multiplicity by
$$
m(G\cdot x,P):=
\frac{|\pi_0(Z_G(x))|}{|\pi_0(Z_G(x)\cap P)|}.
$$
In the problem below this is only used for $x=X_{S,T}$.

## Construction of the representatives

Choose a subspace $V_+\subseteq V_0$ such that
$$
V_0=V_+\oplus\operatorname{Im}X_0.
$$
Choose decompositions
$$
E=L_1\oplus L_0,
\qquad
E'=L'_1\oplus L'_0,
$$
with
$$
\dim L_1=\dim L'_1=c,
\qquad
\dim L_0=\dim L'_0=l,
$$
such that
$$
\lambda(L_i,L'_j)=0\quad(i\neq j),
$$
and such that $\lambda$ restricts to non-degenerate pairings
$$
L_1\times L'_1\to F,
\qquad
L_0\times L'_0\to F.
$$
For each isomorphism
$$
S:L'_1\xrightarrow{\sim}V_+,
$$
define $S^\vee:V_0\to L_1$ to be the unique linear map satisfying
$$
\lambda(S^\vee v,a')=-\langle v,Sa'\rangle_0
\qquad \forall v\in V_0,
\forall a'\in L'_1.
$$

Define
$$
\mathscr T:=\{T\in\operatorname{Hom}_F(L'_0,L_0):
\lambda(Tu,v)+\epsilon \lambda(Tv,u)=0\ \forall u,v\in L'_0\}.
$$
For $T\in\mathscr T$, define a bilinear form on $L'_0$ by
$$
B_T(u,v):=\lambda(Tu,v).
$$
Then $B_T$ has parity $-\epsilon$, i.e.
$$
B_T(v,u)=-\epsilon B_T(u,v).
$$
Let $\mathscr T^\circ\subseteq\mathscr T$ be the subset of maps of maximal possible rank. Equivalently,
$$
\operatorname{rank}T=
\begin{cases}
l,&\epsilon=-1,\\
l,&\epsilon=+1\text{ and }l\text{ is even},\\
l-1,&\epsilon=+1\text{ and }l\text{ is odd}.
\end{cases}
$$

For an isomorphism $S:L'_1\xrightarrow{\sim}V_+$ and $T\in\mathscr T$, define $X_{S,T}:V\to V$ as follows. For
$$
e\in E,
\qquad
v\in V_0,
\qquad
a'\in L'_1,
\qquad
b'\in L'_0,
$$
set
$$
X_{S,T}(e+v+a'+b')
:=\bigl(S^\vee v+Tb'\bigr)+\bigl(X_0v+Sa'\bigr)+0
\in E\oplus V_0\oplus E'.
$$

## Problem

Prove the following statements.

1. For every isomorphism $S:L'_1\xrightarrow{\sim}V_+$ and every $T\in\mathscr T$,
   $$
   X_{S,T}\in X_0+\mathfrak u\subseteq\mathfrak g,
   $$
   where $X_0$ is regarded as an operator on $V$ by acting on $V_0$ and acting as $0$ on $E\oplus E'$.

2. The induced $G$-orbits in $\operatorname{Ind}_P^G(\mathcal O_0)$ are exactly the orbits
   $$
   G\cdot X_{S,T}
   \qquad (T\in\mathscr T^\circ),
   $$
   for any choice of isomorphism $S:L'_1\xrightarrow{\sim}V_+$.

3. The orbit $G\cdot X_{S,T}$ is independent of the choice of $S$. More precisely, for any two isomorphisms
   $$
   S_1,S_2:L'_1\xrightarrow{\sim}V_+
   $$
   and any $T_1,T_2\in\mathscr T^\circ$,
   $$
   G\cdot X_{S_1,T_1}=G\cdot X_{S_2,T_2}
   $$
   if and only if the bilinear spaces
   $$
   (L'_0,B_{T_1})
   \qquad\text{and}\qquad
   (L'_0,B_{T_2})
   $$
   are isometric, meaning that there exists $h\in\mathrm{GL}(L'_0)$ such that
   $$
   B_{T_2}(hu,hv)=B_{T_1}(u,v)
   \qquad \forall u,v\in L'_0.
   $$

4. For $S:L'_1\xrightarrow{\sim}V_+$ and $T\in\mathscr T^\circ$, compute
   $$
   m(G\cdot X_{S,T},P)
   =\frac{|\pi_0(Z_G(X_{S,T}))|}{|\pi_0(Z_G(X_{S,T})\cap P)|}.
   $$
   As part of the computation, prove that
   $$
   Z_G(X_{S,T})^\circ\subseteq Z_G(X_{S,T})\cap P,
   $$
   and hence that
   $$
   m(G\cdot X_{S,T},P)
   =[Z_G(X_{S,T}):Z_G(X_{S,T})\cap P],
   $$
   where the right-hand side is the ordinary index of the corresponding groups of $F$-points. The required answer is
   $$
   m(G\cdot X_{S,T},P)=
   \begin{cases}
   1,& B_T\text{ is non-degenerate},\\
   2,& \epsilon=+1\text{ and }l\text{ is odd}.
   \end{cases}
   $$
