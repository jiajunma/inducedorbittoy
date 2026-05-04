# Short-Kappa Branch of Maximal-Parabolic Induction - Computation Problem

Let
$$
F=\mathbb R.
$$
Let
$$
\epsilon\in\{+1,-1\}.
$$

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
and
$$
\mathfrak g_0:=\{Y\in\mathrm{End}_F(V_0):
\langle Yv,w\rangle_0+\langle v,Yw\rangle_0=0\ \forall v,w\in V_0\}.
$$

Let $X_0\in\mathfrak g_0$ be nilpotent, and let
$$
\mathcal O_0:=G_0\cdot X_0.
$$
Put
$$
c_1:=\dim_F\ker X_0,
\qquad
c_2:=\dim_F(\ker X_0\cap\operatorname{Im}X_0).
$$
Equivalently,
$$
c_2=\dim_F(\ker X_0^2/\ker X_0).
$$

Fix an integer $\kappa$, and let $E,E'$ be $\kappa$-dimensional $F$-vector spaces with a non-degenerate pairing
$$
\lambda:E\times E'\to F.
$$
Assume
$$
\dim_F\ker X_0>\dim_F E=\kappa\ge \dim_F(\ker X_0^2/\ker X_0).
$$
Equivalently,
$$
c_2\le \kappa<c_1.
$$
Put
$$
d:=c_1-\kappa.
$$
Set
$$
V:=E\oplus V_0\oplus E',
$$
and define a bilinear form on $V$ by
$$
\langle e+v+e',\ f+w+f'\rangle
:=\lambda(e,f')+\epsilon\lambda(f,e')+\langle v,w\rangle_0.
$$
Let
$$
G:=\{g\in\mathrm{GL}(V):\langle gx,gy\rangle=\langle x,y\rangle\},
$$
and
$$
\mathfrak g:=\{Y\in\mathrm{End}_F(V):
\langle Yx,y\rangle+\langle x,Yy\rangle=0\ \forall x,y\in V\}.
$$

Let
$$
P:=\{g\in G:g(E)=E\}.
$$
Since $E^\perp=E\oplus V_0$, define
$$
\mathfrak u:=\{Y\in\mathfrak g:
Y(E)=0,\quad
Y(E^\perp)\subseteq E,\quad
Y(V)\subseteq E^\perp
\}.
$$
Regard $\mathcal O_0$ as a subset of $\mathfrak g$ by letting each operator in $\mathcal O_0$ act on the $V_0$-summand and act as $0$ on $E\oplus E'$.

Define the induced set
$$
\operatorname{Ind}_P^G(\mathcal O_0)
:=\overline{G\cdot(\mathcal O_0+\mathfrak u)}\subseteq\mathfrak g,
$$
where the closure is taken in the usual real topology on the finite-dimensional real vector space $\mathfrak g$.

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
For a subgroup $H$ of $G$, let $H^\circ_{\mathrm{top}}$ denote its identity component for the usual real topology, and set
$$
\pi_0(H):=H/H^\circ_{\mathrm{top}}.
$$
For $x\in\mathcal O_0+\mathfrak u$, define the multiplicity by
$$
m(G\cdot x,P):=
\frac{|\pi_0(Z_G(x))|}{|\pi_0(Z_G(x)\cap P)|}.
$$

## The kernel quotient

Since $X_0$ is skew-adjoint, one has
$$
(\operatorname{Im}X_0)^\perp=\ker X_0.
$$
Therefore the restriction of $\langle\cdot,\cdot\rangle_0$ to $\ker X_0$ has radical
$$
\ker X_0\cap\operatorname{Im}X_0.
$$
Define the kernel quotient
$$
K_{X_0}:=\ker X_0/(\ker X_0\cap\operatorname{Im}X_0).
$$
The restriction of $\langle\cdot,\cdot\rangle_0$ to $\ker X_0$ descends to a bilinear form on $K_{X_0}$, denoted by
$$
\langle\cdot,\cdot\rangle_K.
$$
Its dimension is
$$
\dim_F K_{X_0}=c_1-c_2.
$$
The assumption $c_2\le\kappa<c_1$ is equivalent to
$$
0<d\le \dim_F K_{X_0}.
$$

Let $\mathscr A$ be the set of $d$-dimensional subspaces
$$
A\subset K_{X_0}.
$$
For $A\in\mathscr A$, write $\operatorname{rad}(A)$ for the radical of the restricted form $\langle\cdot,\cdot\rangle_K|_A$.
Let $\mathscr A^{\mathrm{mr}}\subseteq\mathscr A$ be the maximal-rank locus: this is the set of all $A$ for which the restricted form on $A$ has the largest possible rank among $d$-dimensional subspaces of $K_{X_0}$.

Two elements $A_1,A_2\in\mathscr A^{\mathrm{mr}}$ are called isometric inside $K_{X_0}$ if there is an isometry
$$
h\in\operatorname{Isom}(K_{X_0},\langle\cdot,\cdot\rangle_K)
$$
such that
$$
h(A_1)=A_2.
$$

## The slice $X_0+\mathfrak u$

With respect to
$$
V=E\oplus V_0\oplus E',
$$
every element of $X_0+\mathfrak u$ has the form
$$
X_{C,B}:=
\begin{bmatrix}
0&C^\vee&B\\
0&X_0&C\\
0&0&0
\end{bmatrix}.
$$
Here
$$
C:E'\to V_0,
\qquad
B:E'\to E,
$$
and $C^\vee:V_0\to E$ is determined by
$$
\lambda(C^\vee v,a')=-\langle v,Ca'\rangle_0
\qquad \forall v\in V_0,\ a'\in E'.
$$
The condition on $B$ is
$$
\lambda(Ba',b')+\epsilon\lambda(Bb',a')=0
\qquad \forall a',b'\in E'.
$$

## Problem

Compute the maximal $G$-orbits in
$$
\operatorname{Ind}_P^G(\mathcal O_0)
$$
and compute their multiplicities with respect to the maximal parabolic subgroup $P$.

The final answer should give a parametrization of the maximal induced orbits in terms of the isometry classes of the $d$-dimensional forms obtained from subspaces of
$$
K_{X_0}=\ker X_0/(\ker X_0\cap\operatorname{Im}X_0).
$$
For each such orbit $\mathcal O$, compute
$$
m(\mathcal O,P)
=
\frac{|\pi_0(Z_G(x))|}
{|\pi_0(Z_G(x)\cap P)|},
$$
where $x\in\mathcal O\cap(\mathcal O_0+\mathfrak u)$ is any representative used in the calculation.

Give a self-contained proof from the maximal parabolic action on the slice $X_0+\mathfrak u$.  Do not use any diagram parametrization.
