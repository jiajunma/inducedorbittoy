# Appendix: the maximal-parabolic orbit calculation used in Proposition 10.5

## Setting

This appendix spells out the orbit calculation used in Proposition 10.5.  The parabolic there is the maximal parabolic subgroup
$$
P=P_{\mathsf{s}'',\mathsf{s}_0}\subset G_{\mathsf{s}''}
$$
whose Levi factor contains $G_{\mathsf{s}'}$.  The isotropic block used for induction has size $\kappa$, where $\kappa$ is defined in Section~\ref{subsec:gdescent}.

Let $(V_0,\langle\ ,\ \rangle_0)$ be a non-degenerate $\epsilon$-Hermitian $\mathbb D$-space, let $G_0$ be its isometry group, and let
$$
X_0\in \mathfrak g_0=\operatorname{Lie}(G_0)
$$
be nilpotent.  Put
$$
\mathcal O_0=G_0\cdot X_0,
\qquad
c=\dim_{\mathbb D}\ker X_0.
$$
Thus $c=\mathbf c_1(\mathcal O_0)$.

Let $E,E'$ be $\kappa$-dimensional right $\mathbb D$-modules with a perfect pairing
$$
\lambda:E\times E'\to \mathbb D.
$$
Set
$$
V=E\oplus V_0\oplus E'
$$
with the standard hyperbolic extension of $\langle\ ,\ \rangle_0$ determined by $\lambda$.  Let $G$ be the isometry group of $V$.  Let $P$ be the maximal parabolic stabilizing $E$, and let $\mathfrak u$ be the Lie algebra of its unipotent radical.

The induced orbit is
$$
\operatorname{Ind}_P^G(\mathcal O_0)
=\overline{G\cdot(\mathcal O_0+\mathfrak u)}.
$$
Since $G_0$ is contained in the Levi factor of $P$,
$$
\mathcal O_0+\mathfrak u=G_0\cdot(X_0+\mathfrak u).
$$
So the orbit calculation reduces to the slice $X_0+\mathfrak u$.

## The slice $X_0+\mathfrak u$

With respect to
$$
V=E\oplus V_0\oplus E',
$$
every element of $X_0+\mathfrak u$ has the form
$$
X_0+Y_{C,B},
\qquad
Y_{C,B}=
\begin{bmatrix}
0&C^\vee&B\\
0&0&C\\
0&0&0
\end{bmatrix}.                                      \tag{1}
$$
Here
$$
C:E'\to V_0,
\qquad
B:E'\to E,
$$
and $C^\vee:V_0\to E$ is determined by
$$
\lambda(C^\vee v,a')=-\langle v,Ca'\rangle_0.
$$
The condition on $B$ is
$$
\lambda(Ba',b')+\epsilon\overline{\lambda(Bb',a')}=0
\qquad(a',b'\in E').                                  \tag{2}
$$

The open part of the induced orbit is controlled by the quotient of $C$ modulo $\operatorname{Im}X_0$.  Since $X_0$ is skew-adjoint,
$$
(\operatorname{Im}X_0)^\perp=\ker X_0,
$$
so
$$
\dim_{\mathbb D}(V_0/\operatorname{Im}X_0)=c.
$$
Let
$$
\bar C:E'\to V_0/\operatorname{Im}X_0
$$
be the quotient map.  The open condition is
$$
\operatorname{rank}_{\mathbb D}\bar C=c.              \tag{3}
$$
Thus this normal-form calculation requires
$$
\kappa=\dim E'\ge c=\dim\ker X_0.                    \tag{4}
$$

## Normal form $X_0+Y_{S,T}$

Assume $\kappa\ge c$, and put
$$
l=\kappa-c.
$$
Choose
$$
V_0=V_+\oplus \operatorname{Im}X_0,
\qquad
\dim V_+=c.
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
such that $\lambda$ pairs $L_i$ perfectly with $L'_i$ and kills $L_i\times L'_j$ for $i\ne j$.

On the open locus (3), the Levi factor of $P$ lets us arrange
$$
\ker \bar C=L'_0,
\qquad
\bar C|_{L'_1}:L'_1\xrightarrow{\sim}V_0/\operatorname{Im}X_0.
$$
Then the unipotent radical lets us remove the part of $C$ lying in $\operatorname{Im}X_0$.  Hence we may assume that the $C$-block is
$$
C=C_S,
$$
where
$$
S:L'_1\xrightarrow{\sim}V_+,
\qquad
C_S|_{L'_1}=S,
\qquad
C_S|_{L'_0}=0.                                      \tag{5}
$$
This is the condition on $S$: it must identify $L'_1$ with the quotient direction $V_0/\operatorname{Im}X_0$, represented by the chosen complement $V_+$.

For such $S$, define $S^\vee:V_0\to L_1$ by
$$
\lambda(S^\vee v,a')=-\langle v,Sa'\rangle_0
\qquad(a'\in L'_1).
$$
The only remaining part of the $B$-block is a map
$$
T:L'_0\to L_0
$$
satisfying
$$
\lambda(Tu,v)+\epsilon\overline{\lambda(Tv,u)}=0
\qquad(u,v\in L'_0).                                  \tag{6}
$$
Equivalently,
$$
B_T(u,v):=\lambda(Tu,v)
$$
is a $(-\epsilon)$-Hermitian form on $L'_0$.

The normalized element is
$$
X_0+Y_{S,T},                                           \tag{7}
$$
where explicitly
$$
(X_0+Y_{S,T})(e+v+a'+b')
=(S^\vee v+Tb')+(X_0v+Sa')
$$
for
$$
e\in E,
\quad v\in V_0,
\quad a'\in L'_1,
\quad b'\in L'_0.
$$

## Open induced orbits

Let $\mathscr T$ be the space of all $T:L'_0\to L_0$ satisfying (6), and let $\mathscr T^\circ$ be the maximal-rank locus:
$$
\operatorname{rank}_{\mathbb D}T=
\begin{cases}
l-1,&\mathbb D=F,\ \bar{\ }=\mathrm{id},\ \epsilon=+1,\ l\text{ odd},\\
l,&\text{otherwise}.
\end{cases}
$$
Then the open $G$-orbits in $\operatorname{Ind}_P^G(\mathcal O_0)$ are exactly
$$
G\cdot(X_0+Y_{S,T}),
\qquad
T\in \mathscr T^\circ.                                \tag{8}
$$
The orbit is independent of $S$, and
$$
G\cdot(X_0+Y_{S,T_1})=G\cdot(X_0+Y_{S,T_2})
$$
if and only if
$$
(L'_0,B_{T_1})\cong (L'_0,B_{T_2}).
$$
The multiplicity is
$$
m(G\cdot(X_0+Y_{S,T}),P)=
\begin{cases}
1,&B_T\text{ is non-degenerate},\\
2,&B_T\text{ has one-dimensional }\mathbb D\text{-radical}.
\end{cases}                                           \tag{9}
$$
The second case occurs exactly in the split alternating odd case
$$
\mathbb D=F,
\qquad
\bar{\ }=\mathrm{id},
\qquad
\epsilon=+1,
\qquad
l\text{ odd}.
$$

## Equal-rank strict-column case

The second induced-orbit calculation needed later is the special case
$$
\kappa=c=\dim_{\mathbb D}\ker X_0
\qquad\text{and}\qquad
\mathbf c_1(\mathcal O_0)>\mathbf c_2(\mathcal O_0).  \tag{10}
$$
Then $l=0$, so $L_0=L'_0=0$ and $\mathscr T=\{0\}$.  There is no residual form $B_T$.  The normal form becomes
$$
X_0+Y_S,
$$
where $S:E'\xrightarrow{\sim}V_+$ and
$$
(X_0+Y_S)(e+v+a')=S^\vee v+X_0v+Sa'.                  \tag{11}
$$
Thus there is a single open $G$-orbit:
$$
G\cdot(X_0+Y_S),
$$
and its multiplicity is $1$.

In Young diagram language, this is the $t_0=0$ branch of Section~\ref{subsec:induced}: two columns of length $\kappa$ are inserted before the diagram of $\mathcal O_0$.  Since $\mathbf c_1(\mathcal O_0)=\kappa$ and $\mathbf c_1(\mathcal O_0)>\mathbf c_2(\mathcal O_0)$, the beginning of the resulting column sequence is
$$
(\kappa,\kappa,\kappa,\mathbf c_2(\mathcal O_0),\mathbf c_3(\mathcal O_0),\ldots).
$$

## Proof sketch

The block expression (1) is the Lie algebra of the unipotent radical of the maximal parabolic stabilizing $E$; (2) is the skew-adjointness condition.

The key open condition is (3).  Once $\bar C$ has rank $c$, the Levi factor puts $\ker \bar C$ in the fixed position $L'_0$ and identifies the quotient with $L'_1$.  The unipotent radical then removes the part of $C$ lying in $\operatorname{Im}X_0$.  Concretely, for $D:E'\to V_0$,
$$
u_D=
\begin{bmatrix}
1&D^\vee&\frac12D^\vee D\\
0&1&D\\
0&0&1
\end{bmatrix}\in P
$$
and
$$
u_D(X_0+Y_{C,B})u_D^{-1}
=X_0+Y_{C-X_0D,\,B+D^\vee C-C^\vee D-D^\vee X_0D}.    \tag{12}
$$
This is the formula which changes $C$ to $C_S$.

After $C=C_S$ is fixed, the same formula with $D$ taking values in $\ker X_0$ kills all $B$-blocks involving $L'_1$.  The only remaining part is $T:L'_0\to L_0$, subject to (6).  The remaining Levi action on $T$ is exactly change of coordinates of the form $B_T$.  Therefore the open induced orbits are classified by the isometry classes of the maximal-rank forms $B_T$, and the multiplicity is given by (9).  When $l=0$, there is no $T$, giving the equal-rank calculation immediately.  $\square$
