# Appendix: the orbit calculation used in Proposition 10.5

## Setting

We isolate the orbit calculation used in Proposition 10.5. There the relevant signatures are
$$
\mathsf{s}'=(\star',p',q'),\qquad
\mathsf{s}''=(\star',p'+\kappa,q'+\kappa),\qquad
\mathsf{s}_0=(\dot\star,\kappa,\kappa),
$$
and the calculation is applied with
$$
G_0=G_{\mathsf{s}'},\qquad G=G_{\mathsf{s}''},\qquad P=P_{\mathsf{s}'',\mathsf{s}_0},
$$
whose Levi factor contains $G_0$. The calculation below explains the induced orbit
$$
\operatorname{Ind}_P^G(\mathcal O_0)=\overline{G\cdot(\mathcal O_0+\mathfrak u)}
$$
and the multiplicity with which its open $G$-orbits occur. This is the orbit-theoretic input behind the ``direct computations'' in Proposition 10.5.

Let $\mathbb D$ be either $F$ or a quaternion division algebra over $F$, with its standard involution. All spaces are right $\mathbb D$-modules and all maps are right $\mathbb D$-linear. Hermitian forms are linear in the first variable. Fix $\epsilon\in\{\pm1\}$.

Let $(V_0,\langle\ ,\ \rangle_0)$ be a non-degenerate $\epsilon$-Hermitian $\mathbb D$-space, let $G_0$ be its isometry group, and let $X_0\in\mathfrak g_0=\operatorname{Lie}(G_0)$ be nilpotent. Put
$$
\mathcal O_0=G_0\cdot X_0,
\qquad
c=\dim_{\mathbb D}\ker X_0.
$$
Let $E,E'$ be $r$-dimensional right $\mathbb D$-modules with a perfect pairing $\lambda:E\times E'\to\mathbb D$, and put
$$
V=E\oplus V_0\oplus E'
$$
with the standard hyperbolic extension of $\langle\ ,\ \rangle_0$ determined by $\lambda$. Let $G$ be the isometry group of $V$. Let $P$ be the parabolic stabilizing $E$, and let $\mathfrak u$ be the Lie algebra of its unipotent radical.

In Proposition 10.5 the inducing isotropic block has size
$$
r=\kappa,
$$
by the definitions of $\kappa$, $\mathsf{s}''$ and $\mathsf{s}_0$ in Section~\ref{subsec:gdescent}.  We will need two induced-orbit calculations.  They are both stated for an arbitrary nilpotent orbit
$$
\mathcal O_0=G_0\cdot X_0,
\qquad
c=\dim_{\mathbb D}\ker X_0=\mathbf c_1(\mathcal O_0).
$$
The first calculation is the general one, under the numerical condition
$$
\kappa\ge c.
$$
The second calculation is the equal-rank strict-column case
$$
\kappa=c
\qquad\text{and}\qquad
\mathbf c_1(\mathcal O_0)>\mathbf c_2(\mathcal O_0).
$$
The second case is a specialization of the first at the level of the linear normal form, but it should be stated separately because this is the form in which it is used in Proposition 10.5 after the relevant signed Young diagram has been modified.

## First induced-orbit calculation: $\kappa\ge \dim\ker X_0$

Assume
$$
\kappa\ge c=\dim_{\mathbb D}\ker X_0,
$$
and put
$$
l=\kappa-c.
$$
In this calculation $E$ and $E'$ have dimension $\kappa$.

Choose
$$
V_0=V_+\oplus\operatorname{Im}X_0,
$$
and decompositions
$$
E=L_1\oplus L_0,
\qquad
E'=L'_1\oplus L'_0,
$$
with
$$
\dim_{\mathbb D} L_1=\dim_{\mathbb D} L'_1=c,
\qquad
\dim_{\mathbb D} L_0=\dim_{\mathbb D} L'_0=l,
$$
such that $\lambda$ pairs $L_i$ perfectly with $L'_i$ and annihilates $L_i\times L'_j$ for $i\ne j$.

For an isomorphism $S:L'_1\xrightarrow{\sim}V_+$ define $S^\vee:V_0\to L_1$ by
$$
\lambda(S^\vee v,a')=-\langle v,Sa'\rangle_0.
$$
Define
$$
\mathscr T=\{T:L'_0\to L_0:\lambda(Tu,v)+\epsilon\overline{\lambda(Tv,u)}=0\},
\qquad
B_T(u,v)=\lambda(Tu,v).
$$
Thus $B_T$ is $(-\epsilon)$-Hermitian. Let $\mathscr T^\circ$ be the maximal-rank locus. Equivalently,
$$
\operatorname{rank}_{\mathbb D}T=
\begin{cases}
l-1,&\mathbb D=F,\ \bar{\ }=\mathrm{id},\ \epsilon=+1,\ l\text{ odd},\\
l,&\text{otherwise}.
\end{cases}
$$
For $T\in\mathscr T$ set
$$
X_{S,T}(e+v+a'+b')=(S^\vee v+Tb')+(X_0v+Sa').
$$

### Statement

With the above notation and the assumption $\kappa\ge c$:

1. $X_{S,T}\in X_0+\mathfrak u$ for every $T\in\mathscr T$.
2. The open induced $G$-orbits in $\operatorname{Ind}_P^G(\mathcal O_0)$ are exactly
   $$
   G\cdot X_{S,T},\qquad T\in\mathscr T^\circ.
   $$
3. The orbit is independent of $S$, and
   $$
   G\cdot X_{S,T_1}=G\cdot X_{S,T_2}
   \quad\Longleftrightarrow\quad
   (L'_0,B_{T_1})\cong(L'_0,B_{T_2}).
   $$
4. For $T\in\mathscr T^\circ$,
   $$
   m(G\cdot X_{S,T},P)=
   \begin{cases}
   1,&B_T\text{ is non-degenerate},\\
   2,&B_T\text{ has one-dimensional }\mathbb D\text{-radical}.
   \end{cases}
   $$
   The second case occurs exactly in the split alternating odd case:
   $$
   \mathbb D=F,
   \qquad
   \bar{\ }=\mathrm{id},
   \qquad
   \epsilon=+1,
   \qquad
   l\text{ odd}.
   $$



## Second induced-orbit calculation: $\kappa=\dim\ker X_0$ and $\mathbf c_1(\mathcal O_0)>\mathbf c_2(\mathcal O_0)$

Assume
$$
\kappa=c=\dim_{\mathbb D}\ker X_0
\qquad\text{and}\qquad
\mathbf c_1(\mathcal O_0)>\mathbf c_2(\mathcal O_0).
$$
Then $l=0$, so $L_0=L'_0=0$ and there is no residual form $B_T$.  Equivalently, $\mathscr T=\{0\}$.  For an isomorphism $S:E'\xrightarrow{\sim}V_+$, set
$$
X_S(e+v+a')=S^\vee v+X_0v+Sa'.
$$
Then the induced set
$$
\operatorname{Ind}_P^G(\mathcal O_0)=\overline{G\cdot(\mathcal O_0+\mathfrak u)}
$$
has a single open $G$-orbit, namely
$$
G\cdot X_S.
$$
This orbit is independent of $S$, and its induction multiplicity is
$$
m(G\cdot X_S,P)=1.
$$
In terms of Young diagrams, this is the case where two columns of length $\kappa$ are inserted in front of the diagram of $\mathcal O_0$.  Since $\mathbf c_1(\mathcal O_0)=\kappa$ and $\mathbf c_1(\mathcal O_0)>\mathbf c_2(\mathcal O_0)$, the beginning of the column sequence is
$$
(\kappa,\kappa,\kappa,\mathbf c_2(\mathcal O_0),\mathbf c_3(\mathcal O_0),\ldots).
$$
This is the equal-rank strict-column calculation that will be used separately from the general $\kappa\ge c$ case.

In signed Young diagram language, the isometry class of $B_T$ is the extra datum appearing in the induction formula for $\operatorname{Ind}_{\mathsf{s}'}^{\mathsf{s}''}$: signatures give the sums over $(a,b)$, quaternionic dimensions give the even restrictions, and the split alternating odd case gives the coefficient $2$. In the second calculation $l=0$, so there is no residual form and hence only one open orbit. The matching with the $\Lambda$-terms in the exceptional branch will be discussed separately.

## Proof sketch for the induced-orbit calculations

**Step 1: the fixed part of the calculation.** Since $X_0$ is skew-adjoint,
$$
(\operatorname{Im}X_0)^\perp=\ker X_0.
$$
Thus $V_+\simeq V_0/\operatorname{Im}X_0$ pairs perfectly with $\ker X_0$, and
$$
S^\vee|_{\ker X_0}:\ker X_0\xrightarrow{\sim}L_1.
$$
This is the reason the $L'_1$-part can be normalized uniquely.

**Step 2: write the slice $X_0+\mathfrak u$ in blocks.** Every element of $X_0+\mathfrak u$ has a unique form
$$
X_{C,B}=X_0+
\begin{bmatrix}0&C^\vee&B\\0&0&C\\0&0&0\end{bmatrix},
$$
where $C:E'\to V_0$ and
$$
\lambda(Bu,v)+\epsilon\overline{\lambda(Bv,u)}=0.
$$
The special choice $C|_{L'_1}=S$, $C|_{L'_0}=0$, $B|_{L'_1}=0$, $B|_{L'_0}=T$ gives $X_{S,T}$.

**Step 3: normalize the $C$-block.** For $D:E'\to V_0$ put
$$
u_D=\begin{bmatrix}1&D^\vee&\frac12D^\vee D\\0&1&D\\0&0&1\end{bmatrix}\in P.
$$
Then
$$
u_DX_{C,B}u_D^{-1}
=X_{C-X_0D,\,B+D^\vee C-C^\vee D-D^\vee X_0D}. \tag{1}
$$
Let $\bar C:E'\to V_0/\operatorname{Im}X_0\simeq V_+$ be the quotient of $C$. On the open dense locus $\operatorname{rank}\bar C=c$, the Levi factor of $P$ lets us arrange
$$
\ker\bar C=L'_0,
\qquad
\bar C|_{L'_1}=S.
$$
Then $C-C_0$ takes values in $\operatorname{Im}X_0$, where $C_0|_{L'_1}=S$ and $C_0|_{L'_0}=0$. Formula (1) makes $C=C_0$.

**Step 4: reduce the $B$-block to one residual form.** Keeping $C=C_0$, use (1) with $D$ taking values in $\ker X_0$. By the perfect pairing $V_+\times\ker X_0$, one kills all $B$-blocks involving $L'_1$. The only remaining block is
$$
T:L'_0\to L_0,
$$
and the skew-Hermitian condition on $B$ says precisely $T\in\mathscr T$.

For normalized elements, the unipotent part no longer changes this block. The remaining Levi action is
$$
T\longmapsto (h^{-1})^\vee T h,
\qquad h\in\operatorname{GL}_{\mathbb D}(L'_0),
$$
which is exactly change of coordinates for $B_T$. Hence the open $P$-orbits in the slice are classified by the isometry classes of $B_T$ with $T\in\mathscr T^\circ$.

**Step 5: pass to the induced $G$-orbits.** Since
$$
\mathcal O_0+\mathfrak u=\iota(G_0)\cdot(X_0+\mathfrak u),
$$
the induced set is $\overline{G\cdot(X_0+\mathfrak u)}$. The locus $\operatorname{rank}\bar C=c$ is open dense, and within it the maximal-rank condition is $T\in\mathscr T^\circ$. Therefore the open induced $G$-orbits are exactly the orbits $G\cdot X_{S,T}$ with $T\in\mathscr T^\circ$, modulo the isometry relation on $B_T$.

This is the orbit calculation used in Proposition 10.5: after translating the possible isometry classes of $B_T$ into signed Young diagrams, one obtains precisely the summands in the definition of $\operatorname{Ind}_{\mathsf{s}'}^{\mathsf{s}''}$.

**Step 6: the multiplicity.** Directly from the definition of $X_{S,T}$,
$$
\ker X_{S,T}=E\oplus\ker T,
\qquad
\operatorname{Im}X_{S,T}=(L_1\oplus\operatorname{Im}T)\oplus V_0.
$$
If $B_T$ is non-degenerate, then $\ker X_{S,T}=E$, so $Z_G(X_{S,T})\subset P$ and the multiplicity is $1$.

In the split alternating odd case, $F_0:=\ker T$ is a line. Choose a complement $M$ of $F_0$ in $L'_0$ and set $\ell=M^\perp\subset L_0$. Then
$$
\ker X_{S,T}/(\ker X_{S,T}\cap\operatorname{Im}X_{S,T})
\simeq \ell\oplus F_0
$$
is a hyperbolic plane. Its two isotropic lines give two maximal isotropic subspaces, $E$ and
$$
E^\sharp=L_1\oplus\operatorname{Im}T\oplus F_0.
$$
The centralizer permutes these two subspaces. The kernel of this action is $Z_G(X_{S,T})\cap P$, and the swap of the two isotropic lines gives an element of $Z_G(X_{S,T})\setminus P$. Hence the index is $2$, giving multiplicity $2$.

When $l=0$, this proof gives the second calculation: $T=0$, the open orbit is unique, and the multiplicity is $1$. $\square$
