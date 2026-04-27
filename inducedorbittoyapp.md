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

## Proof

We prove the assertions in the order in which they are used.

**Step 1: the fixed geometry of $X_0$.**  Since $X_0$ is skew-adjoint,
$$
(\operatorname{Im}X_0)^\perp=\ker X_0.                         \tag{12}
$$
Indeed, if $w\in\ker X_0$ and $y=X_0z$, then
$$
\langle w,y\rangle_0=\langle w,X_0z\rangle_0
=-\langle X_0w,z\rangle_0=0.
$$
Thus $\ker X_0\subseteq (\operatorname{Im}X_0)^\perp$, and equality follows by dimension.  Since
$$
V_0=V_+\oplus \operatorname{Im}X_0,
$$
the quotient map identifies $V_+$ with $V_0/\operatorname{Im}X_0$.  Moreover, (12) implies that the pairing
$$
V_+\times \ker X_0\longrightarrow \mathbb D
$$
is perfect.  Hence for every isomorphism $S:L'_1\xrightarrow{\sim}V_+$, the map
$$
S^\vee|_{\ker X_0}:\ker X_0\xrightarrow{\sim}L_1              \tag{13}
$$
is an isomorphism.

**Step 2: the block parametrization of $X_0+\mathfrak u$.**  Relative to
$$
V=E\oplus V_0\oplus E',
$$
an element of $\mathfrak u$ has the form
$$
Y=
\begin{bmatrix}
0&A&B\\
0&0&C\\
0&0&0
\end{bmatrix}.
$$
The skew-adjointness condition forces
$$
A=C^\vee,
$$
where
$$
\lambda(C^\vee v,a')=-\langle v,Ca'\rangle_0.
$$
The same condition on two vectors in $E'$ gives exactly (2):
$$
\lambda(Ba',b')+\epsilon\overline{\lambda(Bb',a')}=0.
$$
Therefore every element of $X_0+\mathfrak u$ is uniquely of the form $X_0+Y_{C,B}$ in (1).  In particular, the special choice
$$
C|_{L'_1}=S,
\qquad
C|_{L'_0}=0,
\qquad
B|_{L'_1}=0,
\qquad
B|_{L'_0}=T
$$
gives precisely $X_0+Y_{S,T}$.

**Step 3: the unipotent conjugation formula.**  For $D:E'\to V_0$, define
$$
u_D=
\begin{bmatrix}
1&D^\vee&\frac12D^\vee D\\
0&1&D\\
0&0&1
\end{bmatrix}\in P.
$$
The defining property of $D^\vee$ shows that the mixed terms cancel, and hence $u_D$ preserves the form.  A block multiplication gives
$$
u_D(X_0+Y_{C,B})u_D^{-1}
=X_0+Y_{C-X_0D,\,B+D^\vee C-C^\vee D-D^\vee X_0D}.        \tag{14}
$$
This is the main calculation.

**Step 4: normalizing the $C$-block.**  Let
$$
\bar C:E'\to V_0/\operatorname{Im}X_0
$$
be the quotient of $C$.  On the open locus
$$
\operatorname{rank}\bar C=c,
$$
the map $\bar C$ is surjective and $\ker\bar C$ has dimension $l=\kappa-c$.  Using the Levi factor of $P$, we may arrange
$$
\ker\bar C=L'_0,
\qquad
\bar C|_{L'_1}:L'_1\xrightarrow{\sim}V_0/\operatorname{Im}X_0.
$$
After identifying the quotient with the fixed complement $V_+$, this gives the required isomorphism
$$
S:L'_1\xrightarrow{\sim}V_+.
$$
Then $C-C_S$ takes values in $\operatorname{Im}X_0$.  Hence there is $D:E'\to V_0$ such that
$$
X_0D=C-C_S.
$$
Using (14), conjugation by $u_D$ replaces $C$ by
$$
C-X_0D=C_S.
$$
Thus every point of the open locus is $P$-conjugate to one with the normalized $C$-block (5).

**Step 5: reducing the $B$-block.**  Now keep $C=C_S$ fixed.  Write $B$ in blocks according to
$$
E'=L'_1\oplus L'_0,
\qquad
E=L_1\oplus L_0.
$$
We use (14) again, but now with $D$ taking values in $\ker X_0$; this keeps the $C$-block fixed because $X_0D=0$.

First take $D_0:L'_0\to \ker X_0$.  By the perfect pairing $V_+\times\ker X_0$, the map
$$
D_0\longmapsto D_0^\vee S
$$
identifies $\operatorname{Hom}(L'_0,\ker X_0)$ with the space of cross-blocks from $L'_1$ to $L_0$.  Hence we choose $D_0$ to kill the corresponding cross-block of $B$.  The relation (2) then kills the opposite cross-block as well.

Next take $D_1:L'_1\to\ker X_0$.  The remaining $L'_1\to L_1$ block defines a $(-\epsilon)$-Hermitian form on $L'_1$.  Again using the perfect pairing between $V_+$ and $\ker X_0$, we choose $D_1$ so that the correction
$$
D_1^\vee C_S-C_S^\vee D_1
$$
kills this block.  Therefore the only block left is
$$
T:L'_0\to L_0.
$$
The skew-adjointness relation (2) becomes exactly
$$
\lambda(Tu,v)+\epsilon\overline{\lambda(Tv,u)}=0,
$$
so $T\in\mathscr T$.  This proves the normal form $X_0+Y_{S,T}$.

The residual Levi action on $L'_0$ is the usual change of coordinates.  If $\gamma\in\operatorname{GL}_{\mathbb D}(L'_0)$ and the Levi acts on $L_0$ by $(\gamma^{-1})^\vee$, then
$$
T\longmapsto (\gamma^{-1})^\vee T\gamma.                  \tag{15}
$$
This is exactly the change of coordinates for the form
$$
B_T(u,v)=\lambda(Tu,v).
$$
Hence the residual $P$-orbits in the normalized slice are classified by the isometry classes of $(L'_0,B_T)$.

Conversely, suppose two normalized elements are $P$-conjugate.  Write the conjugating element as a unipotent part times a Levi part.  Formula (14) shows that the unipotent part cannot change the residual $L'_0\to L_0$ block: on $L'_0$, the correction terms either vanish because $C_S|_{L'_0}=0$ or land in $L_1$, not in $L_0$.  Therefore the residual block changes only by (15).  Thus two normalized elements are $P$-conjugate if and only if their residual forms are isometric.

**Step 6: passing from the slice to induced $G$-orbits.**  Since $G_0$ is contained in the Levi factor,
$$
\mathcal O_0+\mathfrak u=G_0\cdot(X_0+\mathfrak u),
$$
and hence
$$
\operatorname{Ind}_P^G(\mathcal O_0)
=\overline{G\cdot(X_0+\mathfrak u)}.
$$
The condition $\operatorname{rank}\bar C=c$ is open dense in the slice.  Inside the normalized slice, the open part is obtained by requiring $T$ to have maximal possible rank, i.e. $T\in\mathscr T^\circ$.  Therefore the open induced $G$-orbits are the orbits
$$
G\cdot(X_0+Y_{S,T}),
\qquad
T\in\mathscr T^\circ.
$$
The previous step gives the orbit criterion in terms of the isometry class of $B_T$.  In particular the orbit is independent of the auxiliary choice of $S$.

**Step 7: kernel and image.**  For
$$
x=X_0+Y_{S,T},
$$
one has
$$
\ker x=E\oplus\ker T,                                  \tag{16}
$$
and
$$
\operatorname{Im}x=(L_1\oplus\operatorname{Im}T)\oplus V_0.  \tag{17}
$$
Indeed, if
$$
e+v+a'+b'\in E\oplus V_0\oplus L'_1\oplus L'_0
$$
lies in $\ker x$, then the $V_0$-component gives
$$
X_0v+Sa'=0.
$$
Since $X_0v\in\operatorname{Im}X_0$ and $Sa'\in V_+$, both terms vanish.  Thus $a'=0$ and $v\in\ker X_0$.  The $E$-component is
$$
S^\vee v+Tb'=0.
$$
Here $S^\vee v\in L_1$ and $Tb'\in L_0$, so both vanish.  By (13), $v=0$, and hence $b'\in\ker T$.  This proves (16).  The image formula (17) follows similarly: $Sa'$ gives all of $V_+$, $X_0v$ gives $\operatorname{Im}X_0$, the correction using (13) gives $L_1$, and $Tb'$ gives $\operatorname{Im}T$.

**Step 8: the multiplicity.**  If $B_T$ is non-degenerate, then $\ker T=0$.  By (16),
$$
\ker x=E.
$$
Thus every element of $Z_G(x)$ preserves $E$, hence lies in $P$.  Therefore
$$
Z_G(x)\subseteq P,
\qquad
m(G\cdot x,P)=1.
$$

The only case where $B_T$ has a radical on the maximal-rank locus is the split alternating odd case.  Then
$$
F:=\ker T
$$
is one-dimensional.  Choose a complement $M$ of $F$ in $L'_0$, and set
$$
\ell:=M^\perp\subset L_0.
$$
Then $\ell$ is a line, $\lambda(\ell,F)\ne0$, and
$$
L_0=\operatorname{Im}T\oplus \ell.
$$
Using (16) and (17),
$$
\ker x/(\ker x\cap\operatorname{Im}x)
\simeq \ell\oplus F,                                  \tag{18}
$$
a hyperbolic plane.  Its two isotropic lines give exactly two maximal isotropic subspaces of $\ker x$ containing $\ker x\cap\operatorname{Im}x$:
$$
E
\qquad\text{and}\qquad
E^\sharp:=L_1\oplus\operatorname{Im}T\oplus F.
$$
Every element of $Z_G(x)$ preserves $\ker x$ and $\operatorname{Im}x$, so it permutes the two-point set $\{E,E^\sharp\}$.  The kernel of this action is exactly $Z_G(x)\cap P$.  The permutation is non-trivial: swapping the two lines $\ell$ and $F$ in the hyperbolic plane (18), and fixing the orthogonal complement, gives an element of $Z_G(x)\setminus P$.  Hence
$$
[Z_G(x):Z_G(x)\cap P]=2.
$$
Since the quotient is discrete, $Z_G(x)^\circ\subseteq Z_G(x)\cap P$, so the component-group multiplicity equals this ordinary index.  Therefore
$$
m(G\cdot x,P)=2.
$$

When $l=0$, there is no $T$ and no residual form.  The preceding argument gives the equal-rank strict-column case directly: the open orbit is unique and its multiplicity is $1$. $\square$
