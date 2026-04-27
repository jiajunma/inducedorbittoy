# Appendix: the maximal-parabolic orbit calculation used in Proposition 10.5

## Setting

This appendix spells out the orbit calculation used in Proposition 10.5.  We first put the maximal parabolic in a fixed notation.

Let $D\in\{\mathbb R,\mathbb C,\mathbb H\}$, with its standard involution, and let $\langle\ ,\ \rangle$ be an $\epsilon$-Hermitian sesquilinear form.  Let
$$
V=E\oplus V_0\oplus E'
$$
be a Witt decomposition in which $V_0$ is non-degenerate and $E,E'$ are totally isotropic subspaces paired perfectly by $\langle\ ,\ \rangle$.  We assume
$$
\dim_D E=\dim_D E'=\kappa.
$$
Equivalently, $V_0\simeq E^\perp/E$.  Let
$$
P=P_E\subset G(V)
$$
be the maximal parabolic subgroup stabilizing $E$, where $G=G(V)$, and let $\mathfrak u$ be the Lie algebra of its unipotent radical.  

Let $G_0=G(V_0)$ and let
$$
\mathfrak g_0=\operatorname{Lie}(G_0).
$$
The Levi factor of $P$ contains $G_0$; we regard $\mathfrak g_0$ as a summand of the Lie algebra of this Levi factor, acting on $V_0$ and acting trivially on $E\oplus E'$.  Let
$$
\mathcal O_0\subset \mathfrak g_0
$$
be a nilpotent $G_0$-orbit, and choose $X_0\in\mathcal O_0$.

## The induced orbit to be computed

The object computed in this appendix is
$$
\operatorname{Ind}_P^G(\mathcal O_0)
:=\overline{G\cdot(\mathcal O_0+\mathfrak u)}.
$$
固定 X_0\in O_0. 


Iso_{r, -\epsilon} := -\epsilon-sesquelinear form on $r$-dim $D$ space. 
定义 X_{C,B},


Lemma 1: r =  \kappa - dim_D \ker X_0 >=0. 那么 orbit in Ind (O_0)  in bijection with Iso_{r,-\epsilon}, r even is (\epislon, D) = (1,R) or (1,C) .
multilpity = 1. 

Since $G_0$ is contained in the Levi factor of $P$, and since $\mathfrak u$ is stable under this Levi factor, we have
$$
\mathcal O_0+\mathfrak u
=G_0\cdot(X_0+\mathfrak u).
$$
Therefore
$$
\operatorname{Ind}_P^G(\mathcal O_0)
=\overline{G\cdot(X_0+\mathfrak u)}.                 \tag{I}
$$
Thus the calculation is concrete: write the elements of $X_0+\mathfrak u$ as matrices $X_{C,B}$, use the $P$-action to normalize the pair $(C,B)$ on the open locus, and then read off the open $G$-orbits in (I).  This is the only purpose of the section.

## The slice $X_0+\mathfrak u$

With respect to
$$
V=E\oplus V_0\oplus E',
$$
every element of $X_0+\mathfrak u$ has the form
$$
X_{C,B}:=X_0+Y_{C,B},
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
\langle C^\vee v,a'\rangle=-\langle v,Ca'\rangle_0.
$$
Equivalently,
$$
X_{C,B}(e+v+a')=C^\vee v+Ba'+X_0v+Ca'.              \tag{2}
$$
The condition on $B$ is
$$
\langle Ba',b'\rangle+\epsilon\overline{\langle Bb',a'\rangle}=0
\qquad(a',b'\in E').                                  \tag{3}
$$
Conversely, every pair $(C,B)$ satisfying this condition gives an element $X_{C,B}\in X_0+\mathfrak u$, and this expression is unique.

## The $\operatorname{GL}_D(E)$ and unipotent actions

We first record the two conjugation formulas used in the normalization.  These formulas are part of the calculation, so we put them before the proof.

Let $h\in\operatorname{GL}_D(E)$.  Define $h^\vee:E'\to E'$ by
$$
\langle he,e'\rangle=\langle e,h^\vee e'\rangle
\qquad(e\in E,\ e'\in E').
$$
The corresponding Levi element is
$$
m_h=
\begin{bmatrix}
h&0&0\\
0&1&0\\
0&0&(h^\vee)^{-1}
\end{bmatrix}.
$$
A direct block multiplication gives
$$
m_hX_{C,B}m_h^{-1}=X_{C h^\vee,\,hB h^\vee}.          \tag{L}
$$
Hence
$$
\bar C\longmapsto \bar C h^\vee.
$$
Thus the $\operatorname{GL}_D(E)$-part of the Levi changes coordinates on the source $E'$ of $\bar C$.

Next let $R:E'\to V_0$.  This is the unipotent parameter; to avoid conflict with the coefficient algebra $D$, we write the corresponding unipotent element as $u_R$:
$$
u_R=
\begin{bmatrix}
1&R^\vee&\frac12R^\vee R\\
0&1&R\\
0&0&1
\end{bmatrix}\in P.
$$
Then
$$
u_RX_{C,B}u_R^{-1}
=X_{C-X_0R,\,B+R^\vee C-C^\vee R-R^\vee X_0R}.       \tag{U}
$$
In particular, $u_R$ does not change $\bar C$.

Combining (L) and (U), if we first apply $m_h$ and then $u_R$, then
$$
u_Rm_hX_{C,B}m_h^{-1}u_R^{-1}=X_{C',B'},
$$
where
$$
C'=C h^\vee-X_0R,
$$
and
$$
B'=hB h^\vee+R^\vee C h^\vee-(C h^\vee)^\vee R-R^\vee X_0R. \tag{LU}
$$
This is the calculation used below: $h$ puts the full-rank quotient map $\bar C$ in standard position, and $u_R$ removes the remaining $\operatorname{Im}X_0$-part of $C$.

### Hint for the normalization

The displayed $n_u$-calculation in the notes is exactly the following use of (U).  In the notation of that calculation, the middle-right block called $B$ is our $C$, the top-right block called $C$ is our $B$, and the parameter $u$ is our $R$.

After the quotient map $\bar C$ has been put in standard position, the first use of (U) makes the $C$-block equal to $C_S$.  From this point on, we only use unipotents $u_R$ with
$$
R(E')\subset \ker X_0.
$$
Then $X_0R=0$, so (U) keeps the $C$-block fixed and gives
$$
u_RX_{C_S,B}u_R^{-1}=X_{C_S,B'},
\qquad
B'=B+R^\vee C_S-C_S^\vee R.                         \tag{R}
$$
Write
$$
R=R_1\oplus R_0,
\qquad
R_1:L'_1\to \ker X_0,
\qquad
R_0:L'_0\to \ker X_0.
$$
With rows indexed by $L_1,L_0$ and columns indexed by $L'_1,L'_0$, the correction term is
$$
R^\vee C_S-C_S^\vee R=
\begin{bmatrix}
R_1^\vee S-S^\vee R_1&-S^\vee R_0\\
R_0^\vee S&0
\end{bmatrix}.                                      \tag{R'}
$$
This formula explains the reduction of the $B$-block.

1.  The bottom-right block $L'_0\to L_0$ is unchanged.  This is the residual block which we call
    $$
    T:L'_0\to L_0.
    $$
2.  The map $S^\vee|_{\ker X_0}:\ker X_0\to L_1$ is an isomorphism, because the pairing between $V_+$ and $\ker X_0$ is perfect.  Hence the term $-S^\vee R_0$ can be chosen to kill the $L'_0\to L_1$ cross-block.  The skew-adjointness relation (3) then kills the opposite $L'_1\to L_0$ cross-block at the same time.
3.  After the cross-blocks are gone, the remaining $L'_1\to L_1$ block is killed by choosing $R_1$; this is the term $R_1^\vee S-S^\vee R_1$ in (R').

Thus, once $C=C_S$ is fixed, the unipotent action kills every part of $B$ except the residual block $T:L'_0\to L_0$.  This is the precise meaning of the hint in the older $n_u$ computation.

Put
$$
c:=\dim_D\ker X_0.
$$
Thus $c=\mathbf c_1(\mathcal O_0)$.

The open part of the induced orbit is controlled by the quotient of $C$ modulo $\operatorname{Im}X_0$.  Since $X_0$ is skew-adjoint,
$$
(\operatorname{Im}X_0)^\perp=\ker X_0,
$$
so
$$
\dim_D (V_0/\operatorname{Im}X_0)=c.
$$
Let
$$
\bar C:E'\to V_0/\operatorname{Im}X_0
$$
be the quotient map.  The open condition is
$$
\operatorname{rank}_D \bar C=c.              \tag{4}
$$
Thus this normal-form calculation requires
$$
\kappa=\dim_D E'=\dim_D E\ge c=\dim_D\ker X_0.          \tag{5}
$$

## The normal forms $X_{S,T}$ and the rank-$r$ form locus

Assume
$$
\kappa=\dim_D E\ge c:=\dim_D\ker X_0.
$$
Put
$$
l=\kappa-c.
$$
Choose a complement
$$
V_0=V_+\oplus \operatorname{Im}X_0,
\qquad
\dim_D V_+=c.
$$
Choose decompositions
$$
E=L_1\oplus L_0,
\qquad
E'=L'_1\oplus L'_0,
$$
with
$$
\dim_D L_1=\dim_D L'_1=c,
\qquad
\dim_D L_0=\dim_D L'_0=l,
$$
such that the pairing restricts to perfect pairings $L_i\times L'_i$ and kills $L_i\times L'_j$ for $i\ne j$.

Let
$$
S:L'_1\xrightarrow{\sim}V_+
$$
be an isomorphism.  Define $C_S:E'\to V_0$ by
$$
C_S|_{L'_1}=S,
\qquad
C_S|_{L'_0}=0.                                      \tag{6}
$$
For such $S$, define $S^\vee:V_0\to L_1$ by
$$
\langle S^\vee v,a'\rangle=-\langle v,Sa'\rangle_0
\qquad(a'\in L'_1).
$$

Now let $T:L'_0\to L_0$ satisfy
$$
\langle Tu,v\rangle+\epsilon\overline{\langle Tv,u\rangle}=0
\qquad(u,v\in L'_0).                                  \tag{7}
$$
Equivalently,
$$
B_T(u,v):=\langle Tu,v\rangle
$$
is a $(-\epsilon)$-Hermitian form on $L'_0$.  Let $B(T):E'\to E$ be the map which is $T$ on $L'_0$ and is zero on $L'_1$.  We define
$$
Y_{S,T}:=Y_{C_S,B(T)},
\qquad
X_{S,T}:=X_0+Y_{S,T}.                                  \tag{8}
$$
Explicitly,
$$
X_{S,T}(e+v+a'+b')=(S^\vee v+Tb')+(X_0v+Sa')
$$
for
$$
e\in E,
\quad v\in V_0,
\quad a'\in L'_1,
\quad b'\in L'_0.
$$

Let $\mathscr T$ be the space of all $T:L'_0\to L_0$ satisfying (7).  Put
$$
r=
\begin{cases}
l-1,&D=\mathbb R,\ \epsilon=+1,\ l\text{ odd},\\
l,&\text{otherwise}.
\end{cases}                                           \tag{9}
$$
We write
$$
\operatorname{Form}_r(L'_0)
:=\{T\in\mathscr T:\operatorname{rank}_D T=r\}.
$$
Equivalently, $\operatorname{Form}_r(L'_0)$ is the locus where $B_T$ has maximal possible rank: $B_T$ is non-degenerate except in the real alternating odd case, where it has one-dimensional radical.

## Lemma A.1: the general induced-orbit calculation

**Lemma A.1.**  Assume that
$$
\dim_D E\ge \dim_D\ker X
\qquad\text{for }X\in\mathcal O_0.
$$
Equivalently, for the fixed choice $X_0\in\mathcal O_0$, this says $\kappa\ge c$.  Then the open $G$-orbits in
$$
\operatorname{Ind}_P^G(\mathcal O_0)
=\overline{G\cdot(\mathcal O_0+\mathfrak u)}
$$
are precisely
$$
G\cdot X_{S,T},
\qquad
T\in\operatorname{Form}_r(L'_0).                                \tag{10}
$$
The orbit is independent of the auxiliary choice of $S$.  Moreover,
$$
G\cdot X_{S,T_1}=G\cdot X_{S,T_2}
$$
if and only if
$$
(L'_0,B_{T_1})\cong (L'_0,B_{T_2}).
$$
The multiplicity is
$$
m(G\cdot X_{S,T},P)=
\begin{cases}
1,&B_T\text{ is non-degenerate},\\
2,&B_T\text{ has one-dimensional }D\text{-radical}.
\end{cases}                                           \tag{11}
$$
The second case occurs exactly when
$$
D=\mathbb R,
\qquad
\epsilon=+1,
\qquad
l\text{ is odd}.
$$

## Application to Proposition 10.5

**Case I: naive descent.**  In the naive-descent case, Proposition 10.5 applies Lemma A.1 to
$$
\mathcal O_0=\mathcal O'=D_{\mathrm{naive}}(\mathcal O),
$$
once the inequality $\dim_D E\ge \dim_D\ker X$ for $X\in\mathcal O_0$ has been checked.

**Case II: generalized good descent.**  In the generalized-good-descent case one first applies the one-box $\Lambda$-modification prescribed by the induction formula in Section~\ref{subsec:induced}.  After that modification, the maximal-parabolic calculation is applied to an orbit $\mathcal O_0$ satisfying
$$
\kappa=c=\dim_D \ker X_0
\qquad\text{and}\qquad
\mathbf c_1(\mathcal O_0)>\mathbf c_2(\mathcal O_0).  \tag{12}
$$
In this situation $l=0$, so $L_0=L'_0=0$ and $\mathscr T=\{0\}$.  There is no residual form $B_T$.  The normal form becomes
$$
X_0+Y_S,
$$
where $S:E'\xrightarrow{\sim}V_+$ and
$$
(X_0+Y_S)(e+v+a')=S^\vee v+X_0v+Sa'.                  \tag{13}
$$
Thus there is a single open $G$-orbit:
$$
G\cdot(X_0+Y_S),
$$
and its multiplicity is $1$.

In Young diagram language, after the one-box $\Lambda$-modification this is the $t_0=0$ branch of Section~\ref{subsec:induced}: two columns of length $\kappa$ are inserted before the diagram of $\mathcal O_0$.  Since $\mathbf c_1(\mathcal O_0)=\kappa$ and $\mathbf c_1(\mathcal O_0)>\mathbf c_2(\mathcal O_0)$, the beginning of the resulting column sequence is
$$
(\kappa,\kappa,\kappa,\mathbf c_2(\mathcal O_0),\mathbf c_3(\mathcal O_0),\ldots).
$$

## Proof

We prove the assertions in the order in which they are used.

**Step 1: the fixed geometry of $X_0$.**  Since $X_0$ is skew-adjoint,
$$
(\operatorname{Im}X_0)^\perp=\ker X_0.                         \tag{P1}
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
the quotient map identifies $V_+$ with $V_0/\operatorname{Im}X_0$.  Moreover, (P1) implies that the pairing
$$
V_+\times \ker X_0\longrightarrow D
$$
is perfect.  Hence for every isomorphism $S:L'_1\xrightarrow{\sim}V_+$, the map
$$
S^\vee|_{\ker X_0}:\ker X_0\xrightarrow{\sim}L_1              \tag{P2}
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
\langle C^\vee v,a'\rangle=-\langle v,Ca'\rangle_0.
$$
The same condition on two vectors in $E'$ gives exactly (3):
$$
\langle Ba',b'\rangle+\epsilon\overline{\langle Bb',a'\rangle}=0.
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
gives precisely $X_{S,T}$.

**Step 3: normalizing the $C$-block.**  Let
$$
\bar C:E'\to V_0/\operatorname{Im}X_0
$$
be the quotient of $C$.  On the open locus
$$
\operatorname{rank}\bar C=c,
$$
the map $\bar C$ is surjective and $\ker\bar C$ has dimension $l=\kappa-c$.  Using the Levi formula (L), we may arrange
$$
\ker\bar C=L'_0,
\qquad
\bar C|_{L'_1}:L'_1\xrightarrow{\sim}V_0/\operatorname{Im}X_0.
$$
After identifying the quotient with the fixed complement $V_+$, this gives the required isomorphism
$$
S:L'_1\xrightarrow{\sim}V_+.
$$
Then $C-C_S$ takes values in $\operatorname{Im}X_0$.  Hence there is $R:E'\to V_0$ such that
$$
X_0R=C-C_S.
$$
Using (U), conjugation by $u_R$ replaces $C$ by
$$
C-X_0R=C_S.
$$
Thus every point of the open locus is $P$-conjugate to one with the normalized $C$-block (6).

**Step 4: reducing the $B$-block.**  Now keep $C=C_S$ fixed.  Write $B$ in blocks according to
$$
E'=L'_1\oplus L'_0,
\qquad
E=L_1\oplus L_0.
$$
We use the consequence (R)--(R') of (U), with $R$ taking values in $\ker X_0$; this keeps the $C$-block fixed because $X_0R=0$.

First take $R_0:L'_0\to \ker X_0$.  By the perfect pairing $V_+\times\ker X_0$, the map
$$
R_0\longmapsto R_0^\vee S
$$
identifies $\operatorname{Hom}(L'_0,\ker X_0)$ with the space of cross-blocks from $L'_1$ to $L_0$.  Hence we choose $R_0$ to kill the corresponding cross-block of $B$.  The relation (3) then kills the opposite cross-block as well.

Next take $R_1:L'_1\to\ker X_0$.  The remaining $L'_1\to L_1$ block defines a $(-\epsilon)$-Hermitian form on $L'_1$.  Again using the perfect pairing between $V_+$ and $\ker X_0$, we choose $R_1$ so that the correction
$$
R_1^\vee C_S-C_S^\vee R_1
$$
kills this block.  Therefore the only block left is
$$
T:L'_0\to L_0.
$$
The skew-adjointness relation (3) becomes exactly
$$
\langle Tu,v\rangle+\epsilon\overline{\langle Tv,u\rangle}=0,
$$
so $T\in\mathscr T$.  This proves the normal form $X_{S,T}$.

After this reduction, the stabilizer of $C_S$ still contains the $\operatorname{GL}_D(L'_0)$-part of the Levi.  Its action on the residual block is the usual change of coordinates.  If $\gamma\in\operatorname{GL}_D(L'_0)$ and the Levi acts on $L_0$ by $(\gamma^{-1})^\vee$, then
$$
T\longmapsto (\gamma^{-1})^\vee T\gamma.                  \tag{P4}
$$
This is exactly the change of coordinates for the form
$$
B_T(u,v)=\langle Tu,v\rangle.
$$
Hence the residual $P$-orbits in the normalized slice are classified by the isometry classes of $(L'_0,B_T)$.

Conversely, suppose two normalized elements are $P$-conjugate.  Write the conjugating element as a unipotent part times a Levi part.  Formula (U) shows that the unipotent part cannot change the residual $L'_0\to L_0$ block: on $L'_0$, the correction terms either vanish because $C_S|_{L'_0}=0$ or land in $L_1$, not in $L_0$.  Therefore the residual block changes only by (P4).  Thus two normalized elements are $P$-conjugate if and only if their residual forms are isometric.

**Step 5: passing from the slice to induced $G$-orbits.**  By (I), computing $\operatorname{Ind}_P^G(\mathcal O_0)$ means computing the open $G$-orbits meeting the slice $X_0+\mathfrak u$.
The condition $\operatorname{rank}\bar C=c$ is open dense in the slice.  Inside the normalized slice, the open part is obtained by requiring $T$ to have maximal possible rank, i.e. $T\in\operatorname{Form}_r(L'_0)$.  Therefore the open induced $G$-orbits are the orbits
$$
G\cdot X_{S,T},
\qquad
T\in\operatorname{Form}_r(L'_0).
$$
The previous step gives the orbit criterion in terms of the isometry class of $B_T$.  In particular the orbit is independent of the auxiliary choice of $S$.

**Step 6: kernel and image.**  For
$$
x=X_{S,T},
$$
one has
$$
\ker x=E\oplus\ker T,                                  \tag{P5}
$$
and
$$
\operatorname{Im}x=(L_1\oplus\operatorname{Im}T)\oplus V_0.  \tag{P6}
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
Here $S^\vee v\in L_1$ and $Tb'\in L_0$, so both vanish.  By (P2), $v=0$, and hence $b'\in\ker T$.  This proves (P5).  The image formula (P6) follows similarly: $Sa'$ gives all of $V_+$, $X_0v$ gives $\operatorname{Im}X_0$, the correction using (P2) gives $L_1$, and $Tb'$ gives $\operatorname{Im}T$.

**Step 7: the multiplicity.**  If $B_T$ is non-degenerate, then $\ker T=0$.  By (P5),
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
Then $\ell$ is a line, $\langle \ell,F\rangle\ne0$, and
$$
L_0=\operatorname{Im}T\oplus \ell.
$$
Using (P5) and (P6),
$$
\ker x/(\ker x\cap\operatorname{Im}x)
\simeq \ell\oplus F,                                  \tag{P7}
$$
a hyperbolic plane.  Its two isotropic lines give exactly two maximal isotropic subspaces of $\ker x$ containing $\ker x\cap\operatorname{Im}x$:
$$
E
\qquad\text{and}\qquad
E^\sharp:=L_1\oplus\operatorname{Im}T\oplus F.
$$
Every element of $Z_G(x)$ preserves $\ker x$ and $\operatorname{Im}x$, so it permutes the two-point set $\{E,E^\sharp\}$.  The kernel of this action is exactly $Z_G(x)\cap P$.  The permutation is non-trivial: swapping the two lines $\ell$ and $F$ in the hyperbolic plane (P7), and fixing the orthogonal complement, gives an element of $Z_G(x)\setminus P$.  Hence
$$
[Z_G(x):Z_G(x)\cap P]=2.
$$
Since the quotient is discrete, $Z_G(x)^\circ\subseteq Z_G(x)\cap P$, so the component-group multiplicity equals this ordinary index.  Therefore
$$
m(G\cdot x,P)=2.
$$

When $l=0$, there is no $T$ and no residual form.  This is precisely the generalized-good-descent application after the one-box $\Lambda$-modification: the open orbit is unique and its multiplicity is $1$. $\square$
