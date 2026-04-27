# Appendix: the maximal-parabolic orbit calculation used in Proposition 10.5

## Setting

This appendix spells out the maximal-parabolic orbit calculation used in Proposition 10.5.  Let
$$
D\in\{\mathbb R,\mathbb C,\mathbb H\}
$$
with its standard involution, and let $\langle\ ,\ \rangle$ be an $\epsilon$-Hermitian sesquilinear form.  Fix a Witt decomposition
$$
V=E\oplus V_0\oplus E'
$$
where $V_0$ is non-degenerate and $E,E'$ are totally isotropic and paired perfectly by $\langle\ ,\ \rangle$.  Put
$$
\dim_D E=\dim_D E'=\kappa.
$$
Let $G=G(V)$ and let $P=P_E\subset G$ be the maximal parabolic subgroup stabilizing $E$.  Let $\mathfrak u$ be the Lie algebra of the unipotent radical of $P$.

Let $G_0=G(V_0)$ and
$$
\mathfrak g_0=\operatorname{Lie}(G_0).
$$
We regard $\mathfrak g_0$ as the summand of the Levi Lie algebra which acts on $V_0$ and acts trivially on $E\oplus E'$.  Let
$$
\mathcal O_0\subset \mathfrak g_0
$$
be a nilpotent $G_0$-orbit, and fix
$$
X_0\in\mathcal O_0.
$$

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
The condition on $B$ is
$$
\langle Ba',b'\rangle+\epsilon\overline{\langle Bb',a'\rangle}=0
\qquad(a',b'\in E').                                  \tag{2}
$$
Conversely, every pair $(C,B)$ satisfying (2) gives an element $X_{C,B}\in X_0+\mathfrak u$, and this expression is unique.

## Normal representatives

Put
$$
c:=\dim_D\ker X_0,
\qquad
l:=\kappa-c.
$$
Assume $\kappa\ge c$.  Choose
$$
V_0=V_+\oplus\operatorname{Im}X_0,
\qquad
\dim_D V_+=c,
$$
and decompositions
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
compatible with the pairing.

For an isomorphism $S:L'_1\xrightarrow{\sim}V_+$, define $C_S:E'\to V_0$ by
$$
C_S|_{L'_1}=S,
\qquad
C_S|_{L'_0}=0,                                      \tag{3}
$$
and write $S^\vee:=C_S^\vee:V_0\to L_1$.  For $T:L'_0\to L_0$ satisfying
$$
\langle Tu,v\rangle+\epsilon\overline{\langle Tv,u\rangle}=0
\qquad(u,v\in L'_0),                                  \tag{4}
$$
put
$$
B_T(u,v):=\langle Tu,v\rangle.
$$
Let $B(T):E'\to E$ be $T$ on $L'_0$ and zero on $L'_1$, and set
$$
X_{S,T}:=X_0+Y_{C_S,B(T)}.                            \tag{5}
$$

Let $\mathscr T$ be the space of all $T$ satisfying (4).  Put
$$
r=
\begin{cases}
l-1,&D=\mathbb R,\ \epsilon=+1,\ l\text{ odd},\\
l,&\text{otherwise},
\end{cases}                                           \tag{6}
$$
and
$$
\operatorname{Form}_r(L'_0)
:=\{T\in\mathscr T:\operatorname{rank}_D T=r\}.
$$

## Lemma A.1: the general induced-orbit calculation

Define $\operatorname{Iso}_{r,-\epsilon}$ to be the set of isomorphism classes of non-degenerate $(-\epsilon)$-Hermitian $D$-spaces of $D$-dimension $r$.  If $T\in\operatorname{Form}_r(L'_0)$, let $\operatorname{rad}(B_T)$ be the radical of $B_T$.  The induced form on
$$
L'_0/\operatorname{rad}(B_T)
$$
is non-degenerate of dimension $r$, and we denote its class by
$$
[B_T]\in\operatorname{Iso}_{r,-\epsilon}.             \tag{7}
$$
We regard $B_T$ as the class $[B_T]\in\operatorname{Iso}_{r,-\epsilon}$.

**Lemma A.1.**  Assume that
$$
\dim_D E\ge \dim_D\ker X
\qquad\text{for }X\in\mathcal O_0.
$$
Then the open $G$-orbits in
$$
\operatorname{Ind}_P^G(\mathcal O_0)
:=\overline{G\cdot(\mathcal O_0+\mathfrak u)}
$$
are precisely
$$
G\cdot X_{S,T},
\qquad
T\in\operatorname{Form}_r(L'_0).                      \tag{8}
$$
The $G$-orbit is independent of the auxiliary choice of $S$.  Moreover,
$$
G\cdot X_{S,T_1}=G\cdot X_{S,T_2}
$$
if and only if
$$
[B_{T_1}]=[B_{T_2}]
\qquad\text{in }\operatorname{Iso}_{r,-\epsilon}.
$$
The multiplicity is
$$
m(G\cdot X_{S,T},P)=
\begin{cases}
1,&B_T\text{ is non-degenerate},\\
2,&B_T\text{ has one-dimensional }D\text{-radical}.
\end{cases}                                           \tag{9}
$$
The second case occurs exactly when
$$
D=\mathbb R,
\qquad
\epsilon=+1,
\qquad
l\text{ is odd}.
$$

## Proof of Lemma A.1

The proof is a calculation of the open orbits of
$$
H_{X_0}:=(\operatorname{GL}_D(E)\times S_{X_0})\ltimes U
$$
on the slice $X_0+\mathfrak u$, where
$$
S_{X_0}:=\{g\in G_0:gX_0g^{-1}=X_0\}
$$
and $U$ is the unipotent radical of $P$.  Indeed, since $G_0$ is contained in the Levi factor of $P$ and $\mathfrak u$ is stable under $P$,
$$
\mathcal O_0+\mathfrak u=G_0\cdot(X_0+\mathfrak u),
$$
and therefore
$$
\operatorname{Ind}_P^G(\mathcal O_0)
=\overline{G\cdot(X_0+\mathfrak u)}.                 \tag{10}
$$
After fixing $X_0$, the remaining parabolic action on the slice is exactly the action of $H_{X_0}$.

**Step 1: the linear part of the action.**  Let $h\in\operatorname{GL}_D(E)$ and $s\in S_{X_0}$.  Define $h^\vee:E'\to E'$ by
$$
\langle he,e'\rangle=\langle e,h^\vee e'\rangle
\qquad(e\in E,\ e'\in E').
$$
The corresponding Levi element is
$$
m_{h,s}=
\begin{bmatrix}
h&0&0\\
0&s&0\\
0&0&(h^\vee)^{-1}
\end{bmatrix}.
$$
Since $sX_0s^{-1}=X_0$, direct block multiplication gives
$$
m_{h,s}X_{C,B}m_{h,s}^{-1}
=X_{sC h^\vee,\,hBh^\vee}.                           \tag{11}
$$
Hence the quotient map
$$
\bar C:E'\to V_0/\operatorname{Im}X_0
$$
changes by
$$
\bar C\longmapsto \bar s\,\bar C h^\vee,
$$
where $\bar s$ is the induced action of $s$ on $V_0/\operatorname{Im}X_0$.

**Step 2: the unipotent part of the action.**  Let $R:E'\to V_0$.  Write
$$
u_R=
\begin{bmatrix}
1&R^\vee&\frac12R^\vee R\\
0&1&R\\
0&0&1
\end{bmatrix}\in U.
$$
Then
$$
u_RX_{C,B}u_R^{-1}
=X_{C-X_0R,\,B+R^\vee C-C^\vee R-R^\vee X_0R}.       \tag{12}
$$
In particular, $u_R$ does not change $\bar C$.

Combining (11) and (12), if one first applies $m_{h,s}$ and then $u_R$, then
$$
u_Rm_{h,s}X_{C,B}m_{h,s}^{-1}u_R^{-1}=X_{C',B'},
$$
where
$$
C'=sC h^\vee-X_0R,
$$
and
$$
B'=hB h^\vee+R^\vee sC h^\vee-(sC h^\vee)^\vee R-R^\vee X_0R. \tag{13}
$$
These are the formulas used below.

**Step 3: the open condition and normalization of the $C$-block.**  The open condition is
$$
\operatorname{rank}_D\bar C=c.                         \tag{14}
$$
It is open because $c=\dim_D(V_0/\operatorname{Im}X_0)$, and it is non-empty precisely because $\kappa\ge c$.

On this open locus, $\bar C$ is surjective and $\ker\bar C$ has dimension $l=\kappa-c$.  Using the $\operatorname{GL}_D(E)$-part of (11), we may arrange
$$
\ker\bar C=L'_0,
\qquad
\bar C|_{L'_1}:L'_1\xrightarrow{\sim}V_0/\operatorname{Im}X_0.
$$
After identifying $V_0/\operatorname{Im}X_0$ with the chosen complement $V_+$, this gives an isomorphism $S:L'_1\xrightarrow{\sim}V_+$.  Then $C-C_S$ takes values in $\operatorname{Im}X_0$.  Choose $R:E'\to V_0$ such that
$$
X_0R=C-C_S.
$$
By (12), conjugating by $u_R$ replaces $C$ by
$$
C-X_0R=C_S.
$$
Thus every point of the open locus is $H_{X_0}$-conjugate to one with $C$-block equal to $C_S$.

**Step 4: reduction of the $B$-block.**  Keep $C=C_S$ fixed.  To preserve this $C$-block, use only unipotents $u_R$ with
$$
R(E')\subset\ker X_0.
$$
Then $X_0R=0$, and (12) becomes
$$
u_RX_{C_S,B}u_R^{-1}=X_{C_S,B'},
\qquad
B'=B+R^\vee C_S-C_S^\vee R.                         \tag{15}
$$
Write
$$
R=R_1\oplus R_0,
\qquad
R_1:L'_1\to\ker X_0,
\qquad
R_0:L'_0\to\ker X_0.
$$
With rows indexed by $L_1,L_0$ and columns indexed by $L'_1,L'_0$, the correction term is
$$
R^\vee C_S-C_S^\vee R=
\begin{bmatrix}
R_1^\vee S-S^\vee R_1&-S^\vee R_0\\
R_0^\vee S&0
\end{bmatrix}.                                      \tag{16}
$$
The pairing between $V_+$ and $\ker X_0$ is perfect, so
$$
S^\vee|_{\ker X_0}:\ker X_0\xrightarrow{\sim}L_1
$$
is an isomorphism.  Hence the term $-S^\vee R_0$ can be chosen to kill the $L'_0\to L_1$ cross-block of $B$; then (2) kills the opposite $L'_1\to L_0$ cross-block.  After the cross-blocks are killed, the remaining $L'_1\to L_1$ block is killed by choosing $R_1$, using the term $R_1^\vee S-S^\vee R_1$ in (16).  Thus the only surviving block is
$$
T:L'_0\to L_0,
$$
and the skew-adjointness condition (2) becomes exactly (4).  Therefore the normal form is $X_{S,T}$.

In the older notation using $n_u$, the middle-right block denoted $B$ is the present $C$, the top-right block denoted $C$ is the present $B$, and the parameter $u$ is the present $R$.

**Step 5: the residual invariant.**  The stabilizer of the normalized $C$-block contains the block-diagonal subgroup which is the identity on $L'_1$ and acts by
$$
\gamma\in\operatorname{GL}_D(L'_0)
$$
on $L'_0$.  The corresponding action on $L_0$ is by $(\gamma^{-1})^\vee$, and it sends
$$
T\longmapsto (\gamma^{-1})^\vee T\gamma.             \tag{17}
$$
This is exactly change of coordinates for the form
$$
B_T(u,v)=\langle Tu,v\rangle.
$$
The unipotent part preserving $C_S$ does not change the residual $L'_0\to L_0$ block, by (16).  Consequently, the remaining $H_{X_0}$-orbits in the normalized slice are classified by the class
$$
[B_T]\in\operatorname{Iso}_{r,-\epsilon}.
$$

The auxiliary choice of $S$ does not affect the resulting $G$-orbit.  Indeed, if $S_1,S_2:L'_1\xrightarrow{\sim}V_+$ are two choices, choose $h^\vee\in\operatorname{GL}_D(E')$ which is the identity on $L'_0$ and satisfies
$$
S_1h^\vee|_{L'_1}=S_2.
$$
Then (11), with $s=1$, sends $X_{S_1,T}$ to $X_{S_2,T}$.

**Step 6: the open induced orbits.**  The condition (14) is open in $X_0+\mathfrak u$.  Inside the normalized slice, the open part is obtained by requiring the residual form to have maximal possible rank, namely
$$
T\in\operatorname{Form}_r(L'_0).
$$
By (10), the corresponding open $G$-orbits in $\operatorname{Ind}_P^G(\mathcal O_0)$ are precisely
$$
G\cdot X_{S,T},
\qquad
T\in\operatorname{Form}_r(L'_0).
$$
The orbit criterion in terms of the class $[B_T]\in\operatorname{Iso}_{r,-\epsilon}$ follows from Step 5.

**Step 7: the multiplicity.**  Let $x=X_{S,T}$ with $T\in\operatorname{Form}_r(L'_0)$.  We first record
$$
\ker x=E\oplus\ker T,                                  \tag{18}
$$
and
$$
\operatorname{Im}x=(L_1\oplus\operatorname{Im}T)\oplus V_0.  \tag{19}
$$
Indeed, if $e+v+a'+b'\in E\oplus V_0\oplus L'_1\oplus L'_0$ lies in $\ker x$, then the $V_0$-component gives
$$
X_0v+Sa'=0.
$$
Since $X_0v\in\operatorname{Im}X_0$ and $Sa'\in V_+$, both terms vanish.  Hence $a'=0$ and $v\in\ker X_0$.  The $E$-component is
$$
S^\vee v+Tb'=0.
$$
Here $S^\vee v\in L_1$ and $Tb'\in L_0$, so both vanish.  Since $S^\vee|_{\ker X_0}$ is an isomorphism, $v=0$, and $b'\in\ker T$.  This proves (18).  Formula (19) follows directly from (1) and the definition of $X_{S,T}$.

If $B_T$ is non-degenerate, then $\ker T=0$, so $\ker x=E$.  Every element of $Z_G(x)$ preserves $E$, hence lies in $P$.  Thus
$$
Z_G(x)\subseteq P,
\qquad
m(G\cdot x,P)=1.
$$

The only case where $B_T$ has a radical on the maximal-rank locus is the real alternating odd case.  Then
$$
F:=\ker T
$$
is one-dimensional.  Choose a complement $M$ of $F$ in $L'_0$ and set
$$
\ell:=M^\perp\subset L_0.
$$
Then
$$
L_0=\operatorname{Im}T\oplus \ell,
$$
and (18)--(19) give
$$
\ker x/(\ker x\cap\operatorname{Im}x)
\simeq \ell\oplus F,                                  \tag{20}
$$
a hyperbolic plane.  Its two isotropic lines give exactly two maximal isotropic subspaces of $\ker x$ containing $\ker x\cap\operatorname{Im}x$, namely
$$
E
\qquad\text{and}\qquad
E^\sharp:=L_1\oplus\operatorname{Im}T\oplus F.
$$
Every element of $Z_G(x)$ preserves $\ker x$ and $\operatorname{Im}x$, so it permutes the two-point set $\{E,E^\sharp\}$.  The kernel of this action is $Z_G(x)\cap P$, and the permutation is non-trivial by swapping the two isotropic lines in the hyperbolic plane (20).  Hence
$$
[Z_G(x):Z_G(x)\cap P]=2.
$$
Since the quotient is discrete, $Z_G(x)^\circ\subseteq Z_G(x)\cap P$.  Therefore
$$
m(G\cdot x,P)=2.
$$
This proves Lemma A.1.  $\square$

## Application to Proposition 10.5

**Case I: naive descent.**  In the naive-descent case, Proposition 10.5 applies Lemma A.1 to
$$
\mathcal O_0=\mathcal O'=D_{\mathrm{naive}}(\mathcal O),
$$
once the inequality
$$
\dim_D E\ge \dim_D\ker X
\qquad(X\in\mathcal O_0)
$$
has been checked.

**Case II: generalized good descent.**  In the generalized-good-descent case one first applies the one-box $\Lambda$-modification prescribed by the induction formula in Section~\ref{subsec:induced}.  After that modification, the maximal-parabolic calculation is applied to an orbit $\mathcal O_0$ satisfying
$$
\kappa=c=\dim_D\ker X_0,
\qquad
\mathbf c_1(\mathcal O_0)>\mathbf c_2(\mathcal O_0).  \tag{21}
$$
Here $l=0$, so $L_0=L'_0=0$ and the residual form is absent.  The normal form is
$$
X_{S,0},
$$
and Lemma A.1 gives a single open $G$-orbit with multiplicity $1$.

In Young diagram language, after the one-box $\Lambda$-modification this is the $t_0=0$ branch of Section~\ref{subsec:induced}: two columns of length $\kappa$ are inserted before the diagram of $\mathcal O_0$.  Since $\mathbf c_1(\mathcal O_0)=\kappa$ and $\mathbf c_1(\mathcal O_0)>\mathbf c_2(\mathcal O_0)$, the beginning of the resulting column sequence is
$$
(\kappa,\kappa,\kappa,\mathbf c_2(\mathcal O_0),\mathbf c_3(\mathcal O_0),\ldots).
$$
