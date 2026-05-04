# lemma lem:quotient-form

## statement
One has
$$
(\operatorname{Im} X_0)^\perp=\ker X_0.
$$
Hence the radical of the restricted form on $\ker X_0$ is
$$
\ker X_0\cap (\ker X_0)^\perp
=
\ker X_0\cap \operatorname{Im} X_0
=R,
$$
so the induced form on
$$
K_{X_0}=\ker X_0/R
$$
is non-degenerate and $\epsilon$-symmetric. Moreover
$$
\phi_S=S^\vee|_{\ker X_0}:\ker X_0\to E
$$
is surjective with kernel $L$.

## proof
For $v\in \ker X_0$ and $y=X_0 w\in \operatorname{Im} X_0$,
$$
\langle v,y\rangle_0
=
\langle v,X_0 w\rangle_0
=
-\langle X_0v,w\rangle_0
=0.
$$
Thus
$$
\ker X_0\subseteq (\operatorname{Im} X_0)^\perp.
$$
The two spaces have the same dimension, because
$$
\dim (\operatorname{Im} X_0)^\perp
=
\dim V_0-\dim \operatorname{Im} X_0
=
\dim \ker X_0.
$$
Therefore $(\operatorname{Im} X_0)^\perp=\ker X_0$.

Now
$$
(\ker X_0)^\perp
=
\operatorname{Im} X_0,
$$
so the radical of the restricted form on $\ker X_0$ is exactly
$$
\ker X_0\cap \operatorname{Im} X_0=R.
$$
Hence the form descends to a non-degenerate $\epsilon$-symmetric form on
$K_{X_0}=\ker X_0/R$.

Finally, by assumption $\dim L=d$ and
$$
d=c_1-\kappa=\dim \ker X_0-\dim E.
$$
Therefore
$$
\operatorname{rank}\phi_S
=
\dim \ker X_0-\dim L
=
c_1-d
=
\kappa
=
\dim E,
$$
so $\phi_S$ is surjective and $\ker \phi_S=L$.

# proposition prop:block-form-and-commutator

## statement
A general element of $\mathfrak p$ has the form
$$
Y=
\begin{pmatrix}
a&T^\vee&B\\
0&D&T\\
0&0&-a^\vee
\end{pmatrix},
$$
where
$$
a\in \operatorname{End}(E),\qquad
D\in \mathfrak g_0,\qquad
T\in \operatorname{Hom}(E',V_0),
$$
and $B\in \operatorname{Hom}(E',E)$ satisfies
$$
\lambda(Bu,v)+\epsilon\lambda(Bv,u)=0
\qquad (u,v\in E').
$$
Here $a^\vee\in \operatorname{End}(E')$ is the $\lambda$-adjoint of $a$, and
$T^\vee:V_0\to E$ is defined by
$$
\lambda(T^\vee x,e')=-\langle x,Te'\rangle_0.
$$

For
$$
x_S=
\begin{pmatrix}
0&S^\vee&0\\
0&X_0&S\\
0&0&0
\end{pmatrix},
$$
one has
$$
[Y,x_S]
=
\begin{pmatrix}
0&(DS-X_0T+Sa^\vee)^\vee&T^\vee S-S^\vee T\\
0&[D,X_0]&DS-X_0T+Sa^\vee\\
0&0&0
\end{pmatrix}.
$$
Consequently $Y\in \mathfrak z_{\mathfrak p}(x_S)$ if and only if
$$
[D,X_0]=0,
\qquad
DS-X_0T+Sa^\vee=0,
\qquad
T^\vee S-S^\vee T=0.
$$

## proof
Write a general upper-triangular block matrix in $\mathfrak p$ as
$$
\begin{pmatrix}
a&A&B\\
0&D&T\\
0&0&c
\end{pmatrix}.
$$
The condition $Y\in \operatorname{Lie}\operatorname{Isom}(V)$ is
$$
\langle Yx,y\rangle+\langle x,Yy\rangle=0
\qquad (x,y\in V).
$$
Testing this on $E\times E'$ gives $c=-a^\vee$. Testing it on
$V_0\times E'$ gives $A=T^\vee$. Testing it on $E'\times E'$ gives
$$
\lambda(Bu,v)+\epsilon\lambda(Bv,u)=0.
$$
Testing on $V_0\times V_0$ gives $D\in \mathfrak g_0$. This proves the block
description of $\mathfrak p$.

Now multiply block matrices:
$$
Yx_S=
\begin{pmatrix}
0&aS^\vee+T^\vee X_0&T^\vee S\\
0&DX_0&DS\\
0&0&0
\end{pmatrix},
$$
and
$$
x_SY=
\begin{pmatrix}
0&S^\vee D&S^\vee T\\
0&X_0D&X_0T-Sa^\vee\\
0&0&0
\end{pmatrix}.
$$
Subtracting gives
$$
[Y,x_S]
=
\begin{pmatrix}
0&aS^\vee+T^\vee X_0-S^\vee D&T^\vee S-S^\vee T\\
0&[D,X_0]&DS-X_0T+Sa^\vee\\
0&0&0
\end{pmatrix}.
$$
Since $D^\vee=-D$ and $X_0^\vee=-X_0$,
$$
(DS-X_0T+Sa^\vee)^\vee
=
S^\vee D^\vee-T^\vee X_0^\vee+(a^\vee)^\vee S^\vee
=
-S^\vee D+T^\vee X_0+aS^\vee,
$$
which is exactly the top-middle block. Hence the displayed formula follows,
and the three stated equations are equivalent to $[Y,x_S]=0$.

# proposition prop:projection-to-cL

## statement
Let
$$
\pi:\mathfrak z_{\mathfrak p}(x_S)\to \mathfrak z_{\mathfrak g_0}(X_0),
\qquad
\pi(Y)=D
$$
be the projection to the middle diagonal block. Then
$$
\pi\bigl(\mathfrak z_{\mathfrak p}(x_S)\bigr)=\mathfrak c_L
:=
\{D\in \mathfrak z_{\mathfrak g_0}(X_0):DL\subset L\}.
$$
More precisely:

1. If
   $$
   Y=
   \begin{pmatrix}
   a&T^\vee&B\\
   0&D&T\\
   0&0&-a^\vee
   \end{pmatrix}
   \in \mathfrak z_{\mathfrak p}(x_S),
   $$
   then $D\in \mathfrak c_L$, and $a$ is uniquely determined by
   $$
   a\,\phi_S=\phi_S D
   \qquad\text{on }\ker X_0.
   $$

2. Conversely, if $D\in \mathfrak c_L$, then there is a unique
   $a\in \operatorname{End}(E)$ satisfying
   $$
   a\,\phi_S=\phi_S D
   \qquad\text{on }\ker X_0,
   $$
   and for this $a$ the equation
   $$
   DS-X_0T+Sa^\vee=0
   $$
   has solutions $T:E'\to V_0$.

## proof
Let
$$
Y=
\begin{pmatrix}
a&T^\vee&B\\
0&D&T\\
0&0&-a^\vee
\end{pmatrix}
\in \mathfrak z_{\mathfrak p}(x_S).
$$
By Proposition `prop:block-form-and-commutator`,
$$
[D,X_0]=0,
\qquad
DS-X_0T+Sa^\vee=0.
$$
Take $v\in \ker X_0$ and $e'\in E'$. Pair the middle-right equation with $v$:
$$
0
=
\langle v,DSe'\rangle_0-\langle v,X_0Te'\rangle_0+\langle v,Sa^\vee e'\rangle_0.
$$
The middle term vanishes because $v\in \ker X_0=(\operatorname{Im}X_0)^\perp$.
Also, since $D\in \mathfrak g_0$,
$$
\langle v,DSe'\rangle_0
=
-\langle Dv,Se'\rangle_0
=
\lambda(\phi_S(Dv),e'),
$$
while
$$
\langle v,Sa^\vee e'\rangle_0
=
-\lambda(\phi_S(v),a^\vee e')
=
-\lambda(a\phi_S(v),e').
$$
Hence
$$
\lambda\bigl(\phi_S(Dv)-a\phi_S(v),e'\bigr)=0
\qquad (e'\in E'),
$$
so
$$
\phi_S(Dv)=a\phi_S(v)
\qquad (v\in \ker X_0).
$$
Therefore $DL\subset L$, because $L=\ker \phi_S$, and $a$ is the map induced by
$D$ on the quotient $\ker X_0/L\simeq E$. This proves (1).

Now assume conversely that $D\in \mathfrak c_L$. Since $\phi_S$ is surjective and
$D$ preserves $L=\ker \phi_S$, there is a unique
$a\in \operatorname{End}(E)$ with
$$
a\phi_S=\phi_S D
\qquad\text{on }\ker X_0.
$$
Set
$$
F:=DS+Sa^\vee:E'\to V_0.
$$
We claim that $\operatorname{Im} F\subset \operatorname{Im} X_0$. Indeed, for
$v\in \ker X_0$ and $e'\in E'$,
$$
\langle v,Fe'\rangle_0
=
\langle v,DSe'\rangle_0+\langle v,Sa^\vee e'\rangle_0
=
\lambda\bigl(\phi_S(Dv)-a\phi_S(v),e'\bigr)
=0.
$$
Thus $Fe'$ is orthogonal to $\ker X_0$, so by Lemma `lem:quotient-form`,
$$
Fe'\in (\ker X_0)^\perp=\operatorname{Im} X_0.
$$
Therefore the equation
$$
X_0T=F
$$
has at least one linear solution $T:E'\to V_0$. This proves (2).

# lemma lem:t-fiber

## statement
Fix $D\in \mathfrak c_L$, and let $a$ be the unique endomorphism of $E$
induced by $D$ on $\ker X_0/L$. Then the set of
$$
T:E'\to V_0
$$
satisfying
$$
DS-X_0T+Sa^\vee=0,
\qquad
T^\vee S-S^\vee T=0
$$
is a non-empty affine space of dimension
$$
\kappa d+\frac{\kappa(\kappa+\epsilon)}2.
$$

## proof
By Proposition `prop:projection-to-cL`, there exists at least one
$T_0:E'\to V_0$ such that
$$
X_0T_0=DS+Sa^\vee.
$$
For any map $U:E'\to \ker X_0$, the map $T=T_0+U$ still satisfies
$$
X_0T=DS+Sa^\vee.
$$
Thus the only remaining condition is
$$
U^\vee S-S^\vee U
=
-(T_0^\vee S-S^\vee T_0).
$$

Let
$$
\Gamma:\operatorname{Hom}(E',\ker X_0)\to \operatorname{Hom}(E',E),
\qquad
\Gamma(U)=U^\vee S-S^\vee U.
$$
We first describe $\Gamma$ explicitly. Choose a linear section
$$
\sigma:E\to \ker X_0
$$
of $\phi_S$. Then every $U:E'\to \ker X_0$ decomposes uniquely as
$$
U=U_L+\sigma M,
$$
with
$$
U_L:E'\to L,
\qquad
M:E'\to E.
$$
Since $L=\ker \phi_S$, one has
$$
S^\vee U_L=0,
\qquad
U_L^\vee S=0.
$$
Hence $\Gamma(U)=\Gamma(\sigma M)$.

For $u,v\in E'$,
$$
\lambda\bigl((S^\vee \sigma M)u,v\bigr)=\lambda(Mu,v),
$$
while
$$
\lambda\bigl((\sigma M)^\vee Su,v\bigr)
=
-\langle Su,\sigma Mv\rangle_0
=
-\epsilon\langle \sigma Mv,Su\rangle_0
=
\epsilon\lambda(Mv,u).
$$
Therefore
$$
\lambda\bigl(\Gamma(\sigma M)u,v\bigr)
=
\epsilon\lambda(Mv,u)-\lambda(Mu,v).
$$
Equivalently, after identifying maps $E'\to E$ with bilinear forms via
$\lambda$, $\Gamma$ is the linear operator
$$
b_M(u,v)\longmapsto \epsilon\,b_M(v,u)-b_M(u,v).
$$

Now the bilinear form corresponding to
$$
\eta:=T_0^\vee S-S^\vee T_0
$$
satisfies
$$
\lambda(\eta u,v)+\epsilon\lambda(\eta v,u)=0,
$$
because
$$
\lambda(T_0^\vee Su,v)
=
-\langle Su,T_0v\rangle_0,
\qquad
\lambda(S^\vee T_0u,v)
=
-\langle T_0u,Sv\rangle_0.
$$
So the right-hand side lies in the space of $(-\epsilon)$-symmetric bilinear
forms on $E'$.

Conversely, if $\eta:E'\to E$ corresponds to a $(-\epsilon)$-symmetric
bilinear form, then taking
$$
M=-\frac12\eta
$$
gives
$$
\Gamma(\sigma M)=\eta.
$$
Hence $\Gamma$ is surjective onto the space of $(-\epsilon)$-symmetric
bilinear forms on $E'$, so the inhomogeneous equation is solvable. Therefore
the set of admissible $T$ is a non-empty affine translate of $\ker \Gamma$.

Finally, $U\in \ker \Gamma$ if and only if the bilinear form
$$
b_M(u,v)=\lambda(Mu,v)
$$
is $\epsilon$-symmetric. Thus
$$
\ker \Gamma
\simeq
\operatorname{Hom}(E',L)
\oplus
\{\epsilon\text{-symmetric bilinear forms on }E'\}.
$$
Hence
$$
\dim \ker \Gamma
=
\kappa d+\frac{\kappa(\kappa+\epsilon)}2.
$$
This is the dimension of the $T$-solution space.

# proposition prop:centralizer-description

## statement
The centralizer is exactly the set of all
$$
Y=
\begin{pmatrix}
a&T^\vee&B\\
0&D&T\\
0&0&-a^\vee
\end{pmatrix}
$$
such that

1. $D\in \mathfrak c_L$;
2. $a$ is the unique endomorphism of $E$ satisfying
   $$
   a\phi_S=\phi_S D
   \qquad\text{on }\ker X_0;
   $$
3. $T$ is any solution of
   $$
   DS-X_0T+Sa^\vee=0,
   \qquad
   T^\vee S-S^\vee T=0;
   $$
4. $B:E'\to E$ is arbitrary subject only to
   $$
   \lambda(Bu,v)+\epsilon\lambda(Bv,u)=0
   \qquad (u,v\in E').
   $$

For each fixed $D\in \mathfrak c_L$, the $T$-solutions form an affine space of
dimension
$$
\kappa d+\frac{\kappa(\kappa+\epsilon)}2,
$$
and the $B$-block contributes the linear space of dimension
$$
\frac{\kappa(\kappa-\epsilon)}2.
$$
Consequently
$$
\dim \mathfrak z_{\mathfrak p}(x_S)
=
\dim \mathfrak c_L+\kappa d+\kappa^2.
$$

## proof
The characterization follows immediately by combining Proposition
`prop:block-form-and-commutator`, Proposition `prop:projection-to-cL`, and
Lemma `lem:t-fiber`.

The space of admissible $B$ is the space of $(-\epsilon)$-symmetric bilinear
forms on $E'$, so it has dimension
$$
\frac{\kappa(\kappa-\epsilon)}2.
$$
Adding this to the $T$-fiber dimension from Lemma `lem:t-fiber` gives
$$
\kappa d+\frac{\kappa(\kappa+\epsilon)}2+\frac{\kappa(\kappa-\epsilon)}2
=
\kappa d+\kappa^2.
$$
Since the map $Y\mapsto D$ has image $\mathfrak c_L$, the displayed dimension
formula follows.

# lemma lem:rho-surjective

## statement
Let
$$
\mathfrak z=\mathfrak z_{\mathfrak g_0}(X_0),
\qquad
\mathfrak h=\operatorname{Lie}\operatorname{Isom}(K_{X_0}),
$$
and let
$$
\rho:\mathfrak z\to \mathfrak h
$$
be the induced action on $K_{X_0}=\ker X_0/R$. Then $\rho$ is surjective.

## proof
For $u,v\in \ker X_0$, define the rank-two operator
$$
T_{u,v}(w)=u\langle v,w\rangle_0-\epsilon v\langle u,w\rangle_0.
$$
We first check that $T_{u,v}\in \mathfrak g_0$. For $x,y\in V_0$,
$$
\langle T_{u,v}x,y\rangle_0
=
\langle u,y\rangle_0\langle v,x\rangle_0
-\epsilon\langle v,y\rangle_0\langle u,x\rangle_0,
$$
while
$$
\langle x,T_{u,v}y\rangle_0
=
\langle x,u\rangle_0\langle v,y\rangle_0
-\epsilon\langle x,v\rangle_0\langle u,y\rangle_0
=
\epsilon\langle u,x\rangle_0\langle v,y\rangle_0
-\langle v,y\rangle_0\langle u,x\rangle_0
$$
Therefore
$$
\langle T_{u,v}x,y\rangle_0+\langle x,T_{u,v}y\rangle_0
=
\bigl(\langle u,y\rangle_0\langle v,x\rangle_0-\langle v,x\rangle_0\langle u,y\rangle_0\bigr)
+\bigl(-\epsilon\langle v,y\rangle_0\langle u,x\rangle_0+\epsilon\langle u,x\rangle_0\langle v,y\rangle_0\bigr)
=0,
$$
so $T_{u,v}\in \mathfrak g_0$.

Because $u,v\in \ker X_0$, the image of $T_{u,v}$ is contained in $\ker X_0$,
so
$$
X_0T_{u,v}=0.
$$
Also, for every $w\in V_0$,
$$
T_{u,v}(X_0w)
=
u\langle v,X_0w\rangle_0-\epsilon v\langle u,X_0w\rangle_0
=0,
$$
since $u,v\in \ker X_0$ and $X_0$ is skew-adjoint. Thus
$$
T_{u,v}X_0=0,
$$
and therefore $T_{u,v}\in \mathfrak z$.

If $\bar u,\bar v,\bar w$ denote the classes of $u,v,w$ in $K_{X_0}$, then
the induced operator is
$$
\rho(T_{u,v})(\bar w)
=
\bar u\,\langle \bar v,\bar w\rangle_K
-\epsilon \bar v\,\langle \bar u,\bar w\rangle_K.
$$
These are exactly the standard rank-two generators of the Lie algebra of a
non-degenerate $\epsilon$-symmetric space. In the symmetric case
($\epsilon=1$) they are the elementary wedges generating
$\mathfrak{so}(K_{X_0})$, and in the alternating case ($\epsilon=-1$) they are
the standard generators of $\mathfrak{sp}(K_{X_0})$. Hence they span
$\mathfrak h$, and $\rho$ is surjective.

# lemma lem:kernel-restriction-surjective

## statement
Let
$$
\mathfrak n=\ker \rho.
$$
Then the restriction map
$$
\mathfrak n\to \operatorname{Hom}(L,R),
\qquad
N\mapsto N|_L
$$
is surjective. Consequently
$$
\dim \ker(\mathfrak c_L\to \mathfrak h_A)
=
\dim \mathfrak n-dc_2.
$$

## proof
Fix $r_0\in R$ and $v\in \ker X_0$, and consider
$$
T_{r_0,v}(w)
=
r_0\langle v,w\rangle_0-\epsilon v\langle r_0,w\rangle_0.
$$
By the previous lemma, $T_{r_0,v}\in \mathfrak z$. We claim that
$T_{r_0,v}\in \mathfrak n$.

Indeed, if $\ell\in \ker X_0$, then $r_0\in R\subset \operatorname{Im}X_0$ and
$\ell\in \ker X_0=(\operatorname{Im}X_0)^\perp$, so
$$
\langle r_0,\ell\rangle_0=0.
$$
Therefore
$$
T_{r_0,v}(\ell)=r_0\langle v,\ell\rangle_0\in R,
$$
so the induced action on $K_{X_0}=\ker X_0/R$ is zero. Thus
$T_{r_0,v}\in \ker \rho=\mathfrak n$.

Now let $\alpha\in \operatorname{Hom}(L,R)$. Write
$$
\alpha(\ell)=\sum_{i=1}^{c_2}\alpha_i(\ell)\,r_i
$$
for a basis $r_1,\dots,r_{c_2}$ of $R$ and linear functionals
$\alpha_i\in L^\ast$. Since $L\cap R=0$, the quotient map $q:L\to A$ is an
isomorphism. The form on $K_{X_0}$ is non-degenerate, so each linear
functional on $A$ is represented by pairing with some class in $K_{X_0}$.
Thus for each $i$ there exists $v_i\in \ker X_0$ such that
$$
\alpha_i(\ell)=\langle v_i,\ell\rangle_0
\qquad (\ell\in L).
$$
Then
$$
N:=\sum_{i=1}^{c_2}T_{r_i,v_i}\in \mathfrak n
$$
satisfies, for $\ell\in L$,
$$
N(\ell)
=
\sum_{i=1}^{c_2}r_i\langle v_i,\ell\rangle_0
=
\sum_{i=1}^{c_2}\alpha_i(\ell)r_i
=
\alpha(\ell).
$$
So the restriction map $\mathfrak n\to \operatorname{Hom}(L,R)$ is surjective.

Its kernel is exactly the kernel of the map
$$
\mathfrak c_L\to \mathfrak h_A,
$$
because $N\in \mathfrak c_L$ maps to zero in $\mathfrak h_A$ precisely when
$N\in \mathfrak n$ and $N(L)\subset L$; since $N(L)\subset R$ for every
$N\in \mathfrak n$, and $L\cap R=0$, this means exactly $N|_L=0$. Hence
$$
\dim \ker(\mathfrak c_L\to \mathfrak h_A)
=
\dim \mathfrak n-\dim \operatorname{Hom}(L,R)
=
\dim \mathfrak n-dc_2.
$$

# proposition prop:cL-to-hA-surjective

## statement
The induced map
$$
\mathfrak c_L\to \mathfrak h_A,
\qquad
D\mapsto \rho(D)
$$
is surjective.

## proof
Take $u\in \mathfrak h_A$. By Lemma `lem:rho-surjective`, choose
$D_0\in \mathfrak z$ with
$$
\rho(D_0)=u.
$$
For $\ell\in L$, the class $q(\ell)$ lies in $A$, and since $uA\subset A$ we
have
$$
q(D_0\ell)=u(q(\ell))\in A=q(L).
$$
Choose a linear map $m:L\to L$ such that
$$
q(m(\ell))=u(q(\ell))
\qquad (\ell\in L).
$$
Then
$$
\alpha(\ell):=D_0\ell-m(\ell)\in R,
$$
so $\alpha\in \operatorname{Hom}(L,R)$. By Lemma
`lem:kernel-restriction-surjective`, there exists $N\in \mathfrak n$ with
$$
N|_L=-\alpha.
$$
Set
$$
D:=D_0+N.
$$
Then $\rho(D)=\rho(D_0)=u$, and for $\ell\in L$,
$$
D\ell=D_0\ell+N\ell=m(\ell)\in L.
$$
Thus $D\in \mathfrak c_L$, and the image of $D$ in $\mathfrak h_A$ is $u$.
So the map $\mathfrak c_L\to \mathfrak h_A$ is surjective.

# proposition prop:hA-dimension

## statement
Let
$$
n=\dim K_{X_0},
\qquad
d=\dim A,
\qquad
r=\dim \operatorname{rad}(\langle\,,\,\rangle_K|_A).
$$
Then
$$
\dim \mathfrak h_A
=
\frac{n(n-\epsilon)}2-d(n-d)+\frac{r(r+\epsilon)}2.
$$

## proof
Write
$$
U:=\operatorname{rad}(\langle\,,\,\rangle_K|_A),
\qquad
\dim U=r.
$$
Choose a complement $N$ of $U$ in $A$ such that the restricted form on $N$ is
non-degenerate. Then
$$
A=U\oplus N,
\qquad
\dim N=d-r.
$$
Choose an isotropic subspace $U'$ dual to $U$, and choose a non-degenerate
subspace $W$ such that
$$
K_{X_0}=U\oplus N\oplus W\oplus U'
$$
orthogonally, except for the perfect pairing between $U$ and $U'$. Then
$$
\dim W=n-d-r.
$$

With respect to this decomposition, an element of $\mathfrak h_A$ is exactly a
block matrix of the form
$$
\begin{pmatrix}
\alpha&\beta&\gamma&\delta\\
0&\eta&0&-\beta^\vee\\
0&0&\mu&-\gamma^\vee\\
0&0&0&-\alpha^\vee
\end{pmatrix},
$$
where
$$
\alpha\in \operatorname{End}(U),
\quad
\beta\in \operatorname{Hom}(N,U),
\quad
\gamma\in \operatorname{Hom}(W,U),
\quad
\eta\in \operatorname{Lie}\operatorname{Isom}(N),
\quad
\mu\in \operatorname{Lie}\operatorname{Isom}(W),
$$
and $\delta:U'\to U$ satisfies
$$
\lambda(\delta u',v')+\epsilon\lambda(\delta v',u')=0
\qquad (u',v'\in U').
$$

Indeed, the condition $uA\subset A$ forces the lower-left blocks to vanish.
Then skew-adjointness with respect to the form forces the displayed adjoint
relations and the $(-\epsilon)$-symmetry condition on $\delta$.

Therefore
$$
\dim \mathfrak h_A
=
\dim \operatorname{End}(U)
+\dim \operatorname{Hom}(N,U)
+\dim \operatorname{Hom}(W,U)
+\dim \operatorname{Lie}\operatorname{Isom}(N)
+\dim \operatorname{Lie}\operatorname{Isom}(W)
+\dim \{\delta\}.
$$
That is,
$$
\dim \mathfrak h_A
=
r^2+r(d-r)+r(n-d-r)
+\frac{(d-r)(d-r-\epsilon)}2
+\frac{(n-d-r)(n-d-r-\epsilon)}2
+\frac{r(r-\epsilon)}2.
$$
Now simplify. Since
$$
r^2+r(d-r)+r(n-d-r)=r(n-r),
$$
the right-hand side becomes
$$
r(n-r)+\frac{r(r-\epsilon)}2
+\frac{(d-r)(d-r-\epsilon)}2
+\frac{(n-d-r)(n-d-r-\epsilon)}2.
$$
A straightforward expansion shows that this is
$$
\frac{n(n-\epsilon)}2-d(n-d)+\frac{r(r+\epsilon)}2.
$$
This is the required formula.

# proposition prop:cL-dimension

## statement
One has
$$
\dim \mathfrak c_L
=
\dim \mathfrak z_{\mathfrak g_0}(X_0)
-dc_2-d(n-d)+\frac{r(r+\epsilon)}2.
$$

## proof
By Proposition `prop:cL-to-hA-surjective` and Lemma
`lem:kernel-restriction-surjective`,
$$
\dim \mathfrak c_L
=
\dim \ker(\mathfrak c_L\to \mathfrak h_A)+\dim \mathfrak h_A
=
\dim \mathfrak n-dc_2+\dim \mathfrak h_A.
$$
But
$$
\dim \mathfrak z_{\mathfrak g_0}(X_0)
=
\dim \mathfrak n+\dim \mathfrak h,
$$
and
$$
\dim \mathfrak h=\frac{n(n-\epsilon)}2.
$$
Using Proposition `prop:hA-dimension`, we obtain
$$
\dim \mathfrak c_L
=
\dim \mathfrak z_{\mathfrak g_0}(X_0)
-\frac{n(n-\epsilon)}2
-dc_2
+\left(
\frac{n(n-\epsilon)}2-d(n-d)+\frac{r(r+\epsilon)}2
\right),
$$
which simplifies to
$$
\dim \mathfrak c_L
=
\dim \mathfrak z_{\mathfrak g_0}(X_0)
-dc_2-d(n-d)+\frac{r(r+\epsilon)}2.
$$

# theorem thm:generic-normal-form-centralizer

## statement
## Setup
Let \(F=\mathbb R\). Let \((V_0,\langle\,,\,\rangle_0)\) be a non-degenerate
\(\epsilon\)-symmetric space, where \(\epsilon=1\) is the symmetric case and
\(\epsilon=-1\) is the alternating case. Let
\[
X_0\in\mathfrak g_0:=\operatorname{Lie}\operatorname{Isom}(V_0)
\]
be nilpotent. Set
\[
c_1:=\dim\ker X_0,\qquad
c_2:=\dim(\ker X_0\cap\operatorname{Im}X_0).
\]
Let \(E,E'\) be real vector spaces of dimension \(\kappa\), with perfect pairing
\[
\lambda:E\times E'\to\mathbb R,
\]
and assume
\[
c_2\le \kappa<c_1,\qquad d:=c_1-\kappa.
\]
Let
\[
V=E\oplus V_0\oplus E',
\qquad
G=\operatorname{Isom}(V),
\qquad
P=\operatorname{Stab}_G(E),
\qquad
\mathfrak p=\operatorname{Lie}(P),
\]
where the form on \(V\) is the orthogonal sum of \((V_0,\langle\,,\,\rangle_0)\)
and the hyperbolic pairing between \(E\) and \(E'\).

Put
\[
R:=\ker X_0\cap\operatorname{Im}X_0.
\]
Choose \(V_1\subset\ker X_0\) such that
\[
\ker X_0=V_1\oplus R.
\]
Choose an adapted complement
\[
V_0=V_+\oplus\operatorname{Im}X_0
\]
such that
\[
V_+\cap\ker X_0=V_1.
\]
Then
\[
\dim V_1=c_1-c_2,\qquad
\dim\bigl(V_+/V_1\bigr)=c_2.
\]

For \(S:E'\to V_+\), assume
\[
S \text{ is injective},\qquad
\bar S:E'\to V_+/(V_+\cap\ker X_0) \text{ is surjective}.
\]
Set
\[
K_{X_0}:=\ker X_0/R,
\]
and let \(q:\ker X_0\to K_{X_0}\) be the quotient map. The form on
\(\ker X_0\) induces a non-degenerate \(\epsilon\)-symmetric form
\(\langle\,,\,\rangle_K\) on \(K_{X_0}\).

Define
\[
\phi_S:=S^\vee|_{\ker X_0},\qquad
L:=\ker\phi_S,\qquad
A:=q(L)\subset K_{X_0}.
\]
The assumptions on \(S\) imply
\[
\dim L=d,\qquad L\cap R=0,\qquad \dim A=d.
\]
Set
\[
n:=\dim K_{X_0}=c_1-c_2,\qquad
r:=\dim\operatorname{rad}(\langle\,,\,\rangle_K|_A).
\]

Define
\[
x_S:=X_{S,0}
=
\begin{pmatrix}
0&S^\vee&0\\
0&X_0&S\\
0&0&0
\end{pmatrix}
\in\mathfrak p
\]
relative to \(V=E\oplus V_0\oplus E'\).

## Problem
Compute the Lie algebra centralizer
\[
\mathfrak z_{\mathfrak p}(x_S):=\{Y\in\mathfrak p:[Y,x_S]=0\}.
\]

More precisely:

1. Write a general element \(Y\in\mathfrak p\) in block form relative to
   \[
   V=E\oplus V_0\oplus E'
   \]
   and compute \([Y,x_S]\) explicitly.

2. Solve the resulting block equations completely enough to describe
   \(\mathfrak z_{\mathfrak p}(x_S)\).

3. Show that the \(B\)- and \(T\)-block freedoms contribute only a
   constant-dimensional linear space, independent of the rank of
   \(\langle\,,\,\rangle_K|_A\).

4. Let
   \[
   \mathfrak z:=\mathfrak z_{\mathfrak g_0}(X_0),\qquad
   \mathfrak h:=\operatorname{Lie}\operatorname{Isom}(K_{X_0}),
   \]
   and let
   \[
   \rho:\mathfrak z\to\mathfrak h
   \]
   be the map induced by the action of \(\mathfrak z\) on
   \(K_{X_0}=\ker X_0/R\). Define
   \[
   \mathfrak c_L
   :=
   \{D\in\mathfrak z_{\mathfrak g_0}(X_0):DL\subset L\},
   \qquad
   \mathfrak h_A
   :=
   \{u\in\mathfrak h:uA\subset A\}.
   \]
   Prove that \(\rho\) is surjective and that the induced map
   \[
   \mathfrak c_L\to\mathfrak h_A
   \]
   is surjective.

5. Prove the constant-fiber calculation for
   \(\mathfrak c_L\to\mathfrak h_A\). If
   \[
   \mathfrak n:=\ker\rho,
   \]
   then the restriction map
   \[
   \mathfrak n\to\operatorname{Hom}(L,R),\qquad N\mapsto N|_L
   \]
   is surjective, and hence
   \[
   \dim\ker(\mathfrak c_L\to\mathfrak h_A)
   =
   \dim\mathfrak n-dc_2.
   \]
   In particular the fiber dimension of
   \[
   \mathfrak c_L\to\mathfrak h_A
   \]
   is independent of the rank of \(\langle\,,\,\rangle_K|_A\).

   A useful way to prove the required surjectivity is to use rank-two
   operators: for \(r_0\in R\) and \(v\in\ker X_0\), set
   \[
   T_{r_0,v}(w)
   =
   r_0\langle v,w\rangle_0-\epsilon v\langle r_0,w\rangle_0.
   \]
   Show that \(T_{r_0,v}\in\ker\rho\), and that these operators realize all
   maps \(K_{X_0}\to R\), hence all maps \(L\to R\) because \(L\cap R=0\).

6. Deduce the dimension formula
   \[
   \dim\mathfrak c_L
   =
   \dim\mathfrak z_{\mathfrak g_0}(X_0)
   -dc_2-d(n-d)+\frac{r(r+\epsilon)}2.
   \]

   For this, compute
   \[
   \dim\mathfrak h_A
   =
   \frac{n(n-\epsilon)}2-d(n-d)+\frac{r(r+\epsilon)}2.
   \]
   One direct route is to compute the dimension of the \(H\)-orbit of \(A\),
   where \(H=\operatorname{Isom}(K_{X_0})\). The stratum of \(d\)-planes in
   \(K_{X_0}\) whose restricted form has radical dimension \(r\) has dimension
   \[
   d(n-d)-\frac{r(r+\epsilon)}2.
   \]

7. Deduce that \(\dim\mathfrak z_{\mathfrak p}(x_S)\) is minimal exactly when
   \(\langle\,,\,\rangle_K|_A\) has maximal possible rank. Equivalently, the
   radical dimension \(r\) is minimal: \(r=0\) in the symmetric case, and in
   the alternating case \(r=0\) for even \(d\) and \(r=1\) for odd \(d\).

## Exclusions
Do not use signed Young diagrams, component groups, multiplicities, or
defect-space language.

Do not use SymPy, Sage, Mathematica, computer algebra, or any machine algebra
check in the proof. In particular, do not use Python or any other programming
language to verify dimension identities, ranks, or linear-algebra formulas.
All dimension identities and linear algebra calculations must be proved by
hand in the Rethlas proof. Rethlas infrastructure tools for memory, search, and
verification may still be used when required by AGENTS.md, but they must not
serve as mathematical evidence.

## proof
Assertion (1) is exactly Proposition `prop:block-form-and-commutator`.

For (2), Proposition `prop:projection-to-cL` shows that the projection to the
$D$-block maps $\mathfrak z_{\mathfrak p}(x_S)$ onto
$$
\mathfrak c_L=\{D\in \mathfrak z_{\mathfrak g_0}(X_0):DL\subset L\},
$$
and that for each $D\in \mathfrak c_L$ there is a unique $a\in \operatorname{End}(E)$
with
$$
a\phi_S=\phi_S D
\qquad\text{on }\ker X_0.
$$
For this $a$, the admissible $T$ are exactly the solutions of
$$
DS-X_0T+Sa^\vee=0,
\qquad
T^\vee S-S^\vee T=0,
$$
and $B$ is otherwise unrestricted except for the intrinsic skew-adjointness
condition
$$
\lambda(Bu,v)+\epsilon\lambda(Bv,u)=0.
$$
Therefore
$$
\mathfrak z_{\mathfrak p}(x_S)
=
\left\{
\begin{pmatrix}
a&T^\vee&B\\
0&D&T\\
0&0&-a^\vee
\end{pmatrix}
:
D\in \mathfrak c_L,\ a\phi_S=\phi_S D,\ T \text{ as above},\ B \text{ admissible}
\right\}.
$$

Assertion (3) is Proposition `prop:centralizer-description`: for each fixed
$D\in \mathfrak c_L$, the $T$-solutions form an affine space of dimension
$$
\kappa d+\frac{\kappa(\kappa+\epsilon)}2,
$$
while the $B$-block contributes the linear space of dimension
$$
\frac{\kappa(\kappa-\epsilon)}2.
$$
So the combined $T$- and $B$-freedom has constant dimension
$$
\kappa d+\kappa^2,
$$
independent of the rank of $\langle\,,\,\rangle_K|_A$.

Assertion (4) follows from Lemma `lem:rho-surjective` and Proposition
`prop:cL-to-hA-surjective`.

Assertion (5) is Lemma `lem:kernel-restriction-surjective`, which gives
$$
\dim\ker(\mathfrak c_L\to \mathfrak h_A)=\dim\mathfrak n-dc_2.
$$
In particular the fiber dimension is constant, and therefore independent of
the rank of $\langle\,,\,\rangle_K|_A$.

Assertion (6) is Proposition `prop:cL-dimension`, together with Proposition
`prop:hA-dimension`. Combining Proposition `prop:cL-dimension` with
Proposition `prop:centralizer-description`, we get
$$
\dim \mathfrak z_{\mathfrak p}(x_S)
=
\dim \mathfrak c_L+\kappa d+\kappa^2
$$
and therefore
$$
\dim \mathfrak z_{\mathfrak p}(x_S)
=
\dim \mathfrak z_{\mathfrak g_0}(X_0)
-dc_2-d(n-d)+\frac{r(r+\epsilon)}2+\kappa d+\kappa^2.
$$
Now
$$
n-d=(c_1-c_2)-(c_1-\kappa)=\kappa-c_2,
$$
so
$$
dc_2+d(n-d)=d\kappa.
$$
Hence
$$
\dim \mathfrak z_{\mathfrak p}(x_S)
=
\dim \mathfrak z_{\mathfrak g_0}(X_0)+\kappa^2+\frac{r(r+\epsilon)}2.
$$

Finally, for (7), the only term depending on $A$ is
$$
\frac{r(r+\epsilon)}2.
$$
So $\dim \mathfrak z_{\mathfrak p}(x_S)$ is minimal exactly when $r$ is
minimal. Since
$$
\operatorname{rank}(\langle\,,\,\rangle_K|_A)=d-r,
$$
this is equivalent to maximal possible rank of the restricted form.

If $\epsilon=1$, the restricted form is symmetric, so the minimal possible
radical dimension is $r=0$.

If $\epsilon=-1$, the restricted form is alternating, so its rank must be
even. Equivalently, $d-r$ is even, or
$$
r\equiv d \pmod 2.
$$
Therefore the minimal possible $r$ is
$$
r=0 \quad\text{if $d$ is even},
\qquad
r=1 \quad\text{if $d$ is odd}.
$$
This proves the theorem.
