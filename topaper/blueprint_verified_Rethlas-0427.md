# lemma lem:x0-geometry

## statement
One has
$$
(\operatorname{Im} X_0)^\perp=\ker X_0.
$$
Hence
$$
\dim(V_0/\operatorname{Im} X_0)=\dim \ker X_0=c,
$$
the quotient map identifies the fixed complement $V_+$ with $V_0/\operatorname{Im} X_0$, and the pairing
$$
V_+\times \ker X_0 \to F,\qquad (v,w)\mapsto \langle v,w\rangle_0
$$
is perfect. In particular, for every isomorphism $S:L'_1\xrightarrow{\sim}V_+$, the restriction
$$
S^\vee|_{\ker X_0}:\ker X_0\xrightarrow{\sim}L_1
$$
is an isomorphism.


## proof
If $w\in \ker X_0$ and $y=X_0 z\in \operatorname{Im} X_0$, then
$$
\langle w,y\rangle_0=\langle w,X_0 z\rangle_0=-\langle X_0 w,z\rangle_0=0,
$$
so $w\in (\operatorname{Im} X_0)^\perp$. Therefore
$$
\ker X_0\subseteq (\operatorname{Im} X_0)^\perp.
$$

Now
$$
\dim (\operatorname{Im} X_0)^\perp
=\dim V_0-\dim \operatorname{Im} X_0
=\dim \ker X_0,
$$
so the inclusion above is an equality:
$$
(\operatorname{Im} X_0)^\perp=\ker X_0.
$$

Since $V_0=V_+\oplus \operatorname{Im} X_0$, the quotient map $V_0\to V_0/\operatorname{Im} X_0$ identifies $V_+$ with $V_0/\operatorname{Im} X_0$, hence $\dim V_+=c$. The equality $(\operatorname{Im} X_0)^\perp=\ker X_0$ says exactly that the induced pairing
$$
(V_0/\operatorname{Im} X_0)\times \ker X_0\to F
$$
is non-degenerate, so the pairing $V_+\times \ker X_0\to F$ is perfect.

Finally, by definition,
$$
\lambda(S^\vee v,a')=-\langle v,Sa'\rangle_0.
$$
If $v\in \ker X_0$ and $S^\vee v=0$, then $\langle v,Sa'\rangle_0=0$ for every $a'\in L'_1$. Since $S(L'_1)=V_+$ and the pairing $V_+\times \ker X_0$ is perfect, this forces $v=0$. Because both spaces have dimension $c$, $S^\vee|_{\ker X_0}$ is an isomorphism.

# lemma lem:parametrize-x0-plus-u

## statement
For $C\in \operatorname{Hom}_F(E',V_0)$ let $C^\vee:V_0\to E$ be defined by
$$
\lambda(C^\vee v,e')=-\langle v,Ce'\rangle_0.
$$
For $B\in \operatorname{Hom}_F(E',E)$ satisfying
$$
\lambda(Bu,v)+\epsilon \lambda(Bv,u)=0
\qquad (u,v\in E'),
$$
define
$$
X_{C,B}(e+v+e'):=C^\vee v+Be'+X_0 v+Ce'.
$$
Then $X_{C,B}\in X_0+\mathfrak u$.

Conversely, every element of $X_0+\mathfrak u$ is uniquely of the form $X_{C,B}$.

In particular, for the special choice
$$
C|_{L'_1}=S,\qquad C|_{L'_0}=0,\qquad B|_{L'_1}=0,\qquad B|_{L'_0}=T,
$$
one gets exactly the operator $X_{S,T}$ from the problem statement.

## proof
Relative to the decomposition $V=E\oplus V_0\oplus E'$, an element $Y\in \mathfrak u$ has the shape
$$
Y=
\begin{pmatrix}
0&A&B\\
0&0&C\\
0&0&0
\end{pmatrix}
$$
with $A:V_0\to E$, $B:E'\to E$, $C:E'\to V_0$. The condition $Y\in \mathfrak g$ is equivalent to skew-adjointness:
$$
\langle Yx,y\rangle+\langle x,Yy\rangle=0.
$$
Testing this on $(v,e')\in V_0\times E'$ gives
$$
\lambda(Av,e')+\langle v,Ce'\rangle_0=0,
$$
so $A=C^\vee$. Testing it on $(u,v)\in E'\times E'$ gives
$$
\lambda(Bu,v)+\epsilon \lambda(Bv,u)=0.
$$
Thus every $Y\in \mathfrak u$ is uniquely $Y_{C,B}$ with
$$
Y_{C,B}(e+v+e')=C^\vee v+Be'+Ce'.
$$
Hence every element of $X_0+\mathfrak u$ is uniquely
$$
X_0+Y_{C,B}=X_{C,B}.
$$

Now $X_{C,B}-X_0=Y_{C,B}$ certainly annihilates $E$, maps $E^\perp=E\oplus V_0$ into $E$, and maps $V$ into $E^\perp$, so $Y_{C,B}\in \mathfrak u$. Therefore $X_{C,B}\in X_0+\mathfrak u$.

Taking $C$ and $B$ as in the statement gives exactly the formula
$$
X_{S,T}(e+v+a'+b')=(S^\vee v+Tb')+(X_0v+Sa')
$$
from the problem statement. This proves assertion (1) of the problem.

# lemma lem:unipotent-conjugation

## statement
For $D\in \operatorname{Hom}_F(E',V_0)$ define
$$
u_D(e+v+e')
:=\left(e+D^\vee v+\frac12 D^\vee D\,e'\right)+(v+De')+e'.
$$
Then $u_D\in P$. Moreover, for every pair $(C,B)$ as above,
$$
u_D\,X_{C,B}\,u_D^{-1}
=X_{C-X_0D,\;B+D^\vee C-C^\vee D-D^\vee X_0D}.
$$

## proof
In block form,
$$
u_D=
\begin{pmatrix}
1&D^\vee&\frac12 D^\vee D\\
0&1&D\\
0&0&1
\end{pmatrix}.
$$
To check that $u_D$ preserves the form, it is enough to test it on pairs involving the $E'$-summand. For $u,v\in E'$ one gets
$$
\lambda\!\left(\frac12 D^\vee D\,u,v\right)
+\epsilon \lambda\!\left(\frac12 D^\vee D\,v,u\right)
+\langle Du,Dv\rangle_0
=-\frac12\langle Du,Dv\rangle_0-\frac{\epsilon}{2}\langle Dv,Du\rangle_0+\langle Du,Dv\rangle_0=0,
$$
because $\langle Dv,Du\rangle_0=\epsilon\langle Du,Dv\rangle_0$. The mixed $(V_0,E')$-terms cancel by the defining property of $D^\vee$. Hence $u_D\in P$.

Also
$$
X_{C,B}=
\begin{pmatrix}
0&C^\vee&B\\
0&X_0&C\\
0&0&0
\end{pmatrix}.
$$
Multiplying the two block matrices and simplifying gives
$$
u_D\,X_{C,B}\,u_D^{-1}
=
\begin{pmatrix}
0&(C-X_0D)^\vee&B+D^\vee C-C^\vee D-D^\vee X_0D\\
0&X_0&C-X_0D\\
0&0&0
\end{pmatrix},
$$
which is the stated formula.

# proposition prop:p-normal-form

## statement
Let $x=X_{C,B}\in X_0+\mathfrak u$, and let
$$
\overline C:E'\to V_0/\operatorname{Im} X_0\simeq V_+
$$
be the composition of $C$ with the quotient map.

Assume that $\operatorname{rank}\overline C=c$. Then $x$ is $P$-conjugate to some $X_{S,T}$ with $T\in \mathscr T$.

More precisely:

1. After $P$-conjugation one may arrange
   $$
   C|_{L'_1}=S,\qquad C|_{L'_0}=0.
   $$
2. Keeping this $C$ fixed, one may further $P$-conjugate so that all $B$-blocks involving $L'_1$ vanish, and the remaining $L'_0\to L_0$ block is some $T\in \mathscr T$.
3. The residual action of the Levi factor on the $L_0\oplus L'_0$-block is
   $$
   T\longmapsto (h^{-1})^\vee T h
   \qquad (h\in \operatorname{GL}(L'_0)),
   $$
   so the resulting $P$-orbit is determined exactly by the isometry class of the bilinear space $(L'_0,B_T)$.

## proof
Because $\operatorname{rank}\overline C=c=\dim(V_0/\operatorname{Im} X_0)$, the map $\overline C$ is surjective and $\ker \overline C$ has dimension $l$. By a Levi element of $P$ acting through $\operatorname{GL}(E')$, we may assume
$$
\ker \overline C=L'_0.
$$
Then $\overline C|_{L'_1}:L'_1\to V_0/\operatorname{Im} X_0\simeq V_+$ is an isomorphism. Using another Levi element on $L'_1$, we may assume that this quotient map is exactly the fixed isomorphism induced by $S:L'_1\to V_+$.

Now $C-S$ takes values in $\operatorname{Im} X_0$, so there exists $D:E'\to V_0$ with
$$
X_0D=C-S.
$$
By Lemma `lem:unipotent-conjugation`, conjugation by $u_D$ replaces $C$ by
$$
C-X_0D=S,
$$
that is,
$$
C|_{L'_1}=S,\qquad C|_{L'_0}=0.
$$

We now keep this $C$ fixed and write $B$ in blocks:
$$
B=
\begin{pmatrix}
B_{11}&B_{10}\\
B_{01}&B_{00}
\end{pmatrix}
:
L'_1\oplus L'_0\to L_1\oplus L_0.
$$
Take first $D_0:L'_0\to \ker X_0$. Because the pairing $V_+\times \ker X_0$ is perfect, the map
$$
D_0\longmapsto (D_0^\vee S):L'_1\to L_0
$$
is an isomorphism
$$
\operatorname{Hom}(L'_0,\ker X_0)\xrightarrow{\sim}\operatorname{Hom}(L'_1,L_0).
$$
Hence we may choose $D_0$ so that the $L'_1\to L_0$ block of $B+D_0^\vee C-C^\vee D_0$ is zero. After that, the skew relation
$$
\lambda(Bu,v)+\epsilon \lambda(Bv,u)=0
$$
forces the opposite block $B_{10}:L'_0\to L_1$ to vanish as well.

Next take $D_1:L'_1\to \ker X_0$. Let
$$
b_{11}(u,v):=\lambda(B_{11}u,v).
$$
Then $b_{11}(v,u)=-\epsilon b_{11}(u,v)$. Again by the perfect pairing $V_+\times \ker X_0$, there is a unique $D_1$ such that
$$
\langle Su,D_1v\rangle_0=\frac12\,b_{11}(u,v)
\qquad (u,v\in L'_1).
$$
For this choice one computes
$$
\lambda\!\left((B_{11}+D_1^\vee S-S^\vee D_1)u,v\right)
=b_{11}(u,v)-\frac12 b_{11}(u,v)+\frac{\epsilon}{2}b_{11}(v,u)=0,
$$
so the new $L'_1\to L_1$ block also vanishes.

Therefore, after these conjugations, only the $L'_0\to L_0$ block survives. Call it $T$. The skew relation on $B$ becomes exactly
$$
\lambda(Tu,v)+\epsilon \lambda(Tv,u)=0,
$$
so $T\in \mathscr T$, and the resulting element is precisely $X_{S,T}$.

Finally, if $h\in \operatorname{GL}(L'_0)$ and the Levi element acts on $L_0$ by $(h^{-1})^\vee$, then it sends $T$ to $(h^{-1})^\vee T h$. This is exactly the change of coordinates on the bilinear form
$$
B_T(u,v)=\lambda(Tu,v),
$$
so isometric residual forms give $P$-conjugate normalized representatives.

Conversely, suppose
$$
pX_{S,T_1}p^{-1}=X_{S,T_2}
$$
for some $p\in P$. Write $p=u_Dm$ with $u_D$ as in Lemma `lem:unipotent-conjugation` and $m$ in the Levi factor of $P$. Write $m$ on $E'$ as $d\in \operatorname{GL}(E')$, on $V_0$ as $g_0\in G_0$, and on $E$ as $(d^{-1})^\vee$. A direct block calculation gives
$$
mX_{C,B}m^{-1}=X_{g_0Cd^{-1},\,(d^{-1})^\vee Bd^{-1}}.
$$
For the normalized $C$-block
$$
C_0|_{L'_1}=S,\qquad C_0|_{L'_0}=0,
$$
the quotient class $\overline{C_0}:E'\to V_0/\operatorname{Im}X_0$ has kernel exactly $L'_0$. Since unipotent conjugation changes $C$ by
$$
C\longmapsto C-X_0D,
$$
it does not change $\overline C$. Hence $m$ must preserve $\ker \overline{C_0}=L'_0$; write
$$
h:=d|_{L'_0}\in \operatorname{GL}(L'_0).
$$

Let
$$
C':=g_0C_0d^{-1}.
$$
Since both $C'$ and the final normalized block $C_0$ have kernel $L'_0$, we have
$$
C'|_{L'_0}=0,\qquad (C'-C_0)|_{L'_0}=0.
$$
But $C'-C_0=X_0D$, so
$$
X_0D(L'_0)=0,
$$
hence $D(L'_0)\subseteq \ker X_0$. Lemma `lem:unipotent-conjugation` shows that $u_D$ changes $B$ by
$$
B\longmapsto B+D^\vee C'-{C'}^\vee D-D^\vee X_0D.
$$
When restricted to the source $L'_0$, the first term $D^\vee C'$ is zero because $C'|_{L'_0}=0$, and the last term $D^\vee X_0D$ is zero because $X_0D(L'_0)=0$. For the middle term, if $w\in \ker X_0$, then ${C'}^\vee w\in L_1$ because $C'$ vanishes on $L'_0$, so ${C'}^\vee D(L'_0)\subseteq L_1$. Therefore the whole correction term has zero $L'_0\to L_0$ block. Thus the unipotent factor does not change the residual $L'_0\to L_0$ block at all.

It follows that for a normalized representative, the only effect on the residual block $T$ comes from the Levi factor, namely
$$
T\longmapsto (h^{-1})^\vee T h.
$$
Since $pX_{S,T_1}p^{-1}=X_{S,T_2}$ and both sides are normalized, we get
$$
T_2=(h^{-1})^\vee T_1 h.
$$
Equivalently, $(L'_0,B_{T_1})$ and $(L'_0,B_{T_2})$ are isometric. Thus two normalized representatives are $P$-conjugate if and only if their residual bilinear spaces are isometric.

# proposition prop:kernel-image

## statement
For every $S$ and every $T\in \mathscr T$ one has
$$
\ker X_{S,T}=E\oplus \ker T,
$$
and
$$
\operatorname{Im} X_{S,T}=(L_1\oplus \operatorname{Im} T)\oplus V_0.
$$
Hence
$$
\dim \ker X_{S,T}=r+(l-\operatorname{rank} T).
$$

## proof
Take
$$
x=e+v+a'+b'\in E\oplus V_0\oplus L'_1\oplus L'_0.
$$
Then
$$
X_{S,T}x=(S^\vee v+Tb')+(X_0v+Sa').
$$
If $X_{S,T}x=0$, then the $V_0$-component gives
$$
X_0v+Sa'=0.
$$
Since $X_0v\in \operatorname{Im} X_0$ and $Sa'\in V_+$, and $V_0=V_+\oplus \operatorname{Im} X_0$, both terms must vanish:
$$
a'=0,\qquad v\in \ker X_0.
$$
Then the $E$-component becomes
$$
S^\vee v+Tb'=0.
$$
Now $S^\vee v\in L_1$ and $Tb'\in L_0$, so again each term is zero. By Lemma `lem:x0-geometry`, $S^\vee|_{\ker X_0}$ is injective, hence $v=0$, and therefore $b'\in \ker T$.

So indeed
$$
\ker X_{S,T}=E\oplus \ker T.
$$

For the image, we first prove the reverse inclusion
$$
(L_1\oplus \operatorname{Im} T)\oplus V_0\subseteq \operatorname{Im} X_{S,T}.
$$
Indeed, if $y\in V_+$, then $y=Sa'$ for some $a'\in L'_1$, and
$$
X_{S,T}(a')=y.
$$
If $y\in \operatorname{Im} X_0$, choose $v\in V_0$ with $X_0v=y$. By Lemma `lem:x0-geometry`, the map
$$
S^\vee|_{\ker X_0}:\ker X_0\xrightarrow{\sim}L_1
$$
is surjective, so there exists $k\in \ker X_0$ with
$$
S^\vee k=S^\vee v.
$$
Then
$$
X_{S,T}(v-k)=\bigl(S^\vee v-S^\vee k\bigr)+\bigl(X_0v-X_0k\bigr)=y.
$$
Since $V_0=V_+\oplus \operatorname{Im} X_0$, this proves
$$
V_0\subseteq \operatorname{Im} X_{S,T}.
$$
Also, if $e_1\in L_1$, choose $k\in \ker X_0$ with $S^\vee k=e_1$; then
$$
X_{S,T}(k)=e_1.
$$
Thus $L_1\subseteq \operatorname{Im} X_{S,T}$, and clearly
$$
X_{S,T}(L'_0)=\operatorname{Im} T,
$$
so $\operatorname{Im} T\subseteq \operatorname{Im} X_{S,T}$ as well.

Conversely, every value of $X_{S,T}$ has the form
$$
\bigl(S^\vee v+Tb'\bigr)+\bigl(X_0v+Sa'\bigr),
$$
whose $E$-component lies in $L_1\oplus \operatorname{Im} T$ and whose $V_0$-component lies in $V_0$. Therefore
$$
\operatorname{Im} X_{S,T}\subseteq (L_1\oplus \operatorname{Im} T)\oplus V_0.
$$
Hence
$$
\operatorname{Im} X_{S,T}=(L_1\oplus \operatorname{Im} T)\oplus V_0.
$$
The dimension formula follows immediately.

# lemma lem:local-form-classes

## statement
The maximal-rank forms occurring in $\mathscr T^\circ$ have only finitely many isometry classes over the allowed fields, and each isometry class is open in $\mathscr T^\circ$.

More precisely:

1. If $\epsilon=+1$, then $B_T$ is alternating of maximal rank, and its isometry class is unique.
2. If $\epsilon=-1$ and $F=\mathbb R$, then $B_T$ is a non-degenerate symmetric form, classified by its signature; therefore there are finitely many isometry classes, and each class is open in the non-degenerate locus.
3. If $\epsilon=-1$ and $F$ is non-archimedean of characteristic $0$, then $B_T$ is a non-degenerate symmetric form, classified by the determinant modulo $F^{\times 2}$ and the Hasse invariant; therefore there are finitely many isometry classes, and each class is open in the non-degenerate locus.

## proof
If $\epsilon=+1$, then $B_T$ is alternating. On an even-dimensional space there is only one non-degenerate alternating form up to isometry, and on an odd-dimensional space there is only one alternating form of rank $l-1$ up to isometry: in a suitable basis it is the standard symplectic form on a $2m$-dimensional subspace and $0$ on the radical line.

Now suppose $\epsilon=-1$, so $B_T$ is symmetric and non-degenerate on $L'_0$.

If $F=\mathbb R$, Sylvester's law of inertia gives the classification by signature $(p,q)$ with $p+q=l$. There are only finitely many such signatures, and the signature is unchanged under sufficiently small perturbations inside the non-degenerate locus, so each class is open.

If $F$ is non-archimedean of characteristic $0$, the standard local classification of non-degenerate quadratic forms gives: a symmetric form of dimension $l$ is determined up to isometry by its determinant in $F^\times/F^{\times 2}$ and its Hasse invariant. Both invariants take only finitely many values, and both are locally constant on the non-degenerate locus. Hence there are finitely many isometry classes, each open.

# proposition prop:induced-orbits

## statement
The induced $G$-orbits in $\operatorname{Ind}_P^G(\mathcal O_0)$ are exactly the orbits
$$
G\cdot X_{S,T}\qquad (T\in \mathscr T^\circ),
$$
for any fixed choice of isomorphism $S:L'_1\xrightarrow{\sim}V_+$.

## proof
Embed $G_0$ into the Levi factor of $P$ by
$$
\iota(g_0)(e+v+e'):=e+g_0v+e'.
$$
Then $\iota(g_0)\in P$, and
$$
\iota(g_0)X_0\iota(g_0)^{-1}=g_0X_0g_0^{-1}.
$$
Also $\mathfrak u$ is $P$-stable: if $p\in P$, then $p(E)=E$ and $p(E^\perp)=E^\perp$, so the defining conditions
$$
Y(E)=0,\qquad Y(E^\perp)\subseteq E,\qquad Y(V)\subseteq E^\perp
$$
are preserved by $\operatorname{Ad}(p)$. Therefore
$$
\mathcal O_0+\mathfrak u
=\bigcup_{g_0\in G_0}\bigl(\iota(g_0)X_0\iota(g_0)^{-1}+\mathfrak u\bigr)
=\iota(G_0)\cdot (X_0+\mathfrak u),
$$
and hence
$$
G\cdot(\mathcal O_0+\mathfrak u)=G\cdot(X_0+\mathfrak u).
$$
So
$$
\operatorname{Ind}_P^G(\mathcal O_0)=\overline{G\cdot(X_0+\mathfrak u)}.
$$

We next isolate the open dense part of the slice $X_0+\mathfrak u$. Via Lemma `lem:parametrize-x0-plus-u`, write points of the slice uniquely as
$$
x=X_{C,B}.
$$
Let
$$
U:=\{X_{C,B}\in X_0+\mathfrak u:\operatorname{rank}\overline C=c\}.
$$
Since $\overline C:E'\to V_0/\operatorname{Im} X_0$ has target dimension $c$, the condition
$$
\operatorname{rank}\overline C=c
$$
is open and dense, so $U$ is open dense in $X_0+\mathfrak u$.

Define
$$
\Omega:=\bigcup_{T\in\mathscr T^\circ}P\cdot X_{S,T}\subseteq X_0+\mathfrak u.
$$
We claim that $\Omega$ is open dense in $X_0+\mathfrak u$.

To prove openness, cover $U$ by finitely many standard minor charts. Fix a basis of $E'$ adapted to
$$
E'=L'_1\oplus L'_0.
$$
For each $c$-element subset $I$ of that basis, let $U_I\subseteq U$ be the locus where the images under $\overline C$ of the basis vectors indexed by $I$ form a basis of
$$
V_0/\operatorname{Im} X_0\simeq V_+.
$$
Then
$$
U=\bigcup_I U_I,
$$
with finitely many $I$, and each $U_I$ is open.

On $U_I$, the normalization procedure of Proposition `prop:p-normal-form` can be carried out with a Levi element depending rationally on $C$: first send the span of the basis vectors indexed by $I$ to $L'_1$, then use the quotient map to identify it with the fixed isomorphism
$$
S:L'_1\xrightarrow{\sim}V_+,
$$
and finally apply the explicit unipotent corrections from Proposition `prop:p-normal-form`. The output is a rational map
$$
T_I:U_I\to \mathscr T
$$
such that every $x\in U_I$ is $P$-conjugate to
$$
X_{S,T_I(x)}.
$$
By item (3) of Proposition `prop:p-normal-form`, two points of $U_I$ lie in the same $P$-orbit exactly when their residual forms are isometric; in particular,
$$
\Omega\cap U_I=\{x\in U_I:\operatorname{rank}T_I(x)\text{ is maximal}\}.
$$
Since $\mathscr T^\circ$ is open in $\mathscr T$, each $\Omega\cap U_I$ is open in $U_I$. Because the cover by the $U_I$ is finite, $\Omega$ is open in $U$, hence open in $X_0+\mathfrak u$.

To prove density, let $x\in U$. By Proposition `prop:p-normal-form`, $x$ is $P$-conjugate to some $X_{S,T}$ with $T\in\mathscr T$. Since $\mathscr T^\circ$ is dense in $\mathscr T$, choose a net (or sequence) $T_\nu\in\mathscr T^\circ$ with
$$
T_\nu\to T.
$$
Then
$$
X_{S,T_\nu}\to X_{S,T},
$$
and after conjugating by the fixed element of $P$ carrying $X_{S,T}$ to $x$, we get points of $\Omega$ converging to $x$. Thus $\Omega$ is dense in $U$, and since $U$ is dense in $X_0+\mathfrak u$, $\Omega$ is dense in the whole slice.

Consequently
$$
G\cdot\Omega=\bigcup_{g\in G} g\Omega
$$
is open dense in
$$
G\cdot(X_0+\mathfrak u)=\bigcup_{g\in G} g(X_0+\mathfrak u),
$$
because each translate $g\Omega$ is open dense in $g(X_0+\mathfrak u)$. Therefore
$$
\operatorname{Ind}_P^G(\mathcal O_0)
=\overline{G\cdot(X_0+\mathfrak u)}
=\overline{G\cdot\Omega}.
$$

By Lemma `lem:local-form-classes`, there are only finitely many isometry classes of maximal-rank forms on $L'_0$. Choose representatives
$$
T_1,\dots,T_N\in \mathscr T^\circ
$$
for these classes, and set
$$
\Omega_i:=P\cdot X_{S,T_i}
\qquad (1\le i\le N).
$$
Now item (3) of Proposition `prop:p-normal-form` gives the $P$-orbit decomposition
$$
\Omega=\bigsqcup_{i=1}^N \Omega_i.
$$

Let
$$
\mathcal O_1,\dots,\mathcal O_M
$$
be the distinct $G$-orbits among the finitely many sets
$$
G\cdot X_{S,T_i}.
$$
Then
$$
G\cdot \Omega=\bigcup_{j=1}^M \mathcal O_j.
$$
For each $j$, the intersection
$$
\mathcal O_j\cap \Omega
$$
is a union of some of the open subsets $\Omega_i$, hence is open in $\Omega$. Moreover
$$
\mathcal O_j=G\cdot (\mathcal O_j\cap \Omega)
=\bigcup_{g\in G} g(\mathcal O_j\cap \Omega),
$$
so each $\mathcal O_j$ is open in $G\cdot\Omega$. Since only finitely many $\mathcal O_j$ occur and they partition $G\cdot\Omega$, each $\mathcal O_j$ is also closed in $G\cdot\Omega$.

Because
$$
\operatorname{Ind}_P^G(\mathcal O_0)
\;=\;
\overline{G\cdot\Omega}
=\overline{\bigcup_{j=1}^M \mathcal O_j}
\subseteq \bigcup_{j=1}^M \overline{\mathcal O_j},
$$
every $G$-orbit in the induced set lies in the closure of at least one $\mathcal O_j$.

It remains to prove that the $\mathcal O_j$ are exactly the maximal orbits. First, any orbit
$$
\mathcal O\subseteq \operatorname{Ind}_P^G(\mathcal O_0)
$$
which is not one of the $\mathcal O_j$ lies in some $\overline{\mathcal O_j}$, hence is strictly below $\mathcal O_j$ in the closure order and therefore is not maximal.

Conversely, let $\mathcal O_j$ be fixed and suppose
$$
\mathcal O_j\subseteq \overline{\mathcal O}
$$
for some $G$-orbit $\mathcal O$ in the induced set. As above, $\mathcal O$ lies in $\overline{\mathcal O_k}$ for some $k$, so
$$
\mathcal O_j\subseteq \overline{\mathcal O_k}.
$$
Since $\mathcal O_k$ is closed in $G\cdot\Omega$, this forces
$$
\mathcal O_j\subseteq \overline{\mathcal O_k}\cap G\cdot\Omega=\mathcal O_k.
$$
But the $\mathcal O_j$ are disjoint $G$-orbits, so necessarily
$$
\mathcal O_j=\mathcal O_k.
$$
Hence $\mathcal O\subseteq \overline{\mathcal O_j}$ and also $\mathcal O_j\subseteq \overline{\mathcal O}$. Since an orbit is the unique open dense orbit in its own closure, this implies
$$
\mathcal O=\mathcal O_j.
$$
Therefore each $\mathcal O_j$ is maximal.

Thus the induced $G$-orbits are exactly the orbits
$$
G\cdot X_{S,T}\qquad (T\in \mathscr T^\circ).
$$

# proposition prop:s-independence-and-orbit-criterion

## statement
Fix $T\in \mathscr T$. For any two isomorphisms $S_1,S_2:L'_1\xrightarrow{\sim}V_+$ one has
$$
G\cdot X_{S_1,T}=G\cdot X_{S_2,T}.
$$

More generally, for $T_1,T_2\in \mathscr T^\circ$ and $S_1,S_2:L'_1\xrightarrow{\sim}V_+$,
$$
G\cdot X_{S_1,T_1}=G\cdot X_{S_2,T_2}
$$
if and only if the bilinear spaces $(L'_0,B_{T_1})$ and $(L'_0,B_{T_2})$ are isometric.

## proof
Choose $h_1:=S_2^{-1}S_1\in \operatorname{GL}(L'_1)$ and extend it by the identity on $L'_0$. Let the corresponding Levi element of $P$ act on $L_1$ by $(h_1^{-1})^\vee$ and trivially on $L_0$ and $V_0$. A direct check shows that this sends $X_{S_1,T}$ to $X_{S_2,T}$. So the $G$-orbit is independent of $S$.

Now assume first that $(L'_0,B_{T_1})$ and $(L'_0,B_{T_2})$ are isometric. Then there exists $h_0\in \operatorname{GL}(L'_0)$ such that
$$
B_{T_2}(h_0u,h_0v)=B_{T_1}(u,v).
$$
Equivalently,
$$
T_2 h_0=(h_0^{-1})^\vee T_1.
$$
Extending $h_0$ by the identity on $L'_1$, and letting the Levi element act on $L_0$ by $(h_0^{-1})^\vee$, we get
$$
X_{S,T_1}\mapsto X_{S,T_2}.
$$
Therefore isometric forms give the same $G$-orbit.

For the converse, separate cases.

If $\epsilon=-1$, then $T_i\in \mathscr T^\circ$ is non-degenerate, so Proposition `prop:kernel-image` gives
$$
\ker X_{S_i,T_i}=E.
$$
Hence any $g\in G$ with
$$
gX_{S_1,T_1}g^{-1}=X_{S_2,T_2}
$$
must preserve $\ker X_{S_1,T_1}=E$, so $g\in P$. By Proposition `prop:p-normal-form`, two normalized representatives in the same $P$-orbit have exactly the same residual isometry class. Thus $(L'_0,B_{T_1})$ and $(L'_0,B_{T_2})$ are isometric.

If $\epsilon=+1$ and $l$ is even, then every element of $\mathscr T^\circ$ is a non-degenerate alternating form on the even-dimensional space $L'_0$. Such a form is unique up to isometry, so the converse is automatic.

If $\epsilon=+1$ and $l$ is odd, then every element of $\mathscr T^\circ$ is an alternating form of rank $l-1$. Such a form is again unique up to isometry: one chooses a basis
$$
e_1,\dots,e_m,f_1,\dots,f_m,r
$$
of $L'_0$ in which the form is standard symplectic on the span of the $e_i,f_i$ and vanishes on the radical line $Fr$. Hence the converse is automatic here as well.

So in all cases,
$$
G\cdot X_{S_1,T_1}=G\cdot X_{S_2,T_2}
\iff
(L'_0,B_{T_1})\cong (L'_0,B_{T_2}).
$$

# proposition prop:multiplicity

## statement
Let $x=X_{S,T}$ with $T\in \mathscr T^\circ$.

1. If $B_T$ is non-degenerate, then
   $$
   Z_G(x)\subseteq P.
   $$
   Hence
   $$
   m(G\cdot x,P)=1.
   $$

2. If $\epsilon=+1$ and $l$ is odd, then $B_T$ has one-dimensional radical
   $$
   F:=\ker T.
   $$
   In this case
   $$
   Z_G(x)^\circ\subseteq Z_G(x)\cap P
   $$
   and
   $$
   [Z_G(x):Z_G(x)\cap P]=2.
   $$
   Consequently
   $$
   m(G\cdot x,P)=2.
   $$

## proof
By Proposition `prop:kernel-image`,
$$
\ker x=E\oplus \ker T.
$$

If $B_T$ is non-degenerate, then $\ker T=0$, so $\ker x=E$. Any element of $Z_G(x)$ preserves $\ker x$, hence preserves $E$, so
$$
Z_G(x)\subseteq P.
$$
Therefore
$$
m(G\cdot x,P)=\frac{|\pi_0(Z_G(x))|}{|\pi_0(Z_G(x)\cap P)|}=1.
$$

Now assume $\epsilon=+1$ and $l$ is odd. Then $T$ has rank $l-1$, so $F=\ker T$ is a line. Also
$$
\operatorname{Im} T=\{e\in L_0:\lambda(e,F)=0\},
$$
so $\operatorname{Im} T$ has codimension $1$ in $L_0$. Choose a line $\ell\subset L_0$ such that
$$
L_0=\operatorname{Im} T\oplus \ell
$$
and $\lambda(\ell,F)\neq 0$. More concretely, choose a complement $M$ of $F$ in $L'_0$; then $T|_M:M\xrightarrow{\sim}\operatorname{Im}T$, and one may take
$$
\ell:=M^\perp\subset L_0,
$$
so that $\ell$ is a line pairing non-trivially with $F$ and orthogonally to $M$.
Then
$$
\ker x=(L_1\oplus \operatorname{Im} T)\oplus (\ell\oplus F),
$$
and
$$
\ker x\cap \operatorname{Im} x=L_1\oplus \operatorname{Im} T.
$$

The quotient
$$
\ker x/(\ker x\cap \operatorname{Im} x)\simeq \ell\oplus F
$$
is a hyperbolic plane. Its isotropic lines are exactly the two lines $\ell$ and $F$. Therefore the $r$-dimensional totally isotropic subspaces of $\ker x$ containing $\ker x\cap \operatorname{Im} x$ are exactly
$$
E=L_1\oplus \operatorname{Im} T\oplus \ell
$$
and
$$
E^\sharp=L_1\oplus \operatorname{Im} T\oplus F.
$$

Every element of $Z_G(x)$ preserves both $\ker x$ and $\ker x\cap \operatorname{Im} x$, so it permutes the two-point set
$$
\{E,E^\sharp\}.
$$
This gives a homomorphism
$$
Z_G(x)\to \mathfrak S_2.
$$
Its kernel is exactly $Z_G(x)\cap P$: if an element lies in the kernel, then it fixes $E$, so it lies in $P$; conversely, if an element lies in $Z_G(x)\cap P$, then it preserves $E$, and since it also preserves the two-point set $\{E,E^\sharp\}$, it must fix both points individually, hence lies in the kernel. Since the target is discrete, the identity component $Z_G(x)^\circ$ lies in the kernel, hence
$$
Z_G(x)^\circ\subseteq Z_G(x)\cap P.
$$

It remains to show that the permutation is non-trivial. Choose non-zero vectors $f\in \ell$ and $\eta\in F$ with $\lambda(f,\eta)=1$. Define $\tau\in G$ by:

- $\tau$ fixes $L_1\oplus \operatorname{Im} T\oplus V_0\oplus L'_1$ pointwise,
- $\tau$ fixes the chosen complement $M$ of $F$ in $L'_0$ pointwise,
- $\tau(f)=\eta$ and $\tau(\eta)=f$.

Because $\ell=M^\perp$, the hyperbolic plane $\ell\oplus F$ is orthogonal to $M\oplus \operatorname{Im} T$, and the remaining summands are also orthogonal to it. Hence $\tau$ is an isometry. Also $x$ vanishes on both $\ell$ and $F$, while $x$ is unchanged on all fixed summands, so $\tau x=x\tau$. Thus
$$
\tau\in Z_G(x)\setminus P.
$$
Therefore the image of $Z_G(x)\to \mathfrak S_2$ is all of $\mathfrak S_2$. Because its kernel is $Z_G(x)\cap P$, we get
$$
[Z_G(x):Z_G(x)\cap P]=2.
$$

Since $Z_G(x)^\circ\subseteq Z_G(x)\cap P$, the quotient by component groups equals the ordinary index:
$$
m(G\cdot x,P)
=\frac{|\pi_0(Z_G(x))|}{|\pi_0(Z_G(x)\cap P)|}
=[Z_G(x):Z_G(x)\cap P]
=2.
$$

# theorem thm:main

## statement
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

## proof
Assertion (1) is Lemma `lem:parametrize-x0-plus-u`.

Assertion (2) is Proposition `prop:induced-orbits`.

Assertion (3) is Proposition `prop:s-independence-and-orbit-criterion`.

Assertion (4) is Proposition `prop:multiplicity`.

This proves all four requested statements.
