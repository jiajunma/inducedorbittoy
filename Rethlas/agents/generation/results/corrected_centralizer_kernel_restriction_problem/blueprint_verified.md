# proposition prop:naive-target-is-too-large

## statement
The naive target
\[
\operatorname{Isom}(K,\langle\,,\,\rangle|_K)
\]
is in general strictly larger than the image of the restriction map
\[
\rho_X:Z_G(X)\to \operatorname{GL}(K).
\]
More precisely, in the symplectic example with Jordan block sizes \(4\) and
\(2\), the restricted form on \(K\) is zero, so
\[
\operatorname{Isom}(K,\langle\,,\,\rangle|_K)=\operatorname{GL}(K),
\]
but every element in the image of \(\rho_X\) preserves the proper line
\[
K_3=K\cap \operatorname{Im}X^3.
\]

## proof
Take the standard symplectic example
\[
V
=
Fe_1\oplus Fe_2\oplus Fe_3\oplus Fe_4\oplus Ff_1\oplus Ff_2
\]
with nonzero pairings
\[
\langle e_1,e_4\rangle=1,\qquad
\langle e_4,e_1\rangle=-1,
\]
\[
\langle e_2,e_3\rangle=-1,\qquad
\langle e_3,e_2\rangle=1,
\]
\[
\langle f_1,f_2\rangle=1,\qquad
\langle f_2,f_1\rangle=-1,
\]
and nilpotent operator
\[
Xe_4=e_3,\quad Xe_3=e_2,\quad Xe_2=e_1,\quad Xe_1=0,
\]
\[
Xf_2=f_1,\quad Xf_1=0.
\]
Then
\[
K=\ker X=Fe_1\oplus Ff_1.
\]
The restricted form on \(K\) is identically zero, because \(e_1\) pairs only
with \(e_4\) and \(f_1\) pairs only with \(f_2\). Hence every invertible map
of \(K\) preserves \(\langle\,,\,\rangle|_K\), so the naive target is
\(\operatorname{GL}(K)\).

On the other hand,
\[
\operatorname{Im}X^3=Fe_1,
\]
so
\[
K_3=K\cap \operatorname{Im}X^3=Fe_1.
\]
If \(g\in Z_G(X)\), then \(gX=Xg\) implies \(g(\operatorname{Im}X^3)=\operatorname{Im}X^3\)
and \(g(K)=K\), hence \(g(K_3)=K_3\). Therefore every element in
\(\operatorname{Im}(\rho_X)\) preserves the line \(Fe_1\).

But the swap
\[
h(e_1)=f_1,\qquad h(f_1)=e_1
\]
lies in \(\operatorname{GL}(K)\) and does not preserve \(Fe_1\). Thus
\[
h\notin \operatorname{Im}(\rho_X).
\]
So the naive target forgets real structure remembered by the centralizer,
namely the depth filtration
\[
K_r=K\cap \operatorname{Im}X^r.
\]

# lemma lem:primitive-forms

## statement
For every integer \(r\ge 0\), the formula
\[
b_r(\overline u,\overline v):=\langle \widetilde u,v\rangle
\qquad
(\overline u,\overline v\in K_r/K_{r+1},\ X^r\widetilde u=u)
\]
is well-defined. Moreover \(b_r\) is an \(\epsilon(-1)^r\)-symmetric bilinear
form on \(K_r/K_{r+1}\).

## proof
Fix \(u,v\in K_r\).

First we show that \(\langle \widetilde u,v\rangle\) does not depend on the
choice of \(\widetilde u\). If \(X^r\widetilde u=u=X^r\widetilde u'\), then
\(\widetilde u-\widetilde u'\in \ker X^r\). Since \(v\in K_r\), we can write
\(v=X^r w\) for some \(w\in V\). Therefore
\[
\langle \widetilde u-\widetilde u',v\rangle
=
\langle \widetilde u-\widetilde u',X^r w\rangle
=
(-1)^r\langle X^r(\widetilde u-\widetilde u'),w\rangle
=
0,
\]
because \(X\) is skew-adjoint:
\[
\langle Xa,b\rangle=-\langle a,Xb\rangle.
\]
So the value is independent of \(\widetilde u\).

Now we show that the value depends only on the classes modulo \(K_{r+1}\).
If \(v'=v+x\) with \(x\in K_{r+1}\), then \(x=X^{r+1}y\) for some \(y\in V\),
and \(Xu=0\) because \(u\in K\). Hence
\[
\langle \widetilde u,x\rangle
=
\langle \widetilde u,X^{r+1}y\rangle
=
(-1)^{r+1}\langle X^{r+1}\widetilde u,y\rangle
=
(-1)^{r+1}\langle Xu,y\rangle
=
0.
\]
Thus replacing \(v\) by \(v+x\) does not change the value. Likewise, if
\(u'=u+x\) with \(x\in K_{r+1}\), choose \(\widetilde x\) with
\(X^{r+1}\widetilde x=x\). Then \(\widetilde u+X\widetilde x\) is an
\(r\)-fold preimage of \(u'\), and
\[
\langle X\widetilde x,v\rangle
=
-\langle \widetilde x,Xv\rangle
=
0
\]
because \(v\in K\). So the value also depends only on \(\overline u\).

Bilinearity is immediate.

Finally, if \(u=X^r\widetilde u\) and \(v=X^r\widetilde v\), then
\[
b_r(\overline u,\overline v)
=
\langle \widetilde u,X^r\widetilde v\rangle
=
(-1)^r\langle X^r\widetilde u,\widetilde v\rangle
=
(-1)^r\langle u,\widetilde v\rangle.
\]
Using \(\langle a,b\rangle=\epsilon\langle b,a\rangle\), we obtain
\[
b_r(\overline u,\overline v)
=
\epsilon(-1)^r\langle \widetilde v,u\rangle
=
\epsilon(-1)^r b_r(\overline v,\overline u).
\]
So \(b_r\) is \(\epsilon(-1)^r\)-symmetric.

# lemma lem:graded-kernel-in-the-sl2-normal-form

## statement
Assume the standard facts listed in the problem statement: \(X\) lies in an
\(\mathfrak{sl}_2\)-triple, finite-dimensional \(\mathfrak{sl}_2\)-modules are
completely reducible, and
\[
V\simeq\bigoplus_{d\ge 1}E_d\otimes M_d
\]
with
\[
\langle\,,\,\rangle=\bigoplus_{d\ge 1}s_d\otimes m_d,
\]
where \(E_d\) is the irreducible \(\mathfrak{sl}_2\)-module of dimension \(d\),
\(X\) acts on the \(E_d\)-factor, and \(m_d\) is a non-degenerate
\(\epsilon(-1)^{d-1}\)-symmetric form on \(M_d\).

Choose in each \(E_d\) a basis
\[
e_{d,0},e_{d,1},\dots,e_{d,d-1}
\]
such that
\[
Xe_{d,0}=0,\qquad Xe_{d,i}=e_{d,i-1}\ (1\le i\le d-1),
\]
and
\[
s_d(e_{d,i},e_{d,j})=0\quad\text{unless }i+j=d-1.
\]
Write
\[
C_d:=Fe_{d,0}\subset E_d.
\]
Then for every \(r\ge 0\),
\[
K_r=\bigoplus_{d\ge r+1} C_d\otimes M_d,
\]
hence
\[
K_r/K_{r+1}\simeq C_{r+1}\otimes M_{r+1}\simeq M_{r+1}.
\]
Moreover \(b_r\) identifies with a nonzero scalar multiple of \(m_{r+1}\).
In particular \(b_r\) is non-degenerate and \(\epsilon(-1)^r\)-symmetric.

## proof
This is where the allowed \(\mathfrak{sl}_2\)-structure is used. By
Jacobson-Morozov and complete reducibility, we may work inside the orthogonal
direct sum
\[
V=\bigoplus_{d\ge 1} E_d\otimes M_d.
\]

In each summand \(E_d\otimes M_d\), the kernel of \(X\) is exactly
\[
\ker(X|_{E_d\otimes M_d})=C_d\otimes M_d,
\]
because \(\ker(X|_{E_d})=C_d\). Therefore
\[
K=\ker X=\bigoplus_{d\ge 1} C_d\otimes M_d.
\]

Now \(C_d\otimes M_d\subset \operatorname{Im}X^r\) if and only if \(r\le d-1\),
because \(e_{d,0}=X^r e_{d,r}\) exactly when \(r\le d-1\). Hence
\[
K_r=K\cap \operatorname{Im}X^r
=
\bigoplus_{d\ge r+1} C_d\otimes M_d.
\]
Passing to the quotient by
\[
K_{r+1}=\bigoplus_{d\ge r+2} C_d\otimes M_d
\]
leaves only the \(d=r+1\) summand, so
\[
K_r/K_{r+1}\simeq C_{r+1}\otimes M_{r+1}.
\]
Since \(C_{r+1}\) is one-dimensional, this is canonically \(M_{r+1}\) up to
the choice of the highest-weight basis vector \(e_{r+1,0}\).

To identify \(b_r\), take
\[
u=e_{r+1,0}\otimes m,\qquad
v=e_{r+1,0}\otimes n
\]
in \(C_{r+1}\otimes M_{r+1}\subset K_r\). Choose
\[
\widetilde u=e_{r+1,r}\otimes m,
\]
so that \(X^r\widetilde u=u\). Then
\[
b_r(\overline u,\overline v)
=
\langle e_{r+1,r}\otimes m,\ e_{r+1,0}\otimes n\rangle
=
s_{r+1}(e_{r+1,r},e_{r+1,0})\,m_{r+1}(m,n).
\]
The scalar
\[
c_r:=s_{r+1}(e_{r+1,r},e_{r+1,0})
\]
is nonzero because \(s_{r+1}\) is non-degenerate and antidiagonal in the chosen
basis. Hence
\[
b_r=c_r\,m_{r+1}
\]
under the identification \(K_r/K_{r+1}\simeq M_{r+1}\). Since \(m_{r+1}\) is
non-degenerate and \(\epsilon(-1)^r\)-symmetric, the same is true of \(b_r\).

# proposition prop:image-is-contained-in-HX

## statement
For every \(g\in Z_G(X)\), the restriction \(g|_K\) lies in \(H_X\). Equivalently,
\[
\operatorname{Im}(\rho_X)\subseteq H_X.
\]

## proof
Let \(g\in Z_G(X)\), so \(gX=Xg\).

For every \(r\ge 0\),
\[
g(\operatorname{Im}X^r)
=
g(X^rV)
=
X^r(gV)
=
\operatorname{Im}X^r.
\]
Also \(g(K)=K\) because \(g\) commutes with \(X\). Therefore
\[
g(K_r)
=
g(K\cap \operatorname{Im}X^r)
=
K\cap \operatorname{Im}X^r
=
K_r
\]
for every \(r\). So \(\rho_X(g)\) preserves the filtration.

Now fix \(r\ge 0\), and let \(\overline u,\overline v\in K_r/K_{r+1}\). Choose
\(\widetilde u\in V\) with \(X^r\widetilde u=u\). Since \(gX=Xg\), we have
\[
X^r(g\widetilde u)=g(X^r\widetilde u)=gu.
\]
Thus \(g\widetilde u\) is an \(r\)-fold preimage of \(gu\). Because \(g\in G\),
\[
b_r(\operatorname{gr}_r(g)\overline u,\operatorname{gr}_r(g)\overline v)
=
\langle g\widetilde u,gv\rangle
=
\langle \widetilde u,v\rangle
=
b_r(\overline u,\overline v).
\]
So \(\operatorname{gr}_r(g)\) is an isometry of \((K_r/K_{r+1},b_r)\) for every
\(r\). Hence \(g|_K\in H_X\).

# lemma lem:block-description-of-HX

## statement
With the notation of Lemma `lem:graded-kernel-in-the-sl2-normal-form`, write
\[
K=\bigoplus_{d\ge 1} C_d\otimes M_d
\]
and order the summands by increasing \(d\). Then
\[
K_r=\bigoplus_{d\ge r+1} C_d\otimes M_d.
\]
An element \(h\in \operatorname{GL}(K)\) lies in \(H_X\) if and only if,
relative to this direct sum, it is block upper triangular:
\[
h(C_d\otimes M_d)\subseteq \bigoplus_{e\ge d} C_e\otimes M_e,
\]
and its diagonal block
\[
h_{d,d}:C_d\otimes M_d\to C_d\otimes M_d
\]
belongs to \(\operatorname{Isom}(C_d\otimes M_d,b_{d-1})\), equivalently to
\(\operatorname{Isom}(M_d,m_d)\).

In particular,
\[
H_X=U_X\rtimes L_X,
\]
where
\[
L_X=\prod_{d\ge 1}\operatorname{Isom}(M_d,m_d)
\]
and \(U_X\) is the unitriangular subgroup consisting of those \(h\) with all
diagonal blocks equal to the identity.

## proof
Because
\[
K_r=\bigoplus_{d\ge r+1}C_d\otimes M_d,
\]
the condition \(h(K_r)=K_r\) for every \(r\) is exactly the statement that the
matrix of \(h\) is upper triangular with respect to the ordered summands
\[
C_1\otimes M_1,\ C_2\otimes M_2,\ C_3\otimes M_3,\ \dots.
\]

For each \(d\), the graded quotient
\[
K_{d-1}/K_d
\]
is precisely the \(d\)-th diagonal summand
\[
C_d\otimes M_d,
\]
and by Lemma `lem:graded-kernel-in-the-sl2-normal-form` the form \(b_{d-1}\) on
that quotient is a nonzero scalar multiple of \(m_d\). Therefore the condition
\[
\operatorname{gr}_{d-1}(h)\in \operatorname{Isom}(K_{d-1}/K_d,b_{d-1})
\]
is equivalent to
\[
h_{d,d}\in \operatorname{Isom}(M_d,m_d).
\]
This proves the stated description of \(H_X\).

The semidirect product statement is the usual one for an upper-triangular
matrix group: the diagonal blocks form the Levi factor \(L_X\), and the blocks
strictly above the diagonal form the normal unitriangular subgroup \(U_X\).

# lemma lem:elementary-centralizer-operators

## statement
Fix integers \(e>d\ge 1\) and a linear map
\[
T:M_d\to M_e.
\]
Let
\[
\theta_{e,d}:E_d\to E_e
\]
be the \(X\)-equivariant map determined by
\[
\theta_{e,d}(e_{d,i})=e_{e,i}
\qquad
(0\le i\le d-1).
\]
Let
\[
T^\sharp:M_e\to M_d
\]
be the adjoint of \(T\) with respect to \(m_d\) and \(m_e\), and let
\[
\theta_{e,d}^\sharp:E_e\to E_d
\]
be the adjoint of \(\theta_{e,d}\) with respect to \(s_d\) and \(s_e\). Put
\[
A_{e,d,T}:=\theta_{e,d}\otimes T,
\qquad
N_{e,d,T}:=A_{e,d,T}-A_{e,d,T}^\sharp.
\]
Then:

1. \(N_{e,d,T}\in \mathfrak g\) and \(N_{e,d,T}\) commutes with \(X\).
2. \(u_{e,d,T}:=\exp(N_{e,d,T})\) lies in \(Z_G(X)\).
3. The restriction of \(u_{e,d,T}\) to \(K\) is the elementary filtration
   transvection
   \[
   1+E_{e,d,T},
   \]
   where \(E_{e,d,T}\) sends
   \[
   C_d\otimes M_d\to C_e\otimes M_e,\qquad
   e_{d,0}\otimes m\mapsto e_{e,0}\otimes Tm,
   \]
   and vanishes on every \(C_f\otimes M_f\) for \(f\ne d\).

## proof
The map \(\theta_{e,d}\) commutes with \(X\) by construction:
\[
X\theta_{e,d}(e_{d,i})=Xe_{e,i}=e_{e,i-1}=\theta_{e,d}(e_{d,i-1})
=
\theta_{e,d}X(e_{d,i}).
\]
Taking adjoints and using \(X^\sharp=-X\) on every \(E_d\), we get
\[
X\theta_{e,d}^\sharp=\theta_{e,d}^\sharp X.
\]
Likewise \(A_{e,d,T}\) and \(A_{e,d,T}^\sharp\) commute with \(X\), so their
difference \(N_{e,d,T}\) also commutes with \(X\).

By definition,
\[
N_{e,d,T}^\sharp
=
(A_{e,d,T}-A_{e,d,T}^\sharp)^\sharp
=
A_{e,d,T}^\sharp-A_{e,d,T}
=
-N_{e,d,T},
\]
so \(N_{e,d,T}\) is skew-adjoint. Therefore \(N_{e,d,T}\in\mathfrak g\).

We now prove that \(N_{e,d,T}\) is nilpotent. Put
\[
q:=e-d>0.
\]
The adjoint \(\theta_{e,d}^\sharp:E_e\to E_d\) has the following shape. Since
\(\theta_{e,d}(E_d)\) is spanned by
\[
e_{e,0},e_{e,1},\dots,e_{e,d-1},
\]
and since the standard form \(s_e\) pairs \(e_{e,i}\) only with
\(e_{e,e-1-i}\), the vector \(e_{e,j}\) is orthogonal to
\(\theta_{e,d}(E_d)\) whenever
\[
j<e-d=q.
\]
Thus
\[
\theta_{e,d}^\sharp(e_{e,j})=0\qquad (j<q).
\]
For \(j\ge q\), the same anti-diagonal pairing calculation shows that
\(\theta_{e,d}^\sharp(e_{e,j})\) is a scalar multiple of
\[
e_{d,j-q}.
\]
Consequently \(N_{e,d,T}\) has the following index behavior on the two summands
\[
E_d\otimes M_d\oplus E_e\otimes M_e.
\]
It sends a vector with \(E_d\)-index \(i\) to a vector with \(E_e\)-index \(i\),
and it sends a vector with \(E_e\)-index \(j\) either to \(0\), if \(j<q\), or
to a vector with \(E_d\)-index \(j-q\), if \(j\ge q\). Hence every two
successive nonzero applications of \(N_{e,d,T}\) decrease the \(E\)-index by
exactly \(q>0\). Since all indices are nonnegative and bounded above by
\(\max(e-1,d-1)\), a sufficiently high power of \(N_{e,d,T}\) is zero.
Therefore \(N_{e,d,T}\) is nilpotent.

It follows that \(\exp(N_{e,d,T})\) is a finite sum and hence a well-defined
linear automorphism. Since \(N_{e,d,T}\) is skew-adjoint, \(\exp(N_{e,d,T})\)
preserves the bilinear form, so it lies in \(G\). Since \(N_{e,d,T}\) commutes
with \(X\), so does \(\exp(N_{e,d,T})\). Hence
\[
u_{e,d,T}\in Z_G(X).
\]

It remains to compute the restriction to \(K\). On the source highest-weight
line \(C_d\otimes M_d\), one has
\[
A_{e,d,T}(e_{d,0}\otimes m)=e_{e,0}\otimes Tm.
\]
The adjoint term does not act there, because \(A_{e,d,T}^\sharp\) has source
\(E_e\otimes M_e\). Thus
\[
N_{e,d,T}(e_{d,0}\otimes m)=e_{e,0}\otimes Tm.
\]

On the target highest-weight line \(C_e\otimes M_e\), the first term
\(A_{e,d,T}\) vanishes for source reasons, and the adjoint term also vanishes.
Indeed the image of \(\theta_{e,d}\) is
\[
\operatorname{span}\{e_{e,0},e_{e,1},\dots,e_{e,d-1}\},
\]
while \(e_{e,0}\) pairs under \(s_e\) only with \(e_{e,e-1}\), which does not
lie in that image because \(e>d\). Therefore \(e_{e,0}\) is orthogonal to the
image of \(\theta_{e,d}\), so
\[
\theta_{e,d}^\sharp(e_{e,0})=0.
\]
Hence \(N_{e,d,T}\) vanishes on \(C_e\otimes M_e\). It also vanishes on all
other \(C_f\otimes M_f\).

So on \(K\), the operator \(N_{e,d,T}\) is exactly \(E_{e,d,T}\). Moreover
\[
N_{e,d,T}(K)\subseteq C_e\otimes M_e,
\]
and we have just shown that \(N_{e,d,T}\) vanishes on \(C_e\otimes M_e\). Thus
\[
N_{e,d,T}^2|_K=0.
\]
Therefore
\[
u_{e,d,T}|_K
=
\exp(N_{e,d,T})|_K
=
(1+N_{e,d,T})|_K
=
1+E_{e,d,T}.
\]

# proposition prop:surjectivity-onto-HX

## statement
The restriction map
\[
\rho_X:Z_G(X)\longrightarrow H_X
\]
is surjective.

## proof
Let \(h\in H_X\). By Lemma `lem:block-description-of-HX`, relative to
\[
K=\bigoplus_{d\ge 1} C_d\otimes M_d
\]
we can write
\[
h=u\ell
\]
with
\[
\ell\in L_X=\prod_{d\ge 1}\operatorname{Isom}(M_d,m_d)
\]
diagonal and \(u\in U_X\) unitriangular.

First lift the diagonal part. If
\[
\ell=(\ell_d)_{d\ge 1},\qquad \ell_d\in \operatorname{Isom}(M_d,m_d),
\]
define
\[
g_\ell:=\bigoplus_{d\ge 1} (\operatorname{id}_{E_d}\otimes \ell_d).
\]
Because each \(\ell_d\) preserves \(m_d\), the map \(g_\ell\) preserves
\[
\bigoplus_{d\ge 1} s_d\otimes m_d=\langle\,,\,\rangle,
\]
so \(g_\ell\in G\). It obviously commutes with \(X\), because \(X\) acts only
on the \(E_d\)-factor. Hence \(g_\ell\in Z_G(X)\), and its restriction to
\(K\) is exactly \(\ell\).

Now lift the unitriangular part. Relative to the ordered summands
\[
C_1\otimes M_1,\ C_2\otimes M_2,\ C_3\otimes M_3,\ \dots,
\]
the group \(U_X\) is the standard block upper-unitriangular group. Therefore it
is generated by the elementary transvections
\[
1+E_{e,d,T}
\qquad
(e>d,\ T\in\operatorname{Hom}(M_d,M_e)).
\]
For each such generator, Lemma `lem:elementary-centralizer-operators` produces
an element
\[
u_{e,d,T}\in Z_G(X)
\]
whose restriction to \(K\) is exactly \(1+E_{e,d,T}\).

Write \(u\) as a product of such elementary generators. Multiplying the
corresponding lifts in the same order gives an element \(g_u\in Z_G(X)\) with
\[
g_u|_K=u.
\]
Finally,
\[
g:=g_u g_\ell\in Z_G(X)
\]
satisfies
\[
g|_K=u\ell=h.
\]
Thus every \(h\in H_X\) lies in the image of \(\rho_X\), so \(\rho_X\) is
surjective.

# theorem thm:main

## statement
# Corrected Centralizer Restriction Theorem for a Nilpotent Element

## Problem

Let \(F\) be an algebraically closed field of characteristic \(0\). Let
\((V,\langle\,,\,\rangle)\) be a finite-dimensional non-degenerate
\(\epsilon\)-symmetric space over \(F\), where
\[
\epsilon\in\{+1,-1\},
\qquad
\langle v,w\rangle=\epsilon\langle w,v\rangle.
\]
Let
\[
G=\operatorname{Isom}(V,\langle\,,\,\rangle)
\]
be the corresponding orthogonal group if \(\epsilon=+1\), and symplectic group
if \(\epsilon=-1\). Let
\[
\mathfrak g=\operatorname{Lie}(G)
=
\{X\in\operatorname{End}_F(V):
\langle Xv,w\rangle+\langle v,Xw\rangle=0
\text{ for all }v,w\in V\}.
\]

Let \(X\in\mathfrak g\) be nilpotent and set
\[
K:=\ker X.
\]
For every integer \(r\ge 0\), define
\[
K_r:=K\cap\operatorname{Im}X^r.
\]
Thus
\[
K=K_0\supseteq K_1\supseteq K_2\supseteq\cdots.
\]

For \(u,v\in K_r\), choose \(\widetilde u\in V\) such that
\[
X^r\widetilde u=u.
\]
Define
\[
b_r(\overline u,\overline v)
:=
\langle \widetilde u,v\rangle,
\qquad
\overline u,\overline v\in K_r/K_{r+1}.
\]

First prove that \(b_r\) is well-defined and is a non-degenerate
\(\epsilon(-1)^r\)-symmetric bilinear form on
\[
\operatorname{gr}_r^X K:=K_r/K_{r+1}.
\]

Define the corrected target group
\[
H_X
:=
\left\{
h\in\operatorname{GL}(K):
h(K_r)=K_r\text{ for all }r\ge 0,\text{ and }
\operatorname{gr}_r(h)\in
\operatorname{Isom}(\operatorname{gr}_r^X K,b_r)
\text{ for all }r\ge 0
\right\}.
\]

Since \(gX=Xg\) implies \(g(K_r)=K_r\), restriction to \(K\) defines a group
homomorphism
\[
\rho_X:Z_G(X)\longrightarrow \operatorname{GL}(K),
\qquad
\rho_X(g)=g|_K,
\]
where
\[
Z_G(X)=\{g\in G:gX=Xg\}.
\]

Prove the corrected theorem:
\[
\boxed{\operatorname{Im}(\rho_X)=H_X.}
\]
Equivalently, prove that
\[
\rho_X:Z_G(X)\longrightarrow H_X
\]
is surjective.

## Required proof shape

The proof should explain why the naive target
\[
\operatorname{Isom}(K,\langle\,,\,\rangle|_K)
\]
is too large, and why the corrected target must remember the hidden filtration
\[
K_r=K\cap\operatorname{Im}X^r
\]
together with the primitive forms \(b_r\) on the graded pieces.

You may use the following standard facts without reproving them from scratch,
but you must state clearly where they are used:

1. Jacobson-Morozov: \(X\) lies in an \(\mathfrak{sl}_2\)-triple inside
   \(\mathfrak g\).
2. Complete reducibility of finite-dimensional \(\mathfrak{sl}_2\)-modules.
3. The standard \(X\)-adapted decomposition
   \[
   V\simeq\bigoplus_{d\ge 1} E_d\otimes M_d,
   \]
   where \(E_d\) is the irreducible \(\mathfrak{sl}_2\)-module of dimension
   \(d\), \(X\) acts on the \(E_d\)-factor, and the ambient form decomposes as
   \[
   \langle\,,\,\rangle
   =
   \bigoplus_{d\ge 1} s_d\otimes m_d.
   \]
   Here \(s_d\) is the standard invariant form on \(E_d\), and \(m_d\) is a
   non-degenerate \(\epsilon(-1)^{d-1}\)-symmetric form on \(M_d\).

Using this normal form, identify
\[
K_r/K_{r+1}\simeq M_{r+1}
\]
up to the highest-weight line in \(E_{r+1}\), identify \(b_r\) with a nonzero
scalar multiple of \(m_{r+1}\), and prove the surjectivity of
\[
Z_G(X)\to H_X.
\]

Do not prove only the easier inclusion \(\operatorname{Im}(\rho_X)\subseteq H_X\).
The main point is the reverse inclusion.

## proof
Proposition `prop:naive-target-is-too-large` explains why the naive target
\(\operatorname{Isom}(K,\langle\,,\,\rangle|_K)\) is too large: the centralizer
always remembers the depth filtration
\[
K_r=K\cap \operatorname{Im}X^r,
\]
and that filtration is not detected by the restricted form on \(K\) alone.

Lemma `lem:primitive-forms` proves that each \(b_r\) is well-defined and
\(\epsilon(-1)^r\)-symmetric. Lemma
`lem:graded-kernel-in-the-sl2-normal-form` then uses the allowed
Jacobson-Morozov \(\mathfrak{sl}_2\)-decomposition
\[
V\simeq\bigoplus_{d\ge 1}E_d\otimes M_d
\]
to identify
\[
K_r/K_{r+1}\simeq M_{r+1}
\]
up to the highest-weight line in \(E_{r+1}\), and to identify \(b_r\) with a
nonzero scalar multiple of \(m_{r+1}\). In particular each \(b_r\) is
non-degenerate.

Proposition `prop:image-is-contained-in-HX` gives the easy inclusion
\[
\operatorname{Im}(\rho_X)\subseteq H_X.
\]

For the converse inclusion, Lemma `lem:block-description-of-HX` describes
\(H_X\) concretely as a block upper-triangular group on
\[
K=\bigoplus_{d\ge 1} C_d\otimes M_d,
\]
with diagonal blocks in
\[
\prod_{d\ge 1}\operatorname{Isom}(M_d,m_d).
\]
The diagonal part lifts immediately to \(Z_G(X)\) by acting as
\(\operatorname{id}_{E_d}\otimes \ell_d\) on each summand \(E_d\otimes M_d\).

The strictly upper-triangular part is generated by elementary transvections
between different Jordan lengths. Lemma
`lem:elementary-centralizer-operators` constructs, for every \(e>d\) and every
linear map \(T:M_d\to M_e\), an explicit skew-adjoint \(X\)-equivariant
operator
\[
N_{e,d,T}\in\mathfrak g
\]
whose exponential lies in \(Z_G(X)\) and whose restriction to \(K\) is exactly
the desired elementary transvection. Proposition
`prop:surjectivity-onto-HX` therefore lifts first the Levi part and then every
unitriangular factor, proving that every \(h\in H_X\) is the restriction of an
element of \(Z_G(X)\).

Consequently
\[
\operatorname{Im}(\rho_X)=H_X.
\]
Equivalently, the restriction map
\[
\rho_X:Z_G(X)\to H_X
\]
is surjective. This is the corrected theorem.
