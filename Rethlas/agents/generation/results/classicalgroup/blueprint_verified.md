# note note:completeness-check

## statement
The problem statement is complete after the following minimal convention fixes.

1. `\(\mathrm O(p,q)\)` means the full real orthogonal group of a non-degenerate real symmetric bilinear form of signature `\((p,q)\)`.
2. `\(\mathrm{Sp}(a,b)\)` means the full quaternionic unitary group of a quaternionic Hermitian form of signature `\((a,b)\)`.
3. `\(\mathrm O^*(2n)\)` means the full quaternionic-linear isometry group of a non-degenerate quaternionic skew-Hermitian form on `\(\mathbb H^n\)`; equivalently, the standard real form of `\(\mathrm O(2n,\mathbb C)\)` obtained from a quaternionic structure.
4. In the quaternionic cases we use the standard convention that quaternionic Hermitian and skew-Hermitian forms are linear in the first variable and conjugate-linear in the second.

With these conventions, no further repair of the statement is needed. In the metaplectic case `\(\star=\widetilde C\)` we identify only the underlying real group `\(\mathrm{Sp}_{2p}(\mathbb R)\)`, exactly as requested.

## proof
Items (1)--(4) merely fix the usual meanings of the group names and of the quaternionic sesquilinearity convention. They do not alter the theorem itself; they only remove the ambiguities explicitly mentioned in the problem statement. After these conventions are fixed, every term in properties (1)--(10) has a unique standard meaning, so the theorem is well-posed as stated.

# lemma lem:case-bd

## statement
Assume `\(\star=B\)` or `\(\star=D\)`, so `\((\epsilon,\dot\epsilon)=(1,1)\)`. Let `\(n=p+q\)`. Then there is an explicit quadruple `\((V,\langle\ ,\ \rangle,J,L)\)` satisfying properties (1)--(10), and
`\(
G_{\mathbb C}^J \simeq \mathrm O(p,q).
\)`

## proof
Take
`\[
V=\mathbb C^n
\]`
with basis `\((e_1,\dots,e_n)\)`. Let
`\[
S_{p,q}:=\operatorname{diag}(I_p,-I_q).
\]`
Define the complex bilinear form by
`\[
\langle u,v\rangle:=u^{\mathsf T}S_{p,q}v.
\]`
Thus `\(\langle\ ,\ \rangle\)` is symmetric and non-degenerate. Define
`\[
J(u):=\overline{u},
\qquad
L(u):=S_{p,q}u.
\]`

We verify the required properties.

Property (1) is clear because `\(\dim_{\mathbb C}V=n=p+q=|\mathsf s|\)`. Property (2) holds because the matrix `\(S_{p,q}\)` is invertible and symmetric, so `\(\langle\ ,\ \rangle\)` is a non-degenerate `\(\epsilon\)`-symmetric form with `\(\epsilon=1\)`.

For property (3),
`\[
J^2(u)=\overline{\overline{u}}=u=\epsilon\dot\epsilon\,u,
\]`
because here `\(\epsilon\dot\epsilon=1\)`. For property (4),
`\[
L^2=S_{p,q}^2=I_n=\dot\epsilon\,I_n.
\]`

For property (5), since `\(S_{p,q}\)` has real entries,
`\[
\langle Ju,Jv\rangle
=\overline{u}^{\mathsf T}S_{p,q}\overline{v}
=\overline{u^{\mathsf T}S_{p,q}v}
=\overline{\langle u,v\rangle}.
\]`
For property (6),
`\[
\langle Lu,Lv\rangle
=u^{\mathsf T}S_{p,q}^{\mathsf T}S_{p,q}S_{p,q}v
=u^{\mathsf T}S_{p,q}v
=\langle u,v\rangle,
\]`
because `\(S_{p,q}^{\mathsf T}=S_{p,q}\)` and `\(S_{p,q}^2=I_n\)`. Property (7) is immediate because `\(L\)` is real:
`\[
LJ(u)=S_{p,q}\overline{u}=\overline{S_{p,q}u}=JL(u).
\]`

For property (8),
`\[
H(u,v):=\langle Lu,Jv\rangle
=(S_{p,q}u)^{\mathsf T}S_{p,q}\overline{v}
=u^{\mathsf T}\overline{v}.
\]`
So `\(H\)` is the standard positive-definite Hermitian form on `\(\mathbb C^n\)`.

For property (9), the `\((+1)\)`-eigenspace of `\(L=S_{p,q}\)` is
`\[
V_+=\operatorname{span}_{\mathbb C}(e_1,\dots,e_p),
\]`
so `\(\dim V_+=p\)`, and the `\((-1)\)`-eigenspace is
`\[
V_-=\operatorname{span}_{\mathbb C}(e_{p+1},\dots,e_n),
\]`
so `\(\dim V_-=q\)`.

For property (10), `\(G_{\mathbb C}\)` is the complex isometry group of the symmetric form with matrix `\(S_{p,q}\)`, so
`\[
G_{\mathbb C}=\{g\in \operatorname{GL}_n(\mathbb C):g^{\mathsf T}S_{p,q}g=S_{p,q}\}.
\]`
The relation `\(gJ=Jg\)` means exactly that `\(g\)` has real entries. Therefore
`\[
G_{\mathbb C}^J
=\{g\in \operatorname{GL}_n(\mathbb R):g^{\mathsf T}S_{p,q}g=S_{p,q}\}
=\mathrm O(p,q).
\]`
This is an isomorphism of real Lie groups.

# lemma lem:case-c

## statement
Assume `\(\star=C\)` or `\(\star=\widetilde C\)`, so `\((\epsilon,\dot\epsilon)=(-1,-1)\)` and `\(p=q\)`. Write `\(n:=p=q\)`. Then there is an explicit quadruple `\((V,\langle\ ,\ \rangle,J,L)\)` satisfying properties (1)--(10), and
`\[
G_{\mathbb C}^J \simeq \mathrm{Sp}_{2n}(\mathbb R)=\mathrm{Sp}_{2p}(\mathbb R).
\]`

## proof
Take
`\[
V=\mathbb C^{2n}
\]`
with basis
`\[
e_1,\dots,e_n,f_1,\dots,f_n.
\]`
Let
`\[
\Omega_n:=
\begin{pmatrix}
0&I_n\\
-I_n&0
\end{pmatrix}.
\]`
Define
`\[
\langle u,v\rangle:=u^{\mathsf T}\Omega_nv,
\qquad
J(u):=\overline{u},
\qquad
L(u):=\Omega_nu.
\]`
Equivalently,
`\[
\langle e_i,f_j\rangle=\delta_{ij},
\qquad
\langle f_i,e_j\rangle=-\delta_{ij},
\]`
and all pairings of two `\(e\)`'s or two `\(f\)`'s are zero.

Property (1) holds because `\(\dim_{\mathbb C}V=2n=2p=p+q=|\mathsf s|\)`. Property (2) holds because `\(\Omega_n^{\mathsf T}=-\Omega_n\)` and `\(\det(\Omega_n)\neq 0\)`, so `\(\langle\ ,\ \rangle\)` is alternating and non-degenerate.

For property (3), `\(J^2=1\)` and here `\(\epsilon\dot\epsilon=(-1)(-1)=1\)`. For property (4),
`\[
L^2=\Omega_n^2=-I_{2n}=\dot\epsilon\,I_V.
\]`

For property (5), since `\(\Omega_n\)` is real,
`\[
\langle Ju,Jv\rangle
=\overline{u}^{\mathsf T}\Omega_n\overline{v}
=\overline{u^{\mathsf T}\Omega_nv}
=\overline{\langle u,v\rangle}.
\]`
For property (6),
`\[
\langle Lu,Lv\rangle
=u^{\mathsf T}\Omega_n^{\mathsf T}\Omega_n\Omega_nv
=u^{\mathsf T}(-\Omega_n)\Omega_n^2v
=u^{\mathsf T}\Omega_nv
=\langle u,v\rangle.
\]`
For property (7), `\(L\)` has real matrix, so `\(LJ=JL\)`.

For property (8),
`\[
H(u,v)=\langle Lu,Jv\rangle
=(\Omega_nu)^{\mathsf T}\Omega_n\overline{v}
=u^{\mathsf T}\Omega_n^{\mathsf T}\Omega_n\overline{v}
=u^{\mathsf T}\overline{v}.
\]`
Hence `\(H\)` is the standard positive-definite Hermitian form. In particular,
`\[
H(e_i,e_j)=\delta_{ij},
\qquad
H(f_i,f_j)=\delta_{ij},
\qquad
H(e_i,f_j)=0=H(f_i,e_j).
\]`

Property (9) is not applicable here because `\(\dot\epsilon=-1\)`.

For property (10),
`\[
G_{\mathbb C}
=\{g\in \operatorname{GL}_{2n}(\mathbb C):g^{\mathsf T}\Omega_ng=\Omega_n\}
=\mathrm{Sp}_{2n}(\mathbb C).
\]`
The condition `\(gJ=Jg\)` again means exactly that `\(g\)` has real entries. Therefore
`\[
G_{\mathbb C}^J
=\{g\in \operatorname{GL}_{2n}(\mathbb R):g^{\mathsf T}\Omega_ng=\Omega_n\}
=\mathrm{Sp}_{2n}(\mathbb R).
\]`
This is exactly the required group for both `\(\star=C\)` and `\(\star=\widetilde C\)`. In the metaplectic case one stops here, because the double cover is not part of the present construction.

# lemma lem:case-cstar

## statement
Assume `\(\star=C^*\)`, so `\((\epsilon,\dot\epsilon)=(-1,1)\)` and `\(p,q\)` are even. Write
`\[
p=2a,
\qquad
q=2b.
\]`
Then there is an explicit quadruple `\((V,\langle\ ,\ \rangle,J,L)\)` satisfying properties (1)--(10), and
`\[
G_{\mathbb C}^J \simeq \mathrm{Sp}(a,b)=\mathrm{Sp}(p/2,q/2).
\]`

## proof
Take
`\[
V=\mathbb C^{2a+2b}
\]`
with basis
`\[
e_1,\dots,e_a,f_1,\dots,f_a,e'_1,\dots,e'_b,f'_1,\dots,f'_b.
\]`
Define the alternating form by the basis rules
`\[
\langle e_i,f_j\rangle=\delta_{ij},
\qquad
\langle f_i,e_j\rangle=-\delta_{ij},
\]`
`\[
\langle e'_r,f'_s\rangle=-\delta_{rs},
\qquad
\langle f'_r,e'_s\rangle=\delta_{rs},
\]`
and all remaining basis pairings equal to `\(0\)`. Thus the positive block is a standard symplectic block and the negative block is the same block with the opposite sign.

Define `\(J\)` conjugate-linearly by
`\[
Je_i=f_i,
\qquad
Jf_i=-e_i,
\qquad
Je'_r=f'_r,
\qquad
Jf'_r=-e'_r.
\]`
Define `\(L\)` complex-linearly by
`\[
Le_i=e_i,
\quad
Lf_i=f_i,
\quad
Le'_r=-e'_r,
\quad
Lf'_r=-f'_r.
\]`

Property (1) holds because
`\[
\dim_{\mathbb C}V=2a+2b=p+q=|\mathsf s|.
\]`
Property (2) holds because the form is alternating by construction and each `\(2\times 2\)` block is non-degenerate, so the whole form is non-degenerate.

For property (3), using the displayed formulas,
`\[
J^2e_i=Jf_i=-e_i,
\qquad
J^2f_i=J(-e_i)=-f_i,
\]`
and similarly on the primed basis. Hence `\(J^2=-1=\epsilon\dot\epsilon\)`.

For property (4), `\(L^2=1=\dot\epsilon\)`. For property (7), `\(LJ=JL\)` because `\(L\)` acts by a scalar on each `\(J\)`-stable plane `\(\operatorname{span}_{\mathbb C}(e_i,f_i)\)` and `\(\operatorname{span}_{\mathbb C}(e'_r,f'_r)\)`.

For property (5), it is enough to check on basis vectors. For example,
`\[
\langle Je_i,Jf_j\rangle
=\langle f_i,-e_j\rangle
=\delta_{ij}
=\overline{\langle e_i,f_j\rangle},
\]`
and similarly for the primed block:
`\[
\langle Je'_r,Jf'_s\rangle
=\langle f'_r,-e'_s\rangle
=-\delta_{rs}
=\overline{\langle e'_r,f'_s\rangle}.
\]`
All other basis checks are equally immediate, so
`\[
\langle Ju,Jv\rangle=\overline{\langle u,v\rangle}
\qquad
(u,v\in V).
\]`

For property (6), again it is enough to check on the basis. On the unprimed block,
`\[
\langle Le_i,Lf_j\rangle
=\langle e_i,f_j\rangle
=\delta_{ij}
=\langle e_i,f_j\rangle.
\]`
On the primed block,
`\[
\langle Le'_r,Lf'_s\rangle
=\langle -e'_r,-f'_s\rangle
=\langle e'_r,f'_s\rangle.
\]`
Thus `\(\langle Lu,Lv\rangle=\langle u,v\rangle\)` for all `\(u,v\)`.

For property (8), direct basis calculation gives
`\[
H(e_i,e_j)=\langle Le_i,Je_j\rangle=\langle e_i,f_j\rangle=\delta_{ij},
\]`
`\[
H(f_i,f_j)=\langle Lf_i,Jf_j\rangle=\langle f_i,-e_j\rangle=\delta_{ij},
\]`
`\[
H(e'_r,e'_s)=\langle Le'_r,Je'_s\rangle=\langle -e'_r,f'_s\rangle=\delta_{rs},
\]`
`\[
H(f'_r,f'_s)=\langle Lf'_r,Jf'_s\rangle=\langle -f'_r,-e'_s\rangle=\delta_{rs},
\]`
and all mixed terms vanish. Therefore `\(H\)` is the standard positive-definite Hermitian form in this basis.

For property (9), the `\((+1)\)`-eigenspace of `\(L\)` is
`\[
V_+=\operatorname{span}_{\mathbb C}(e_1,\dots,e_a,f_1,\dots,f_a),
\]`
so `\(\dim V_+=2a=p\)`, and the `\((-1)\)`-eigenspace is
`\[
V_-=\operatorname{span}_{\mathbb C}(e'_1,\dots,e'_b,f'_1,\dots,f'_b),
\]`
so `\(\dim V_-=2b=q\)`.

It remains to identify `\(G_{\mathbb C}^J\)`. Because `\(J^2=-1\)`, the operator `\(J\)` defines a quaternionic structure on `\(V\)`: if we write `\(\mathbf j\)` for the quaternionic unit, then right multiplication by `\(\mathbf j\)` is `\(J\)`. Put
`\[
u_i:=e_i \quad (1\le i\le a),
\qquad
u_{a+r}:=e'_r \quad (1\le r\le b).
\]`
Then `\((u_1,\dots,u_{a+b})\)` is a quaternionic basis because `\(Ju_i=f_i\)` for `\(i\le a\)` and `\(Ju_{a+r}=f'_r\)` for `\(r\le b\)`.

Define an `\(\mathbb H\)`-valued form by
`\[
\mathbf h(x,y):=\langle x,Jy\rangle-\langle x,y\rangle\,\mathbf j.
\]`
We claim that this is exactly the standard quaternionic Hermitian form of signature `\((a,b)\)` in the quaternionic basis `\((u_1,\dots,u_{a+b})\)`.

Indeed, take one positive basis vector `\(u_i=e_i\)` and write
`\[
x=u_i\alpha,
\qquad
y=u_i\beta,
\qquad
\alpha=z+w\mathbf j,
\qquad
\beta=z'+w'\mathbf j
\qquad
(z,w,z',w'\in\mathbb C).
\]`
Because `\(u_i\mathbf j=Ju_i=f_i\)`, one has
`\[
x=e_iz+f_iw,
\qquad
y=e_iz'+f_iw'.
\]`
Using
`\(
\langle e_i,f_i\rangle=1,
\langle f_i,e_i\rangle=-1,
\langle e_i,e_i\rangle=\langle f_i,f_i\rangle=0,
\)`
we get
`\[
\langle x,Jy\rangle=z\overline{z'}+w\overline{w'},
\qquad
\langle x,y\rangle=zw'-wz'.
\]`
Hence
`\[
\mathbf h(x,y)
=z\overline{z'}+w\overline{w'}-(zw'-wz')\mathbf j
=\alpha\,\overline{\beta}.
\]`
Now take a negative basis vector `\(u_{a+r}=e'_r\)` and write `\(x=u_{a+r}\alpha\)`, `\(y=u_{a+r}\beta\)` in the same way. Since
`\(
\langle e'_r,f'_r\rangle=-1,
\langle f'_r,e'_r\rangle=1,
\)`
the same calculation gives
`\[
\mathbf h(x,y)=-\,\alpha\,\overline{\beta}.
\]`
Finally, if `\(i\neq j\)`, then all pairings between the quaternionic lines `\(\mathbb H u_i\)` and `\(\mathbb H u_j\)` vanish, so `\(\mathbf h(u_i\alpha,u_j\beta)=0\)`.

Therefore the matrix of `\(\mathbf h\)` in the quaternionic basis `\((u_1,\dots,u_{a+b})\)` is
`\[
\operatorname{diag}(I_a,-I_b),
\]`
so `\(\mathbf h\)` is the standard quaternionic Hermitian form of signature `\((a,b)\)`.

Now let `\(g\in G_{\mathbb C}^J\)`. Then `\(g\)` is complex-linear, preserves `\(\langle\ ,\ \rangle\)`, and commutes with `\(J\)`, so
`\[
\mathbf h(gx,gy)
=\langle gx,Jgy\rangle-\langle gx,gy\rangle\mathbf j
=\langle gx,gJy\rangle-\langle gx,gy\rangle\mathbf j
=\mathbf h(x,y).
\]`
Thus every element of `\(G_{\mathbb C}^J\)` is a quaternionic-linear isometry of `\(\mathbf h\)`.

Conversely, let `\(g\)` be a quaternionic-linear isometry of `\(\mathbf h\)`. Quaternionic-linearity means exactly that `\(g\)` is complex-linear and commutes with `\(J\)`. Since
`\[
\mathbf h(gx,gy)=\mathbf h(x,y),
\]`
comparison of the complex part and the `\(\mathbf j\)`-part gives
`\[
\langle gx,Jgy\rangle=\langle x,Jy\rangle,
\qquad
\langle gx,gy\rangle=\langle x,y\rangle
\]`
for all `\(x,y\in V\)`. Hence `\(g\in G_{\mathbb C}\)` and `\(gJ=Jg\)`, so `\(g\in G_{\mathbb C}^J\)`.

Thus `\(G_{\mathbb C}^J\)` is exactly the quaternionic-linear isometry group of the standard quaternionic Hermitian form of signature `\((a,b)\)`. By the convention fixed in the completeness check,
`\[
G_{\mathbb C}^J\simeq \mathrm{Sp}(a,b)=\mathrm{Sp}(p/2,q/2).
\]`

# lemma lem:case-dstar

## statement
Assume `\(\star=D^*\)`, so `\((\epsilon,\dot\epsilon)=(1,-1)\)` and `\(p=q\)`. Write `\(n:=p=q\)`. Then there is an explicit quadruple `\((V,\langle\ ,\ \rangle,J,L)\)` satisfying properties (1)--(10), and
`\[
G_{\mathbb C}^J \simeq \mathrm O^*(2n)=\mathrm O^*(2p).
\]`

## proof
Take
`\[
V=\mathbb C^{2n}
\]`
with basis
`\[
e_1,\dots,e_n,f_1,\dots,f_n.
\]`
Define the symmetric bilinear form by
`\[
\langle e_i,e_j\rangle=\delta_{ij},
\qquad
\langle f_i,f_j\rangle=\delta_{ij},
\qquad
\langle e_i,f_j\rangle=0=\langle f_i,e_j\rangle.
\]`
Equivalently, the matrix of `\(\langle\ ,\ \rangle\)` in this basis is `\(I_{2n}\)`.

Define `\(J\)` conjugate-linearly by
`\[
Je_i=f_i,
\qquad
Jf_i=-e_i,
\]`
and define `\(L\)` complex-linearly by the same formulas
`\[
Le_i=f_i,
\qquad
Lf_i=-e_i.
\]`

Property (1) holds because `\(\dim_{\mathbb C}V=2n=2p=p+q=|\mathsf s|\)`. Property (2) holds because the form is symmetric and its matrix is `\(I_{2n}\)`.

For property (3),
`\[
J^2e_i=Jf_i=-e_i,
\qquad
J^2f_i=J(-e_i)=-f_i,
\]`
so `\(J^2=-1=\epsilon\dot\epsilon\)`. For property (4),
`\[
L^2e_i=Lf_i=-e_i,
\qquad
L^2f_i=L(-e_i)=-f_i,
\]`
so `\(L^2=-1=\dot\epsilon\)`.

For property (5), because the matrix of the form is real and `\(J\)` is orthogonal,
`\[
\langle Ju,Jv\rangle=\overline{\langle u,v\rangle}.
\]`
One can check this directly on the basis:
`\[
\langle Je_i,Je_j\rangle=\langle f_i,f_j\rangle=\delta_{ij}
=\overline{\langle e_i,e_j\rangle},
\]`
`\[
\langle Jf_i,Jf_j\rangle=\langle -e_i,-e_j\rangle=\delta_{ij}
=\overline{\langle f_i,f_j\rangle},
\]`
and all mixed terms vanish on both sides.

For property (6),
`\[
\langle Le_i,Le_j\rangle=\langle f_i,f_j\rangle=\delta_{ij}
=\langle e_i,e_j\rangle,
\]`
`\[
\langle Lf_i,Lf_j\rangle=\langle -e_i,-e_j\rangle=\delta_{ij}
=\langle f_i,f_j\rangle,
\]`
and again the mixed terms vanish, so `\(L\)` is an isometry of `\(\langle\ ,\ \rangle\)`.

For property (7),
`\[
LJ(e_i)=L(f_i)=-e_i=J(f_i)=JL(e_i),
\]`
and similarly on the `\(f_i\)`'s, so `\(LJ=JL\)`.

For property (8),
`\[
H(e_i,e_j)=\langle Le_i,Je_j\rangle=\langle f_i,f_j\rangle=\delta_{ij},
\]`
`\[
H(f_i,f_j)=\langle Lf_i,Jf_j\rangle=\langle -e_i,-e_j\rangle=\delta_{ij},
\]`
and all mixed terms vanish. Thus `\(H\)` is again the standard positive-definite Hermitian form.

Property (9) is not applicable here because `\(\dot\epsilon=-1\)`.

For property (10), because `\(J^2=-1\)`, the operator `\(J\)` defines a quaternionic structure on `\(V\)`. Let
`\[
u_i:=e_i \qquad (1\le i\le n).
\]`
Then `\((u_1,\dots,u_n)\)` is a quaternionic basis, since `\(Ju_i=f_i\)`.

Define an `\(\mathbb H\)`-valued form by
`\[
\kappa(x,y):=-\langle x,Jy\rangle+\langle x,y\rangle\,\mathbf j.
\]`
We claim that this is the standard quaternionic skew-Hermitian form with matrix `\(\mathbf j I_n\)` in the quaternionic basis `\((u_1,\dots,u_n)\)`.

Take one basis vector `\(u_i=e_i\)` and write
`\[
x=u_i\alpha,
\qquad
y=u_i\beta,
\qquad
\alpha=z+w\mathbf j,
\qquad
\beta=z'+w'\mathbf j
\qquad
(z,w,z',w'\in\mathbb C).
\]`
Because `\(u_i\mathbf j=Ju_i=f_i\)`, we have
`\[
x=e_iz+f_iw,
\qquad
y=e_iz'+f_iw'.
\]`
Using
`\(
\langle e_i,e_i\rangle=\langle f_i,f_i\rangle=1,
\langle e_i,f_i\rangle=\langle f_i,e_i\rangle=0,
\)`
we get
`\[
\langle x,Jy\rangle=-z\overline{w'}+w\overline{z'},
\qquad
\langle x,y\rangle=zz'+ww'.
\]`
Hence
`\[
\kappa(x,y)
=z\overline{w'}-w\overline{z'}+(zz'+ww')\mathbf j
=\alpha\,\mathbf j\,\overline{\beta}.
\]`
If `\(i\neq j\)`, then the quaternionic lines `\(\mathbb H u_i\)` and `\(\mathbb H u_j\)` are orthogonal for both `\(\langle\ ,\ \rangle\)` and `\(\kappa\)`, so `\(\kappa(u_i\alpha,u_j\beta)=0\)`.

Therefore
`\[
\kappa\!\left(\sum_{i=1}^n u_iq_i,\sum_{i=1}^n u_ir_i\right)
=\sum_{i=1}^n q_i\,\mathbf j\,\overline{r_i},
\]`
so `\(\kappa\)` is exactly the standard quaternionic skew-Hermitian form on `\(\mathbb H^n\)`.

Now let `\(g\in G_{\mathbb C}^J\)`. Then `\(g\)` is complex-linear, commutes with `\(J\)`, hence is quaternionic-linear, and preserves `\(\langle\ ,\ \rangle\)`. Therefore
`\[
\kappa(gx,gy)
=-\langle gx,Jgy\rangle+\langle gx,gy\rangle\mathbf j
=-\langle gx,gJy\rangle+\langle gx,gy\rangle\mathbf j
=\kappa(x,y).
\]`
So every element of `\(G_{\mathbb C}^J\)` is a quaternionic-linear isometry of `\(\kappa\)`.

Conversely, let `\(g\)` be a quaternionic-linear isometry of `\(\kappa\)`. Then `\(g\)` is complex-linear and commutes with `\(J\)`. Since
`\[
\kappa(gx,gy)=\kappa(x,y),
\]`
comparison of the complex part and the `\(\mathbf j\)`-part gives
`\[
\langle gx,Jgy\rangle=\langle x,Jy\rangle,
\qquad
\langle gx,gy\rangle=\langle x,y\rangle
\]`
for all `\(x,y\in V\)`. Hence `\(g\)` preserves `\(\langle\ ,\ \rangle\)` and lies in `\(G_{\mathbb C}^J\)`.

Thus `\(G_{\mathbb C}^J\)` is exactly the quaternionic-linear isometry group of the standard quaternionic skew-Hermitian form `\(\kappa\)`. By the convention fixed in the completeness check,
`\[
G_{\mathbb C}^J\simeq \mathrm O^*(2n)=\mathrm O^*(2p).
\]`

# theorem thm:classical-signature-models

## statement
For every classical signature `\(\mathsf s=(\star,p,q)\)`, there exists a quadruple
`\[
(V,\langle\ ,\ \rangle,J,L)
\]`
with the following properties:

1. `\(V\)` is a complex vector space of dimension `\(|\mathsf s|\)`.
2. `\(\langle\ ,\ \rangle\)` is a non-degenerate `\(\epsilon\)`-symmetric complex bilinear form on `\(V\)`.
3. `\(J:V\to V\)` is conjugate-linear and satisfies
   `\[
   J^2=\epsilon\dot\epsilon.
   \]`
4. `\(L:V\to V\)` is complex-linear and satisfies
   `\[
   L^2=\dot\epsilon.
   \]`
5. For all `\(u,v\in V\)`,
   `\[
   \langle Ju,Jv\rangle=\overline{\langle u,v\rangle}.
   \]`
6. For all `\(u,v\in V\)`,
   `\[
   \langle Lu,Lv\rangle=\langle u,v\rangle.
   \]`
7. `\(LJ=JL\)`.
8. The Hermitian form
   `\[
   H(u,v):=\langle Lu,Jv\rangle
   \]`
   is positive definite.
9. If `\(\dot\epsilon=1\)`, then
   `\[
   \dim\{v\in V:Lv=v\}=p,
   \qquad
   \dim\{v\in V:Lv=-v\}=q.
   \]`
10. With
    `\[
    G_{\mathbb C}=\operatorname{Isom}_{\mathbb C}(V,\langle\ ,\ \rangle),
    \qquad
    G_{\mathbb C}^{J}=Z_{G_{\mathbb C}}(J),
    \]`
    one has an isomorphism of real Lie groups
    `\[
    G_{\mathbb C}^{J}\simeq
    \begin{cases}
    \mathrm O(p,q),&\star=B\text{ or }D,\\
    \mathrm {Sp}_{2p}(\mathbb R),&\star=C\text{ or }\widetilde C,\\
    \mathrm {Sp}(p/2,q/2),&\star=C^*,\\
    \mathrm O^*(2p),&\star=D^*.
    \end{cases}
    \]`

## proof
The completeness check was carried out in Note `note:completeness-check`.

If `\(\star=B\)` or `\(\star=D\)`, apply Lemma `lem:case-bd`. It gives an explicit basis, a symmetric form, explicit operators `\(J\)` and `\(L\)`, verifies properties (1)--(9), and identifies `\(G_{\mathbb C}^J\)` with `\(\mathrm O(p,q)\)`.

If `\(\star=C\)` or `\(\star=\widetilde C\)`, then `\(p=q\)`. Apply Lemma `lem:case-c` with `\(n=p\)`. It gives an explicit symplectic basis, explicit operators `\(J\)` and `\(L\)`, verifies properties (1)--(8), and identifies `\(G_{\mathbb C}^J\)` with `\(\mathrm{Sp}_{2p}(\mathbb R)\)`. Property (9) is irrelevant here because `\(\dot\epsilon=-1\)`.

If `\(\star=C^*\)`, write `\(p=2a\)` and `\(q=2b\)`. Lemma `lem:case-cstar` gives an explicit symplectic basis, explicit operators `\(J\)` and `\(L\)`, proves properties (1)--(9), and identifies `\(G_{\mathbb C}^J\)` with `\(\mathrm{Sp}(a,b)=\mathrm{Sp}(p/2,q/2)\)`.

If `\(\star=D^*\)`, then `\(p=q\)`. Lemma `lem:case-dstar` gives an explicit orthonormal basis, explicit operators `\(J\)` and `\(L\)`, proves properties (1)--(8), and identifies `\(G_{\mathbb C}^J\)` with `\(\mathrm O^*(2p)\)`. Again property (9) is irrelevant because `\(\dot\epsilon=-1\)`.

These four cases exhaust all classical signatures. Hence for every classical signature `\(\mathsf s=(\star,p,q)\)` there exists a quadruple `\((V,\langle\ ,\ \rangle,J,L)\)` with properties (1)--(10), exactly as claimed.
