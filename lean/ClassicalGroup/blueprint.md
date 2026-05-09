# ClassicalGroup blueprint

Source: `/Users/hoxide/mydoc/inducedorbittoy/Rethlas/agents/generation/results/classicalgroup/blueprint_verified.md`

# proposition prop:completeness-check

## statement
The problem statement is complete after the following minimal convention fixes.

1. `\(\mathrm O(p,q)\)` means the full real orthogonal group preserving a real symmetric bilinear form of signature `\((p,q)\)`.
2. `\(\mathrm{Sp}(a,b)\)` means the quaternionic-linear isometry group of a quaternionic Hermitian form of signature `\((a,b)\)`.
3. `\(\mathrm O^*(2p)\)` means the quaternionic-linear isometry group of a non-degenerate quaternionic skew-Hermitian form on `\(\mathbb H^p\)`.
4. In the quaternionic cases we use the convention that quaternionic forms are linear in the first variable and conjugate-linear in the second.

No further repair is needed.

## proof
The only possible ambiguities are the connectedness convention for `\(\mathrm O(p,q)\)` and the linearity convention for quaternionic forms. Once those are fixed as above, every group appearing in the theorem has a standard meaning, and the rest of the statement is unambiguous.

# theorem thm:classicalgroup

## statement
For every classical signature
\[
\mathsf s=(\star,p,q),
\]
there exists a quadruple
\[
(V,\langle\ ,\ \rangle,J,L)
\]
with the following properties:

1. \(V\) is a complex vector space of dimension \(|\mathsf s|\).
2. \(\langle\ ,\ \rangle\) is a non-degenerate \(\epsilon\)-symmetric complex bilinear form on \(V\).
3. \(J:V\to V\) is conjugate-linear and satisfies
   \[
   J^2=\epsilon\dot\epsilon.
   \]
4. \(L:V\to V\) is complex-linear and satisfies
   \[
   L^2=\dot\epsilon.
   \]
5. For all \(u,v\in V\),
   \[
   \langle Ju,Jv\rangle=\overline{\langle u,v\rangle}.
   \]
6. For all \(u,v\in V\),
   \[
   \langle Lu,Lv\rangle=\langle u,v\rangle.
   \]
7. \(LJ=JL\).
8. The Hermitian form
   \[
   H(u,v):=\langle Lu,Jv\rangle
   \]
   is positive definite.
9. If \(\dot\epsilon=1\), then
   \[
   \dim\{v\in V:Lv=v\}=p,
   \qquad
   \dim\{v\in V:Lv=-v\}=q.
   \]
10. With
    \[
    G_{\mathbb C}=\operatorname{Isom}_{\mathbb C}(V,\langle\ ,\ \rangle),
    \qquad
    G_{\mathbb C}^{J}=Z_{G_{\mathbb C}}(J),
    \]
    one has an isomorphism of real Lie groups
    \[
    G_{\mathbb C}^{J}\simeq
    \begin{cases}
    \mathrm O(p,q),&\star=B\text{ or }D,\\
    \mathrm {Sp}_{2p}(\mathbb R),&\star=C\text{ or }\widetilde C,\\
    \mathrm {Sp}(p/2,q/2),&\star=C^*,\\
    \mathrm O^*(2p),&\star=D^*.
    \end{cases}
    \]

11. (**Uniqueness**) If another quadruple \((V',\langle\ ,\ \rangle',J',L')\) satisfies the same conditions for the same \(\mathsf s\), then there exists a complex-linear isomorphism \(\phi:V\to V'\) such that \(\phi\) carries \(\langle\ ,\ \rangle\) to \(\langle\ ,\ \rangle'\), \(J\) to \(J'\), and \(L\) to \(L'\).

## proof
We first fix the conventions from Proposition `prop:completeness-check`. In particular, in the quaternionic cases we view a complex vector space with a conjugate-linear operator `\(J\)` satisfying `\(J^2=-1\)` as a right `\(\mathbb H\)`-module by
\[
v\cdot(a+bj):=va+J(v)b
\qquad(a,b\in\mathbb C).
\]
We now construct the required quadruple in the four sign patterns.

### Case 1: `\(\star=B,D\)`

Here `\((\epsilon,\dot\epsilon)=(1,1)\)`. Let
\[
V=\mathbb C^{p+q},
\qquad
S_{p,q}:=\operatorname{diag}(I_p,-I_q),
\]
with standard basis `\(e_1,\dots,e_{p+q}\)`. Define
\[
\langle u,v\rangle:=u^T S_{p,q}v,
\qquad
J(u):=\overline u,
\qquad
L(u):=S_{p,q}u.
\]

Then `\(\dim_{\mathbb C}V=p+q=|\mathsf s|\)`. Since `\(S_{p,q}^T=S_{p,q}\)`, the form is symmetric. It is non-degenerate because `\(S_{p,q}\)` is invertible. Also `\(J\)` is conjugate-linear, `\(J^2=1=\epsilon\dot\epsilon\)`, `\(L^2=1=\dot\epsilon\)`, and `\(LJ=JL\)` because `\(S_{p,q}\)` is real.

For `\(u,v\in V\)`,
\[
\langle Ju,Jv\rangle
=\overline u^{\,T}S_{p,q}\overline v
=\overline{u^TS_{p,q}v}
=\overline{\langle u,v\rangle},
\]
and
\[
\langle Lu,Lv\rangle
=u^TS_{p,q}^3v
=u^TS_{p,q}v
=\langle u,v\rangle.
\]
Moreover
\[
H(u,v)=\langle Lu,Jv\rangle
=u^TS_{p,q}^2\overline v
=u^T\overline v,
\]
so `\(H\)` is the standard positive-definite Hermitian form on `\(\mathbb C^{p+q}\)`.

The `\((+1)\)`-eigenspace of `\(L\)` is spanned by `\(e_1,\dots,e_p\)`, hence has dimension `\(p\)`, and the `\((-1)\)`-eigenspace is spanned by `\(e_{p+1},\dots,e_{p+q}\)`, hence has dimension `\(q\)`.

Finally, `\(G_{\mathbb C}\)` is the complex orthogonal group of `\(u^TS_{p,q}v\)`. An element `\(g\in G_{\mathbb C}\)` satisfies `\(gJ=Jg\)` exactly when all matrix entries of `\(g\)` are real. Thus
\[
G_{\mathbb C}^J
=\{g\in\operatorname{GL}_{p+q}(\mathbb R):g^TS_{p,q}g=S_{p,q}\}
=\mathrm O(p,q).
\]
So properties (1)-(10) hold in the `\(B,D\)` case.

### Case 2: `\(\star=C,\widetilde C\)`

Here `\((\epsilon,\dot\epsilon)=(-1,-1)\)` and `\(p=q\)`. Write `\(r:=p=q\)`. Let
\[
V=\mathbb C^{2r}=\mathbb C^r\oplus\mathbb C^r,
\]
with basis
\[
e_1,\dots,e_r,f_1,\dots,f_r,
\]
where `\(e_i\)` is the `\(i\)`-th vector in the first summand and `\(f_i\)` is the `\(i\)`-th vector in the second summand. Define
\[
\langle (z,w),(z',w')\rangle:=z^Tw'-w^Tz',
\]
\[
J(z,w):=(\overline z,\overline w),
\qquad
L(z,w):=(w,-z).
\]

The form is alternating, hence `\((-1)\)`-symmetric, and it is non-degenerate. The map `\(J\)` is conjugate-linear and `\(J^2=1=\epsilon\dot\epsilon\)`. Also `\(L\)` is complex-linear and
\[
L^2(z,w)=L(w,-z)=(-z,-w)=- (z,w),
\]
so `\(L^2=-1=\dot\epsilon\)`. Because `\(J\)` is entrywise conjugation, `\(LJ=JL\)`.

For `\(u=(z,w)\)` and `\(v=(z',w')\)`,
\[
\langle Ju,Jv\rangle
=\overline z^{\,T}\overline w'-\overline w^{\,T}\overline z'
=\overline{z^Tw'-w^Tz'}
=\overline{\langle u,v\rangle},
\]
and
\[
\langle Lu,Lv\rangle
=\langle (w,-z),(w',-z')\rangle
=w^T(-z')-(-z)^Tw'
=z^Tw'-w^Tz'
=\langle u,v\rangle.
\]
Furthermore
\[
H((z,w),(z',w'))
=\langle (w,-z),(\overline z',\overline w')\rangle
=w^T\overline w'+z^T\overline z',
\]
which is the standard positive-definite Hermitian form.

Thus properties (1)-(8) hold. Property (9) is vacuous here because `\(\dot\epsilon=-1\)`.

For the group identification, `\(G_{\mathbb C}\)` is the complex symplectic group of the standard alternating form. The condition `\(gJ=Jg\)` says exactly that the matrix of `\(g\)` is real. Hence
\[
G_{\mathbb C}^J
=\{g\in\operatorname{GL}_{2r}(\mathbb R):g^T\Omega_rg=\Omega_r\}
=\mathrm{Sp}_{2r}(\mathbb R)
=\mathrm{Sp}_{2p}(\mathbb R),
\]
where
\[
\Omega_r=
\begin{pmatrix}
0&I_r\\
-I_r&0
\end{pmatrix}.
\]
The same calculation applies to `\(\widetilde C\)`: the metaplectic double cover is not part of the present construction, so here one only obtains `\(\mathrm{Sp}_{2p}(\mathbb R)\)`.

### Case 3: `\(\star=C^*\)`

Here `\((\epsilon,\dot\epsilon)=(-1,1)\)` and `\(p,q\)` are even. Write
\[
p=2a,\qquad q=2b,\qquad m:=a+b,
\]
and let
\[
S_{a,b}:=\operatorname{diag}(I_a,-I_b).
\]
Set
\[
V=\mathbb C^{2m}=\mathbb C^m\oplus\mathbb C^m,
\]
with basis `\(e_1,\dots,e_m,f_1,\dots,f_m\)` as above. Define
\[
\langle (z,w),(z',w')\rangle:=z^TS_{a,b}w'-w^TS_{a,b}z',
\]
\[
J(z,w):=(-\overline w,\overline z),
\qquad
L(z,w):=(S_{a,b}z,S_{a,b}w).
\]

The form is alternating because its matrix is
\[
\begin{pmatrix}
0&S_{a,b}\\
-S_{a,b}&0
\end{pmatrix}.
\]
It is non-degenerate because `\(S_{a,b}\)` is invertible. The map `\(J\)` is conjugate-linear and
\[
J^2(z,w)=J(-\overline w,\overline z)=(-z,-w)=-(z,w),
\]
so `\(J^2=-1=\epsilon\dot\epsilon\)`. Also `\(L\)` is complex-linear and `\(L^2=1=\dot\epsilon\)`. Since `\(S_{a,b}\)` is real, `\(LJ=JL\)`.

Now compute
\[
\langle Ju,Jv\rangle
=\langle (-\overline w,\overline z),(-\overline w',\overline z')\rangle
=\overline z^{\,T}S_{a,b}\overline w'
-\overline w^{\,T}S_{a,b}\overline z'
=\overline{\langle u,v\rangle}.
\]
Also
\[
\langle Lu,Lv\rangle
=z^TS_{a,b}^3w'-w^TS_{a,b}^3z'
=\langle u,v\rangle,
\]
because `\(S_{a,b}^2=I_m\)`. Finally
\[
H((z,w),(z',w'))
=\langle (S_{a,b}z,S_{a,b}w),(-\overline w',\overline z')\rangle
=z^T\overline z'+w^T\overline w',
\]
so `\(H\)` is again the standard positive-definite Hermitian form.

The `\((+1)\)`-eigenspace of `\(L\)` is
\[
\mathbb C^a\oplus 0\oplus \mathbb C^a\oplus 0,
\]
which has complex dimension `\(2a=p\)`, and the `\((-1)\)`-eigenspace has complex dimension `\(2b=q\)`. Thus property (9) holds.

To identify the group, use the quaternionic structure coming from `\(J\)`. Regard `\(V\)` as a right `\(\mathbb H\)`-module by `\(v\cdot j:=Jv\)`. Define
\[
h(u,v):=\langle u,Jv\rangle+\langle u,v\rangle j.
\]
Because `\(J\)` is conjugate-linear and `\(J^2=-1\)`, this is `\(\mathbb H\)`-linear in the first variable and conjugate-linear in the second. In coordinates,
\[
h((z,w),(z',w'))
=z^TS_{a,b}\overline z'+w^TS_{a,b}\overline w'
+(z^TS_{a,b}w'-w^TS_{a,b}z')j.
\]
Its diagonal values on the quaternionic basis `\(q_r:=e_r\)` are
\[
h(q_r,q_r)=
\begin{cases}
1,&1\le r\le a,\\
-1,&a<r\le a+b,
\end{cases}
\]
so `\(h\)` is the standard quaternionic Hermitian form of signature `\((a,b)\)`.

Moreover, if `\(g\in G_{\mathbb C}^J\)`, then `\(g\)` commutes with `\(J\)`, hence is quaternionic-linear, and
\[
h(gu,gv)
=\langle gu,Jgv\rangle+\langle gu,gv\rangle j
=\langle gu,gJv\rangle+\langle gu,gv\rangle j
=h(u,v).
\]
So `\(G_{\mathbb C}^J\)` is contained in the quaternionic isometry group of `\(h\)`. Conversely, if a quaternionic-linear map preserves `\(h\)`, then it preserves both the complex part `\(\langle u,Jv\rangle\)` and the `\(j\)`-part `\(\langle u,v\rangle\)`, hence it preserves `\(\langle\ ,\ \rangle\)` and commutes with `\(J\)`. Therefore
\[
G_{\mathbb C}^J\simeq \mathrm{Sp}(a,b)=\mathrm{Sp}(p/2,q/2).
\]
So properties (1)-(10) hold in the `\(C^*\)` case.

### Case 4: `\(\star=D^*\)`

Here `\((\epsilon,\dot\epsilon)=(1,-1)\)` and `\(p=q\)`. Write `\(r:=p=q\)`. Let
\[
V=\mathbb C^{2r}=\mathbb C^r\oplus\mathbb C^r,
\]
with basis `\(e_1,\dots,e_r,f_1,\dots,f_r\)`. Define
\[
\langle (z,w),(z',w')\rangle:=-i(z^Tw'+w^Tz'),
\]
\[
J(z,w):=(-\overline w,\overline z),
\qquad
L(z,w):=(iz,-iw).
\]

The matrix of the form is
\[
-i
\begin{pmatrix}
0&I_r\\
I_r&0
\end{pmatrix},
\]
so the form is symmetric and non-degenerate. Again `\(J\)` is conjugate-linear and `\(J^2=-1=\epsilon\dot\epsilon\)`. Also `\(L\)` is complex-linear and
\[
L^2(z,w)=(-z,-w)=-(z,w),
\]
so `\(L^2=-1=\dot\epsilon\)`. A direct check gives `\(LJ=JL\)`.

For `\(u=(z,w)\)` and `\(v=(z',w')\)`,
\[
\langle Ju,Jv\rangle
=-i\bigl((-\overline w)^T\overline z'+\overline z^{\,T}(-\overline w')\bigr)
=\overline{-i(z^Tw'+w^Tz')}
=\overline{\langle u,v\rangle}.
\]
Also
\[
\langle Lu,Lv\rangle
=-i\bigl((iz)^T(-iw')+(-iw)^T(iz')\bigr)
=-i(z^Tw'+w^Tz')
=\langle u,v\rangle.
\]
Finally
\[
H((z,w),(z',w'))
=\langle (iz,-iw),(-\overline w',\overline z')\rangle
=z^T\overline z'+w^T\overline w',
\]
so `\(H\)` is positive definite. Thus properties (1)-(8) hold, and property (9) is again vacuous.

As in the `\(C^*\)` case, `\(J\)` gives a right `\(\mathbb H\)`-module structure on `\(V\)`. Define
\[
\kappa(u,v):=\langle u,Jv\rangle+\langle u,v\rangle j.
\]
Because the bilinear form is symmetric and `\(J^2=-1\)`, one has
\[
\kappa(v,u)=-\overline{\kappa(u,v)},
\]
so `\(\kappa\)` is quaternionic skew-Hermitian. In coordinates,
\[
\kappa((z,w),(z',w'))
=-i(z^T\overline z'-w^T\overline w')
-i(z^Tw'+w^Tz')j.
\]
Its values on the quaternionic basis `\(q_r:=e_r\)` satisfy
\[
\kappa(q_r,q_s)=-i\,\delta_{rs},
\]
so this is the standard non-degenerate quaternionic skew-Hermitian form on `\(\mathbb H^r\)`.

If `\(g\in G_{\mathbb C}^J\)`, then `\(g\)` is quaternionic-linear and
\[
\kappa(gu,gv)
=\langle gu,Jgv\rangle+\langle gu,gv\rangle j
=\kappa(u,v).
\]
Conversely, a quaternionic-linear isometry of `\(\kappa\)` preserves both `\(\langle u,Jv\rangle\)` and `\(\langle u,v\rangle\)`, so it belongs to `\(G_{\mathbb C}^J\)`. Therefore
\[
G_{\mathbb C}^J\simeq \mathrm O^*(2r)=\mathrm O^*(2p).
\]
This proves properties (1)-(10) in the `\(D^*\)` case.

### Uniqueness

Let `\((V,\langle\ ,\ \rangle,J,L)\)` and `\((V',\langle\ ,\ \rangle',J',L')\)` be two quadruples for the same classical signature. We show that each is isomorphic to the corresponding standard model above, hence to each other.

#### Uniqueness for `\(B,D\)`

Set
\[
V_{\mathbb R}:=V^J=\{v\in V:Jv=v\}.
\]
Then `\(V=V_{\mathbb R}\otimes_{\mathbb R}\mathbb C\)`, and `\(\langle\ ,\ \rangle\)` restricts to a real symmetric bilinear form `\(B\)` on `\(V_{\mathbb R}\)`. Let
\[
E_+^{\mathbb R}:=\ker(L-1)\cap V_{\mathbb R},
\qquad
E_-^{\mathbb R}:=\ker(L+1)\cap V_{\mathbb R}.
\]
Because `\(LJ=JL\)`, the complex eigenspaces
\[
\widetilde E_+:=\ker(L-1),
\qquad
\widetilde E_-:=\ker(L+1)
\]
are `\(J\)`-stable. If `\(v\in \widetilde E_+\)` and we write `\(v=x+iy\)` with `\(x,y\in V_{\mathbb R}\)`, then
\[
x-iy
=Jv
\in \widetilde E_+,
\]
so
\[
x=\frac12(v+Jv)\in \widetilde E_+\cap V_{\mathbb R}=E_+^{\mathbb R},
\qquad
y=\frac{1}{2i}(v-Jv)\in E_+^{\mathbb R}.
\]
Hence `\(\widetilde E_+=E_+^{\mathbb R}\otimes_{\mathbb R}\mathbb C\)`. The same argument gives
\[
\widetilde E_-=E_-^{\mathbb R}\otimes_{\mathbb R}\mathbb C.
\]
Property (9) says `\(\dim_{\mathbb C}\widetilde E_+=p\)` and `\(\dim_{\mathbb C}\widetilde E_-=q\)`, so
\[
\dim_{\mathbb R}E_+^{\mathbb R}=p,
\qquad
\dim_{\mathbb R}E_-^{\mathbb R}=q.
\]

If `\(x\in E_+^{\mathbb R}\)` and `\(y\in E_-^{\mathbb R}\)`, then
\[
B(x,y)=B(Lx,Ly)=B(x,-y)=-B(x,y),
\]
so `\(E_+^{\mathbb R}\perp_B E_-^{\mathbb R}\)`. Also
\[
H(x,x)=\langle Lx,Jx\rangle=\langle x,x\rangle=B(x,x)>0
\qquad(x\in E_+^{\mathbb R}\setminus 0),
\]
while
\[
H(y,y)=\langle Ly,Jy\rangle=-\langle y,y\rangle=-B(y,y)>0
\qquad(y\in E_-^{\mathbb R}\setminus 0).
\]
Thus `\(B\)` is positive definite on `\(E_+^{\mathbb R}\)` and negative definite on `\(E_-^{\mathbb R}\)`. Choosing a `\(B\)`-orthonormal basis of `\(E_+^{\mathbb R}\)` and a `\((-B)\)`-orthonormal basis of `\(E_-^{\mathbb R}\)` gives a real basis in which
\[
B=\operatorname{diag}(I_p,-I_q),
\qquad
L=\operatorname{diag}(I_p,-I_q),
\qquad
J=\text{complex conjugation}.
\]
So every solution in this sign case is isomorphic to the model of Case 1.

#### Uniqueness for `\(C,\widetilde C\)`

Again put `\(V_{\mathbb R}:=V^J\)`. The restriction
\[
\omega:=\langle\ ,\ \rangle|_{V_{\mathbb R}}
\]
is a real symplectic form, and
\[
g:=H|_{V_{\mathbb R}}
\]
is a positive-definite real inner product. For `\(x,y\in V_{\mathbb R}\)`,
\[
g(x,y)=\langle Lx,y\rangle=\omega(Lx,y).
\]
Since `\(\omega(Lx,Ly)=\omega(x,y)\)` by property (6), we get
\[
g(Lx,Ly)=g(x,y),
\qquad
g(x,Lx)=\omega(Lx,Lx)=0.
\]
Choose a `\(g\)`-unit vector `\(e_1\)` and set `\(f_1:=-Le_1\)`. Then
\[
g(e_1,f_1)=0,
\qquad
\omega(e_1,f_1)=g(e_1,e_1)=1.
\]
Because `\(L\)` is `\(g\)`-orthogonal, the `\(g\)`-orthogonal complement of `\(\operatorname{span}_{\mathbb R}\{e_1,f_1\}\)` is `\(L\)`-stable. Repeating the construction inductively yields a `\(g\)`-orthonormal basis
\[
e_1,\dots,e_p,f_1,\dots,f_p
\]
with `\(f_i=-Le_i\)` and
\[
\omega(e_i,f_j)=\delta_{ij},
\qquad
\omega(e_i,e_j)=\omega(f_i,f_j)=0.
\]
In the corresponding complex basis the matrices of `\(\omega,J,L\)` are exactly those of Case 2. Hence every solution is isomorphic to the model of Case 2.

#### Uniqueness for `\(C^*\)`

Now `\(J^2=-1\)`, so `\(V\)` is a right `\(\mathbb H\)`-module. Put
\[
E_+:=\ker(L-1),
\qquad
E_-:=\ker(L+1).
\]
Because `\(LJ=JL\)`, both `\(E_+\)` and `\(E_-\)` are quaternionic subspaces. Their complex dimensions are `\(p=2a\)` and `\(q=2b\)`.

If `\(x\in E_+\)` and `\(y\in E_-\)`, then
\[
\langle x,y\rangle=\langle Lx,Ly\rangle=\langle x,-y\rangle=-\langle x,y\rangle,
\]
so `\(\langle x,y\rangle=0\)`. Also
\[
\langle x,Jy\rangle
=\langle Lx,JLy\rangle
=\langle x,-Jy\rangle
=-\langle x,Jy\rangle,
\]
so `\(\langle x,Jy\rangle=0\)`. Thus `\(E_+\)` and `\(E_-\)` are orthogonal for both `\(\langle\ ,\ \rangle\)` and the quaternionic Hermitian form `\(h(u,v)=\langle u,Jv\rangle+\langle u,v\rangle j\)`.

On `\(E_+\)` one has
\[
\langle x,Jy\rangle
=\langle Lx,Jy\rangle
=H(x,y),
\]
while on `\(E_-\)` one has
\[
\langle x,Jy\rangle
=-\;H(x,y).
\]
Therefore `\(H\)` is positive definite on each quaternionic subspace, and it is compatible with `\(J\)`.

Choose `\(H\)`-unit vectors `\(e_1,\dots,e_a\in E_+\)` inductively so that
\[
\{e_1,Je_1,\dots,e_a,Je_a\}
\]
is an `\(H\)`-orthonormal basis of `\(E_+\)`. This is possible because the `\(H\)`-orthogonal complement of a quaternionic line `\(\mathbb H e\)` is `\(J\)`-stable. Likewise choose `\(H\)`-unit vectors `\(e_{a+1},\dots,e_{a+b}\in E_-\)` such that
\[
\{e_{a+1},Je_{a+1},\dots,e_{a+b},Je_{a+b}\}
\]
is an `\(H\)`-orthonormal basis of `\(E_-\)`. Put
\[
f_r:=Je_r\qquad(1\le r\le a+b).
\]

For `\(1\le r,s\le a\)`,
\[
\langle e_r,f_s\rangle
=\langle e_r,Je_s\rangle
=H(e_r,e_s)
=\delta_{rs}.
\]
For `\(a<r,s\le a+b\)`,
\[
\langle e_r,f_s\rangle
=\langle e_r,Je_s\rangle
=-H(e_r,e_s)
=-\delta_{rs}.
\]
Also `\(\langle e_r,e_s\rangle=\langle f_r,f_s\rangle=0\)` because the form is alternating and
\[
\langle f_r,f_s\rangle
=\langle Je_r,Je_s\rangle
=\overline{\langle e_r,e_s\rangle}.
\]
So in the complex basis
\[
e_1,\dots,e_{a+b},f_1,\dots,f_{a+b}
\]
the matrices of `\(\langle\ ,\ \rangle,J,L\)` are exactly those of Case 3. Hence every solution is isomorphic to the model of Case 3.

#### Uniqueness for `\(D^*\)`

Set
\[
A:=-iL.
\]
Then `\(A^2=1\)`. Also
\[
H(Au,v)
=-iH(Lu,v)
=-i(-H(u,Lv))
=H(u,Av),
\]
so `\(A\)` is `\(H\)`-self-adjoint. Let
\[
E_+:=\ker(A-1),
\qquad
E_-:=\ker(A+1).
\]
Then `\(V=E_+\oplus E_-\)` is an `\(H\)`-orthogonal decomposition. Because `\(J\)` is conjugate-linear and `\(LJ=JL\)`,
\[
JAu
=J(-iLu)
=iLJu
=-AJu,
\]
so `\(AJ=-JA\)`. Hence `\(J\)` maps `\(E_+\)` anti-linearly isomorphically onto `\(E_-\)`. In particular,
\[
\dim_{\mathbb C}E_+=\dim_{\mathbb C}E_-=p.
\]

If `\(x,y\in E_+\)`, then `\(Lx=ix\)` and `\(Ly=iy\)`, so property (6) gives
\[
\langle x,y\rangle
=\langle Lx,Ly\rangle
=\langle ix,iy\rangle
=-\langle x,y\rangle,
\]
hence `\(\langle x,y\rangle=0\)`. The same argument shows that `\(\langle x,y\rangle=0\)` for `\(x,y\in E_-\)`.

Choose an `\(H\)`-orthonormal basis `\(e_1,\dots,e_p\)` of `\(E_+\)` and put
\[
f_r:=Je_r\in E_-.
\]
Then `\(\{e_1,\dots,e_p,f_1,\dots,f_p\}\)` is an `\(H\)`-orthonormal basis of `\(V\)`. Moreover
\[
\delta_{rs}
=H(e_r,e_s)
=\langle Le_r,Je_s\rangle
=\langle ie_r,f_s\rangle
=i\langle e_r,f_s\rangle,
\]
so
\[
\langle e_r,f_s\rangle=-i\,\delta_{rs}.
\]
Since `\(E_+\)` and `\(E_-\)` are totally isotropic, the matrix of `\(\langle\ ,\ \rangle\)` in this basis is exactly the matrix of Case 4, and `\(L\)` acts by `\(i\)` on `\(E_+\)` and by `\(-i\)` on `\(E_-\)`. Therefore every solution is isomorphic to the model of Case 4.

We have now proved existence, properties (1)-(10), and uniqueness in all four sign patterns. This proves the theorem.
