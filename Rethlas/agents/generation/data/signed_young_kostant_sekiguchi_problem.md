# Problem Suite: Signed Young Diagrams and Kostant-Sekiguchi Compatibility

## Main Goal

Prove the following compatibility statement, not the full classification of
nilpotent orbits.

Let \(\mathsf s=(\star,p,q)\) be a classical signature, and let
\[
(V,\langle\ ,\ \rangle,J,L)
\]
be the corresponding classical space.  Let
\[
G_{\mathbb C}:=\operatorname{Isom}_{\mathbb C}(V,\langle\ ,\ \rangle),
\qquad
\mathfrak g:=\operatorname{Lie}(G_{\mathbb C}),
\]
\[
G:=Z_{G_{\mathbb C}}(J),\qquad
K:=Z_{G_{\mathbb C}}(L),
\]
\[
\mathfrak g_{\mathbb R}:=\{X\in\mathfrak g:JXJ^{-1}=X\},
\qquad
\mathfrak p:=\{X\in\mathfrak g:LXL^{-1}=-X\}.
\]

Kostant-Sekiguchi gives a bijection
\[
\operatorname{Nil}(\mathfrak p)/K
\longrightarrow
\operatorname{Nil}(\sqrt{-1}\,\mathfrak g_{\mathbb R})/G.
\]
For a real-form nilpotent \(G\)-orbit
\[
\mathcal N\subset\sqrt{-1}\,\mathfrak g_{\mathbb R},
\]
there are two signed Young diagrams:

1. the **direct real-form signed Young diagram**
   \(\operatorname{SYD}_{\mathbb R}(\mathcal N)\), defined directly from the
   real nilpotent orbit \(\mathcal N\);
2. the **Kostant-Sekiguchi signed Young diagram**
   \(\operatorname{SYD}_{KS}(\mathcal N)\), defined by taking the inverse
   \(K\)-orbit
   \[
   \mathcal O=KS^{-1}(\mathcal N)\subset\mathfrak p
   \]
   and then taking the signed Young diagram of \(\mathcal O\).

The target theorem is
\[
\boxed{
\operatorname{SYD}_{\mathbb R}(\mathcal N)
=
\operatorname{SYD}_{KS}(\mathcal N)
}
\]
for every nilpotent \(G\)-orbit
\(\mathcal N\subset\sqrt{-1}\,\mathfrak g_{\mathbb R}\).
Both sides must be signed Young diagrams of type \(\star\) whose total
signature is exactly the signature \((p,q)\) of the original classical space:
\[
\operatorname{SYD}_{\mathbb R}(\mathcal N),
\operatorname{SYD}_{KS}(\mathcal N)
\in \operatorname{SYD}_{\star}(p,q).
\]

The point of this suite is to split that theorem into small solver-ready
subproblems.

## What Must Be Aligned

The main technical issue is not orbit classification; it is the consistency of
notation.  A correct proof must align the following four pieces of data.

1. **Ambient signature.**  The classical space \(V\) has signature
   \[
   \mathsf s=(\star,p,q).
   \]
   The ordered pair \((p,q)\) is the same ordered pair used in the definition
   of classical signatures.

2. **Multiplicity-space signature.**  For each \(i\), the multiplicity space
   \(M_i(\varphi)\) has a classical signature
   \[
   \operatorname{sig}(M_i(\varphi))
   =
   (\star_i^\varphi,p_i^\varphi,q_i^\varphi).
   \]
   The symbols \(p_i^\varphi,q_i^\varphi\) must mean the signature parameters
   of \(M_i(\varphi)\) in exactly the same convention as the ambient
   \((p,q)\), not a newly chosen sign convention.

3. **Signed Young diagram entries.**  The \(i\)-th row-entry of both signed
   Young diagrams must be
   \[
   (p_i^\varphi,q_i^\varphi).
   \]
   Thus the equality
   \(\operatorname{SYD}_{\mathbb R}=\operatorname{SYD}_{KS}\) is an equality
   of ordered pairs at every row length \(i\), not merely an equality after
   forgetting signs or interchanging \(p_i\) and \(q_i\).

4. **Total signature.**  The signed Young diagram must reconstruct the
   original ambient signature:
   \[
   \operatorname{Sign}(\mathcal D)=(p,q).
   \]
   This is a required compatibility condition, not an optional consistency
   check.

Before any agent attempts the Kostant-Sekiguchi equality, it must produce the
following alignment table:

| Object | Notation | What the signature means | Required output |
|---|---|---|---|
| Ambient classical space | \(V\) | classical signature of the given space | \((\star,p,q)\) |
| \(i\)-th multiplicity space | \(M_i(\varphi)\) | classical signature in the same convention as \(V\) | \((\star_i^\varphi,p_i^\varphi,q_i^\varphi)\) |
| Direct real nilpotent label | \(\operatorname{SYD}_{\mathbb R}(\mathcal N)(i)\) | the row-length \(i\) signed entry from the real-form convention | \((p_i^\varphi,q_i^\varphi)\) |
| KS-side label | \(\operatorname{SYD}_{\mathfrak p}(K\cdot X_\varphi)(i)\) | the row-length \(i\) signed entry from the \(\mathfrak p\)-orbit convention | \((p_i^\varphi,q_i^\varphi)\) |
| Total diagram signature | \(\operatorname{Sign}(\mathcal D)\) | tensor-product reconstruction of the ambient signature | \((p,q)\) |

If any row of this table cannot be justified from the stated conventions, the
solver must stop and report the missing convention.  In particular, it is not
enough to show that the two diagrams have the same underlying unsigned Young
diagram or that the sums of their signs agree.

## Common Notation

Let
\[
\star\in\{B,C,D,\widetilde C,C^*,D^*\}.
\]
Define an equivalence relation \(\sim\) on labels by
\[
\{\{B,D\},\{C,\widetilde C\},\{C^*\},\{D^*\}\}.
\]
Let \(\star'\) be the Howe-dual label of \(\star\).  Only its \(\sim\)-class
is needed:
\[
\star\in\{B,D\}\Rightarrow \star'\in\{C,\widetilde C\},
\qquad
\star\in\{C,\widetilde C\}\Rightarrow \star'\in\{B,D\},
\]
\[
\star=C^*\Rightarrow \star'=D^*,
\qquad
\star=D^*\Rightarrow \star'=C^*.
\]

For \(i\ge 1\), put
\[
\operatorname{St}_i:=\operatorname{Sym}^{i-1}(\mathbb C^2).
\]
It carries the fixed standard triple
\[
(\langle\ ,\ \rangle_{\operatorname{St}_i},
J_{\operatorname{St}_i},L_{\operatorname{St}_i})
\]
from the source text:

1. \(\langle\ ,\ \rangle_{\operatorname{St}_i}\) is
   \(\mathfrak{sl}_2\)-invariant;
2. \(J_{\operatorname{St}_i}\) is conjugation from
   \(\operatorname{Sym}^{i-1}(\mathbb R^2)\);
3. \(L_{\operatorname{St}_i}=(-1)^{\lfloor(i-1)/2\rfloor}
   \operatorname{Sym}^{i-1}
   \begin{psmallmatrix}0&1\\-1&0\end{psmallmatrix}\), so
   \(L_{\operatorname{St}_i}^2=(-1)^{i-1}\);
4. \((u,v)\mapsto
   \langle L_{\operatorname{St}_i}u,J_{\operatorname{St}_i}v\rangle\)
   is positive definite.

The classical signature of \(\operatorname{St}_i\) is
\[
\begin{cases}
(B,(i+1)/2,(i-1)/2),& i\text{ odd},\\
(C,i/2,i/2),& i\text{ even}.
\end{cases}
\]

Let
\[
X_0=
\begin{pmatrix}1&\sqrt{-1}\\ \sqrt{-1}&-1\end{pmatrix},
\qquad
e_0=
\begin{pmatrix}0&\sqrt{-1}\\0&0\end{pmatrix}.
\]
Let
\[
\tau(Y):=JYJ^{-1},\qquad \theta(Y):=LYL^{-1}
\]
on \(\mathfrak g\).  Thus
\(\mathfrak g_{\mathbb R}=\{Y:\tau(Y)=Y\}\) and
\(\sqrt{-1}\mathfrak g_{\mathbb R}=\{Y:\tau(Y)=-Y\}\).

An **admissible Kostant-Sekiguchi parameter** is a Lie algebra homomorphism
\[
\varphi:\mathfrak{sl}_2\to\mathfrak g
\]
satisfying
\[
\varphi(\overline{x})=\tau(\varphi(x)),
\qquad
\varphi(-x^t)=\theta(\varphi(x))
\qquad(x\in\mathfrak{sl}_2).
\]
For such \(\varphi\), set
\[
X_\varphi:=\varphi(X_0),\qquad
\xi_\varphi:=\varphi(e_0).
\]

For every \(\varphi\), let \(V_\varphi\) denote \(V\) as an
\(\mathfrak{sl}_2\)-module through \(\varphi\), and write
\[
M_i(\varphi):=\operatorname{Hom}_{\mathfrak{sl}_2}
(\operatorname{St}_i,V_\varphi).
\]
Then
\[
V_\varphi\simeq
\bigoplus_{i\ge1}M_i(\varphi)\otimes\operatorname{St}_i.
\]

## Signed Young Diagrams

A signed Young diagram is a finitely supported map
\[
\mathcal D:\mathbb N^+\to\mathbb N\times\mathbb N,
\qquad
i\mapsto(p_i,q_i).
\]
It has type \(\star\) if:

1. for \(\star\in\{B,D\}\), \(p_i=q_i\) when \(i\) is even;
2. for \(\star\in\{C,\widetilde C\}\), \(p_i=q_i\) when \(i\) is odd;
3. for \(\star=C^*\), \(p_i,q_i\) are both even when \(i\) is odd, and
   \(p_i=q_i\) when \(i\) is even;
4. for \(\star=D^*\), \(p_i=q_i\) when \(i\) is odd, and \(p_i,q_i\) are both
   even when \(i\) is even.

Let \(\operatorname{SYD}_{\star}\) be the set of signed Young diagrams of type
\(\star\).

For \(\mathcal D(i)=(p_i,q_i)\), define its total signature
\[
\operatorname{Sign}(\mathcal D)=(p_{\mathcal D},q_{\mathcal D})
\]
by
\[
\begin{aligned}
(p_{\mathcal D},q_{\mathcal D})
=&\sum_{a\ge1}
\bigl(a p_{2a}+a q_{2a},\,a p_{2a}+a q_{2a}\bigr)\\
&+\sum_{a\ge1}
\bigl(a p_{2a-1}+(a-1)q_{2a-1},\,
(a-1)p_{2a-1}+a q_{2a-1}\bigr).
\end{aligned}
\]
This is the signature contributed by the summands
\[
M_i\otimes\operatorname{St}_i
\]
when \(\operatorname{sig}(M_i)=(\star_i,p_i,q_i)\).

Define
\[
\operatorname{SYD}_{\star}(p,q)
:=
\{\mathcal D\in\operatorname{SYD}_{\star}:
\operatorname{Sign}(\mathcal D)=(p,q)\}.
\]

For a finite-dimensional classical space \(M\), write
\[
\operatorname{sig}(M)=(\star_M,p_M,q_M)
\]
for its classical signature.  The values \(p_M,q_M\) mean the same signature
parameters as in the already-constructed theory of classical spaces; do not
replace them by the signature of the positive definite Hermitian form.

## Allowed Inputs

The solver may use these facts as black boxes.

1. Complete reducibility of finite-dimensional
   \(\mathfrak{sl}_2\)-modules.
2. The fixed standard triples on \(\operatorname{St}_i\) listed above.
3. Existence and uniqueness up to \(K\)-conjugacy of admissible
   Kostant-Sekiguchi parameters for nilpotent \(K\)-orbits in \(\mathfrak p\).
4. The Kostant-Sekiguchi bijection:
   \[
   K\cdot X_\varphi\longmapsto G\cdot \xi_\varphi
   \]
   from nilpotent \(K\)-orbits in \(\mathfrak p\) to nilpotent \(G\)-orbits in
   \(\sqrt{-1}\mathfrak g_{\mathbb R}\).
5. The standard real-form signed Young diagram classification may be quoted
   only in the following limited form: a real-form nilpotent orbit
   \(\mathcal N\subset\sqrt{-1}\mathfrak g_{\mathbb R}\) has a direct signed
   Young diagram \(\operatorname{SYD}_{\mathbb R}(\mathcal N)\), computed from
   any admissible real/Cayley-normalized \(\mathfrak{sl}_2\)-parameter by the
   classical signatures of the multiplicity spaces.

Do not use the desired equality
\(\operatorname{SYD}_{\mathbb R}=\operatorname{SYD}_{KS}\) as a black box.

## Problem DAG

The subproblems below are meant to be solved in order.  Each one should return
a short proof or a precise failure report before the next one is attempted.

### P-1. Signature Convention Audit

**Depends on:** common notation and the already-constructed theory of
classical spaces.

**Task.**  State precisely what the symbols
\[
\star,\quad p,q,\quad \star_i^\varphi,\quad p_i^\varphi,q_i^\varphi
\]
mean.  In particular:

1. record the signature restrictions on \((\star,p,q)\);
2. record how \(p,q\) are read from a classical space of type
   \(B,C,D,\widetilde C,C^*,D^*\);
3. record the identical convention for
   \((p_i^\varphi,q_i^\varphi)\) on the multiplicity spaces;
4. state explicitly that neither the direct real-form construction nor the
   Kostant-Sekiguchi construction is allowed to swap
   \(p_i^\varphi\) and \(q_i^\varphi\).

**Expected output.**  A signature dictionary.  If the convention for any of
\(C^*\) or \(D^*\) is missing, stop and state exactly which convention must be
supplied before continuing.  The output must include the alignment table from
the section "What Must Be Aligned".

### P-0. Tensor-Product Signature Dictionary

**Depends on:** P-1 and the fixed signatures of \(\operatorname{St}_i\).

**Task.**  For a classical space \(M_i\) of signature
\[
(\star_i,p_i,q_i),
\]
compute the contribution of
\[
M_i\otimes\operatorname{St}_i
\]
to the ambient signature of \(V\).  The output must be the table
\[
i=2a:\quad
(p,q)\text{-contribution}
=
\bigl(a p_{2a}+a q_{2a},\,a p_{2a}+a q_{2a}\bigr),
\]
\[
i=2a-1:\quad
(p,q)\text{-contribution}
=
\bigl(a p_{2a-1}+(a-1)q_{2a-1},\,
(a-1)p_{2a-1}+a q_{2a-1}\bigr).
\]
Also determine, from the tensor-product type rule, why
\[
\star_i\sim\star\quad(i\text{ odd}),
\qquad
\star_i\sim\star'\quad(i\text{ even}).
\]

**Expected output.**  A table aligning:
\[
i,\quad \operatorname{sig}(\operatorname{St}_i),\quad
\operatorname{sig}(M_i),\quad
\operatorname{sig}(M_i\otimes\operatorname{St}_i).
\]
This table is the reference dictionary for all later signed Young diagram
entries.  It must explicitly identify which part of the tensor product
contributes to the ambient \(p\)-coordinate and which part contributes to the
ambient \(q\)-coordinate.

### P0. Check the Normalizations

**Depends on:** P-1.

**Task.**  Compute
\[
\overline{e_0},\qquad -X_0^t,\qquad -e_0^t.
\]
Use these identities to verify what the two admissibility equations imply for
\[
X_\varphi=\varphi(X_0),\qquad \xi_\varphi=\varphi(e_0).
\]
In particular, prove
\[
X_\varphi\in\mathfrak p,
\qquad
\xi_\varphi\in\sqrt{-1}\mathfrak g_{\mathbb R}.
\]

**Expected output.**  A calculation showing exactly why
\(K\cdot X_\varphi\) is a \(K\)-orbit in \(\mathfrak p\) and
\(G\cdot\xi_\varphi\) is a real-form nilpotent orbit.

### P1. Decomposition and Stability of Multiplicity Spaces

**Depends on:** P0 and complete reducibility.

**Task.**  For an admissible \(\varphi\), prove the decomposition
\[
V_\varphi\simeq
\bigoplus_{i\ge1}M_i(\varphi)\otimes\operatorname{St}_i.
\]
Then prove that the two compatibility equations for \(\varphi\) imply that
this decomposition is stable under both \(J\) and \(L\), in the precise sense
that there are induced operators
\[
J_i^\varphi:M_i(\varphi)\to M_i(\varphi),
\qquad
L_i^\varphi:M_i(\varphi)\to M_i(\varphi)
\]
with
\[
J_i^\varphi\otimes J_{\operatorname{St}_i}=J,
\qquad
L_i^\varphi\otimes L_{\operatorname{St}_i}=L
\]
on \(M_i(\varphi)\otimes\operatorname{St}_i\).

**Expected output.**  A proof that no mixing occurs between different
\(\operatorname{St}_i\)-isotypic summands, and that \(J_i^\varphi,L_i^\varphi\)
are well-defined.

### P2. Multiplicity-Space Classical Forms

**Depends on:** P1 and the invariant form on \(\operatorname{St}_i\).

**Task.**  Prove that each summand
\[
M_i(\varphi)\otimes\operatorname{St}_i\subset V
\]
is non-degenerate for \(\langle\ ,\ \rangle\), and that there is a unique
bilinear form
\[
\langle\ ,\ \rangle_i^\varphi
\]
on \(M_i(\varphi)\) such that
\[
\langle\ ,\ \rangle_i^\varphi
\otimes
\langle\ ,\ \rangle_{\operatorname{St}_i}
=
\langle\ ,\ \rangle
\]
on the \(i\)-th summand.

Then prove that
\[
\bigl(M_i(\varphi),
\langle\ ,\ \rangle_i^\varphi,
J_i^\varphi,L_i^\varphi\bigr)
\]
is a classical space.  Denote its signature by
\[
(\star_i^\varphi,p_i^\varphi,q_i^\varphi).
\]
The meaning of this signature must be the one fixed in P-1.

**Expected output.**  A local construction of the data
\((\langle\ ,\ \rangle_i^\varphi,J_i^\varphi,L_i^\varphi)\) and a proof that
it is independent of auxiliary choices in the decomposition.

### P3. The \(K\)-Orbit Signed Young Diagram

**Depends on:** P-0 and P2.

**Task.**  Define the signed Young diagram of the \(K\)-orbit
\[
\mathcal O_\varphi:=K\cdot X_\varphi\subset\mathfrak p
\]
by
\[
\operatorname{SYD}_{\mathfrak p}(\mathcal O_\varphi)(i)
:=(p_i^\varphi,q_i^\varphi).
\]
Here the ordered pair is the one fixed in P-1 and computed using the
dictionary in P-0.
Prove that this definition is independent of the admissible parameter
\(\varphi\) representing the same \(K\)-orbit.
Do not yet prove the type and total-signature constraints here; those are
isolated in P7.

**Do not prove:** the full classification
\(\operatorname{Nil}(\mathfrak p)/K\simeq\operatorname{SYD}_{\star}\).
Only prove well-definedness of this label.

**Expected output.**  A proof that \(K\)-conjugate admissible parameters give
isomorphic multiplicity-space classical data.

### P4. The Direct Real-Form Signed Young Diagram in This Model

**Depends on:** P-1, P-0, P2, and the allowed real-form classification input.

**Task.**  Rewrite the direct real-form signed Young diagram
\[
\operatorname{SYD}_{\mathbb R}(\mathcal N)
\]
for
\(\mathcal N\subset\sqrt{-1}\mathfrak g_{\mathbb R}\) in the present
\((V,\langle\ ,\ \rangle,J,L)\)-language.

More precisely, if \(\varphi\) is an admissible real/Cayley-normalized
parameter with \(\xi_\varphi\in\mathcal N\), prove that the direct real-form
label is
\[
\operatorname{SYD}_{\mathbb R}(\mathcal N)(i)
=(p_i^\varphi,q_i^\varphi),
\]
where \((p_i^\varphi,q_i^\varphi)\) are the classical signature parameters of
the same multiplicity spaces from P2.
The proof must explicitly check that the real-form signed Young diagram uses
the same order of the two signs as P-1.

**Expected output.**  A dictionary lemma: the standard real-form signed Young
diagram construction and the present \(J,L\)-multiplicity-space construction
produce the same pair \((p_i,q_i)\) for each \(i\).

### P5. The Kostant-Sekiguchi Signed Young Diagram

**Depends on:** P3 and the Kostant-Sekiguchi bijection.

**Task.**  For a real-form nilpotent orbit
\[
\mathcal N=G\cdot\xi_\varphi
\subset\sqrt{-1}\mathfrak g_{\mathbb R},
\]
define
\[
\operatorname{SYD}_{KS}(\mathcal N)
:=
\operatorname{SYD}_{\mathfrak p}(K\cdot X_\varphi).
\]
Prove that this is independent of the admissible \(\varphi\) with
\(G\cdot\xi_\varphi=\mathcal N\).

**Expected output.**  A proof that the inverse Kostant-Sekiguchi orbit is
well-defined and that its signed Young diagram is therefore well-defined.

### P6. Equality of the Two Signed Young Diagrams

**Depends on:** P-1, P-0, P4, and P5.

**Task.**  Prove the main theorem:
\[
\operatorname{SYD}_{\mathbb R}(\mathcal N)
=
\operatorname{SYD}_{KS}(\mathcal N)
\]
for every nilpotent \(G\)-orbit
\[
\mathcal N\subset\sqrt{-1}\mathfrak g_{\mathbb R}.
\]

**Expected output.**  A short proof reducing both sides to the same admissible
parameter \(\varphi\) and the same multiplicity-space signatures
\[
(p_i^\varphi,q_i^\varphi).
\]
The proof must explicitly say why no \(p_i/q_i\) swap occurs.

### P7. Type and Total-Signature Check

**Depends on:** P-0, P2, and P6.

**Task.**  Verify that the common signed Young diagram lies in
\[
\operatorname{SYD}_{\star}(p,q).
\]
This has two parts.

First, check the type/parity conditions:

1. for \(\star\in\{B,D\}\), \(p_i=q_i\) when \(i\) is even;
2. for \(\star\in\{C,\widetilde C\}\), \(p_i=q_i\) when \(i\) is odd;
3. for \(\star=C^*\), \(p_i,q_i\) are both even when \(i\) is odd, and
   \(p_i=q_i\) when \(i\) is even;
4. for \(\star=D^*\), \(p_i=q_i\) when \(i\) is odd, and \(p_i,q_i\) are both
   even when \(i\) is even.

Second, prove the total-signature identity
\[
\operatorname{Sign}\bigl(\operatorname{SYD}_{\mathbb R}(\mathcal N)\bigr)
=
\operatorname{Sign}\bigl(\operatorname{SYD}_{KS}(\mathcal N)\bigr)
=(p,q).
\]
This must be derived from the decomposition
\[
V\simeq
\bigoplus_{i\ge1}M_i(\varphi)\otimes\operatorname{St}_i
\]
and from the tensor-product signature dictionary in P-0.  In particular, the
solver must recover the displayed formula defining
\(\operatorname{Sign}(\mathcal D)\) and verify that the resulting pair is the
ambient \((p,q)\), not merely a pair with the same sum \(p+q\).

**Expected output.**  A case-by-case table for the parity conditions, followed
by the calculation showing that the signed Young diagram has the same total
signature \((p,q)\) as the original classical space \(V\).

## Final Deliverable for a Solver Agent

Return a proof package with:

1. a one-paragraph completeness check listing any convention still missing;
2. the P-1 signature convention audit, including the alignment table;
3. the P-0 tensor-product dictionary, including the \(p\)-coordinate and
   \(q\)-coordinate contribution calculation;
4. solutions to P0 through P6 in order;
5. the P7 type/parity and total-signature check;
6. a final statement of the theorem
   \[
   \operatorname{SYD}_{\mathbb R}(\mathcal N)
   =
   \operatorname{SYD}_{KS}(\mathcal N)
   \in\operatorname{SYD}_{\star}(p,q).
   \]

If any subproblem cannot be proved from the allowed inputs, stop at that
subproblem and state the missing hypothesis precisely.  Do not continue by
silently assuming the desired compatibility.
