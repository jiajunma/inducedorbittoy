# Induced Orbit Representative — Toy Problem

> Self-contained linear-algebra problem extracted from [[problem/induce_orbit.md]] (§5–§7). No $p$-adic analysis, no representation theory, no $\mathbf{i}$ / Cartan-involution data — just bilinear algebra over a generic field $F$.
>
> Goal: prove that the explicit operator $X_{S,T}$ constructed below lies in the Lie algebra of the isometry group of a formed space $V$.

## 1. Data

- A **local field of characteristic $0$**: $F = \mathbb{R}$ or $F$ a finite extension of $\mathbb{Q}_p$ for some prime $p$. (In particular, $\mathrm{char}(F) = 0$, so $2 \neq 0$ and the symmetric/skew-symmetric split is clean.)
- A sign $\epsilon \in \{+1, -1\}$.
- A finite-dimensional $F$-vector space $V_0$ with a non-degenerate $F$-bilinear form
  $$\langle\cdot,\cdot\rangle_0 : V_0 \times V_0 \to F, \qquad \langle v, w\rangle_0 = \epsilon\, \langle w, v\rangle_0.$$
- An $F$-linear map $X_0 : V_0 \to V_0$ that is **skew-adjoint** with respect to $\langle\cdot,\cdot\rangle_0$:
  $$\langle X_0 v, w\rangle_0 + \langle v, X_0 w\rangle_0 = 0 \qquad \forall v, w \in V_0.$$
- A subspace $V_+ \subseteq V_0$ with
  $$V_0 = V_+ \oplus \mathrm{Im}(X_0).$$
- An integer $r \geq 1$, two $r$-dimensional $F$-vector spaces $E, E'$, and a non-degenerate pairing
  $$p : E \times E' \to F.$$
- Direct-sum decompositions
  $$E = L_1 \oplus L_0, \qquad E' = L'_1 \oplus L'_0,$$
  with $\dim L_1 = \dim L'_1 = \dim V_+$, such that:
  - $p$ pairs $L_1$ with $L'_1$ non-degenerately,
  - $p$ pairs $L_0$ with $L'_0$ non-degenerately,
  - $p(L_1, L'_0) = 0$ and $p(L_0, L'_1) = 0$.
- An $F$-linear isomorphism
  $$S : L'_1 \xrightarrow{\;\sim\;} V_+.$$
- An $F$-linear map $T : L'_0 \to L_0$ satisfying
  $$p(Tu, v) + \epsilon\, p(u, Tv) = 0 \qquad \forall u, v \in L'_0.$$

## 2. Derived Objects

### Form on $V := E \oplus V_0 \oplus E'$

$$\langle e + v + e',\; \tilde e + \tilde v + \tilde e'\rangle \;:=\; p(e, \tilde e') + \epsilon\, p(\tilde e, e') + \langle v, \tilde v\rangle_0,$$
for $e, \tilde e \in E$, $v, \tilde v \in V_0$, $e', \tilde e' \in E'$.

This is a non-degenerate $\epsilon$-symmetric bilinear form on $V$ (free fact, not part of the proof goal).

### Map $S^* : V_+ \to L_1$

Defined uniquely by
$$p(S^* w, v) \;=\; \langle w, S v\rangle_0 \qquad \forall w \in V_+,\ v \in L'_1.$$
The pairing $p|_{L_1 \times L'_1}$ is non-degenerate, so $S^*$ is well-defined.

### Operator $X_{S,T} : V \to V$

With $\pi_+ : V_0 \to V_+$ the projection along $\mathrm{Im}(X_0)$, and $\pi'_1 : E' \to L'_1$, $\pi'_0 : E' \to L'_0$ the projections from the decomposition $E' = L'_1 \oplus L'_0$:

$$X_{S,T}(e + v + e') \;:=\; \underbrace{\bigl(S^*(\pi_+ v) + T(\pi'_0 e')\bigr)}_{\in\, E} \;+\; \underbrace{\bigl(X_0 v + S(\pi'_1 e')\bigr)}_{\in\, V_0} \;+\; \underbrace{0}_{\in\, E'}.$$

In particular: $X_{S,T}|_E = 0$ and $\mathrm{pr}_{E'} \circ X_{S,T} = 0$.

## 3. Goal

Prove: $X_{S,T}$ is **skew-adjoint** with respect to $\langle\cdot, \cdot\rangle$, i.e.
$$\boxed{\;\langle X_{S,T}\, x,\, y\rangle + \langle x,\, X_{S,T}\, y\rangle \;=\; 0 \qquad \forall\, x, y \in V.\;}$$

## 4. Reduction Strategy

By bilinearity, write $x = e_x + v_x + e'_x$ and $y = e_y + v_y + e'_y$ and check the nine block-by-block cases for $(x, y) \in \{E, V_0, E'\} \times \{E, V_0, E'\}$.

| $(x, y)$ block | Reduces to |
|----------------|-----------|
| $(E, E)$ | both terms vanish: $X_{S,T}|_E = 0$ and form is $0$ on $E \times E$ |
| $(E, V_0)$ | uses $X_{S,T}(E) = 0$ and form is $0$ on $E \times V_0$ |
| $(V_0, E)$ | symmetric to above |
| $(E, E')$ | uses defining relation of $S^*$ + $\epsilon$-symmetry of $p$ |
| $(E', E)$ | symmetric to above |
| $(V_0, V_0)$ | skew-adjointness of $X_0$ |
| $(V_0, E')$ | uses defining relation of $S^*$ |
| $(E', V_0)$ | symmetric to above |
| $(E', E')$ | uses $p(Tu, v) + \epsilon\, p(u, Tv) = 0$ |

Each non-trivial case is a one-line application of one defining identity.

## 5. Worked Sample Case: $(E', E')$

Take $x = e'_x \in E'$, $y = e'_y \in E'$. Decompose $e'_x = a'_x + b'_x$ with $a'_x \in L'_1$, $b'_x \in L'_0$, and similarly for $e'_y$.

Then
$$X_{S,T} e'_x \;=\; T b'_x \;+\; S a'_x \;\in\; L_0 \oplus V_+.$$

Compute, using $\langle E, E'\rangle$- and $\langle V_0, V_0\rangle$-blocks of the form:
$$\langle X_{S,T} e'_x, e'_y\rangle \;=\; p(T b'_x,\, e'_y) + \langle S a'_x,\, 0\rangle_0 \;=\; p(T b'_x,\, b'_y),$$
since $T b'_x \in L_0$ and $p(L_0, L'_1) = 0$, while $S a'_x \in V_0$ and the form's $V_0$-component of $e'_y$ is zero.

Symmetrically, $\langle e'_x, X_{S,T} e'_y\rangle = p(b'_x,\, T b'_y) \cdot \epsilon$ (the $\epsilon$ comes from swapping arguments in the $E \oplus E'$ form).

Wait — careful. The form on $E \oplus E'$ is $\langle e + e', \tilde e + \tilde e'\rangle = p(e, \tilde e') + \epsilon\, p(\tilde e, e')$. So:

$$\langle e'_x,\, X_{S,T} e'_y\rangle \;=\; \langle 0 + 0 + e'_x,\; T b'_y + S a'_y + 0\rangle \;=\; \epsilon\, p(T b'_y,\, e'_x) \;=\; \epsilon\, p(T b'_y,\, b'_x).$$

Sum:
$$p(T b'_x,\, b'_y) + \epsilon\, p(T b'_y,\, b'_x) \;=\; p(T b'_x,\, b'_y) + \epsilon\, p(T b'_y,\, b'_x).$$

Apply the defining relation $p(Tu, v) + \epsilon\, p(u, Tv) = 0$ with $u = b'_x$, $v = b'_y$: $p(T b'_x, b'_y) = -\epsilon\, p(b'_x, T b'_y)$. So
$$p(T b'_x, b'_y) + \epsilon\, p(T b'_y, b'_x) \;=\; -\epsilon\, p(b'_x, T b'_y) + \epsilon\, p(T b'_y, b'_x).$$

If we identify $p(b'_x, T b'_y) = p(T b'_y, b'_x)$ — but $p$ is a pairing $E \times E' \to F$, and $b'_x, b'_y \in E' = L'_1 \oplus L'_0$ while $Tb'_y \in L_0 \subset E$. So $p(T b'_y, b'_x)$ is the pairing in the correct order $(E, E')$, and $p(b'_x, T b'_y)$ is **not** an evaluation of $p$ — it would require $b'_x \in E$, which it is not.

So the correct reading is: the only meaningful pairing is $p(T b'_y, b'_x)$ with $T b'_y \in L_0 \subset E$ and $b'_x \in L'_0 \subset E'$. The relation $p(Tu, v) + \epsilon\, p(u, Tv) = 0$ has both sides in this form: $u, v \in L'_0$, and $Tu, Tv \in L_0$, with the pairing always applied as $p(L_0\text{-thing},\, L'_0\text{-thing})$.

Thus, with $u = b'_x$ and $v = b'_y$:
$$p(T b'_x, b'_y) + \epsilon\, p(b'_x, T b'_y) \;=\; 0.$$
(Where the second term is implicitly understood as the pairing in the order $(E, E')$ after swapping; equivalently, this is the defining identity of $T$.)

So the sum
$$\langle X_{S,T} e'_x, e'_y\rangle + \langle e'_x, X_{S,T} e'_y\rangle \;=\; p(T b'_x, b'_y) + \epsilon\, p(T b'_y, b'_x) \;=\; 0$$
by the defining identity (rewriting $\epsilon\, p(T b'_y, b'_x)$ as $\epsilon \cdot (-\epsilon^{-1}) \cdot p(T b'_x, b'_y) = -p(T b'_x, b'_y)$ via the same identity applied to the pair $(b'_y, b'_x)$ and then $\epsilon^2 = 1$).

## 6. Optional Follow-Up (P1+)

Show further that $X_{S,T} \in \mathfrak{u}(F)$ over $X_0$, where $\mathfrak{u}(F) \subseteq \mathfrak{g}(F)$ is the unipotent-radical Lie algebra:
$$\mathfrak{u}(F) \;=\; \bigl\{\, Y \in \mathfrak{g}(F) \;\big|\; Y(V) \subseteq E^\perp,\ Y(E^\perp) \subseteq E,\ Y(E) = 0 \,\bigr\},$$
with $E^\perp = E \oplus V_0$ under the chosen form. Specifically:

$$X_{S,T} - \widehat{X_0} \;\in\; \mathfrak{u}(F),$$

where $\widehat{X_0}$ extends $X_0$ by zero on $E \oplus E'$.

This is again a finite block-by-block check.

## 7. Notes for the Prover

- $F \in \{\mathbb{R}\} \cup \{\text{finite extensions of } \mathbb{Q}_p\}$ — both are characteristic-$0$ local fields. The toy problem itself is pure **finite-dimensional bilinear algebra** and does not invoke the topology, valuation, archimedean structure, or any field-specific feature of $F$. The restriction is inherited from the parent setting (induced nilpotent orbits over local fields), not from the proof.
- Consequently, any solution that goes through for an arbitrary characteristic-$0$ field works verbatim.
- All maps are finite-rank between finite-dimensional spaces; no topology, completeness, or measure theory is involved.
- A formalization can take any of the following shapes:
  - Pen-and-paper proof: ~1 page if the nine cases are written compactly.
  - Lean 4 / Mathlib: `LinearMap.BilinForm` + `LinearMap` machinery; instantiate `F := ℝ` or use a generic `[Field F] [CharZero F]`.
  - Coq / Isabelle / Agda: similarly, working in a `Module F V` with a `BilinForm`.

## 8. References

- Parent note: [[problem/induce_orbit.md]] §5 (construction of $X_{S,T}$) and §7 (proof goals P1–P6).
- Source paper: Lemma 4.8 / Appendix A.2 (proof of induced orbit representatives for real classical groups). The toy problem strips the $\mathbf{i}$ / J-action layer of the original.
