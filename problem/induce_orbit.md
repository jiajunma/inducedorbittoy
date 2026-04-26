# Induced Nilpotent Orbits for Classical Groups over Local Fields

## 1. Setup

Let $F$ be a **local field of characteristic $0$**: $F = \mathbb{R}$ or $F$ is a finite extension of $\mathbb{Q}_p$. A **formed space** $(V, \langle\cdot,\cdot\rangle)$ is a finite-dimensional $F$-vector space with a non-degenerate bilinear form of parity $\epsilon \in \{+1,-1\}$. The associated algebraic group is
$$\mathbf{G} = \mathrm{Isom}(V, \langle\cdot,\cdot\rangle), \qquad G := \mathbf{G}(F), \qquad \mathfrak{g}(F) := \mathrm{Lie}(\mathbf{G})(F).$$

Let $\mathcal{N}(\mathfrak{g})(F)$ denote the nilpotent cone in $\mathfrak{g}(F)$. All topological notions refer to the natural topology on $F$ (archimedean if $F = \mathbb{R}$, $p$-adic otherwise).

## 2. Maximal Parabolic from a Totally Isotropic Subspace

Let $X \subset V$ be totally isotropic, $r = \dim X$. The **quotient formed space** is
$$V_0 := X^\perp / X,$$
with the induced form of parity $\epsilon$ and $\dim V_0 = \dim V - 2r$. The stabilizer
$$\mathbf{P} = \mathrm{Stab}_{\mathbf{G}}(X) = \mathbf{L}\mathbf{U}$$
is a maximal parabolic with Levi factor $\mathbf{L} \cong \mathbf{GL}(X) \times \mathbf{G}_0$, where $\mathbf{G}_0 = \mathrm{Isom}(V_0)$, and unipotent radical $\mathbf{U}$.

## 3. Induced Orbits

Let $\mathcal{O}_0$ be a $G_0$-orbit on $\mathcal{N}(\mathfrak{g}_0)(F)$. Embed it into $\mathrm{Lie}(\mathbf{L})(F)$ as $\{0\} \times \mathcal{O}_0$.

**Induced set.**
$$\mathrm{Ind}_P^G\, \mathcal{O}_0 \;:=\; \overline{\,G \cdot (\mathcal{O}_0 + \mathfrak{u}(F))\,}.$$
This is a closed, $G$-stable subset of $\mathcal{N}(\mathfrak{g})(F)$, and a finite union of $G$-orbit closures.

**Closure partial order.** On $G$-orbits in $\mathcal{N}(\mathfrak{g})(F)$, define
$$\mathcal{O}' \preceq \mathcal{O} \iff \mathcal{O}' \subseteq \overline{\mathcal{O}}.$$

**Induced orbit.** A $G$-orbit $\mathcal{O} \subseteq \mathrm{Ind}_P^G\,\mathcal{O}_0$ is **induced from $\mathcal{O}_0$ via $P$** if it is $\preceq$-maximal in $\mathrm{Ind}_P^G\,\mathcal{O}_0$. Equivalently:
- $\mathcal{O}$ meets $\mathcal{O}_0 + \mathfrak{u}(F)$, and
- no other $G$-orbit in $\mathrm{Ind}_P^G\,\mathcal{O}_0$ has $\mathcal{O}$ in its closure.

**Multiplicity.** For $x \in \mathcal{O} \cap (\mathcal{O}_0 + \mathfrak{u}(F))$, set
$$m(\mathcal{O}, P) \;:=\; \bigl[\,Z_G(x) : Z_G(x) \cap P\,\bigr],$$
the index of the $P$-stabilizer in the $G$-stabilizer of $x$.

## 4. The Setting Under Consideration

### Data

1. A formed space $(V_0, \langle\cdot,\cdot\rangle_0)$ of parity $\epsilon$ over $F$, with $G_0 = \mathrm{Isom}(V_0)(F)$.
2. A rational nilpotent orbit $\mathcal{O}_0$ of $G_0$ on $\mathcal{N}(\mathfrak{g}_0)(F)$. Fix $X_0 \in \mathcal{O}_0$.
3. An integer $r \geq 1$ satisfying
$$r \;\geq\; \dim_F \ker(X_0 : V_0 \to V_0).$$

### Construction

Let $E, E'$ be $r$-dimensional $F$-vector spaces in duality via a non-degenerate pairing $E \times E' \to F$. Equip $E \oplus E'$ with the form of parity $\epsilon$:
$$\langle e + e',\; \tilde{e} + \tilde{e}'\rangle \;=\; \langle e, \tilde{e}'\rangle_{E \times E'} + \epsilon\,\langle \tilde{e}, e'\rangle_{E \times E'},$$
so that $E$ and $E'$ are each totally isotropic and $E \oplus E' \cong H^r$. Set
$$V \;=\; E \;\oplus\; V_0 \;\oplus\; E',$$
with $\langle E, V_0\rangle = \langle E', V_0\rangle = 0$. Then $(V, \langle\cdot,\cdot\rangle)$ is a formed space of parity $\epsilon$ and $\dim V = \dim V_0 + 2r$.

Let $G = \mathrm{Isom}(V)(F)$ and
$$P \;=\; \mathrm{Stab}_G(E) \;=\; LU, \qquad L \cong \mathrm{GL}(E) \times G_0.$$

### The Condition $r \geq \dim \ker X_0$

For $X_0 \in \mathcal{O}_0$ acting on $V_0$, the kernel $\ker X_0$ is the $V_0$-subspace annihilated by $X_0$. The condition $r \geq \dim \ker X_0$ ensures that the totally isotropic subspace $E$ is large enough to absorb the full kernel of $X_0$.

## 5. Construction of Representatives

Set $c := \dim \ker X_0$ and $l := r - c \geq 0$.

### 5.1 Auxiliary Decompositions

Choose a complement $V_+$ of $\mathrm{Im}(X_0)$ in $V_0$:
$$V_0 = V_+ \oplus \mathrm{Im}(X_0), \qquad \dim V_+ = c.$$

Decompose $E = L_1 \oplus L_0$ and $E' = L'_1 \oplus L'_0$ such that:
- $\dim L_1 = \dim L'_1 = c$, $\quad \dim L_0 = \dim L'_0 = l$,
- $L_1$ and $L'_1$ are in duality, $L_0$ and $L'_0$ are in duality,
- $(L_1 \oplus L'_1) \perp (L_0 \oplus L'_0)$.

Fix a linear isomorphism $S : L'_1 \xrightarrow{\;\sim\;} V_+$.

### 5.2 The Space $\mathscr{T}$

Define
$$\mathscr{T} \;:=\; \bigl\{\, T \in \mathrm{Hom}_F(L'_0,\, L_0) \;\big|\; \langle Tu, v \rangle + \langle u, Tv \rangle = 0 \;\;\forall\, u, v \in L'_0 \,\bigr\},$$
$$\mathscr{T}^\circ \;:=\; \bigl\{\, T \in \mathscr{T} \;\big|\; \mathrm{rank}(T) \text{ is maximal} \,\bigr\}.$$

Each $T \in \mathscr{T}$ defines a bilinear form $\langle\cdot,\cdot\rangle_T$ on $L'_0$ of parity $(-\epsilon)$:
$$\langle u, v \rangle_T \;:=\; -\langle u,\, Tv \rangle, \qquad u, v \in L'_0.$$

Concretely, $T = -\epsilon\, T^t$ in any pair of dual bases, so:
- $\epsilon = +1$ (orthogonal): $T$ is skew-symmetric, $\langle\cdot,\cdot\rangle_T$ is **alternating**.
- $\epsilon = -1$ (symplectic): $T$ is symmetric, $\langle\cdot,\cdot\rangle_T$ is **symmetric**.

The maximal rank is:
$$\mathrm{rank}_{\max} = \begin{cases} l & \text{if } \epsilon = -1, \text{ or } \epsilon = +1 \text{ and } l \text{ even},\\ l - 1 & \text{if } \epsilon = +1 \text{ and } l \text{ odd}.\end{cases}$$

### 5.3 The Representative $X_{S,T}$

Define $S^* : V_+ \to L_1$ by $\langle S^* w, v \rangle = \langle w, Sv \rangle$ for $w \in V_+$, $v \in L'_1$. The element
$$X_{S,T} \;:=\; \begin{pmatrix} 0 & S^* & T \\ 0 & X_0 & S \\ 0 & 0 & 0 \end{pmatrix} \;\in\; X_0 + \mathfrak{u}(F)$$
(block decomposition with respect to $V = E \oplus V_0 \oplus E'$, where $S^*$ acts on the $V_+$-component of $V_0$ and $T$ acts on the $L'_0$-component of $E'$) lies in $\mathfrak{g}(F)$ and belongs to $\mathcal{O}_0 + \mathfrak{u}(F)$.

### 5.4 The Auxiliary Set $\mathfrak{A}$

To prove that $\{X_{S,T} : T \in \mathscr{T}^\circ\}$ exhausts the induced orbits, introduce
$$\mathfrak{A} \;:=\; \left\{\, \begin{pmatrix} 0 & B^* & C \\ 0 & X_0 & B \\ 0 & 0 & 0 \end{pmatrix} \in X_0 + \mathfrak{u}(F) \;\Bigm|\; X_0 \oplus B : V_0 \oplus E' \to V_0 \;\text{is surjective} \,\right\}.$$

Here $B \in \mathrm{Hom}_F(E', V_0)$ and $C \in \mathrm{Hom}_F(E', E)$ are arbitrary subject to the skew-adjoint condition (so the matrix lies in $\mathfrak{g}(F)$), and $B^* \in \mathrm{Hom}_F(V_0, E)$ is determined by $B$ via $\langle B^* w, v\rangle = \langle w, Bv\rangle$.

The unipotent-radical-extended Levi $P' := \mathrm{GL}(E) \ltimes U$ acts on $\mathfrak{A}$. The proof strategy is:

1. $\mathfrak{A}$ is open dense (in the $p$-adic topology) in $\mathcal{O}_0 + \mathfrak{u}(F)$.
2. Every element of $\mathfrak{A}$ is $P'$-conjugate to some $X_{S,T}$ with $T \in \mathscr{T}$.
3. The non-empty open subset $P' \cdot \{X_{S,T} : T \in \mathscr{T}^\circ\}$ is therefore open dense in $\mathfrak{A}$, hence in $\mathcal{O}_0 + \mathfrak{u}(F)$.

This yields the enumeration in the Main Theorem.

## 6. Main Theorem

**Theorem.** Under the setting of Section 4, with $c = \dim\ker X_0$ and $l = r - c$:

### (A) Enumeration of induced orbits

The set of $\preceq$-maximal $G$-orbits in $\mathrm{Ind}_P^G\,\mathcal{O}_0$ is
$$\mathrm{Ind}_P^G\,\mathcal{O}_0 \;=\; \bigl\{\, G \cdot X_{S,T} \;\big|\; T \in \mathscr{T}^\circ \,\bigr\}.$$

Two elements $X_{S,T_1}$ and $X_{S,T_2}$ lie in the same $G$-orbit if and only if $(L'_0, \langle\cdot,\cdot\rangle_{T_1}) \cong (L'_0, \langle\cdot,\cdot\rangle_{T_2})$ as formed spaces of parity $(-\epsilon)$.

### (B) Orbit count

| Case | Condition | Number of induced orbits |
|------|-----------|--------------------------|
| Orthogonal | $\epsilon = +1$ | $1$ (alternating forms of given rank are unique up to isometry) |
| Symplectic | $\epsilon = -1$ | number of isometry classes of non-degenerate symmetric forms of dimension $l$ over $F$ |

### (C) Centralizer structure and multiplicity

Let $\mathcal{O} = G \cdot X_{S,T}$ with $T \in \mathscr{T}^\circ$.

**Case 1: $\langle\cdot,\cdot\rangle_T$ is non-degenerate** (always when $\epsilon = -1$; when $\epsilon = +1$ and $l$ even).

The reductive quotients of $Z_G(X_{S,T})$ and $Z_P(X_{S,T})$ are both isomorphic to
$$R \;\times\; \mathrm{Isom}(L'_0, \langle\cdot,\cdot\rangle_T),$$
where $R$ is the reductive quotient of $Z_{G_0}(X_0)$. In particular:
- $Z_P(X_{S,T}) \trianglelefteq Z_G(X_{S,T})$,
- $m(\mathcal{O}, P) = 1$.

**Case 2: $\langle\cdot,\cdot\rangle_T$ has 1-dimensional radical** (only when $\epsilon = +1$ and $l$ odd).

Let $K = \ker(T) \subset L'_0$ ($\dim K = 1$) and let $K^\vee \subset L_0$ be its dual. Write $L'_0 = L'_2 \oplus K$ and $L_0 = L_2 \oplus K^\vee$ where $\langle\cdot,\cdot\rangle_T|_{L'_2}$ is non-degenerate alternating. Then:

| | Reductive quotient |
|---|---|
| $Z_P(X_{S,T})$ | $R \;\times\; \mathrm{Sp}(L'_2,\, \langle\cdot,\cdot\rangle_T|_{L'_2}) \;\times\; \mathrm{GL}(K)$ |
| $Z_G(X_{S,T})$ | $R \;\times\; \mathrm{Sp}(L'_2,\, \langle\cdot,\cdot\rangle_T|_{L'_2}) \;\times\; \mathrm{O}(K \oplus K^\vee)$ |

The inclusion $\mathrm{GL}(K) \hookrightarrow \mathrm{O}(K \oplus K^\vee)$ has index 2. In particular:
- $Z_P(X_{S,T}) \trianglelefteq Z_G(X_{S,T})$ with $Z_G(X_{S,T}) / Z_P(X_{S,T}) \cong \mathbb{Z}/2\mathbb{Z}$,
- $m(\mathcal{O}, P) = 2$.

## 7. Proof Goals

The following are the statements to be verified:

**(P1) $X_{S,T} \in \mathfrak{g}(F)$.** The element $X_{S,T}$ satisfies $\langle X_{S,T}\, v, w\rangle + \langle v, X_{S,T}\, w\rangle = 0$ for all $v, w \in V$.

**(P2) Open density.**
- (P2a) $\mathfrak{A}$ is open dense in $\mathcal{O}_0 + \mathfrak{u}(F)$.
- (P2b) Every element of $\mathfrak{A}$ is $P'$-conjugate to $X_{S,T}$ for some $T \in \mathscr{T}$.
- (P2c) Consequently the $P$-orbit of $\{X_{S,T} \mid T \in \mathscr{T}^\circ\}$ is open dense in $\mathcal{O}_0 + \mathfrak{u}(F)$.

**(P3) Orbit separation.** $G \cdot X_{S,T_1} = G \cdot X_{S,T_2}$ if and only if $(L'_0, \langle\cdot,\cdot\rangle_{T_1}) \cong (L'_0, \langle\cdot,\cdot\rangle_{T_2})$.

**(P4) Centralizer computation.** Compute the reductive quotients of $Z_G(X_{S,T})$ and $Z_P(X_{S,T})$ as stated in Section 6(C).

**(P5) Normality.** $Z_P(X_{S,T}) \trianglelefteq Z_G(X_{S,T})$.

**(P6) Multiplicity.** $m(\mathcal{O}, P) = 1$ when $\langle\cdot,\cdot\rangle_T$ is non-degenerate, and $m(\mathcal{O}, P) = 2$ when $\epsilon = +1$ and $l$ is odd.

## 8. Self-Contained Problem for an AI Theorem Prover

The cleanest piece to formalize is **(P1)**, the skew-adjointness of $X_{S,T}$. Stripped of $p$-adic analysis, representation theory, and the $\mathbf{i}$ / Cartan-involution layer, it becomes a pure finite-dimensional bilinear-algebra exercise over a generic field $F$.

See the dedicated note: [[problem/induced_orbit_toy_problem.md]].
