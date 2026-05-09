# lemma lem:injective-transitivity

## statement
Assume that $\dim E\ge \dim K$. Then $\operatorname{GL}(E)$ acts transitively on the set of injective linear maps $\lambda:K\to E$. Consequently
$$
H=\operatorname{GL}(E)\times \mathcal A
$$
acts transitively on the same set.

## proof
Let $\lambda_1,\lambda_2:K\to E$ be injective. Choose a basis $k_1,\dots,k_n$ of $K$, where $n=\dim K$. Since each $\lambda_i$ is injective, the $n$-tuple
$$
\lambda_i(k_1),\dots,\lambda_i(k_n)
$$
is linearly independent in $E$.

Because $\dim E\ge n$, there exists $a\in \operatorname{GL}(E)$ such that
$$
a\bigl(\lambda_1(k_j)\bigr)=\lambda_2(k_j)
\qquad (1\le j\le n).
$$
Hence $a\circ\lambda_1=\lambda_2$ on the basis of $K$, so
$$
a\circ \lambda_1=\lambda_2.
$$
Thus $\operatorname{GL}(E)$ acts transitively on injective maps. Since $\operatorname{GL}(E)$ is a factor of $H$, the group $H$ also acts transitively.

# lemma lem:kernel-image-geometry

## statement
Let $\lambda:K\to E$ be surjective and put
$$
N:=\ker \lambda.
$$
Assume that $N$ is non-degenerate for $b$. Let $\pi:K\to \overline K:=K/R$ be the quotient map. Then:

1. $N\cap R=0$;
2. $\pi|_N:N\to \overline K$ is injective;
3. $\pi(N)$ is non-degenerate for the induced form on $\overline K$;
4. $\dim \pi(N)=\dim N=\dim K-\dim E$.

## proof
If $x\in N\cap R$, then $x\in R=\operatorname{rad}(b)$, so $b(x,y)=0$ for every $y\in N$. Since $N$ is non-degenerate, this forces $x=0$. Therefore
$$
N\cap R=0.
$$
This proves (1), and (2) follows immediately because $\ker(\pi|_N)=N\cap R$.

To prove (3), let $\bar x\in \pi(N)$ be orthogonal to $\pi(N)$ in $\overline K$. Choose $x\in N$ with $\pi(x)=\bar x$. For every $y\in N$ we have $\pi(y)\in \pi(N)$, hence
$$
0=\bar b(\bar x,\pi(y))=b(x,y),
$$
where $\bar b$ is the induced form on $\overline K$. Thus $x$ is orthogonal to $N$. Since $N$ is non-degenerate, $x=0$, so $\bar x=0$. Therefore $\pi(N)$ is non-degenerate.

Finally,
$$
\dim N=\dim K-\dim E
$$
because $\lambda$ is surjective. Since $\pi|_N$ is injective, $\dim \pi(N)=\dim N$, proving (4).

# proposition prop:surjections-with-fixed-kernel

## statement
Let $\lambda_1,\lambda_2:K\to E$ be surjective linear maps with the same kernel $N$. Then there exists a unique element $a\in \operatorname{GL}(E)$ such that
$$
\lambda_2=a\circ \lambda_1.
$$

## proof
Since $\lambda_i$ is surjective with kernel $N$, it factors as
$$
K\xrightarrow{q} K/N \xrightarrow{\alpha_i} E,
$$
where $q$ is the quotient map and $\alpha_i$ is an isomorphism. Set
$$
a:=\alpha_2\circ \alpha_1^{-1}\in \operatorname{GL}(E).
$$
Then
$$
a\circ \lambda_1
=a\circ \alpha_1\circ q
=\alpha_2\circ q
=\lambda_2.
$$
Uniqueness is immediate because $\lambda_1$ is surjective.

# proposition prop:a-orbits-on-kernels

## statement
Let $d\ge 0$, and let $\mathcal N_d$ be the set of $d$-dimensional subspaces $N\subseteq K$ that are non-degenerate for $b$. For $N\in \mathcal N_d$, define
$$
\Phi(N):=\pi(N)\subseteq \overline K.
$$
Then:

1. $\Phi(N)$ is a non-degenerate $d$-dimensional subspace of $\overline K$;
2. the map $N\mapsto \Phi(N)$ induces a bijection between the set of $\mathcal A$-orbits on $\mathcal N_d$ and the set of $G(\overline K)$-orbits on non-degenerate $d$-dimensional subspaces of $\overline K$.

## proof
The first assertion follows by applying Lemma `lem:kernel-image-geometry` to the quotient map
$$
q_N:K\to K/N,
$$
whose kernel is exactly $N$, or directly by the same argument: non-degeneracy of $N$ implies $N\cap R=0$, hence $\pi|_N$ is injective and identifies $N$ with a non-degenerate $d$-dimensional subspace of $\overline K$.

We now prove the orbit statement.

First, if $h\in \mathcal A$ and $N\in \mathcal N_d$, then $h$ preserves $b$, so $hN$ is again in $\mathcal N_d$. Let $\bar h\in G(\overline K)$ be the induced isometry on $\overline K$. Since $\pi\circ h=\bar h\circ \pi$, we get
$$
\Phi(hN)=\bar h\bigl(\Phi(N)\bigr).
$$
Thus $\Phi$ is constant on $\mathcal A$-orbits up to the natural $G(\overline K)$-action.

Next we prove surjectivity on orbit sets. Let $V\subseteq \overline K$ be a non-degenerate $d$-dimensional subspace. Because $\pi|_L:L\to \overline K$ is an isomorphism, there is a unique subspace
$$
V_L:=(\pi|_L)^{-1}(V)\subseteq L.
$$
Since $\pi|_L$ is an isometry from $L$ onto $\overline K$, the subspace $V_L$ is non-degenerate of dimension $d$. Hence $V_L\in \mathcal N_d$ and
$$
\Phi(V_L)=V.
$$
So every $G(\overline K)$-orbit is hit.

Finally we prove injectivity on orbit sets. Let $N_1,N_2\in \mathcal N_d$, and assume that $\Phi(N_1)$ and $\Phi(N_2)$ lie in the same $G(\overline K)$-orbit. Put
$$
V_i:=\Phi(N_i)\subseteq \overline K,
\qquad
V_{i,L}:=(\pi|_L)^{-1}(V_i)\subseteq L
\qquad (i=1,2).
$$
Choose $\bar g\in G(\overline K)$ such that $\bar g(V_1)=V_2$, and transport it to
$$
g:=(\pi|_L)^{-1}\circ \bar g\circ (\pi|_L)\in G(L).
$$
Then $g(V_{1,L})=V_{2,L}$, and by definition of $\mathcal A$, the extension
$$
\widetilde g(\ell+r):=g\ell+r
\qquad (\ell\in L,\ r\in R)
$$
lies in $\mathcal A$.

We claim that each $N_i$ is the graph of a linear map over $V_{i,L}$. Indeed, $N_i\cap R=0$, so every $x\in N_i$ has a unique decomposition
$$
x=v+\psi_i(v)
\qquad (v\in V_{i,L}),
$$
for a uniquely determined linear map $\psi_i:V_{i,L}\to R$. Thus
$$
N_i=\{v+\psi_i(v)\mid v\in V_{i,L}\}.
$$

Choose any linear extension $\Psi_i:L\to R$ of $\psi_i$. Then the shear
$$
\tau_{-\Psi_i}(\ell+r)=\ell+r-\Psi_i(\ell)
$$
lies in $\mathcal A$, and for $v\in V_{i,L}$ we have
$$
\tau_{-\Psi_i}\bigl(v+\psi_i(v)\bigr)=v.
$$
Therefore
$$
\tau_{-\Psi_i}(N_i)=V_{i,L}.
$$

Now define
$$
h:=\tau_{\Psi_2}\circ \widetilde g\circ \tau_{-\Psi_1}\in \mathcal A.
$$
Then
$$
h(N_1)
=\tau_{\Psi_2}\bigl(\widetilde g(V_{1,L})\bigr)
=\tau_{\Psi_2}(V_{2,L})
=N_2.
$$
So $N_1$ and $N_2$ are in the same $\mathcal A$-orbit.

Conversely, if $N_2=hN_1$ for some $h\in \mathcal A$, then
$$
\Phi(N_2)=\Phi(hN_1)=\bar h\bigl(\Phi(N_1)\bigr),
$$
so $\Phi(N_1)$ and $\Phi(N_2)$ are in the same $G(\overline K)$-orbit. This proves injectivity on orbit sets, hence the required bijection.

# theorem thm:kernel-quotient-orbit-classification

## statement
Let $F=\mathbb R$ or $F=\mathbb C$, and let
$\epsilon\in\{\pm1\}$. Let $K$ be a finite-dimensional $F$-vector
space equipped with an $\epsilon$-symmetric bilinear form
$$
b(x,y)=\epsilon b(y,x).
$$
Let $R=\operatorname{rad}(b)$, and assume that the induced form on
$$
\overline K:=K/R
$$
is non-degenerate. Choose a linear complement
$$
K=L\oplus R.
$$
Then $L$ is identified with $\overline K$, and the restriction of $b$
to $L$ is non-degenerate.

Let $E$ be a finite-dimensional $F$-vector space. Let
$$
\mathcal A
$$
be the subgroup of $\operatorname{GL}(K)$ generated by the following two
families of maps:

1. for $g\in G(L):=\operatorname{Isom}(L,b|_L)$,
   $$
   \widetilde g(\ell+r):=g\ell+r
   \qquad(\ell\in L,\ r\in R);
   $$
2. for $\phi\in\operatorname{Hom}(L,R)$,
   $$
   \tau_\phi(\ell+r):=\ell+r+\phi(\ell)
   \qquad(\ell\in L,\ r\in R).
   $$

Thus every element of $\mathcal A$ preserves the bilinear form $b$, and
the induced action of $\mathcal A$ on $K/R$ is the full group
$$
G(\overline K):=\operatorname{Isom}(\overline K).
$$
Let
$$
H:=\operatorname{GL}(E)\times \mathcal A
$$
act on $\operatorname{Hom}(K,E)$ by
$$
(a,h)\cdot \lambda:=a\circ \lambda\circ h^{-1}.
$$

Prove the following statements. This is a purely linear-algebraic problem;
do not prove or discuss any openness or density assertion.

1. If $\dim E\ge \dim K$, then $H$ acts transitively on the set of
   injective linear maps
   $$
   \lambda:K\to E.
   $$

2. Suppose $\dim K>\dim E$. Put
   $$
   d:=\dim K-\dim E.
   $$
   Let $\mathcal M\subseteq\operatorname{Hom}(K,E)$ be the set of
   surjective maps $\lambda:K\to E$ such that $\ker\lambda$ is
   non-degenerate for $b$. For $\lambda\in\mathcal M$, define
   $$
   V_\lambda:=\text{the image of }\ker\lambda\text{ in }K/R.
   $$
   Then $V_\lambda$ is a non-degenerate $d$-dimensional subspace of
   $K/R$, and the map
   $$
   \lambda\longmapsto V_\lambda
   $$
   induces a bijection between the set of $H$-orbits on $\mathcal M$
   and the set of $G(K/R)$-orbits on non-degenerate $d$-dimensional
   subspaces of $K/R$.

## proof
The first assertion is exactly Lemma `lem:injective-transitivity`.

Assume now that $\dim K>\dim E$, and put
$$
d:=\dim K-\dim E.
$$
Let $\lambda\in \mathcal M$, and write
$$
N:=\ker \lambda.
$$
By Lemma `lem:kernel-image-geometry`, the quotient image
$$
V_\lambda=\pi(N)\subseteq \overline K=K/R
$$
is a non-degenerate $d$-dimensional subspace. This proves the first sentence in part (2).

We next reduce the classification of $H$-orbits on $\mathcal M$ to the classification of $\mathcal A$-orbits on non-degenerate $d$-dimensional subspaces of $K$.

If $(a,h)\in H$ and $\lambda\in \mathcal M$, then
$$
\ker\bigl((a,h)\cdot \lambda\bigr)
=\ker(a\circ \lambda\circ h^{-1})
=h(\ker \lambda),
$$
because $a$ is invertible. Hence the kernel depends only on the $\mathcal A$-part of the action.

Conversely, let $N\subseteq K$ be any non-degenerate $d$-dimensional subspace. Choose an isomorphism
$$
\alpha:K/N\xrightarrow{\sim} E,
$$
and define
$$
\lambda_N:=\alpha\circ q_N:K\to E,
$$
where $q_N:K\to K/N$ is the quotient map. Then $\lambda_N$ is surjective and
$$
\ker \lambda_N=N.
$$
Thus every non-degenerate $d$-dimensional subspace occurs as the kernel of some element of $\mathcal M$.

If two elements of $\mathcal M$ have the same kernel, then Proposition `prop:surjections-with-fixed-kernel` shows that they differ by postcomposition with an element of $\operatorname{GL}(E)$. Therefore the map
$$
\lambda\longmapsto \ker\lambda
$$
induces a bijection between the set of $H$-orbits on $\mathcal M$ and the set of $\mathcal A$-orbits on non-degenerate $d$-dimensional subspaces of $K$.

Finally, Proposition `prop:a-orbits-on-kernels` identifies the latter orbit set with the set of $G(\overline K)$-orbits on non-degenerate $d$-dimensional subspaces of $\overline K$, via
$$
N\longmapsto \pi(N).
$$
Under the preceding bijection, this is exactly the map
$$
\lambda\longmapsto V_\lambda.
$$
Hence $\lambda\mapsto V_\lambda$ induces a bijection between the set of $H$-orbits on $\mathcal M$ and the set of $G(K/R)$-orbits on non-degenerate $d$-dimensional subspaces of $K/R$.
This proves part (2), and therefore the whole theorem.
