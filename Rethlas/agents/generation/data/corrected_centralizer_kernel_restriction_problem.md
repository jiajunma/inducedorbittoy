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
