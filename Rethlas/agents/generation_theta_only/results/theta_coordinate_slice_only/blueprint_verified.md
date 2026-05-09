# Proof

Let \(A_{S,T}=X_0+Y_{S,T}\).  We use the block decomposition
\(V=E\oplus V_0\oplus E'\).  For a map \(R:E'\to V_0\) put
\[
Y_R=\begin{bmatrix}0&-R^*&0\\0&0&R\\0&0&0\end{bmatrix}\in\mathfrak u .
\]
Since \(\mathfrak u\) is two-step nilpotent,
\[
\exp(Y_R)A_{S,T}\exp(-Y_R)
=A_{S,T}+[Y_R,A_{S,T}]+\frac12[Y_R,[Y_R,A_{S,T}]] .
\]
Direct block multiplication gives
\[
[Y_R,A_{S,T}]
=
\begin{bmatrix}
0&-R^*X_0&S^*R-R^*S\\
0&0&-X_0R\\
0&0&0
\end{bmatrix},
\qquad
\frac12[Y_R,[Y_R,A_{S,T}]]
=
\begin{bmatrix}
0&0&R^*X_0R\\
0&0&0\\
0&0&0
\end{bmatrix}.
\]
Here \(X_0^*=-X_0\), so \(-R^*X_0=(X_0R)^*\).  Thus unipotent conjugation
has the formula
\[
\boxed{\quad
S\mapsto S-X_0R,\qquad
T\mapsto T+S^*R-R^*S+R^*X_0R .
\quad}
\tag{1}
\]
The central \(T\)-part of \(U\) commutes with \(A_{S,T}\), so it has no
additional effect.

We first prove that \(\Theta^P_{S,T}\) is independent of \(P\).  If
\(P'\) is another choice, then \(Q=P'-P\) maps \(N\) into
\(K=\ker X_0\).  For \(u,v\in N\), using \(Su=X_0Pu=X_0P'u\) and
\(\operatorname{Im}X_0=K^\perp\),
\[
\begin{aligned}
\Theta^{P'}_{S,T}(u,v)-\Theta^P_{S,T}(u,v)
&=\langle Qu,Sv\rangle-\langle Su,Qv\rangle
  +\langle X_0Pu,Qv\rangle+\langle X_0Qu,Pv\rangle
  +\langle X_0Qu,Qv\rangle\\
&=0-\langle Su,Qv\rangle+\langle Su,Qv\rangle+0+0=0.
\end{aligned}
\]
Indeed, \(\langle Qu,Sv\rangle=0\) because \(Qu\in K\) and
\(Sv=X_0Pv\in\operatorname{Im}X_0=K^\perp\), while the last two terms
vanish because \(X_0Q=0\).
Hence the form is well-defined; denote it by \(\Theta_{S,T}\).  It is
\((-\epsilon)\)-symmetric because it will be identified below with the
restriction of a \((-\epsilon)\)-symmetric \(T\)-coordinate.

Choose one \(P:N\to V_0\) with \(X_0P=S|_N\), and extend it arbitrarily to a
linear map \(R:E'\to V_0\).  Put
\[
S_0=S-X_0R,\qquad
T_0=T+S^*R-R^*S+R^*X_0R .
\]
For \(u\in N\) the equality \(X_0Ru=Su\) gives \(S_0u=0\).  Conversely,
if \(S_0u=0\), then \(Su=X_0Ru\in\operatorname{Im}X_0\), hence
\(u\in N=\ker\overline S\).  Therefore
\[
\ker S_0=N=\ker\overline{S_0};
\tag{2}
\]
indeed \(\overline{S_0}=\overline S\), since \(X_0R(E')\subset\operatorname{Im}X_0\).
Moreover, for \(u,v\in N\),
\[
T_0(u,v)
=T(u,v)+\langle Ru,Sv\rangle-\langle Su,Rv\rangle+\langle X_0Ru,Rv\rangle
=\Theta_{S,T}(u,v).
\tag{3}
\]
Thus the fixed unipotent element \(\exp(Y_R)\) carries every
\(A_{S,T}\) to \(A_{S_0,T_0}\), preserves equality of \(H\)-orbits, and
turns the theta invariant into the ordinary restriction \(T_0|_N\).  It is
therefore enough to prove the asserted classification in the normal form
case \(\ker S=\ker\overline S\), where \(N=L:=\ker S\) and
\(\Theta_{S,T}=T|_L\) by taking \(P=0\).

Assume now that \(S\) satisfies this normal form condition and write
\(L=\ker S\).  The Levi factor acts by
\[
(a,c):\quad S\mapsto cSa^{-1},\qquad
T(u,v)\mapsto T(a^{-1}u,a^{-1}v),
\tag{4}
\]
where \(a\in\operatorname{GL}(E')\) and \(c\in Z_{G_0}(X_0)\).  Hence a
Levi element stabilizing \(S\) preserves \(L\) and acts on \(T|_L\) by
congruence.  Conversely, every \(\alpha\in\operatorname{GL}(L)\) occurs:
choose a complement \(E'=L\oplus M\), define
\[
a(l+m)=\alpha^{-1}l+m\qquad(l\in L,\ m\in M),
\]
and take \(c=1\).  Then for every \(l+m\in E'\),
\[
Sa^{-1}(l+m)=S(\alpha l+m)=S m=S(l+m),
\]
because \(S(L)=0\).  Hence \((a,1)\) stabilizes \(S\), and the induced
congruence on the restricted \(T\)-coordinate is
\[
T(u,v)\mapsto T(a^{-1}u,a^{-1}v)=T(\alpha u,\alpha v)
\qquad(u,v\in L).
\]
Thus the Levi stabilizer acts on \(L\) through the full group
\(\operatorname{GL}(L)\).

Suppose first that \(A_{S,T_1}\) and \(A_{S,T_2}\) are \(H\)-conjugate.
Write a conjugating element as a unipotent element with parameter \(R\),
followed by a Levi element \((a,c)\).  By (1) and (4), the final
\(S\)-coordinate condition is
\[
c(S-X_0R)a^{-1}=S .
\tag{5}
\]
Thus \(\ker(S-X_0R)=a^{-1}L\).  If \(u\in\ker(S-X_0R)\), then
\(Su=X_0Ru\in\operatorname{Im}X_0\), so the normal form condition gives
\(u\in L\).  Since the two kernels in (5) have dimension \(\dim L\), we get
\[
\ker(S-X_0R)=L,\qquad a^{-1}L=L.
\]
For \(u,v\in L\) the unipotent change in \(T\) vanishes:
\[
\langle (S^*R-R^*S+R^*X_0R)u,v\rangle
=\langle Ru,Sv\rangle-\langle Su,Rv\rangle+\langle X_0Ru,Rv\rangle=0,
\]
because \(Su=Sv=0\) and \(X_0Ru=0\).  Therefore only the Levi part changes
the restricted form, and it changes it by congruence under \(a|_L\).  Hence
\(T_1|_L\) and \(T_2|_L\) are congruent.

Conversely suppose \(T_1|_L\) and \(T_2|_L\) are congruent.  Using the
surjectivity of the stabilizer action on \(L\), apply a Levi element
stabilizing \(S\) and replace \(T_1\) by \(T_1'\) with
\[
T_1'|_{L\times L}=T_2|_{L\times L}.
\]
Let \(D=T_2-T_1'\).  Then \(D\) is \((-\epsilon)\)-symmetric and vanishes
on \(L\times L\).  We claim there is \(R:E'\to K\) such that
\[
D=S^*R-R^*S .
\tag{6}
\]
Indeed, set \(W=E'/L\).  The map
\[
K\to W^*,\qquad k\mapsto (u+L\mapsto \langle k,Su\rangle)
\]
is surjective.  To see this, the equality
\(\operatorname{Im}X_0=K^\perp\) makes the pairing
\[
K\times V_0/\operatorname{Im}X_0\longrightarrow F,\qquad
(k,\overline v)\mapsto \langle k,v\rangle
\]
perfect.  Also \(\bar S:W=E'/L\to V_0/\operatorname{Im}X_0\) is injective
by the normal form condition.  Given \(\lambda\in W^*\), first define a
functional on the subspace \(\bar S(W)\) by
\(\bar S(w)\mapsto \lambda(w)\).  Extend it linearly to all of
\(V_0/\operatorname{Im}X_0\).  By the perfect pairing this extension has
the form \(\overline v\mapsto\langle k,v\rangle\) for some \(k\in K\), and
then \(k\) maps to \(\lambda\).  Thus the displayed map is surjective.  Fix
a linear section
\[
\sigma:W^*\to K
\]
of this surjection, and choose a complement \(E'=L\oplus M\), identifying
\(M\) with \(W\).  Define \(R\) linearly by
\[
Rl=\sigma\big(m+L\mapsto D(l,m)\big)\qquad(l\in L),
\]
and
\[
Rm_1=\sigma\big(m_2+L\mapsto \tfrac12D(m_1,m_2)\big)\qquad(m_1\in M).
\]
These formulas are linear in \(l\) and \(m_1\), so they give a linear map
\(R:E'\to K\).  Since \(S(L)=0\), both sides of (6) vanish on
\(L\times L\).  On \(L\times M\) the equality follows from the definition
of \(R|_L\), and the reverse order follows from \((-\epsilon)\)-symmetry.
On \(M\times M\),
\[
\begin{aligned}
\langle (S^*R-R^*S)m_1,m_2\rangle
&=\langle Rm_1,Sm_2\rangle-\langle Sm_1,Rm_2\rangle\\
&=\frac12D(m_1,m_2)-\epsilon\frac12D(m_2,m_1)\\
&=D(m_1,m_2).
\end{aligned}
\]
Thus (6) holds.  Since \(R(E')\subset K\), formula (1) fixes \(S\) and
sends \(T_1'\) to \(T_2\).  Hence \(A_{S,T_1}\) and \(A_{S,T_2}\) are
\(H\)-conjugate.

The normal form classification is therefore exactly congruence of
\(T|_{\ker S}\).  Applying the fixed preliminary unipotent conjugation and
using (3) gives the original statement: for
\(T_1,T_2\in\mathcal B_{-\epsilon}^{\max}(E',S)\),
\[
H\cdot (X_0+Y_{S,T_1})=H\cdot (X_0+Y_{S,T_2})
\]
if and only if \(\Theta_{S,T_1}\) and \(\Theta_{S,T_2}\) are congruent under
\(\operatorname{GL}(N)\).  The maximal non-degeneracy hypothesis is preserved
under congruence and is precisely the condition that these theta forms lie in
the announced class; no further invariant appears.
