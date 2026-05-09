# Proof

Let \(A_{S,T}=X_0+Y_{S,T}\). We use the block decomposition
\(V=E\oplus V_0\oplus E'\). For a map \(R:E'\to V_0\), put
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
Here \(X_0^*=-X_0\), so \(-R^*X_0=(X_0R)^*\). Thus unipotent conjugation has
the formula
\[
\boxed{\quad
S\mapsto S-X_0R,\qquad
T\mapsto T+S^*R-R^*S+R^*X_0R .
\quad}
\tag{1}
\]
The central \(T\)-coordinate in \(U\) commutes with \(A_{S,T}\), so it has no
additional effect on these coordinates.

Next record the two elementary consequences of the normal-form hypothesis.
First, the map
\[
\Phi:K\to (E'/L)^*,\qquad
\Phi(k)(u+L)=\langle k,Su\rangle
\tag{2}
\]
is surjective. Indeed, the equality \(\operatorname{Im}X_0=K^\perp\) makes
\[
K\times V_0/\operatorname{Im}X_0\longrightarrow F,\qquad
(k,\overline v)\mapsto \langle k,v\rangle
\]
a perfect pairing. The normal-form condition says precisely that the induced
map
\[
\bar S:E'/L\to V_0/\operatorname{Im}X_0
\]
is injective. Given \(\lambda\in (E'/L)^*\), define a functional on the
subspace \(\bar S(E'/L)\) by \(\bar S(u+L)\mapsto \lambda(u+L)\), extend it
linearly to \(V_0/\operatorname{Im}X_0\), and use the perfect pairing to write
the extension as \(\overline v\mapsto \langle k,v\rangle\) for some \(k\in K\).
Then \(\Phi(k)=\lambda\).

Second, the Levi stabilizer of \(S\) acts on \(L\) through the full group
\(\operatorname{GL}(L)\). The Levi action is
\[
(a,c):\quad S\mapsto cSa^{-1},\qquad
T(u,v)\mapsto T(a^{-1}u,a^{-1}v).
\tag{3}
\]
If a Levi element stabilizes \(S\), it preserves \(L=\ker S\) and acts on
\(T|_L\) by congruence. Conversely, for any
\(\alpha\in\operatorname{GL}(L)\), choose a complement \(E'=L\oplus M\) and
define
\[
a(l+m)=\alpha^{-1}l+m\qquad(l\in L,\ m\in M),
\]
with \(c=1\). Then
\[
Sa^{-1}(l+m)=S(\alpha l+m)=Sm=S(l+m),
\]
because \(S(L)=0\). Hence \((a,1)\) stabilizes \(S\), and on \(L\) it changes
the restricted form by \(T(u,v)\mapsto T(\alpha u,\alpha v)\).

We prove the two implications. Suppose first that
\[
H\cdot A_{S,T_1}=H\cdot A_{S,T_2}.
\]
Write a conjugating element as a unipotent element with parameter \(R\),
followed by a Levi element \((a,c)\). By (1) and (3), the final
\(S\)-coordinate condition is
\[
c(S-X_0R)a^{-1}=S.
\tag{4}
\]
Thus \(\ker(S-X_0R)=a^{-1}L\). If \(u\in\ker(S-X_0R)\), then
\[
Su=X_0Ru\in\operatorname{Im}X_0.
\]
By (NF), \(u\in L\). Since the kernel in (4) has dimension \(\dim L\), this
gives
\[
\ker(S-X_0R)=L,\qquad a^{-1}L=L.
\]
For \(u,v\in L\), the unipotent change in \(T\) vanishes:
\[
\langle (S^*R-R^*S+R^*X_0R)u,v\rangle
=\langle Ru,Sv\rangle-\langle Su,Rv\rangle+\langle X_0Ru,Rv\rangle=0,
\]
because \(Su=Sv=0\) and \(X_0Ru=0\). Therefore only the Levi part changes
the restricted form, and it changes it by congruence under \(a|_L\). Hence
\(T_1|_L\) and \(T_2|_L\) are congruent.

Conversely, assume \(T_1|_L\) and \(T_2|_L\) are congruent. By the full
\(\operatorname{GL}(L)\)-action of the Levi stabilizer, apply a Levi element
stabilizing \(S\) and replace \(T_1\) by \(T_1'\) such that
\[
T_1'|_{L\times L}=T_2|_{L\times L}.
\]
Set \(D=T_2-T_1'\). Then \(D\) is \((-\epsilon)\)-symmetric and vanishes on
\(L\times L\). We claim there is \(R:E'\to K\) such that
\[
D=S^*R-R^*S.
\tag{5}
\]
Choose a complement \(E'=L\oplus M\), identifying \(M\) with \(E'/L\). Let
\(\sigma:(E'/L)^*\to K\) be a linear section of the surjective map \(\Phi\)
from (2). Define \(R\) linearly by
\[
Rl=\sigma(m+L\mapsto D(l,m))\qquad(l\in L),
\]
and
\[
Rm_1=\sigma(m_2+L\mapsto \tfrac12D(m_1,m_2))\qquad(m_1\in M).
\]
Since \(S(L)=0\), both sides of (5) vanish on \(L\times L\). On \(L\times M\),
the equality follows from the definition of \(R|_L\), and the reverse order
follows from \((-\epsilon)\)-symmetry. On \(M\times M\),
\[
\begin{aligned}
\langle (S^*R-R^*S)m_1,m_2\rangle
&=\langle Rm_1,Sm_2\rangle-\langle Sm_1,Rm_2\rangle\\
&=\frac12D(m_1,m_2)-\epsilon\frac12D(m_2,m_1)\\
&=D(m_1,m_2).
\end{aligned}
\]
Thus (5) holds. Since \(R(E')\subset K\), formula (1) fixes \(S\) and sends
\(T_1'\) to \(T_2\). Hence \(A_{S,T_1}\) and \(A_{S,T_2}\) are
\(H\)-conjugate.

This proves that the \(H\)-orbit of \(X_0+Y_{S,T}\), with \(S\) fixed in
normal form, is classified by the \(\operatorname{GL}(L)\)-congruence class
of \(T|_L\).
