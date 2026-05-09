# Proof

Let \(A_{S,T}=X_0+Y_{S,T}\).  We use the block decomposition
\(V=E\oplus V_0\oplus E'\), and for a map \(R:E'\to V_0\) write
\[
Y_R=\begin{bmatrix}0&-R^*&0\\0&0&R\\0&0&0\end{bmatrix}\in\mathfrak u .
\]
Since \(\mathfrak u\) is two-step nilpotent, conjugation by
\(\exp(Y_R)\) is
\[
\exp(Y_R)A_{S,T}\exp(-Y_R)
=A_{S,T}+[Y_R,A_{S,T}]+\frac12[Y_R,[Y_R,A_{S,T}]] .
\]
A direct block multiplication gives
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
Here \(X_0^*=-X_0\), so the upper middle block is indeed the adjoint
block for the new \(S\)-coordinate.  Thus
\[
\boxed{\quad
S\mapsto S-X_0R,\qquad
T\mapsto T+S^*R-R^*S+R^*X_0R .
\quad}
\tag{1}
\]
The extra central coordinate of \(U\) commutes with \(A_{S,T}\), so it does
not affect this formula.

The Levi factor acts as follows.  If \(a\in \operatorname{GL}(E')\) and
\(c\in Z_{G_0}(X_0)\), then
\[
S\mapsto cSa^{-1},\qquad
T(u,v)\mapsto T(a^{-1}u,a^{-1}v).
\tag{2}
\]
Consequently any Levi element stabilizing the \(S\)-coordinate preserves
\(L=\ker S\), and its action on \(T|_L\) is ordinary congruence.  Conversely,
the stabilizer of \(S\) acts on \(L\) through all of \(\operatorname{GL}(L)\):
given \(\alpha\in\operatorname{GL}(L)\), choose a complement
\(E'=L\oplus M\), define \(a=\alpha\oplus 1_M\), and take \(c=1\).  Then
\(Sa=S\), hence \(cSa^{-1}=S\), and the induced action on \(L\) is \(\alpha\)
(up to replacing \(\alpha\) by \(\alpha^{-1}\), which is immaterial).

We now prove the two implications.

First suppose
\[
H\cdot A_{S,T_1}=H\cdot A_{S,T_2}.
\]
Write an element carrying \(A_{S,T_1}\) to \(A_{S,T_2}\) as a unipotent
element with parameter \(R:E'\to V_0\), followed by a Levi element
\((a,c)\).  By (1) and (2), the final \(S\)-coordinate condition is
\[
c(S-X_0R)a^{-1}=S .
\tag{3}
\]
Hence \(\ker(S-X_0R)=a^{-1}L\).  If \(u\in\ker(S-X_0R)\), then
\[
Su=X_0Ru\in\operatorname{Im}X_0 .
\]
By the normal form condition \(S^{-1}(\operatorname{Im}X_0)=\ker S=L\), this
implies \(u\in L\), and therefore \(Su=0\) and \(X_0Ru=0\).  Since
\(\dim\ker(S-X_0R)=\dim L\) by (3), we get
\[
\ker(S-X_0R)=L,\qquad a^{-1}L=L .
\]
For \(u,v\in L\), the unipotent change in \(T\) from (1) vanishes:
\[
\langle (S^*R-R^*S+R^*X_0R)u,v\rangle
=\langle Ru,Sv\rangle-\langle Su,Rv\rangle+\langle X_0Ru,Rv\rangle=0.
\]
Thus the unipotent part does not change \(T_1|_L\), while the Levi part
changes the restriction only by congruence through \(a|_L\).  Therefore
\(T_1|_L\) and \(T_2|_L\) are congruent under \(\operatorname{GL}(L)\).

Conversely assume \(T_1|_L\) and \(T_2|_L\) are congruent.  By the preceding
surjectivity of the stabilizer action on \(L\), after applying a Levi element
that stabilizes \(S\) we may replace \(T_1\) by a form \(T_1'\) satisfying
\[
T_1'|_L=T_2|_L .
\]
Put \(D=T_2-T_1'\).  Then \(D\) is \((-\epsilon)\)-symmetric and
\(D|_{L\times L}=0\).  We claim that there is \(R:E'\to K\) such that
\[
D=S^*R-R^*S .
\tag{4}
\]
Indeed, set \(W=E'/L\).  The hypothesis says that
\[
\Phi:K\to W^*,\qquad \Phi(k)(u+L)=\langle k,Su\rangle
\]
is surjective.  Choose a complement \(E'=L\oplus M\), so \(M\simeq W\).
For each \(l\in L\), choose \(Rl\in K\) such that
\[
\Phi(Rl)(m+L)=D(l,m)\qquad(m\in M).
\]
For each \(m_1\in M\), choose \(Rm_1\in K\) such that
\[
\Phi(Rm_1)(m_2+L)=\frac12D(m_1,m_2)\qquad(m_2\in M).
\]
Extending linearly gives \(R:E'\to K\).  Since \(S(L)=0\), for
\(l,l'\in L\) both sides of (4) vanish.  For \(l\in L\), \(m\in M\),
\[
\langle (S^*R-R^*S)l,m\rangle
=\langle Rl,Sm\rangle=D(l,m),
\]
and the reversed order follows from \((-\epsilon)\)-symmetry.  Finally, for
\(m_1,m_2\in M\),
\[
\begin{aligned}
\langle (S^*R-R^*S)m_1,m_2\rangle
&=\langle Rm_1,Sm_2\rangle-\langle Sm_1,Rm_2\rangle\\
&=\frac12D(m_1,m_2)-\epsilon\frac12D(m_2,m_1)\\
&=D(m_1,m_2),
\end{aligned}
\]
because \(D(m_2,m_1)=-\epsilon D(m_1,m_2)\).  This proves (4).

For this \(R\), we have \(X_0R=0\), since \(R(E')\subset K=\ker X_0\).
The unipotent formula (1) therefore fixes \(S\) and sends
\[
T_1'\mapsto T_1'+S^*R-R^*S=T_2 .
\]
Hence \(A_{S,T_1'}\) and \(A_{S,T_2}\) are \(H\)-conjugate; composing with the
initial Levi element shows that \(A_{S,T_1}\) and \(A_{S,T_2}\) are
\(H\)-conjugate.

Thus the two \(H\)-orbits are equal exactly when the restricted forms on
\(L=\ker S\) are congruent under \(\operatorname{GL}(L)\).
