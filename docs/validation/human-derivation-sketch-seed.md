# Human derivation sketch — seed map \(F\) (compact)

## Setup
Let \(u=1+xy\). Define
\[
\begin{aligned}
F_1 &= u^3 z + y^2 u (4+3xy),\\
F_2 &= y + 3x u^2 z + 3x y^2(4+3xy),\\
F_3 &= 2x - 3x^2 y - x^3 z.
\end{aligned}
\]

## Jacobian determinant
Compute \(J=\mathrm{D}F\) symbolically over \(\mathbb{Q}[x,y,z]\). After expansion and cancellation (verified independently by SymPy and by a pure-Python polynomial ring), every non-constant term cancels and
\[
\det J = -2.
\]
Hence \(\det J\) is a unit in characteristic not dividing \(2\).

## Three-point collision
Direct substitution:
\[
\begin{aligned}
F(0,0,-1/4)&=(-1/4,0,0),\\
F(1,-3/2,13/2)&=(-1/4,0,0),\\
F(-1,3/2,13/2)&=(-1/4,0,0).
\end{aligned}
\]
The three inputs are pairwise distinct over \(\mathbb{Q}\), so \(F\) is not injective and admits no polynomial inverse.

## Remark
A determinant-one normalization \(G\) exists in the Lean package (`ExoticCCR.AnchorG`); D0-seed freezes the announced \(\det=-2\) form as the primary anchor. Family constructions of higher generic degree are **not** covered here (S015).
