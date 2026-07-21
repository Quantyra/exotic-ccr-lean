# Family theorem extract — Ulam preprint Thm 5.1–5.2 / Cor 5.3

**Source:** “A Counterexample to the Jacobian Conjecture”, https://www.ulam.ai/research/jacobian.pdf  
**Local PDF:** `docs/literature/jacobian-counterexample-ulam-2026-07-20.pdf`  
**Text extract:** `docs/literature/_ulam_extract.txt` (pdftotext)  
**Status:** structured intake for G0-family (S015). **Not** a Quantyra certification until CAS/Lean rows pass.

## 0. Seed (already G0-seed certified)
From §3 / Thm 3.1, with \(A=1+xy\), \(B=A^2 z + y^2(4+3xy)\), \(P=AB\):
\[
\begin{aligned}
P &= (1+xy)^3 z + y^2(1+xy)(4+3xy),\\
Q &= y + 3x(1+xy)^2 z + 3xy^2(4+3xy),\\
R &= 2x - 3x^2 y - x^3 z.
\end{aligned}
\]
\(\det \mathrm{Jac} F=-2\); three-point collision to \((-1/4,0,0)\). Quantyra D0-seed closed 2026-07-21.

## 1. Theorem 5.1 (deformations, still degree 3)
Parameters \(\lambda,a,c\in\mathbb{C}^\times\), \(H\in\mathbb{C}[x,y]\):
\[
A=\lambda+xy,\quad W=cz+H(x,y),\quad
B=A^2 W + \frac{3}{a\lambda^2} y^2(4\lambda+3xy),
\]
\[
F_{\lambda,a,c,H}=\Bigl(AB,\; y+axB,\;
\frac{2}{\lambda}x - \frac{3}{\lambda}x^2 y - \frac{a}{3}x^3 W\Bigr).
\]
Claimed: \(\det\mathrm{Jac}=-2c\lambda^2\), generic degree **3**, fiber cubic deformed.  
Original seed is \(F_{1,3,1,0}\). Det-one via \(c=-1/(2\lambda^2)\).

## 2. Theorem 5.2 (degree-raising family) — constructive core
Retain seed \(A=1+xy\), \(B=A^2z+y^2(4+3xy)\), \(P=AB\), and seed \((Q,R)\) from (1).

Choose \(N\ge 1\) and polynomials \(\psi_j(T)\in\mathbb{C}[T]\) for \(1\le j\le N\). Define
\[
\begin{aligned}
Q_\psi &= Q + A^2\sum_{j=1}^{N} x^{j}\, B^{j+2}\,\psi_j(P),\\
R_\psi &= R - \sum_{j=1}^{N} \frac{j}{j+2}\, x^{j+2}\, B^{j+2}\,\psi_j(P),\\
F_\psi &= (P,\, Q_\psi,\, R_\psi).
\end{aligned}
\]
**Claimed:**
- \(\det\mathrm{Jac} F_\psi = -2\) (constant);
- finite inverse branches governed by
\[
\Phi_{p,q,r}(s)=2ps^3 - qs^2 + 2s - r + \sum_{j=1}^{N}\frac{2}{j+2}\, p^{j+2}\psi_j(p)\, s^{j+2}=0;
\]
  (fiber polynomial; exact coefficient of the sum term as in preprint eq. (10));
- if \(d=\max\bigl(\{3\}\cup\{j+2:\psi_j\not\equiv 0\}\bigr)\), then generic degree \(\mu(F_\psi)=d\).

**Reconstruction (preprint):** on \(A\neq 0\), \(s=x/A\); for simple finite root,
\(y=q-I_+(p,s)\), \(D=1-sy\), \(x=s/D\), \(z=pD^3-y^2(4-sy)D\).

## 3. Corollary 5.3 (every \(d\ge 3\), collision retained)
For every integer \(d\ge 3\), there is a nonproper Keller map \(\mathbb{C}^3\to\mathbb{C}^3\) of generic degree \(d\) with the **same three-point collision** as Thm 3.1.

**Explicit recipe (preprint proof):**
- \(d=3\): use seed \(F\).
- \(d\ge 4\): set \(N=d-2\), \(\psi_{d-2}(T)=c(4T+1)\) with \(c\in\mathbb{C}^\times\), all other \(\psi_j=0\).
- Added terms vanish on the three collision sources because their common first coordinate is \(P=-1/4\), hence \(\psi_{d-2}(P)=c(4\cdot(-1/4)+1)=0\).
- Det \(-2\) and degree \(d\) by Thm 5.2; nonproper by Thm 2.2 (preprint).

## 4. Stabilization (higher ambient dimension)
For \(n\ge 3\): \((x,y,z,u_4,\ldots,u_n)\mapsto\bigl(F(x,y,z),u_4,\ldots,u_n\bigr)\). Out of G0-family pilot scope.

## 5. Quantyra certification targets (this story)
| ID | Statement | Target evidence |
|----|-----------|-----------------|
| F-T5.2-det | \(\det\mathrm{Jac} F_\psi=-2\) for pilot \(\psi\) | dual CAS |
| F-T5.2-coll | three collision points unchanged for Cor 5.3 \(\psi\) | dual CAS |
| F-T5.2-deg | generic degree \(=d\) for pilot | CAS fiber-poly degree / random fiber count (partial) or Lean later |
| F-C5.3 | existence recipe for each \(d\ge 3\) | constructive pilot \(d=4\) + schema; full ∀d is proof-level |

## 6. Parsing notes / OCR hazards
pdftotext mangles Greek (\(\psi,\lambda,\Delta\)) and some fractions. The \(R_\psi\) coefficient \(\frac{j}{j+2}\) and fiber sum coefficient \(\frac{2}{j+2}\) follow the standard pattern matching the \(I_\pm\) identities in the proof (\(I_{-,s}=s^2 I_{+,s}\)). If CAS det fails, first debug coefficient of \(R_\psi\) against preprint PDF page 6–7 visually.

## 7. Non-claims
- Extract is **not** independent certification.
- No “factory false” public claim from this file alone.
- No Poisson/Weyl/physical language.
