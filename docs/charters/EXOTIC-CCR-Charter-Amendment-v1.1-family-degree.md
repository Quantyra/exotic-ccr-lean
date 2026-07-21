# EXOTIC-CCR Charter Amendment v1.1 — Degree-indexed family framing

**Status:** Draft amendment (Chief Scientist direction, 2026-07-20)  
**Amends:** `Project_EXOTIC_CCR_Research_Charter.docx` v1.0  
**Authority:** Does not replace v1.0 integrity/claim-control; strengthens scientific scope and gates.

## 1. Trigger
Public technical strengthening of the counterexample landscape beyond a single specimen:

1. **Parameterized constructions and compositions** described as making the Jacobian Conjecture “factory false” (not merely coordinate clones of one map).  
   - Source: Guy Zyskind, X post, https://x.com/GuyZys/status/2079335737829580957
2. **Preprint (20 July 2026):** “A Counterexample to the Jacobian Conjecture” (Ulam).  
   - URL: https://www.ulam.ai/research/jacobian.pdf  
   - Local: `docs/literature/jacobian-counterexample-ulam-2026-07-20.pdf`  
   - Claimed results (as stated in intake; **G0 must independently certify**):  
     - Theorem 5.2: families of 3D Keller maps with constant Jacobian \(-2\)  
     - Corollary 5.3: for every integer \(d\ge 3\), a nonproper Keller map of generic degree \(d\) retaining the original three-point collision

## 2. Revised central framing
### v1.0 framing
Start with one exceptional Keller map; test whether it yields a physically admissible exotic endomorphism.

### v1.1 framing (adopted for planning)
Construct and classify a **degree-indexed family** of Poisson and Weyl-algebra endomorphisms from nonproper Keller maps, and determine which algebraic invariants—especially **generic fiber degree** \(d=\mu(F)\)—survive quantization and operator-algebra completion.

Controlled variable:
\[
d = \mu(F) = [\mathbb{C}(x):\mathbb{C}(F)]
\]
(generic number of preimages). Distinct \(d\) are not related by polynomial coordinate change.

## 3. Classical and quantum lifts (working definitions)
For each \(F_d\) with \(\det J_d = c \neq 0\):
\[
\Phi_d(q,p)=\bigl(F_d(q),\, J_d(q)^{-T}p\bigr)
\]
preserves \(P^T dQ = p^T dq\) hence the symplectic/Poisson structure; generically \(\mu(\Phi_d)=\mu(F_d)=d\).

Weyl candidate (coefficient-left; symmetric ordering as a separate test):
\[
\widehat Q_i = F_{d,i}(\hat q),\qquad
\widehat P_j = \sum_k (J_d^{-1})_{kj}(\hat q)\,\hat p_k
\]
with optional half-density / anticommutator symmetrization. Formal \([\widehat Q_i,\widehat P_j]=i\hbar\delta_{ij}\) is algebraic; essential self-adjointness and strong Weyl relations are not automatic.

## 4. Composition semigroup
For generically finite dominant maps, \(\mu(F\circ G)=\mu(F)\mu(G)\) and \(\det J(F\circ G)=(\det JF)(\det JG)\). Cotangent lifts compose: \(\Phi_{F\circ G}=\Phi_F\circ\Phi_G\).  
Iterates: \(\mu(F_d^{\circ k})=d^k\), suggesting algebraic growth \(h_{\mathrm{alg}}=\log d\) as a candidate invariant vs operator-algebraic index/entropy/defect.

## 5. Continuous-time no-go (heuristic, to formalize)
Generic degree is integer-valued and multiplicative. A continuous family through the identity has \(\mu=1\) and cannot smoothly reach \(d>1\). Nontrivial family members are not expected as \(\exp(tX)\) Hamiltonian flows connected to the identity. Prefer interpretations: discrete irreversible maps, subsystem embeddings, CV encodings, open-system ops, polynomial-level noninvertibility.

## 6. Decisive quantum question
**Does generic degree \(d\) remain visible after completing the polynomial Weyl algebra into a physical operator algebra?**

| Outcome | Meaning |
|---------|---------|
| Degree disappears under completion | Proper polynomial image; closure fills observables (Stone–von Neumann filter) |
| Degree becomes inclusion index | Proper subalgebra closure; \(\mathrm{Index}\sim d\) or \(f(d)\) |
| Operators fail admissibility | Self-adjointness / strong CCR / positivity / CP failure — valuable no-go |

**Highest-value hypothesis (testable; may be false):**
> Generic fiber degree becomes a quantized measure of endomorphism defect.

## 7. Revised gates (replace v1.0 G0–G5 numbering for forward work)
| Gate | Required result |
|------|-----------------|
| **G0** | Independently certify seed map **and** family theorem (Thm 5.2 / Cor 5.3 or equivalent) |
| **G1** | Degree-indexed counterexample atlas (selected \(d=3,\ldots,D\) + compositions/iterates) |
| **G2** | Poisson preservation + degree retention for \(\Phi_d\) |
| **G3** | Certified Weyl endomorphisms for atlas entries |
| **G4** | Domains, adjoints, essential self-adjointness, strong CCR |
| **G5** | Whether \(d\) survives \(C^*\) / von Neumann completion |
| **G6** | CP, dilations, channel interpretations |
| **G7** | Composition, iteration, index/entropy growth |

v1.0 evidence ladder A–G and claim-control §6.3 **remain in force**.

## 8. New workstream: Counterexample Atlas
For each selected \(d\) and chosen compositions/iterates, record:
- explicit polynomials; exact Jacobian certificate; generic degree
- collision fibers; discriminant / nonproperness set; omitted set
- monodromy or Galois group; primitive decomposition
- real-locus notes
- cotangent-lift formula; Weyl formula
- *-preservation and operator-domain status

## 9. Infrastructure impact
- Lean repo `Quantyra/exotic-ccr-lean`: extend beyond seed T0.1/T0.2 toward family certificates (new stories).
- Science satellite `jacobian-weyl-quantum-phase-space`: atlas data model + CAS certificates.
- Zenodo: still Soft Blocker until GitHub↔Zenodo hook enabled for Lean (and later atlas) releases.

## 10. Non-claims
- Preprint and social posts are **intake**, not G0-passed facts.
- No physical/channel/gate/advantage language before matching gate.
- No claim that “factory false” is Quantyra’s theorem until independent certification.
