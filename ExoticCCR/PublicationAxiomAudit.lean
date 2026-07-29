/-
Copyright (c) 2026 Daniel Eric Fredriksen, Quantyra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Eric Fredriksen
-/
import ExoticCCR.TheoremFExtensionMultiplicity

/-!
# Publication axiom audit

CI elaborates this file and verifies the emitted `#print axioms` profiles.
The shell check is intentionally downstream of Lean elaboration: it does not
infer trust from a source-text search.
-/

#print axioms ExoticCCR.theoremE
#print axioms ExoticCCR.theoremF
#print axioms ExoticCCR.hilbertDeficiencyIndex_X1_eq_aleph0
#print axioms ExoticCCR.theoremFVonNeumannClassification
#print axioms ExoticCCR.theoremFDeficiencySigmaEquiv
#print axioms ExoticCCR.theoremF_exists_two_distinct_selfAdjointExtensions
#print axioms ExoticCCR.theoremFUnitPhaseExtension_injective
