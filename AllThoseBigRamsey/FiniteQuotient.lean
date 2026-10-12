import Std

/-!
# Finite equivalence-class capacity and covered types

The manuscript defines capacities as the greatest number of inequivalent
realisations of one full type. Amalgamation gives `joint`, and an admissible
type map gives `saturated`. This module proves the resulting abstract counting
argument; it does not assume the class-level full-type interpretation.
-/
namespace AllThoseBigRamsey.FiniteQuotient

universe u v

theorem covers_of_capacity {P : Type u} {Q : Type v}
    (f : P → Q) (restrict : Q → P) (source : P → Nat) (target : Q → Nat)
    (sectionLaw : ∀ p, restrict (f p) = p)
    (positive : ∀ q, 0 < target q)
    (saturated : ∀ p, source p ≤ target (f p))
    (joint : ∀ q q', restrict q = restrict q' → q ≠ q' →
      target q + target q' ≤ source (restrict q)) :
    ∀ q, f (restrict q) = q := by
  intro q
  by_contra h
  have hj := joint (f (restrict q)) q (sectionLaw (restrict q)) h
  rw [sectionLaw] at hj
  have hs := saturated (restrict q)
  have hp := positive q
  omega

end AllThoseBigRamsey.FiniteQuotient
