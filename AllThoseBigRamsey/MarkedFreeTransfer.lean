import AllThoseBigRamsey.IrreducibleCover

/-!
# Guarded forbidden-copy core for binary marked TRAP

If the inserted vertex z only has positive relations to future vertices
with a prescribed (image) singleton type, any irreducible forbidden copy
containing z must use prescribed future vertices exclusively.

The actual source-padding and class-level continuation construction are
proved in the manuscript and are not assumptions/claims in this module.
-/
namespace AllThoseBigRamsey.MarkedFreeTransfer

variable {L : Language} {α β : Type}
variable {F : RelStructure L α} {D : RelStructure L β}

/-- Positive tuples witnessing the pair (z,x) require x to lie in the
prescribed part of the future. In the binary type-insertion construction
this is exactly the rule "false outside the image of F₁". -/
def GuardedAt (D : RelStructure L β) (z : β)
    (Future Prescribed : β → Prop) : Prop :=
  ∀ R t, D.rel R t →
    ∀ i j, t i = z → Future (t j) → Prescribed (t j)

/-- Every future vertex of an irreducible forbidden copy containing z
belongs to the prescribed part. Neither cardinality nor relation arity
bounds are used in this elementary obstruction step. -/
theorem forbidden_future_is_prescribed
    (irr : Irreducible F) (e : Embedding F D)
    (z : β) (Future Prescribed : β → Prop)
    (hg : GuardedAt D z Future Prescribed)
    (hz : ∃ w : α, e.toFun w = z)
    (hnz : ¬ Future z) :
    ∀ v : α, Future (e.toFun v) → Prescribed (e.toFun v) := by
  rcases hz with ⟨w, hw⟩
  intro v hv
  by_cases h : w = v
  · subst v
    exact False.elim (hnz (by simpa [hw] using hv))
  · rcases irr w v h with ⟨R, q, i, j, hR, hi, hj⟩
    have hD : D.rel R (fun u => e.toFun (q u)) :=
      (e.map_rel R q).mp hR
    have hzi : e.toFun (q i) = z := by rw [hi, hw]
    have hvj : Future (e.toFun (q j)) := by simpa [hj] using hv
    have hp := hg R (fun u => e.toFun (q u)) hD i j hzi hvj
    simpa [hj] using hp

/-- The fact that the prescribed image is the only possible source of
new positive relations follows directly from a no-positive-off-image
condition. -/
theorem guarded_of_no_positive_off_image
    (z : β) (Future Prescribed : β → Prop)
    (h : ∀ R t, D.rel R t →
        ∀ i j, t i = z → Future (t j) → Prescribed (t j)) :
    GuardedAt D z Future Prescribed :=
  h

end AllThoseBigRamsey.MarkedFreeTransfer
