import PseudotreeValidation.Cones
import Mathlib.Data.Fintype.Order

/-!
# The four one-point insertion cases

These lemmas verify the target-side choices in the manuscript's identification
of the concrete model. Each conclusion gives the new point's meets with every
old point, rather than merely the existence of a point in a desired interval.
A separate finite-diagram classification and back-and-forth are still needed
to conclude ultrahomogeneity.
-/

namespace AllThoseBigRamsey.Pseudotree

section General

variable {M : Type u} [SemilatticeInf M]

/-- Moving above `s` does not change the meet with an old point which is not
strictly above `s`. -/
theorem inf_above_eq_of_not_lt
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    {s v a : M} (hsv : s ≤ v) (ha : ¬s < a) : v ⊓ a = s ⊓ a := by
  classical
  apply le_antisymm
  · by_cases hsa : s ≤ a
    · have hEq : s = a := by
        by_contra hne
        exact ha (lt_of_le_of_ne hsa hne)
      subst a
      simpa only [inf_idem] using (inf_le_right : v ⊓ s ≤ s)
    · rcases htree (inf_le_left : v ⊓ a ≤ v) hsv with h | h
      · exact le_inf h inf_le_right
      · exact False.elim (hsa (le_trans h inf_le_right))
  · exact inf_le_inf_right a hsv

/-- A point in the cone opposite `r` has meet exactly `s` with every point
sharing `r`'s cone above `s`. -/
theorem inf_eq_of_opposite_cone
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    {s v r a : M} (hsv : s ≤ v) (hsa : s ≤ a)
    (hvr : v ⊓ r = s) (har : s < a ⊓ r) : v ⊓ a = s := by
  apply le_antisymm
  · rcases htree (inf_le_right : v ⊓ a ≤ a) (inf_le_left : a ⊓ r ≤ a) with h | h
    · have : v ⊓ a ≤ v ⊓ r := le_inf inf_le_left (le_trans h inf_le_right)
      simpa only [hvr] using this
    · have : a ⊓ r ≤ v ⊓ r := le_inf (le_trans h inf_le_left) inf_le_right
      rw [hvr] at this
      exact False.elim (not_le_of_gt har this)
  · exact le_inf hsv hsa

/-- Below a minimum, all old meets are the newly inserted point. -/
theorem insertion_below [NoMinOrder M] (A : Set M) (m : M)
    (hm : ∀ a ∈ A, m ≤ a) :
    ∃ v, v < m ∧ v ∉ A ∧ ∀ a ∈ A, v ⊓ a = v := by
  obtain ⟨v, hvm⟩ := NoMinOrder.exists_lt m
  exact ⟨v, hvm, fun hv => (not_le_of_gt hvm) (hm v hv),
    fun a ha => inf_eq_left.mpr (le_trans hvm.le (hm a ha))⟩

/-- The precise empty-interval insertion profile. The side condition says
that each old point is either above `m` or branches off at or below `s`. -/
theorem insertion_between [DenselyOrdered M] (A : Set M) (s m : M)
    (hsm : s < m) (hA : ∀ a ∈ A, m ≤ a ∨ m ⊓ a ≤ s) :
    ∃ v, s < v ∧ v < m ∧ v ∉ A ∧
      ∀ a ∈ A, (m ≤ a ∧ v ⊓ a = v) ∨ (m ⊓ a ≤ s ∧ v ⊓ a = m ⊓ a) := by
  obtain ⟨v, hsv, hvm⟩ := _root_.exists_between hsm
  refine ⟨v, hsv, hvm, ?_, ?_⟩
  · intro hv
    rcases hA v hv with h | h
    · exact (not_le_of_gt hvm) h
    · rw [inf_eq_right.mpr hvm.le] at h
      exact (not_le_of_gt hsv) h
  · intro a ha
    rcases hA a ha with hma | hma
    · exact Or.inl ⟨hma, inf_eq_left.mpr (le_trans hvm.le hma)⟩
    · refine Or.inr ⟨hma, le_antisymm ?_ ?_⟩
      · exact inf_le_inf_right a hvm.le
      · exact le_inf (le_trans hma hsv.le) inf_le_right

/-- Above a maximal old point, every old meet remains its meet with that point. -/
theorem insertion_above_maximal [NoMaxOrder M]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (A : Set M) (s : M) (hs : ∀ a ∈ A, ¬s < a) :
    ∃ v, s < v ∧ v ∉ A ∧ ∀ a ∈ A, v ⊓ a = s ⊓ a := by
  obtain ⟨v, hsv⟩ := NoMaxOrder.exists_gt s
  exact ⟨v, hsv, fun hv => hs v hv hsv,
    fun a ha => inf_above_eq_of_not_lt htree hsv.le (hs a ha)⟩

/-- The below case applies to every finite old set, including the empty set. -/
theorem insertion_below_finite [Nonempty M] [NoMinOrder M]
    {A : Set M} (hA : A.Finite) :
    ∃ v, v ∉ A ∧ ∀ a ∈ A, v < a ∧ v ⊓ a = v := by
  obtain ⟨m, hm⟩ := hA.exists_ge
  obtain ⟨v, hvm, hv, hmeet⟩ := insertion_below A m hm
  exact ⟨v, hv, fun a ha => ⟨lt_of_lt_of_le hvm (hm a ha), hmeet a ha⟩⟩

end General

namespace RayTree

variable {α : Type u} [LinearOrder α]

/-- There is always an upper point in the other cone. -/
theorem exists_opposite_cone [NoMaxOrder α] {s r : RayTree α} (hr : s < r) :
    ∃ v, s < v ∧ v ⊓ r = s := by
  obtain ⟨v, hv, hcode⟩ := coneCode_surjective s (!(coneCode s r))
  refine ⟨v, hv, ?_⟩
  have hle : s ≤ v ⊓ r := le_inf hv.le hr.le
  apply le_antisymm _ hle
  by_contra hnot
  have hlt : s < v ⊓ r := lt_iff_le_not_ge.mpr ⟨hle, hnot⟩
  have heq := (lt_inf_iff_coneCode_eq hv hr).1 hlt
  rw [hcode] at heq
  cases coneCode s r <;> simp at heq

/-- The unused-cone insertion case. If every old point above `s` lies in
`r`'s cone, the new point can be placed in the other cone while preserving
all required meets with the old set. -/
theorem insertion_unused_cone [NoMaxOrder α]
    (A : Set (RayTree α)) (s r : RayTree α) (hr : s < r)
    (hA : ∀ a ∈ A, s < a → s < a ⊓ r) :
    ∃ v, s < v ∧ v ⊓ r = s ∧ v ∉ A ∧ ∀ a ∈ A, v ⊓ a = s ⊓ a := by
  classical
  obtain ⟨v, hv, hvr⟩ := exists_opposite_cone hr
  refine ⟨v, hv, hvr, ?_, ?_⟩
  · intro hvA
    have hbad := hA v hvA hv
    rw [hvr] at hbad
    exact (lt_irrefl s) hbad
  intro a ha
  by_cases hsa : s < a
  · have hmeet := inf_eq_of_opposite_cone le_or_ge_of_le_common hv.le hsa.le hvr (hA a ha hsa)
    simpa only [inf_eq_left.mpr hsa.le] using hmeet
  · exact inf_above_eq_of_not_lt le_or_ge_of_le_common hv.le hsa

end RayTree
end AllThoseBigRamsey.Pseudotree
