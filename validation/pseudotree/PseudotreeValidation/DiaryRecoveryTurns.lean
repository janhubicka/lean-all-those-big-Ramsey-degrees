import PseudotreeValidation.DiaryRecoveryMaps

/-! First upper-cone turns are intrinsic under ray-preserving maps. -/

namespace AllThoseBigRamsey.Pseudotree.DiaryRecovery

open RayEmbeddings DiaryNormalization

theorem turnAt_map (f : RayStrongMap) {C : Finset Word} {v : Word} {j : ℕ}
    (hj : TurnAt C v j) : TurnAt (C.image f.map) (f.map v) (f.level j) := by
  classical
  obtain ⟨p, hp, hpj, hnext, hnot, hone, hfirst⟩ := hj
  have hjlen : j < v.length := (List.getElem?_eq_some_iff.mp hone).1
  have hplen : p < v.length := lt_trans hpj hjlen
  refine ⟨f.level p, ?_, f.level_strict hpj, ?_, ?_, ?_, ?_⟩
  · rw [essential_image]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  · intro k hk hpk
    rw [essential_image] at hk
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hk
    have hpl : p < l := (show StrictMono f.level from fun _ _ h => f.level_strict h).lt_iff_lt.mp hpk
    exact f.level_strict (hnext l hl hpl)
  · rw [map_get f v p hplen]
    exact hnot
  · rw [map_get f v j hjlen]
    exact hone
  · intro k hpk hkj hkOne
    obtain ⟨i, hpi, hij, hlow, hhigh⟩ := level_interval f hpk.le hkj
    have hiOne := one_edge_origin f v (lt_trans hij hjlen) hlow hhigh hkOne
    rcases hpi.eq_or_lt with h | h
    · exact hnot (h ▸ hiOne)
    · exact hfirst i h hij hiOne

/-- A first mapped 1 after an essential level cannot be hidden in padding:
it is the retained image of the corresponding first source 1. -/
theorem turnAt_image_iff (f : RayStrongMap) (C : Finset Word) (v : Word) (j : ℕ) :
    TurnAt (C.image f.map) (f.map v) j ↔ ∃ i, TurnAt C v i ∧ j = f.level i := by
  classical
  constructor
  · rintro ⟨p', hp', hpj, hnext, hnot, hone, hfirst⟩
    rw [essential_image] at hp'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hp'
    have hjlen : j < f.level v.length := by
      simpa only [f.length_map] using (List.getElem?_eq_some_iff.mp hone).1
    obtain ⟨i, hpi, hilen, hlow, hhigh⟩ := level_interval f hpj.le hjlen
    have hplen := lt_of_le_of_lt hpi hilen
    have hiOne := one_edge_origin f v hilen hlow hhigh hone
    have hsourceNot : v[p]? ≠ some 1 := by simpa only [map_get f v p hplen] using hnot
    have hpi' : p < i := by
      rcases hpi.eq_or_lt with h | h
      · exact False.elim (hsourceNot (h ▸ hiOne))
      · exact h
    have heq : j = f.level i := by
      by_contra hne
      have hij : f.level i < j := lt_of_le_of_ne hlow (Ne.symm hne)
      exact hfirst (f.level i) (f.level_strict hpi') hij
        ((map_get f v i hilen).trans hiOne)
    refine ⟨i, ⟨p, hp, hpi', ?_, hsourceNot, hiOne, ?_⟩, heq⟩
    · intro k hk hpk
      have h := hnext (f.level k) (by rw [essential_image]; exact Finset.mem_image.mpr ⟨k, hk, rfl⟩)
        (f.level_strict hpk)
      rw [heq] at h
      exact (show StrictMono f.level from fun _ _ h => f.level_strict h).lt_iff_lt.mp h
    · intro k hpk hki hkOne
      apply hfirst (f.level k) (f.level_strict hpk) (by rw [heq]; exact f.level_strict hki)
      exact (map_get f v k (lt_trans hki hilen)).trans hkOne
  · rintro ⟨i, hi, rfl⟩
    exact turnAt_map f hi

/-- The complete selected level set is natural for arbitrary ray maps.
This is stronger than the sparse-chain application: the distinguished word
and coding set here are arbitrary. -/
theorem selected_image (f : RayStrongMap) (C : Finset Word) (v : Word) :
    selected (C.image f.map) (f.map v) = (selected C v).image f.level := by
  classical
  ext j
  rw [mem_selected_iff, essential_image, Finset.mem_image, turnAt_image_iff, Finset.mem_image]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, essential_subset_selected C v hi, rfl⟩
    · exact ⟨i, turn_mem_selected hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    rcases mem_selected_iff.mp hi with hi | hi
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨i, hi, rfl⟩

end AllThoseBigRamsey.Pseudotree.DiaryRecovery
