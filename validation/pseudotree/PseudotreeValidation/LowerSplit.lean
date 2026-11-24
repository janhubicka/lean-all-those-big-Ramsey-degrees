import PseudotreeValidation.LowerGeometry
import AllThoseBigRamsey.Pseudotree.SparseShape

/-! The splitting step in the literal lower-bound realization argument. -/

namespace AllThoseBigRamsey.Pseudotree.LowerGeometry

private theorem binary_no_one (s : List Bool) : TernaryLetter.one ∉ s.map binaryLetter := by
  intro h
  obtain ⟨b, _, hb⟩ := List.mem_map.mp h
  cases b <;> simp [binaryLetter] at hb

namespace RayCopy

/-- Distinct sparse points on one ambient ray are prefix-incomparable. -/
theorem sparse_prefix_antichain (Q : RayCopy)
    (hsparse : ∀ q, Sparse.InSparse (fromBlocks (Q q))) {a b : ℚ}
    (hp : (fromBlocks (Q a)).IsPrefix (fromBlocks (Q b))) : a = b := by
  obtain ⟨n, hn⟩ := (Sparse.inSparse_iff_code _).mp (hsparse a)
  obtain ⟨m, hm⟩ := (Sparse.inSparse_iff_code _).mp (hsparse b)
  by_cases hnm : n = m
  · apply Q.embedding.injective
    apply wordEquiv.symm.injective
    exact hn.trans (hnm ▸ hm.symm)
  · have h1 := Sparse.code_prefix_one (hn ▸ hm ▸ hp) hnm
    rw [← hn, ← hm, Q.fromBlocks_eq, Q.fromBlocks_eq, List.append_assoc] at h1
    have htail := (List.prefix_append_right_inj (rayRoot Q.stem)).mp h1
    exact False.elim (binary_no_one (Q.coordinates b).word
      (htail.subset (by simp)))

/-- Precomposing a ray copy with a rational order embedding preserves its
ambient ray and records the exact source points. -/
def precompose (Q : RayCopy) (e : ℚ ↪o ℚ) : RayCopy :=
  ⟨e.trans Q.embedding, Q.stem, fun q => Q.same_ray (e q)⟩

theorem upper_subcopy (Q : RayCopy) (a : ℚ) :
    ∃ R : RayCopy, R.stem = Q.stem ∧ Set.range R.embedding ⊆ Set.range Q.embedding ∧
      ∀ q, ∃ t, a < t ∧ R q = Q t := by
  obtain ⟨e⟩ := Order.iso_of_countable_dense ℚ (Set.Ioi a)
  let R := Q.precompose (e.toOrderEmbedding.trans (OrderEmbedding.subtype _))
  refine ⟨R, rfl, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    exact ⟨(e q).val, rfl⟩
  · intro q
    exact ⟨(e q).val, (e q).property, rfl⟩

theorem lower_subcopy (Q : RayCopy) (a : ℚ) :
    ∃ R : RayCopy, R.stem = Q.stem ∧ Set.range R.embedding ⊆ Set.range Q.embedding ∧
      ∀ q, ∃ t, t < a ∧ R q = Q t := by
  obtain ⟨e⟩ := Order.iso_of_countable_dense ℚ (Set.Iio a)
  let R := Q.precompose (e.toOrderEmbedding.trans (OrderEmbedding.subtype _))
  refine ⟨R, rfl, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    exact ⟨(e q).val, rfl⟩
  · intro q
    exact ⟨(e q).val, (e q).property, rfl⟩

end RayCopy

/-- A family of finite words has a longest common prefix. The proof searches
only among prefixes of one fixed member of the family. -/
theorem longest_common_prefix (words : ℚ → List TernaryLetter)
    (p : List TernaryLetter) (hp : ∀ q, p.IsPrefix (words q)) :
    ∃ v : List TernaryLetter, p.IsPrefix v ∧ (∀ q, v.IsPrefix (words q)) ∧
      ∀ a : TernaryLetter, ¬∀ q, (v ++ [a]).IsPrefix (words q) := by
  classical
  let good := (Finset.range ((words 0).length + 1)).filter
    (fun k => ∀ q, ((words 0).take k).IsPrefix (words q))
  have hzero : 0 ∈ good := by simp [good]
  let k := good.max' ⟨0, hzero⟩
  have hk := Finset.max'_mem good ⟨0, hzero⟩
  have hklen : k ≤ (words 0).length := by
    have h := (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    omega
  have hkprefix : ∀ q, ((words 0).take k).IsPrefix (words q) := (Finset.mem_filter.mp hk).2
  have hvlen : ((words 0).take k).length = k := by simp [Nat.min_eq_left hklen]
  have hpk : p.length ≤ k := by
    apply Finset.le_max' good p.length
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by have := (hp 0).length_le; omega), ?_⟩
    rw [← List.prefix_iff_eq_take.mp (hp 0)]
    exact hp
  refine ⟨(words 0).take k, List.prefix_take_iff.mpr ⟨hp 0, hpk⟩, hkprefix, ?_⟩
  intro a ha
  have hal := (ha 0).length_le
  rw [List.length_append, hvlen, List.length_singleton] at hal
  have hatake : (words 0).take k ++ [a] = (words 0).take (k + 1) := by
    simpa only [List.length_append, hvlen, List.length_singleton] using
      List.prefix_iff_eq_take.mp (ha 0)
  have hnext : k + 1 ∈ good := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    rw [← hatake]
    exact ha
  have := Finset.le_max' good (k + 1) hnext
  omega

private theorem not_zero_below_two (v s t : List TernaryLetter) :
    ¬wordBelow (v ++ .zero :: s) (v ++ .two :: t) := by
  rw [Sparse.below_common_prefix]
  cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp [wordBelow, parseWord, prependBlock, hs, ht, RayTree.first, binaryLE]

namespace RayCopy

theorem binary_tail_after_prefix (Q : RayCopy) (v : List TernaryLetter)
    (hroot : (rayRoot Q.stem).length ≤ v.length)
    (hp : ∀ q, v.IsPrefix (fromBlocks (Q q)))
    (hne : ∀ q, v ≠ fromBlocks (Q q)) (q : ℚ) :
    (∃ b : List TernaryLetter, .one ∉ b ∧ fromBlocks (Q q) = v ++ .zero :: b) ∨
    (∃ b : List TernaryLetter, .one ∉ b ∧ fromBlocks (Q q) = v ++ .two :: b) := by
  obtain ⟨tail, htail⟩ := hp q
  have htailne : tail ≠ [] := by
    intro h
    apply hne q
    simpa [h] using htail
  obtain ⟨a, b, rfl⟩ := List.exists_cons_of_ne_nil htailne
  have hr : (rayRoot Q.stem).IsPrefix v := List.prefix_of_prefix_length_le
    (by rw [Q.fromBlocks_eq]; exact List.prefix_append _ _) (hp q) hroot
  obtain ⟨s, rfl⟩ := hr
  have heq : s ++ a :: b = (Q.coordinates q).word.map binaryLetter := by
    rw [Q.fromBlocks_eq, List.append_assoc] at htail
    exact List.append_cancel_left htail
  have hnot : TernaryLetter.one ∉ s ++ a :: b := by
    rw [heq]
    exact binary_no_one _
  have ha : a ≠ .one := by intro h; subst a; exact hnot (by simp)
  have hb : TernaryLetter.one ∉ b := by intro h; exact hnot (by simp [h])
  cases a with
  | zero => exact Or.inl ⟨b, hb, htail.symm⟩
  | one => exact False.elim (ha rfl)
  | two => exact Or.inr ⟨b, hb, htail.symm⟩

/-- At a longest common prefix, a sparse single-ray rational suborder
splits into genuine rational suborders on both binary sides. The tails are
explicitly binary, which is needed for exact normalization of diary levels. -/
theorem sparse_split (Q : RayCopy)
    (hsparse : ∀ q, Sparse.InSparse (fromBlocks (Q q)))
    (p : List TernaryLetter) (hp : ∀ q, p.IsPrefix (fromBlocks (Q q)))
    (hroot : (rayRoot Q.stem).length ≤ p.length) :
    ∃ v : List TernaryLetter, ∃ Q0 Q2 : RayCopy,
      p.IsPrefix v ∧ Q0.stem = Q.stem ∧ Q2.stem = Q.stem ∧
      Set.range Q0.embedding ⊆ Set.range Q.embedding ∧
      Set.range Q2.embedding ⊆ Set.range Q.embedding ∧
      (∀ q, ∃ b : List TernaryLetter, .one ∉ b ∧ fromBlocks (Q0 q) = v ++ .zero :: b) ∧
      (∀ q, ∃ b : List TernaryLetter, .one ∉ b ∧ fromBlocks (Q2 q) = v ++ .two :: b) := by
  obtain ⟨v, hpv, hv, hmax⟩ := longest_common_prefix (fun q => fromBlocks (Q q)) p hp
  have hne : ∀ q, v ≠ fromBlocks (Q q) := by
    intro q heq
    obtain ⟨r, hqr⟩ := exists_gt q
    have hsame := Q.sparse_prefix_antichain hsparse (heq ▸ hv r)
    exact hqr.ne hsame
  have tails := Q.binary_tail_after_prefix v (hroot.trans hpv.length_le) hv hne
  have hz : ∃ q, ∃ b : List TernaryLetter, .one ∉ b ∧ fromBlocks (Q q) = v ++ .zero :: b := by
    by_contra h
    apply hmax .two
    intro q
    rcases tails q with h0 | ⟨b, hb, heq⟩
    · exact False.elim (h ⟨q, h0⟩)
    · exact ⟨b, by simpa using heq.symm⟩
  have ht : ∃ q, ∃ b : List TernaryLetter, .one ∉ b ∧ fromBlocks (Q q) = v ++ .two :: b := by
    by_contra h
    apply hmax .zero
    intro q
    rcases tails q with ⟨b, hb, heq⟩ | h2
    · exact ⟨b, by simpa using heq.symm⟩
    · exact False.elim (h ⟨q, h2⟩)
  obtain ⟨a, ba, hba, ha⟩ := hz
  obtain ⟨b, bb, hbb, hb⟩ := ht
  obtain ⟨Q0, h0stem, h0range, h0src⟩ := Q.upper_subcopy a
  obtain ⟨Q2, h2stem, h2range, h2src⟩ := Q.lower_subcopy b
  refine ⟨v, Q0, Q2, hpv, h0stem, h2stem, h0range, h2range, ?_, ?_⟩
  · intro q
    obtain ⟨t, hat, htq⟩ := h0src q
    rcases tails t with h0 | ⟨bt, hbt, ht⟩
    · simpa only [htq] using h0
    · have hle : wordBelow (fromBlocks (Q a)) (fromBlocks (Q t)) :=
        (wordBelow_iff_toBlocks_le _ _).mpr
          (by simpa only [toBlocks_fromBlocks] using Q.embedding.monotone hat.le)
      rw [ha, ht] at hle
      exact False.elim (not_zero_below_two v ba bt hle)
  · intro q
    obtain ⟨t, htb, htq⟩ := h2src q
    rcases tails t with ⟨bt, hbt, ht⟩ | h2
    · have hle : wordBelow (fromBlocks (Q t)) (fromBlocks (Q b)) :=
        (wordBelow_iff_toBlocks_le _ _).mpr
          (by simpa only [toBlocks_fromBlocks] using Q.embedding.monotone htb.le)
      rw [ht, hb] at hle
      exact False.elim (not_zero_below_two v bt bb hle)
    · simpa only [htq] using h2

end RayCopy

end AllThoseBigRamsey.Pseudotree.LowerGeometry
