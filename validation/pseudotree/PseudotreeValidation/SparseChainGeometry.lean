import AllThoseBigRamsey.Pseudotree.SparseFrontier
import AllThoseBigRamsey.Pseudotree.SparseOrder
import PseudotreeValidation.DiaryChains

/-! The maximum branch of an actual sparse pseudotree chain carries every
upper-cone continuation. This is the precise corrected geometric statement;
it does not assert that the maximal coding word is lexicographically least.
-/

namespace AllThoseBigRamsey.Pseudotree.Sparse

private theorem words_split (s t : Word) :
    s.IsPrefix t ∨ t.IsPrefix s ∨ ∃ p a b u v,
      s = p ++ a :: u ∧ t = p ++ b :: v ∧ a ≠ b := by
  induction s generalizing t with
  | nil => exact Or.inl (by simp)
  | cons a s ih =>
    cases t with
    | nil => exact Or.inr (Or.inl (by simp))
    | cons b t =>
      by_cases hab : a = b
      · subst b
        rcases ih t with h | h | ⟨p, c, d, u, v, hs, ht, hcd⟩
        · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
        · exact Or.inr (Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩))
        · exact Or.inr (Or.inr ⟨a :: p, c, d, u, v, by simp [hs], by simp [ht], hcd⟩)
      · exact Or.inr (Or.inr ⟨[], a, b, s, t, rfl, rfl, hab⟩)

theorem sibling_letters {p : Word} {a b : TernaryLetter}
    (ha : InTree (p ++ [a])) (hb : InTree (p ++ [b])) (hab : a ≠ b) :
    (a = TernaryLetter.zero ∧ b = TernaryLetter.two) ∨ (a = TernaryLetter.two ∧ b = TernaryLetter.zero) := by
  have hp := inTree_prefix ha (List.prefix_append p [a])
  have hA := (critical_children p.length p hp rfl a).mp ha
  have hB := (critical_children p.length p hp rfl b).mp hb
  by_cases heq : p = critical p.length
  · rw [CriticalChildren, ite_eq_left heq] at hA hB
    by_cases hphase : p.length % 3 = 2
    · simp only [hphase, decide_true, ↓reduceIte] at hA hB
      exact False.elim (hab (hA.trans hB.symm))
    · simp only [hphase, decide_false, Bool.false_eq_true, ↓reduceIte] at hA hB
      rcases hA with ha0 | ha2
      · rcases hB with hb0 | hb2
        · exact False.elim (hab (ha0.trans hb0.symm))
        · exact Or.inl ⟨ha0, hb2⟩
      · rcases hB with hb0 | hb2
        · exact Or.inr ⟨ha2, hb0⟩
        · exact False.elim (hab (ha2.trans hb2.symm))
  · rw [CriticalChildren, ite_eq_right heq] at hA hB
    exact False.elim (hab (hA.trans hB.symm))

private theorem noOne_iff_point (s : Word) :
    RayMapModel.NoOne s ↔ ∃ b, parseWord s = .point b := by
  induction s with
  | nil => simp [parseWord]
  | cons a s ih =>
    cases h : parseWord s with
    | point b =>
      have hs : RayMapModel.NoOne s := ih.mpr ⟨b, h⟩
      cases a <;> simp [parseWord, prependBlock, h, hs]
    | above b t =>
      have hs : ¬ RayMapModel.NoOne s := by
        intro hbin
        obtain ⟨c, hc⟩ := ih.mp hbin
        rw [h] at hc
        cases hc
      cases a <;> simp [parseWord, prependBlock, h, hs]

private theorem below_cons_distinct (a b : TernaryLetter) (s t : Word)
    (hab : a ≠ b) : wordBelow (a :: s) (b :: t) ↔ a = TernaryLetter.two ∧ RayMapModel.NoOne s := by
  rw [noOne_iff_point]
  cases a <;> cases b <;> cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp_all [wordBelow, parseWord, prependBlock, RayTree.first, binaryLE]

private theorem not_below_one_nil (s : Word) : ¬ wordBelow (TernaryLetter.one :: s) [] := by
  simp [wordBelow, parseWord]

private theorem below_same (a : TernaryLetter) (s t : Word) :
    wordBelow (a :: s) (a :: t) ↔ wordBelow s t := by
  cases a <;> cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp [wordBelow, parseWord, prependBlock, hs, ht, RayTree.Below, RayTree.first, binaryLE]

private theorem below_cons_nil (a : TernaryLetter) (s : Word) :
    wordBelow (a :: s) [] ↔ a = TernaryLetter.two ∧ RayMapModel.NoOne s := by
  rw [noOne_iff_point]
  cases a <;> cases h : parseWord s <;>
    simp [wordBelow, parseWord, prependBlock, h, RayTree.first, binaryLE]

/-- Upper-cone prefixes are monotone in the actual pseudotree order.
No sparse-set or chain-shape assumption is required. -/
theorem wordBelow_one_prefix (p tail v : Word)
    (hbelow : wordBelow (p ++ TernaryLetter.one :: tail) v) :
    (p ++ [TernaryLetter.one]).IsPrefix v := by
  induction p generalizing v with
  | nil =>
    cases v with
    | nil => exact False.elim (not_below_one_nil tail hbelow)
    | cons b v =>
      by_cases hb : TernaryLetter.one = b
      · subst b
        simp
      · have h := (below_cons_distinct TernaryLetter.one b tail v hb).mp hbelow
        cases h.1
  | cons a p ih =>
    cases v with
    | nil =>
      have h := (below_cons_nil a (p ++ TernaryLetter.one :: tail)).mp hbelow
      exact False.elim (h.2 TernaryLetter.one (by simp) rfl)
    | cons b v =>
      by_cases hab : a = b
      · subst b
        exact List.cons_prefix_cons.mpr ⟨rfl,
          ih v ((below_same a (p ++ TernaryLetter.one :: tail) v).mp hbelow)⟩
      · have h := (below_cons_distinct a b (p ++ TernaryLetter.one :: tail) v hab).mp hbelow
        exact False.elim (h.2 TernaryLetter.one (by simp) rfl)

/-- Exact spine dichotomy for actual sparse nodes below a given maximum:
non-prefix nodes leave that maximum to the right, and cannot turn upward
again afterwards. -/
theorem below_spine {w v : Word} (hw : InSparse w) (hv : InSparse v)
    (hbelow : wordBelow w v) :
    w.IsPrefix v ∨ ∃ p s t, w = p ++ TernaryLetter.two :: s ∧ v = p ++ TernaryLetter.zero :: t ∧ TernaryLetter.one ∉ s := by
  have hwTree : InTree w := by
    obtain ⟨n, rfl⟩ := (inSparse_iff_code w).mp hw
    exact ⟨n, List.prefix_rfl⟩
  have hvTree : InTree v := by
    obtain ⟨n, rfl⟩ := (inSparse_iff_code v).mp hv
    exact ⟨n, List.prefix_rfl⟩
  rcases words_split w v with hp | hp | ⟨p, a, b, s, t, hwform, hvform, hab⟩
  · exact Or.inl hp
  · by_cases heq : w = v
    · exact Or.inl (heq ▸ List.prefix_rfl)
    obtain ⟨nw, hnw⟩ := (inSparse_iff_code w).mp hw
    obtain ⟨nv, hnv⟩ := (inSparse_iff_code v).mp hv
    have hnvw : nv ≠ nw := by intro hn; exact heq (hnw.trans (hn ▸ hnv.symm))
    have hprefix : (v ++ [TernaryLetter.one]).IsPrefix w := by
      rw [hnv, hnw]
      apply code_prefix_one
      · simpa only [← hnw, ← hnv] using hp
      · exact hnvw
    obtain ⟨tail, htail⟩ := hprefix
    have hform : w = v ++ TernaryLetter.one :: tail := by
      simpa only [List.append_assoc, List.singleton_append] using htail.symm
    have hbad : wordBelow (TernaryLetter.one :: tail) [] := by
      have hh : wordBelow (v ++ (TernaryLetter.one :: tail)) (v ++ []) := by
        simpa only [hform, List.append_nil] using hbelow
      exact (below_common_prefix v _ _).mp hh
    exact False.elim (not_below_one_nil tail hbad)
  · have ha : InTree (p ++ [a]) := inTree_prefix hwTree (by
      rw [hwform]
      exact ⟨s, by simp⟩)
    have hb : InTree (p ++ [b]) := inTree_prefix hvTree (by
      rw [hvform]
      exact ⟨t, by simp⟩)
    have hlocal : wordBelow (a :: s) (b :: t) := by
      rw [hwform, hvform] at hbelow
      exact (below_common_prefix p _ _).mp hbelow
    have haTwo := (below_cons_distinct a b s t hab).mp hlocal
    rcases sibling_letters ha hb hab with ⟨haz, hb2⟩ | ⟨ha2, hbz⟩
    · have : (TernaryLetter.zero : TernaryLetter) = TernaryLetter.two := haz.symm.trans haTwo.1
      contradiction
    · refine Or.inr ⟨p, s, t, by simpa only [ha2] using hwform,
        by simpa only [hbz] using hvform, ?_⟩
      exact fun hmem => haTwo.2 TernaryLetter.one hmem rfl

/-- Every initial segment ending in `1` below the maximum is on its branch. -/
theorem one_prefix_on_spine {w v : Word} (hw : InSparse w) (hv : InSparse v)
    (hbelow : wordBelow w v) {p t : Word} (heq : w = p ++ TernaryLetter.one :: t) :
    (p ++ [TernaryLetter.one]).IsPrefix v := by
  rcases below_spine hw hv hbelow with hp | ⟨q, s, u, hwq, hvq, hbinary⟩
  · apply List.IsPrefix.trans _ hp
    rw [heq]
    exact ⟨t, by simp⟩
  · have hpref : (p ++ [TernaryLetter.one]).IsPrefix w := by rw [heq]; exact ⟨t, by simp⟩
    have hqlen : (p ++ [TernaryLetter.one]).length ≤ q.length := by
      by_contra h
      have hpq : q.IsPrefix p := by
        have hq : q.IsPrefix w := by rw [hwq]; exact List.prefix_append q _
        have hp : p.IsPrefix w := by rw [heq]; exact List.prefix_append p _
        apply List.prefix_of_prefix_length_le hq hp
        simp only [List.length_append, List.length_singleton] at h
        omega
      obtain ⟨r, hr⟩ := hpq
      have htail : TernaryLetter.two :: s = r ++ TernaryLetter.one :: t := by
        rw [← hr, List.append_assoc] at heq
        rw [hwq] at heq
        exact List.append_cancel_left heq
      have hmem : TernaryLetter.one ∈ (TernaryLetter.two :: s) := by rw [htail]; simp
      exact hbinary (by simpa using hmem)
    have hpq : (p ++ [TernaryLetter.one]).IsPrefix q :=
      List.prefix_of_prefix_length_le hpref (by rw [hwq]; exact List.prefix_append q _) hqlen
    rw [hvq]
    exact hpq.trans (List.prefix_append q _)

/-- Indexed version used to prove that compressed gaps are binary. -/
theorem one_at_on_spine {w v : Word} (hw : InSparse w) (hv : InSparse v)
    (hbelow : wordBelow w v) (k : ℕ) (hk : k < w.length) (hOne : w[k] = TernaryLetter.one) :
    k < v.length ∧ w.take (k + 1) = v.take (k + 1) := by
  have heq : w = w.take k ++ TernaryLetter.one :: w.drop (k + 1) := by
    simpa only [List.drop_eq_getElem_cons hk, hOne] using (List.take_append_drop k w).symm
  have hp := one_prefix_on_spine hw hv hbelow heq
  have hl : (w.take k ++ [TernaryLetter.one]).length = k + 1 := by
    simp only [List.length_append, List.length_take, List.length_singleton, Nat.min_eq_left hk.le]
  have hb := hp.length_le
  rw [hl] at hb
  refine ⟨by omega, ?_⟩
  rw [List.take_succ_eq_append_getElem hk, hOne]
  simpa only [hl] using List.prefix_iff_eq_take.mp hp

/-- The same prefix conclusion on the diary's `Fin 3` alphabet, with the
order hypothesis stated in the actual functional model. -/
theorem fin_one_prefix_on_spine {w v p t : DiaryWord}
    (hw : InSparse (w.map RayMapModel.toLetter))
    (hv : InSparse (v.map RayMapModel.toLetter))
    (hbelow : DiaryChains.model w ≤ DiaryChains.model v)
    (heq : w = p ++ 1 :: t) : (p ++ [1]).IsPrefix v := by
  have hb : wordBelow (w.map RayMapModel.toLetter) (v.map RayMapModel.toLetter) :=
    (wordBelow_iff_toBlocks_le _ _).mpr hbelow
  have hform : w.map RayMapModel.toLetter = p.map RayMapModel.toLetter ++
      TernaryLetter.one :: t.map RayMapModel.toLetter := by
    simp only [heq, List.map_append, List.map_cons]
    rfl
  have hp := one_prefix_on_spine hw hv hb hform
  have hmap := hp.map RayMapModel.toFin
  have hOne : RayMapModel.toFin TernaryLetter.one = (1 : Fin 3) := rfl
  simpa [List.map_append, List.map_map, Function.comp_def, hOne] using hmap

end AllThoseBigRamsey.Pseudotree.Sparse
