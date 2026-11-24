import AllThoseBigRamsey.Pseudotree.Oscillation
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! The finite-set/characteristic-word bridge for the oscillation lemma. -/

namespace AllThoseBigRamsey.Pseudotree.FiniteOscillation

open Oscillation

def support (w : List Bool) : Finset ℕ :=
  (Finset.range w.length).filter (fun i => w[i]?.getD false = true)

@[simp] theorem mem_support (w : List Bool) (i : ℕ) :
    i ∈ support w ↔ w[i]? = some true := by
  by_cases hi : i < w.length <;> simp [support, hi]

theorem mem_support_lt {w : List Bool} {i : ℕ} (hi : i ∈ support w) : i < w.length := by
  exact ((List.getElem?_eq_some_iff).mp ((mem_support w i).mp hi)).1

def bits (s : Finset ℕ) (start size : ℕ) : List Bool :=
  List.ofFn (fun i : Fin size => decide (start + i.val ∈ s))

@[simp] theorem bits_length (s : Finset ℕ) (start size : ℕ) :
    (bits s start size).length = size := List.length_ofFn

theorem bits_get (s : Finset ℕ) (start size i : ℕ) :
    (bits s start size)[i]? = if i < size then some (decide (start + i ∈ s)) else none := by
  by_cases hi : i < size <;> simp [bits, hi]

def wordOf (s : Finset ℕ) : List Bool := bits s 0 (s.sup id + 1)

@[simp] theorem support_wordOf (s : Finset ℕ) : support (wordOf s) = s := by
  ext i
  rw [mem_support, wordOf, bits_get]
  by_cases hi : i < s.sup id + 1
  · simp [hi]
  · have hn : i ∉ s := by
      intro hmem
      have hb : i ≤ s.sup id := Finset.le_sup (f := id) hmem
      omega
    simp [hi, hn]

theorem support_pad (w : List Bool) (n : ℕ) :
    support (w ++ List.replicate n false) = support w := by
  ext i
  simp only [mem_support]
  by_cases hi : i < w.length
  · rw [List.getElem?_append_left hi]
  · rw [List.getElem?_append_right (by omega)]
    have hnone : w[i]? = none := List.getElem?_eq_none (by omega)
    simp [hnone, List.getElem?_replicate]

theorem word_eq_of_support_length (s t : List Bool)
    (hs : support s = support t) (hlen : s.length = t.length) : s = t := by
  apply List.ext_getElem hlen
  intro i hi hit
  have hh : s[i] = true ↔ t[i] = true := by
    have hm : i ∈ support s ↔ i ∈ support t := by rw [hs]
    simpa [hi, hit] using hm
  cases hs' : s[i] <;> cases ht' : t[i] <;> simp_all

theorem oscillation_pad_left (s t : List Bool) (n : ℕ) :
    oscillation (s ++ List.replicate n false) t = oscillation s t := by
  simp only [oscillation, differenceWord_pad_left]

theorem oscillation_pad_right (s t : List Bool) (n : ℕ) :
    oscillation s (t ++ List.replicate n false) = oscillation s t := by
  rw [oscillation_symm, oscillation_pad_left, oscillation_symm]

theorem oscillation_support_left (s s' t : List Bool) (hs : support s = support s') :
    oscillation s t = oscillation s' t := by
  let n := max s.length s'.length
  have hn : s.length ≤ n := le_max_left _ _
  have hn' : s'.length ≤ n := le_max_right _ _
  have heq : s ++ List.replicate (n - s.length) false =
      s' ++ List.replicate (n - s'.length) false := by
    apply word_eq_of_support_length
    · simpa only [support_pad] using hs
    · simp only [List.length_append, List.length_replicate]
      omega
  calc
    oscillation s t = oscillation (s ++ List.replicate (n - s.length) false) t :=
      (oscillation_pad_left s t _).symm
    _ = oscillation (s' ++ List.replicate (n - s'.length) false) t := by rw [heq]
    _ = oscillation s' t := oscillation_pad_left s' t _

def osc (s t : Finset ℕ) : ℕ := oscillation (wordOf s) (wordOf t)

theorem osc_symm (s t : Finset ℕ) : osc s t = osc t s :=
  oscillation_symm (wordOf t) (wordOf s)

theorem osc_le_one_of_subset {s t : Finset ℕ} (h : s ⊆ t) : osc s t ≤ 1 := by
  apply oscillation_le_one_of_subset
  intro i hi
  have his : i ∈ s := by
    simpa using (mem_support (wordOf s) i).mpr hi
  have hit : i ∈ support (wordOf t) := by simpa using h his
  exact (mem_support (wordOf t) i).mp hit

/-- Oscillation is independent of the length of characteristic words. -/
theorem osc_support (s t : List Bool) : osc (support s) (support t) = oscillation s t := by
  unfold osc
  rw [oscillation_support_left _ s _ (support_wordOf _)]
  rw [oscillation_symm, oscillation_support_left _ t _ (support_wordOf _), oscillation_symm]

private theorem support_extension (w : List Bool) (N : ℕ) (t : Finset ℕ)
    (hsub : support w ⊆ t)
    (hnew : ∀ i ∈ t, i ∉ support w → w.length + N ≤ i) :
    support (w ++ List.replicate N false ++ bits t (w.length + N) (t.sup id + 1)) = t := by
  ext i
  rw [mem_support]
  by_cases hi : i < w.length + N
  · rw [List.getElem?_append_left (by simp only [List.length_append, List.length_replicate]; exact hi)]
    by_cases hiw : i < w.length
    · rw [List.getElem?_append_left hiw]
      have heq : i ∈ t ↔ i ∈ support w := by
        constructor
        · intro hit
          by_contra hnot
          have := hnew i hit hnot
          omega
        · exact fun h => hsub h
      exact (mem_support w i).symm.trans heq.symm
    · rw [List.getElem?_append_right (by omega)]
      have hnot : i ∉ t := by
        intro hit
        have hns : i ∉ support w := fun h => hiw (mem_support_lt h)
        have := hnew i hit hns
        omega
      simp [List.getElem?_replicate, hnot]
  · rw [List.getElem?_append_right (by simp only [List.length_append, List.length_replicate]; omega)]
    simp only [List.length_append, List.length_replicate]
    rw [bits_get]
    have heq : w.length + N + (i - (w.length + N)) = i := by omega
    by_cases hj : i - (w.length + N) < t.sup id + 1
    · simp [hj, heq]
    · have hnot : i ∉ t := by
        intro hit
        have hbound : i ≤ t.sup id := Finset.le_sup (f := id) hit
        omega
      simp [hj, hnot]

/-- Proper end-extensions of finite sets give exactly the word hypothesis used
in the checked elementary oscillation construction. -/
theorem word_endExtensions (X : Finset ℕ → Prop)
    (hext : ∀ s, X s → ∀ N, ∃ t, X t ∧ s ⊂ t ∧ ∀ i ∈ t, i ∉ s → N < i) :
    EndExtensions (fun w => X (support w)) := by
  intro w hw N
  obtain ⟨t, ht, hst, hnew⟩ := hext (support w) hw (w.length + N)
  obtain ⟨i, hit, his⟩ : ∃ i, i ∈ t ∧ i ∉ support w := by
    by_contra h
    push Not at h
    have heq := Finset.Subset.antisymm hst.subset h
    exact (Finset.ssubset_iff_subset_ne.mp hst).2 heq
  let u := bits t (w.length + N) (t.sup id + 1)
  have hli : w.length + N ≤ i := Nat.le_of_lt (hnew i hit his)
  have hbound : i ≤ t.sup id := Finset.le_sup (f := id) hit
  have hj : i - (w.length + N) < t.sup id + 1 := by omega
  have hu : true ∈ u := by
    apply List.mem_iff_getElem.mpr
    refine ⟨i - (w.length + N), ?_, ?_⟩
    · simp only [u, bits_length]
      omega
    · change (List.ofFn (fun j : Fin (t.sup id + 1) =>
        decide (w.length + N + j.val ∈ t)))[i - (w.length + N)]'
          (by simpa only [List.length_ofFn] using hj) = true
      rw [List.getElem_ofFn]
      simpa only [Nat.add_sub_of_le hli, decide_eq_true_eq] using hit
  refine ⟨u, hu, ?_⟩
  have hsupp : support (w ++ List.replicate N false ++ u) = t :=
    support_extension w N t hst.subset (fun i hi hni => Nat.le_of_lt (hnew i hi hni))
  simpa only [hsupp] using ht

/-- Every natural oscillation occurs in any nonempty end-extensible family
of finite subsets of the naturals. In particular this proves the FIN lemma
in the exact end-extension formulation used by the revised manuscript. -/
theorem all_oscillations (X : Finset ℕ → Prop)
    (hne : ∃ s, X s)
    (hext : ∀ s, X s → ∀ N, ∃ t, X t ∧ s ⊂ t ∧ ∀ i ∈ t, i ∉ s → N < i)
    (k : ℕ) : ∃ s t, X s ∧ X t ∧ osc s t = k := by
  obtain ⟨s, hs⟩ := hne
  have hY : ∃ w, X (support w) := ⟨wordOf s, by simpa using hs⟩
  obtain ⟨w, v, hw, hv, hk⟩ := Oscillation.all_oscillations
    (fun w => X (support w)) hY (word_endExtensions X hext) k
  exact ⟨support w, support v, hw, hv, by simpa only [osc_support] using hk⟩

end AllThoseBigRamsey.Pseudotree.FiniteOscillation
