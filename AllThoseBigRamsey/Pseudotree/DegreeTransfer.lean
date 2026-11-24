import AllThoseBigRamsey.Relational

/-!
# The finite-palette steps in the pseudotree note

This file checks the final counting deductions. It does not assume that
pseudotree diaries have already been shown canonical or unavoidable: those
are explicit hypotheses of `exact_degree_of_types` and remain application
obligations. The existing repository definition counts embeddings. For finite
chains these agree with copies, because each finite chain is rigid.
-/

namespace AllThoseBigRamsey.Pseudotree

private theorem flatten_length_bound (palette : List (List α)) (K : Nat)
    (hsmall : ∀ c ∈ palette, c.length ≤ K) :
    palette.flatten.length ≤ palette.length * K := by
  induction palette with
  | nil => simp
  | cons c palette ih =>
    have hc := hsmall c (by simp)
    have hp := ih (fun d hd => hsmall d (by simp [hd]))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [Nat.add_mul]
    simp only [Nat.one_mul]
    omega

/-- Set-valued residue colours: covering all `m` residues requires at least
`m / K` colours. The use of lists allows repetitions and so proves a slightly
stronger assertion than the finite-set version in the manuscript. -/
theorem residue_cover_bound (palette : List (List (Fin m))) (K : Nat)
    (hsmall : ∀ c ∈ palette, c.length ≤ K)
    (hcover : ∀ i : Fin m, ∃ c ∈ palette, i ∈ c) :
    m ≤ palette.length * K := by
  have hsub : List.finRange m ⊆ palette.flatten := by
    intro i _
    obtain ⟨c, hc, hi⟩ := hcover i
    exact List.mem_flatten.mpr ⟨c, hc, hi⟩
  have hlen := (List.nodup_finRange m).length_le_of_subset hsub
  have hflat := flatten_length_bound palette K hsmall
  simp only [List.length_finRange] at hlen
  exact Nat.le_trans hlen hflat

/-- Choosing more than `d*K` residues contradicts any palette of at most `d`
colours. This is the arithmetic step proving infinite degrees for every
finite structure containing an incomparable pair. -/
theorem residue_palette_not_bounded
    (d K : Nat) (palette : List (List (Fin (d * K + 1))))
    (hsmall : ∀ c ∈ palette, c.length ≤ K)
    (hcover : ∀ i : Fin (d * K + 1), ∃ c ∈ palette, i ∈ c) :
    ¬ palette.length ≤ d := by
  intro hlen
  have h := residue_cover_bound palette K hsmall hcover
  have hmul := Nat.mul_le_mul_right K hlen
  omega

/-- Canonization and unavoidability imply an exact embedding big Ramsey degree.
Both geometric assertions are hypotheses, rather than declarations masquerading
as a completed validation of the pseudotree theorem. -/
theorem exact_degree_of_types {L : Language} {α κ : Type}
    (A : RelStructure L α) (H : RelStructure L κ)
    (n : Nat) (hn : 0 < n) (typeOf : Embedding A H → Fin n)
    (canon : ∀ r : Nat, 0 < r → ∀ χ : Embedding A H → Fin r,
      ∃ f : Embedding H H, ∃ c : Fin n → Fin r,
        ∀ g : Embedding A H, χ (Embedding.comp f g) = c (typeOf g))
    (unavoidable : ∀ f : Embedding H H, ∀ i : Fin n,
      ∃ g : Embedding A H, typeOf (Embedding.comp f g) = i) :
    IsBigRamseyDegree A H (some n) := by
  constructor
  · intro r hr χ
    obtain ⟨f, c, hc⟩ := canon r hr χ
    refine ⟨f, List.ofFn c, ?_, ?_⟩
    · simp
    · intro g
      rw [hc g]
      exact List.mem_ofFn.mpr ⟨typeOf g, rfl⟩
  · intro s hs
    obtain ⟨f, palette, hlen, hpalette⟩ := hs n hn typeOf
    have hsub : List.finRange n ⊆ palette := by
      intro i _
      obtain ⟨g, hg⟩ := unavoidable f i
      simpa only [hg] using hpalette g
    have h := (List.nodup_finRange n).length_le_of_subset hsub
    simp only [List.length_finRange] at h
    exact Nat.le_trans h hlen

end AllThoseBigRamsey.Pseudotree
