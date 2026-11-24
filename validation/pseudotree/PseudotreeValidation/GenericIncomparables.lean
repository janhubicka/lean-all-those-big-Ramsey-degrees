import PseudotreeValidation.Incomparables

/-!
# Infinite degrees from the structural properties of a dense meet-tree

This generalization applies to countable ultrahomogeneous meet-trees with
dense chains, no maximal points, and a second branch above every point on a
chain. In particular, the profile argument is not restricted to binary
branching. The final theorem assumes precisely these geometric and
homogeneity properties; it does not assume oscillation or profile
conclusions. A separate identification of any named model with these
properties remains an application, not a new axiom.
-/

namespace AllThoseBigRamsey.Pseudotree.GenericIncomparables

open FirstOrder Profiles FiniteOscillation
open scoped FirstOrder

variable {M : Type*} [SemilatticeInf M]

theorem profile_osc_le_one (E : System M) {a b : M} (hab : a ≤ b ∨ b ≤ a) :
    osc (E.profile a) (E.profile b) ≤ 1 := by
  rcases hab with hab | hba
  · exact osc_le_one_of_subset (E.profile_monotone hab)
  · rw [osc_symm]
    exact osc_le_one_of_subset (E.profile_monotone hba)

/-- The exact oscillation result holds on any subset with the proved
geometric richness properties. No homogeneity is needed at this stage. -/
theorem every_oscillation_of_rich (E : System M) {S : Set M} (hS : E.RichSubset S)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ a b, a ∈ S ∧ b ∈ S ∧ ¬a ≤ b ∧ ¬b ≤ a ∧ osc (E.profile a) (E.profile b) = k := by
  obtain ⟨s, t, hs, ht, hosc⟩ := FiniteOscillation.all_oscillations
    (E.Repeated S) (E.repeated_nonempty hS)
    (fun _ hs N => E.repeated_endExtension hS hs N) k
  obtain ⟨u, hu, a, ha, hua, hus, has⟩ := hs
  obtain ⟨v, hv, b, hb, hvb, hvt, hbt⟩ := ht
  have habosc : osc (E.profile a) (E.profile b) = k := by simpa only [has, hbt] using hosc
  refine ⟨a, b, ha, hb, ?_, ?_, habosc⟩
  · intro hab
    have hbound := profile_osc_le_one E (Or.inl hab)
    omega
  · intro hba
    have hbound := profile_osc_le_one E (Or.inr hba)
    omega

noncomputable def pairColour (E : System M) (m : ℕ) (hm : 0 < m) (a b : M) : Fin m :=
  ⟨osc (E.profile a) (E.profile b) % m, Nat.mod_lt _ hm⟩

theorem pairColour_symm (E : System M) (m : ℕ) (hm : 0 < m) (a b : M) :
    pairColour E m hm a b = pairColour E m hm b a := by
  apply Fin.ext
  simp only [pairColour, osc_symm]

theorem every_pairColour_of_rich (E : System M) {S : Set M} (hS : E.RichSubset S)
    (m : ℕ) (hm : 0 < m) (i : Fin m) :
    ∃ a b, a ∈ S ∧ b ∈ S ∧ ¬a ≤ b ∧ ¬b ≤ a ∧ pairColour E m hm a b = i := by
  obtain ⟨a, b, ha, hb, hab, hba, hosc⟩ :=
    every_oscillation_of_rich E hS (i.val + 2 * m) (by omega)
  refine ⟨a, b, ha, hb, hab, hba, ?_⟩
  apply Fin.ext
  simp [pairColour, hosc, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

section Functional

variable [language.Structure M] [MeetsInterpreted M]

/-- Geometric assumptions on the ambient meet-tree pass to each functional
self-copy and imply the exact hypotheses used in the profile proof. -/
theorem copy_rich [Nonempty M] [DenselyOrdered M] [NoMaxOrder M]
    (E : System M) (hbranch : ∀ {x a : M}, x < a → ∃ z, x < z ∧ z ⊓ a = x)
    (f : M ↪[language] M) : E.RichSubset (Set.range f) :=
  E.richSubset_range hbranch (embeddingOrderEmbedding f) (embedding_map_inf f)

/-- The fork extension uses the stated ultrahomogeneity of the model. -/
theorem extend_pair (hhom : language.IsUltrahomogeneous M)
    {A : Type*} [SemilatticeInf A] [language.Structure A] [MeetsInterpreted A]
    (hA : Nonempty (A ↪[language] M))
    {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x)
    {a b : M} (hab : ¬a ≤ b) (hba : ¬b ≤ a) :
    ∃ e : A ↪[language] M, e x = a ∧ e y = b := by
  obtain ⟨e, he⟩ := hhom.extend_embedding
    (FirstOrder.Language.Structure.FG.of_finite :
      FirstOrder.Language.Structure.FG language Incomparables.Fork)
    (Incomparables.Fork.embedding hab hba) (Incomparables.Fork.embedding hxy hyx) (h := hA)
  refine ⟨e, ?_, ?_⟩
  · have h := congrArg (fun g : Incomparables.Fork ↪[language] M => g .left) he
    simpa using h.symm
  · have h := congrArg (fun g : Incomparables.Fork ↪[language] M => g .right) he
    simpa using h.symm

noncomputable def pairPalette {A : Type*} [Fintype A] [SemilatticeInf A]
    [language.Structure A] [MeetsInterpreted A]
    (E : System M) (m : ℕ) (hm : 0 < m) (e : A ↪[language] M) : Finset (Fin m) := by
  classical
  exact (Finset.univ.filter (fun p : A × A => ¬p.1 ≤ p.2 ∧ ¬p.2 ≤ p.1)).image
    (fun p => pairColour E m hm (e p.1) (e p.2))

omit [MeetsInterpreted M] in
theorem mem_pairPalette {A : Type*} [Fintype A] [SemilatticeInf A]
    [language.Structure A] [MeetsInterpreted A]
    (E : System M) (m : ℕ) (hm : 0 < m) (e : A ↪[language] M) (i : Fin m) :
    i ∈ pairPalette E m hm e ↔
      ∃ x y, ¬x ≤ y ∧ ¬y ≤ x ∧ pairColour E m hm (e x) (e y) = i := by
  classical
  simp only [pairPalette, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Prod.exists]
  aesop

omit [MeetsInterpreted M] in
theorem pairPalette_card_le {A : Type*} [Fintype A] [SemilatticeInf A]
    [language.Structure A] [MeetsInterpreted A]
    (E : System M) (m : ℕ) (hm : 0 < m) (e : A ↪[language] M) :
    (pairPalette E m hm e).card ≤ Fintype.card A ^ 2 := by
  classical
  calc
    (pairPalette E m hm e).card ≤
        (Finset.univ.filter (fun p : A × A => ¬p.1 ≤ p.2 ∧ ¬p.2 ≤ p.1)).card :=
      Finset.card_image_le
    _ ≤ (Finset.univ : Finset (A × A)).card := Finset.card_filter_le _ _
    _ = Fintype.card A ^ 2 := by simp [pow_two]

theorem pairPalette_subset_of_range_subset {A B : Type*} [Fintype A] [Fintype B]
    [SemilatticeInf A] [SemilatticeInf B]
    [language.Structure A] [MeetsInterpreted A] [language.Structure B] [MeetsInterpreted B]
    (E : System M) (m : ℕ) (hm : 0 < m) (e : A ↪[language] M)
    (g : B ↪[language] M) (hrange : Set.range e ⊆ Set.range g) :
    pairPalette E m hm e ⊆ pairPalette E m hm g := by
  classical
  intro i hi
  obtain ⟨x, y, hxy, hyx, hc⟩ := (mem_pairPalette E m hm e i).mp hi
  obtain ⟨u, hu⟩ := hrange (Set.mem_range_self x)
  obtain ⟨v, hv⟩ := hrange (Set.mem_range_self y)
  apply (mem_pairPalette E m hm g i).mpr
  refine ⟨u, v, ?_, ?_, ?_⟩
  · intro huv
    have h : g u ≤ g v := (embeddingOrderEmbedding g).monotone huv
    rw [hu, hv] at h
    exact hxy ((embeddingOrderEmbedding e).le_iff_le.mp h)
  · intro hvu
    have h : g v ≤ g u := (embeddingOrderEmbedding g).monotone hvu
    rw [hu, hv] at h
    exact hyx ((embeddingOrderEmbedding e).le_iff_le.mp h)
  · simpa only [hu, hv] using hc

theorem pairPalette_eq_of_range_eq {A B : Type*} [Fintype A] [Fintype B]
    [SemilatticeInf A] [SemilatticeInf B]
    [language.Structure A] [MeetsInterpreted A] [language.Structure B] [MeetsInterpreted B]
    (E : System M) (m : ℕ) (hm : 0 < m) (e : A ↪[language] M)
    (g : B ↪[language] M) (hrange : Set.range e = Set.range g) :
    pairPalette E m hm e = pairPalette E m hm g :=
  Finset.Subset.antisymm (pairPalette_subset_of_range_subset E m hm e g hrange.subset)
    (pairPalette_subset_of_range_subset E m hm g e hrange.symm.subset)

theorem every_colour_in_pattern [Nonempty M] [DenselyOrdered M] [NoMaxOrder M]
    (E : System M) (hbranch : ∀ {x a : M}, x < a → ∃ z, x < z ∧ z ⊓ a = x)
    (hhom : language.IsUltrahomogeneous M)
    {A : Type*} [Fintype A] [SemilatticeInf A] [language.Structure A] [MeetsInterpreted A]
    (hA : Nonempty (A ↪[language] M)) {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x)
    (m : ℕ) (hm : 0 < m) (f : M ↪[language] M) (i : Fin m) :
    ∃ e : A ↪[language] M, i ∈ pairPalette E m hm (f.comp e) := by
  obtain ⟨a, b, ⟨u, rfl⟩, ⟨v, rfl⟩, hab, hba, hc⟩ :=
    every_pairColour_of_rich E (copy_rich E hbranch f) m hm i
  have huv : ¬u ≤ v := fun h => hab ((embeddingOrderEmbedding f).monotone h)
  have hvu : ¬v ≤ u := fun h => hba ((embeddingOrderEmbedding f).monotone h)
  obtain ⟨e, hex, hey⟩ := extend_pair hhom hA hxy hyx huv hvu
  refine ⟨e, (mem_pairPalette E m hm (f.comp e) i).mpr ⟨x, y, hxy, hyx, ?_⟩⟩
  simpa only [FirstOrder.Language.Embedding.comp_apply, hex, hey] using hc

end Functional

/-- Standard finite big Ramsey bound for functional embeddings. -/
def FunctionalBigRamseyBound (A M : Type*) [language.Structure A]
    [language.Structure M] (d : ℕ) : Prop :=
  ∀ r : ℕ, 0 < r → ∀ χ : (A ↪[language] M) → Fin r,
    ∃ f : M ↪[language] M, ∃ palette : Finset (Fin r),
      palette.card ≤ d ∧ ∀ e : A ↪[language] M, χ (f.comp e) ∈ palette

section Bounds

variable [language.Structure M] [MeetsInterpreted M]
    [Nonempty M] [DenselyOrdered M] [NoMaxOrder M]

/-- Quantitative, image-invariant colourings for the general structural
hypotheses. The same enumeration is used in every self-copy. -/
theorem arbitrarily_many_copy_colours
    (E : System M) (hbranch : ∀ {x a : M}, x < a → ∃ z, x < z ∧ z ⊓ a = x)
    (hhom : language.IsUltrahomogeneous M)
    {A : Type*} [Fintype A] [SemilatticeInf A] [language.Structure A] [MeetsInterpreted A]
    (hA : Nonempty (A ↪[language] M)) {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x) (d : ℕ) :
    ∃ r : ℕ, ∃ _hr : 0 < r, ∃ χ : (A ↪[language] M) → Fin r,
      (∀ e g : A ↪[language] M, Set.range e = Set.range g → χ e = χ g) ∧
      ∀ f : M ↪[language] M, ∀ palette : Finset (Fin r),
        (∀ e : A ↪[language] M, χ (f.comp e) ∈ palette) → d < palette.card := by
  classical
  let K := Fintype.card A ^ 2
  let m := d * K + 1
  have hm : 0 < m := by dsimp [m]; omega
  let r := Fintype.card (Incomparables.BoundedPalette m K)
  have hr : 0 < r := Fintype.card_pos_iff.mpr ⟨⟨∅, by simp⟩⟩
  let encode := Fintype.equivFin (Incomparables.BoundedPalette m K)
  let χ : (A ↪[language] M) → Fin r := fun e =>
    encode ⟨pairPalette E m hm e, pairPalette_card_le E m hm e⟩
  let decode : Fin r → Finset (Fin m) := fun c => (encode.symm c).val
  have hdecode (c : Fin r) : (decode c).card ≤ K := (encode.symm c).property
  have hχ (e : A ↪[language] M) : decode (χ e) = pairPalette E m hm e := by
    simp only [decode, χ, Equiv.symm_apply_apply]
  refine ⟨r, hr, χ, ?_, ?_⟩
  · intro e g hrange
    apply encode.injective.eq_iff.mpr
    apply Subtype.ext
    exact pairPalette_eq_of_range_eq E m hm e g hrange
  · intro f palette hcover
    have hfull : (Finset.univ : Finset (Fin m)) ⊆ palette.biUnion decode := by
      intro i _
      obtain ⟨e, hi⟩ := every_colour_in_pattern E hbranch hhom hA hxy hyx m hm f i
      apply Finset.mem_biUnion.mpr
      exact ⟨χ (f.comp e), hcover e, by simpa only [hχ] using hi⟩
    have hbound : m ≤ palette.card * K := calc
      m = (Finset.univ : Finset (Fin m)).card := by simp
      _ ≤ (palette.biUnion decode).card := Finset.card_le_card hfull
      _ ≤ ∑ c ∈ palette, (decode c).card := Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ palette, K := Finset.sum_le_sum (fun c _ => hdecode c)
      _ = palette.card * K := by simp
    by_contra hnot
    have hle : palette.card ≤ d := Nat.le_of_not_gt hnot
    have hmul := Nat.mul_le_mul_right K hle
    dsimp [m] at hbound
    omega

theorem no_finite_bound
    (E : System M) (hbranch : ∀ {x a : M}, x < a → ∃ z, x < z ∧ z ⊓ a = x)
    (hhom : language.IsUltrahomogeneous M)
    {A : Type*} [Finite A] [SemilatticeInf A] [language.Structure A] [MeetsInterpreted A]
    (hA : Nonempty (A ↪[language] M)) {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x) (d : ℕ) :
    ¬FunctionalBigRamseyBound A M d := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  intro hbound
  obtain ⟨r, hr, χ, _, hχ⟩ := arbitrarily_many_copy_colours E hbranch hhom hA hxy hyx d
  obtain ⟨f, palette, hcard, hcover⟩ := hbound r hr χ
  have hlarge := hχ f palette hcover
  omega

end Bounds

/-- A countable nonempty meet-tree has the fixed enumeration used in the
profile proof; no preferred order on its enumeration is required. -/
noncomputable def systemOfCountable [Countable M] [Nonempty M]
    (hpredecessors : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x) : System M where
  enumerate := (exists_surjective_nat M).choose
  onto := (exists_surjective_nat M).choose_spec
  predecessors := hpredecessors

/-- The general infinite-degree theorem, stated without an auxiliary profile
system or an assumed oscillation/end-extension property. Its hypotheses
are the ordinary structural properties of a countable dense homogeneous
meet-tree, allowing any branching degree at least two. -/
theorem no_finite_bound_of_countable [Countable M] [Nonempty M]
    [DenselyOrdered M] [NoMaxOrder M] [language.Structure M] [MeetsInterpreted M]
    (hpredecessors : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbranch : ∀ {x a : M}, x < a → ∃ z, x < z ∧ z ⊓ a = x)
    (hhom : language.IsUltrahomogeneous M)
    {A : Type*} [Finite A] [SemilatticeInf A] [language.Structure A] [MeetsInterpreted A]
    (hA : Nonempty (A ↪[language] M)) {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x) (d : ℕ) :
    ¬FunctionalBigRamseyBound A M d :=
  no_finite_bound (systemOfCountable hpredecessors) hbranch hhom hA hxy hyx d

end AllThoseBigRamsey.Pseudotree.GenericIncomparables
