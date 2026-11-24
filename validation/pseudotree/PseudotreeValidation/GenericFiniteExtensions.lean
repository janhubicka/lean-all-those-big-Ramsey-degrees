import PseudotreeValidation.FraisseModel

/-!
# Dense branching meet-trees have the binary finite extension property

The concrete block-model proof only uses four geometric properties of its
target: density, no endpoints, linearly ordered predecessor sets, and an
inhabited opposite upper cone. This module states the same checked argument
with precisely those hypotheses, allowing its application to the *actual*
sparse coding set. No extension or homogeneity premise is assumed.
-/

namespace AllThoseBigRamsey.Pseudotree.DenseMeetTree

open FirstOrder
open scoped FirstOrder

variable {M : Type u} [SemilatticeInf M] [language.Structure M] [MeetsInterpreted M]
variable {N : Type v} [SemilatticeInf N] [NoMinOrder N] [NoMaxOrder N]
    [DenselyOrdered N] [Nonempty N]

/-- The unused-cone insertion profile only needs an opposite upper point. -/
theorem insertion_unused_cone
    (htarget : ∀ {x y z : N}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbranch : ∀ s r : N, s < r → ∃ v, s < v ∧ v ⊓ r = s)
    (A : Set N) (s r : N) (hr : s < r)
    (hA : ∀ a ∈ A, s < a → s < a ⊓ r) :
    ∃ v, s < v ∧ v ⊓ r = s ∧ v ∉ A ∧ ∀ a ∈ A, v ⊓ a = s ⊓ a := by
  obtain ⟨v, hv, hvr⟩ := hbranch s r hr
  refine ⟨v, hv, hvr, ?_, ?_⟩
  · intro hvA
    have hbad := hA v hvA hv
    rw [hvr] at hbad
    exact (lt_irrefl s) hbad
  intro a ha
  by_cases hsa : s < a
  · have hmeet := inf_eq_of_opposite_cone htarget hv.le hsa.le hvr (hA a ha hsa)
    simpa only [inf_eq_left.mpr hsa.le] using hmeet
  · exact inf_above_eq_of_not_lt htarget hv.le hsa

theorem extend_one_point [Finite M]
    (htarget : ∀ {x y z : N}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbranch : ∀ s r : N, s < r → ∃ v, s < v ∧ v ⊓ r = s)
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbinary : BinaryBranching M)
    (S : language.Substructure M) (b : M) (hb : b ∉ S)
    (hcover : ∀ x : M, x = b ∨ x ∈ S)
    (f : S ↪[language] N) :
    ∃ g : M ↪[language] N, ∀ a : S, g a = f a := by
  classical
  let A : Set (N) := Set.range f
  have hAfin : A.Finite := Set.finite_range f
  have hmeetOld (a : S) (hnot : ¬b ≤ (a : M)) : b ⊓ (a : M) ∈ S := by
    apply (hcover _).resolve_left
    exact fun h => hnot (inf_eq_left.mp h)
  have finish (v : N) (hv : v ∉ A)
      (hmixed : ∀ a : S, onePointFun S b hcover f v (b ⊓ a) = v ⊓ f a) :
      ∃ g : M ↪[language] N, ∀ a : S, g a = f a := by
    have hfresh : ∀ a : S, v ≠ f a := fun a h => hv ⟨a, h.symm⟩
    exact ⟨onePointEmbedding S b hb hcover f v hfresh hmixed,
      onePointEmbedding_old S b hb hcover f v hfresh hmixed⟩
  let L : Set M := {a | a ∈ S ∧ a ≤ b}
  by_cases hL : L.Nonempty
  · obtain ⟨l, hl⟩ := (Set.toFinite L).exists_maximal hL
    have hlS : l ∈ S := hl.1.1
    have hlb : l ≤ b := hl.1.2
    have hlb' : l < b := lt_of_le_of_ne hlb (fun h => hb (h ▸ hlS))
    have hmax (a : M) (ha : a ∈ S) (hab : a ≤ b) : a ≤ l := by
      rcases htree hab hlb with h | h
      · exact h
      · exact hl.2 ⟨ha, hab⟩ h
    let ls : S := ⟨l, hlS⟩
    let U : Set M := {a | a ∈ S ∧ b ≤ a}
    by_cases hU : U.Nonempty
    · obtain ⟨m, hm⟩ := (Set.toFinite U).exists_minimal hU
      have hmS : m ∈ S := hm.1.1
      have hbm : b ≤ m := hm.1.2
      have hmin (a : M) (ha : a ∈ S) (hba : b ≤ a) : m ≤ a := by
        have hinf : m ⊓ a ∈ U := ⟨inf_mem S hmS ha, le_inf hbm hba⟩
        exact le_trans (hm.2 hinf inf_le_left) inf_le_right
      let ms : S := ⟨m, hmS⟩
      have hlm : f ls < f ms := by
        apply (embedding_lt_iff f ls ms).2
        change l < m
        exact lt_of_lt_of_le hlb' hbm
      have hma (a : S) (hnot : ¬b ≤ (a : M)) : m ⊓ (a : M) = b ⊓ a :=
        inf_above_eq_of_not_lt htree hbm (fun h => hnot h.le)
      have hprofile : ∀ y ∈ A, f ms ≤ y ∨ f ms ⊓ y ≤ f ls := by
        rintro y ⟨a, rfl⟩
        by_cases hba : b ≤ (a : M)
        · exact Or.inl ((embedding_le_iff f ms a).2 (hmin a a.property hba))
        · right
          rw [← embedding_map_inf f ms a]
          apply (embedding_le_iff f _ ls).2
          change ((ms ⊓ a : S) : M) ≤ l
          rw [coe_substructure_inf]
          exact (hma a hba).symm ▸ hmax _ (hmeetOld a hba) inf_le_left
      obtain ⟨v, hlv, hvm, hv, hvprofile⟩ := insertion_between A (f ls) (f ms) hlm hprofile
      apply finish v hv
      intro a
      by_cases hba : b ≤ (a : M)
      · rw [inf_eq_left.mpr hba, onePointFun_new]
        exact (inf_eq_left.mpr (le_trans hvm.le
          ((embedding_le_iff f ms a).2 (hmin a a.property hba)))).symm
      · have hca := hmeetOld a hba
        rw [onePointFun_old S b hb hcover f v ⟨b ⊓ a, hca⟩]
        rcases hvprofile (f a) ⟨a, rfl⟩ with ⟨hwrong, _⟩ | ⟨_, hvmeet⟩
        · exact False.elim (hba (le_trans hbm ((embedding_le_iff f ms a).1 hwrong)))
        · rw [hvmeet, ← embedding_map_inf f ms a]
          congr 1
          apply Subtype.ext
          exact (hma a hba).symm
    · have hnotupper (a : S) : ¬b ≤ (a : M) := fun h => hU ⟨a, a.property, h⟩
      have hmeets (a : S) : b ⊓ (a : M) = l ⊓ a := by
        apply le_antisymm
        · exact le_inf (hmax _ (hmeetOld a (hnotupper a)) inf_le_left) inf_le_right
        · exact inf_le_inf_right _ hlb
      have hex : ∃ v : N, v ∉ A ∧ ∀ a : S, v ⊓ f a = f ls ⊓ f a := by
        by_cases hR : ∃ r : S, l < (r : M)
        · obtain ⟨r, hlr⟩ := hR
          have hlrF : f ls < f r := (embedding_lt_iff f ls r).2 hlr
          have hused : ∀ y ∈ A, f ls < y → f ls < y ⊓ f r := by
            rintro y ⟨a, rfl⟩ hlaF
            have hla : l < (a : M) := (embedding_lt_iff f ls a).1 hlaF
            have hba : b ⊓ (a : M) = l := (hmeets a).trans (inf_eq_left.mpr hla.le)
            have hbr : b ⊓ (r : M) = l := (hmeets r).trans (inf_eq_left.mpr hlr.le)
            have har : l < (a : M) ⊓ r := by
              rcases hbinary l b a r hlb' hla hlr with h | h | h
              · exact False.elim ((lt_irrefl l) (hba ▸ h))
              · exact False.elim ((lt_irrefl l) (hbr ▸ h))
              · exact h
            rw [← embedding_map_inf f a r]
            apply (embedding_lt_iff f ls _).2
            change l < ((a ⊓ r : S) : M)
            simpa only [coe_substructure_inf] using har
          obtain ⟨v, _, _, hv, hvm⟩ := insertion_unused_cone htarget hbranch A (f ls) (f r) hlrF hused
          exact ⟨v, hv, fun a => hvm (f a) ⟨a, rfl⟩⟩
        · have hmaximal : ∀ y ∈ A, ¬f ls < y := by
            rintro y ⟨a, rfl⟩ h
            exact hR ⟨a, (embedding_lt_iff f ls a).1 h⟩
          obtain ⟨v, _, hv, hvm⟩ := insertion_above_maximal
            htarget A (f ls) hmaximal
          exact ⟨v, hv, fun a => hvm (f a) ⟨a, rfl⟩⟩
      obtain ⟨v, hv, hvm⟩ := hex
      apply finish v hv
      intro a
      have hca := hmeetOld a (hnotupper a)
      rw [onePointFun_old S b hb hcover f v ⟨b ⊓ a, hca⟩, hvm,
        ← embedding_map_inf f ls a]
      congr 1
      apply Subtype.ext
      exact hmeets a
  · have hbelow (a : S) : b ≤ (a : M) := by
      by_contra hnot
      exact hL ⟨b ⊓ a, hmeetOld a hnot, inf_le_left⟩
    obtain ⟨v, hv, hvm⟩ := insertion_below_finite hAfin
    apply finish v hv
    intro a
    rw [inf_eq_left.mpr (hbelow a), onePointFun_new]
    exact (hvm (f a) ⟨a, rfl⟩).2.symm


theorem extend_finite [Finite M]
    (htarget : ∀ {x y z : N}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbranch : ∀ s r : N, s < r → ∃ v, s < v ∧ v ⊓ r = s)
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbinary : BinaryBranching M)
    (S : language.Substructure M) (f : S ↪[language] N) :
    ∃ g : M ↪[language] N, ∀ a : S, g a = f a := by
  classical
  suffices H : ∀ n : ℕ, ∀ (S : language.Substructure M) (f : S ↪[language] N),
      ((S : Set M)ᶜ).ncard = n →
      ∃ g : M ↪[language] N, ∀ a : S, g a = f a from H _ S f rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S f hn
    by_cases hall : ∀ x : M, x ∈ S
    · have htop : S = ⊤ := by ext x; simp [hall x]
      subst S
      refine ⟨f.comp FirstOrder.Language.Substructure.topEquiv.symm.toEmbedding, ?_⟩
      intro a
      rfl
    · have hmissing : ((S : Set M)ᶜ).Nonempty := by
        push Not at hall
        exact hall
      obtain ⟨b, hbmin⟩ := (Set.toFinite ((S : Set M)ᶜ)).exists_minimal hmissing
      have hb : b ∉ S := hbmin.1
      have hinsert : ∀ x ∈ insert b (S : Set M), ∀ y ∈ insert b (S : Set M),
          x ⊓ y ∈ insert b (S : Set M) := by
        have hmix (a : M) (ha : a ∈ S) : b ⊓ a ∈ insert b (S : Set M) := by
          by_cases hc : b ⊓ a ∈ S
          · exact Set.mem_insert_of_mem _ hc
          · have hcb : b ⊓ a = b := le_antisymm inf_le_left (hbmin.2 hc inf_le_left)
            exact Set.mem_insert_iff.mpr (Or.inl hcb)
        rintro x (rfl | hx) y (rfl | hy)
        · exact Set.mem_insert_iff.mpr (Or.inl (inf_idem _))
        · exact hmix y hy
        · simpa only [inf_comm] using hmix x hx
        · exact Set.mem_insert_of_mem _ (inf_mem S hx hy)
      let B := substructureOfInfClosed (insert b (S : Set M)) hinsert
      have hSB : S ≤ B := fun _ hx => Set.mem_insert_of_mem _ hx
      let bs : B := ⟨b, Set.mem_insert _ _⟩
      have hbInside : bs ∉ inside S B := hb
      have hcover : ∀ x : B, x = bs ∨ x ∈ inside S B := by
        intro x
        rcases x.property with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr h
      let fInside := f.comp (insideEquiv S B hSB).toEmbedding
      obtain ⟨fB, hfB⟩ := extend_one_point htarget hbranch
        (predecessor_comparability_substructure htree B)
        (binaryBranching_substructure hbinary B) (inside S B) bs hbInside hcover fInside
      have hfB_old (a : S) : fB ⟨a, hSB a.property⟩ = f a := by
        exact hfB ⟨⟨a, hSB a.property⟩, a.property⟩
      have hstrict : (B : Set M)ᶜ ⊂ (S : Set M)ᶜ := by
        constructor
        · intro x hx hxS
          exact hx (hSB hxS)
        · intro hreverse
          exact hreverse hb (Set.mem_insert _ _)
      have hlt : ((B : Set M)ᶜ).ncard < n := by
        rw [← hn]
        exact Set.ncard_lt_ncard hstrict
      obtain ⟨g, hg⟩ := ih _ hlt B fB rfl
      exact ⟨g, fun a => (hg ⟨a, hSB a.property⟩).trans (hfB_old a)⟩

/-- The same theorem in the ambient-substructure form used by mathlib's
back-and-forth interface. -/
theorem extend_finite_substructure
    (htarget : ∀ {x y z : N}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbranch : ∀ s r : N, s < r → ∃ v, s < v ∧ v ⊓ r = s)
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbinary : BinaryBranching M)
    (S B : language.Substructure M) [Finite B] (hSB : S ≤ B)
    (f : S ↪[language] N) :
    ∃ g : B ↪[language] N, ∀ a : S, g ⟨a, hSB a.property⟩ = f a := by
  let fInside := f.comp (insideEquiv S B hSB).toEmbedding
  obtain ⟨g, hg⟩ := extend_finite htarget hbranch (predecessor_comparability_substructure htree B)
    (binaryBranching_substructure hbinary B) (inside S B) fInside
  exact ⟨g, fun a => hg ⟨⟨a, hSB a.property⟩, a.property⟩⟩

/-- Every finite binary meet-tree embeds in the concrete model. -/
theorem finite_universal [Finite M]
    (htarget : ∀ {x y z : N}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbranch : ∀ s r : N, s < r → ∃ v, s < v ∧ v ⊓ r = s)
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbinary : BinaryBranching M) : Nonempty (M ↪[language] N) := by
  let E : language.Substructure M := substructureOfInfClosed ∅ (by simp)
  let f : E ↪[language] N := embeddingOfInfMap
    (fun x => False.elim x.property) (fun x => False.elim x.property)
    (fun x => False.elim x.property)
  obtain ⟨g, _⟩ := extend_finite htarget hbranch htree hbinary E f
  exact ⟨g⟩


/-- Back-and-forth uses the proved finite extension property and finite meet
closures. -/
theorem isUltrahomogeneous [Countable N]
    (htarget : ∀ {x y z : N}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbranch : ∀ s r : N, s < r → ∃ v, s < v ∧ v ⊓ r = s)
    (hbinary : BinaryBranching N) : language.IsUltrahomogeneous N := by
  apply (FirstOrder.Language.isUltrahomogeneous_iff_IsExtensionPair
    FirstOrder.Language.Structure.cg_of_countable).2
  apply FirstOrder.Language.isExtensionPair_iff_exists_embedding_closure_singleton_sup.2
  intro S hS f m
  let B : language.Substructure N :=
    FirstOrder.Language.Substructure.closure language {m} ⊔ S
  have hBfg : B.FG := (FirstOrder.Language.Substructure.fg_closure_singleton m).sup hS
  obtain ⟨X, hX, hXB⟩ := FirstOrder.Language.Substructure.fg_def.mp hBfg
  have hBfinite := finite_meet_closure htarget hX
  rw [hXB] at hBfinite
  let _ : Finite B := hBfinite.to_subtype
  obtain ⟨g, hg⟩ := extend_finite_substructure htarget hbranch htarget hbinary
    S B le_sup_right f
  refine ⟨g, ?_⟩
  ext a
  exact (hg a).symm

/-- The age consists of all finite binary meet-trees, including the empty
structure, for every target with these explicit geometric properties. -/
theorem age_eq_finiteBinaryClass
    (htarget : ∀ {x y z : N}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbranch : ∀ s r : N, s < r → ∃ v, s < v ∧ v ⊓ r = s)
    (hbinary : BinaryBranching N) : language.age N = finiteBinaryClass := by
  ext S
  constructor
  · rintro ⟨hfg, ⟨f⟩⟩
    have hrange := hfg.range f.toHom
    obtain ⟨X, hX, hXrange⟩ := FirstOrder.Language.Substructure.fg_def.mp hrange
    have hrangeFinite := finite_meet_closure htarget hX
    rw [hXrange] at hrangeFinite
    letI : Finite f.toHom.range := hrangeFinite.to_subtype
    have hSfinite : Finite S := Finite.of_injective f.equivRange f.equivRange.injective
    letI := semilatticeOfEmbedding f
    letI := meetsInterpreted_of_embedding f
    refine ⟨hSfinite, inferInstance, inferInstance, ?_, ?_⟩
    · intro x y z hx hy
      have hx' : f x ≤ f z := (embedding_le_iff f x z).2 hx
      have hy' : f y ≤ f z := (embedding_le_iff f y z).2 hy
      rcases htarget hx' hy' with h | h
      · exact Or.inl ((embedding_le_iff f x y).1 h)
      · exact Or.inr ((embedding_le_iff f y x).1 h)
    · intro s x y z hx hy hz
      have h := hbinary (f s) (f x) (f y) (f z)
        ((embedding_lt_iff f s x).2 hx)
        ((embedding_lt_iff f s y).2 hy)
        ((embedding_lt_iff f s z).2 hz)
      simpa only [← embedding_map_inf, embedding_lt_iff] using h
  · rintro ⟨hfinite, i, hinterpreted, htree, hbinary⟩
    letI := hfinite
    letI := i
    letI := hinterpreted
    exact ⟨FirstOrder.Language.Structure.FG.of_finite,
      finite_universal htarget hbranch htree hbinary⟩

/-- The native Fraïssé-limit statement follows from the geometric hypotheses;
none of these hypotheses asserts an extension property or a desired limit. -/
theorem isFraisseLimit [Countable N]
    (htarget : ∀ {x y z : N}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbranch : ∀ s r : N, s < r → ∃ v, s < v ∧ v ⊓ r = s)
    (hbinary : BinaryBranching N) : language.IsFraisseLimit finiteBinaryClass N where
  ultrahomogeneous := isUltrahomogeneous htarget hbranch hbinary
  age := age_eq_finiteBinaryClass htarget hbranch hbinary

end AllThoseBigRamsey.Pseudotree.DenseMeetTree
