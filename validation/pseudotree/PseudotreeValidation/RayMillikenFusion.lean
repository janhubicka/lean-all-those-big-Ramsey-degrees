import PseudotreeValidation.RayMillikenBase

/-! Finite batching and fusion for the restricted ray-preserving theorem.

The local fibre input is an explicit hypothesis here. The geometric theorem
must discharge it using the mixed product and boundary grafting. This module
proves the countable fusion deduction, with actual finite embeddings as its
colouring domain.
-/

namespace AllThoseBigRamsey.Pseudotree.RayMilliken

open RayEmbeddings

variable {F G : Shape} {κ : Type}

@[simp] theorem induced_comp (colour : Embedding F → κ) (f g : RayStrongMap) :
    induced (induced colour f) g = induced colour (f.comp g) := by
  funext e
  simp only [induced, Embedding.comp_comp]

@[simp] theorem induced_identity (colour : Embedding F → κ) :
    induced colour RayStrongMap.identity = colour := by
  funext e
  simp only [induced, Embedding.comp_identity]

theorem finite_fibre_batch (hGF : G.nodes ⊆ F.nodes) (j : ℕ)
    (localStep : ∀ (colour : Embedding F → κ) (e' : Embedding G), e'.topLevel = j →
      ∃ h : RayStrongMap, FixesThrough j h ∧ FibreConstant hGF (induced colour h) e')
    (es : List (Embedding G)) (hes : ∀ e' ∈ es, e'.topLevel = j)
    (colour : Embedding F → κ) :
    ∃ h : RayStrongMap, FixesThrough j h ∧
      ∀ e' ∈ es, FibreConstant hGF (induced colour h) e' := by
  induction es generalizing colour with
  | nil => exact ⟨RayStrongMap.identity, fun _ _ => rfl, by simp⟩
  | cons e es ih =>
    have he : e.topLevel = j := hes e (by simp)
    obtain ⟨g, hg, hc⟩ := localStep colour e he
    obtain ⟨h, hh, hs⟩ := ih (fun e' he' => hes e' (by simp [he'])) (induced colour g)
    refine ⟨g.comp h, fixes_comp hg hh, ?_⟩
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · simpa only [induced_comp] using
        fibreConstant_comp hGF (induced colour g) e' j hc h hh (Nat.le_of_eq he)
    · simpa only [induced_comp] using hs e' he'

/-- There are only finitely many lower embeddings at a fixed top image level,
so all their extension fibres can be homogenized in one finite batch. -/
theorem all_fibres_at_level (hGF : G.nodes ⊆ F.nodes) (j : ℕ)
    (localStep : ∀ (colour : Embedding F → κ) (e' : Embedding G), e'.topLevel = j →
      ∃ h : RayStrongMap, FixesThrough j h ∧ FibreConstant hGF (induced colour h) e')
    (colour : Embedding F → κ) :
    ∃ h : RayStrongMap, FixesThrough j h ∧
      ∀ e' : Embedding G, e'.topLevel = j → FibreConstant hGF (induced colour h) e' := by
  classical
  let : Fintype {e : Embedding G // e.topLevel = j} := Fintype.ofFinite _
  let es : List (Embedding G) :=
    (Finset.univ.toList : List {e : Embedding G // e.topLevel = j}).map Subtype.val
  have hes : ∀ e' ∈ es, e'.topLevel = j := by
    intro e' he'
    obtain ⟨e, _he, rfl⟩ := List.mem_map.mp he'
    exact e.property
  obtain ⟨h, hh, hbatch⟩ := finite_fibre_batch hGF j localStep es hes colour
  refine ⟨h, hh, ?_⟩
  intro e' he'
  apply hbatch e'
  exact List.mem_map.mpr ⟨⟨e', he'⟩, by simp, rfl⟩

/-- The actual ray-map fusion turns the local fibre theorem into a colouring
which depends only on restriction to the lower shape. -/
theorem all_fibres_fusion (hGF : G.nodes ⊆ F.nodes)
    (localStep : ∀ (colour : Embedding F → κ) (e' : Embedding G) (j : ℕ),
      e'.topLevel = j →
      ∃ h : RayStrongMap, FixesThrough j h ∧ FibreConstant hGF (induced colour h) e')
    (colour : Embedding F → κ) :
    ∃ h : RayStrongMap, ∀ e' : Embedding G, FibreConstant hGF (induced colour h) e' := by
  classical
  have batches := fun j c => all_fibres_at_level hGF j
    (fun c e' he' => localStep c e' j he') c
  let step (j : ℕ) (f : RayStrongMap) : RayStrongMap :=
    (batches j (induced colour f)).choose
  have stepfix (j : ℕ) (f : RayStrongMap) : FixesThrough j (step j f) :=
    (batches j (induced colour f)).choose_spec.1
  have stepcolour (j : ℕ) (f : RayStrongMap) (e' : Embedding G) (he' : e'.topLevel = j) :
      FibreConstant hGF (induced colour (f.comp (step j f))) e' := by
    simpa only [step, induced_comp] using (batches j (induced colour f)).choose_spec.2 e' he'
  let totals : ℕ → RayStrongMap :=
    Nat.rec RayStrongMap.identity (fun j f => f.comp (step j f))
  let increments : ℕ → RayStrongMap :=
    fun n => match n with
    | 0 => RayStrongMap.identity
    | j + 1 => step j (totals j)
  have htotals (j : ℕ) : RayStrongMap.compositions increments j = totals j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change (RayStrongMap.compositions increments j).comp (step j (totals j)) =
        (totals j).comp (step j (totals j))
      rw [ih]
  have hfix : ∀ j (s : Word), s.length ≤ j → (increments (j + 1)).map s = s :=
    fun j s hs => stepfix j (totals j) s hs
  let limit := RayStrongMap.fusion increments hfix
  refine ⟨limit, ?_⟩
  intro e'
  let j := e'.topLevel
  have hstage : FibreConstant hGF (induced colour (totals (j + 1))) e' :=
    stepcolour j (totals j) e' rfl
  obtain ⟨tail, htail, hfactor⟩ := RayStrongMap.fusion_factors increments hfix (j + 1)
  have htailfix : FixesThrough j tail := fun s hs => htail s (by omega)
  have hpres := fibreConstant_comp hGF (induced colour (totals (j + 1))) e' j
    hstage tail htailfix (Nat.le_refl _)
  have hemb (e : Embedding F) :
      Embedding.comp limit e = Embedding.comp (totals (j + 1)) (Embedding.comp tail e) := by
    apply Embedding.ext
    funext s
    change limit.map (e s) = (totals (j + 1)).map (tail.map (e s))
    exact (hfactor (e s)).trans (congrArg (fun f : RayStrongMap => f.map (tail.map (e s)))
      (htotals (j + 1)))
  intro e₁ e₂ h₁ h₂
  change colour (Embedding.comp limit e₁) = colour (Embedding.comp limit e₂)
  rw [hemb, hemb]
  exact hpres e₁ e₂ h₁ h₂

end AllThoseBigRamsey.Pseudotree.RayMilliken
