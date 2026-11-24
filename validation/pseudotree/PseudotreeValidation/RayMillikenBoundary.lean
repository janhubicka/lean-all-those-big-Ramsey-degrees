import PseudotreeValidation.RayMillikenBase

/-! The actual mixed theorem homogenizes arbitrary finite boundary products
with at most one incoming `1` edge. Unused factors are filled with zero words;
they carry no hypothesis about the colouring. -/

namespace AllThoseBigRamsey.Pseudotree.RayMilliken

open RayEmbeddings

variable {ι : Type} [Fintype ι]

noncomputable def boundarySlot (roots : ι → Word) (i : ι) : Fin (Fintype.card ι + 1) := by
  classical
  exact if LastOne (roots i) then Fin.last _ else (Fintype.equivFin ι i).castSucc

theorem boundarySlot_eq_last (roots : ι → Word) (i : ι) :
    boundarySlot roots i = Fin.last _ ↔ LastOne (roots i) := by
  classical
  simp only [boundarySlot]
  split_ifs with h
  · simp [h]
  · simp [h, Fin.castSucc_ne_last]

theorem boundarySlot_injective (roots : ι → Word)
    (hOne : ∀ i k, LastOne (roots i) → LastOne (roots k) → i = k) :
    Function.Injective (boundarySlot roots) := by
  classical
  intro i k h
  by_cases hi : LastOne (roots i)
  · have hk : LastOne (roots k) := (boundarySlot_eq_last roots k).mp
      (h.symm.trans ((boundarySlot_eq_last roots i).mpr hi))
    exact hOne i k hi hk
  · have hk : ¬ LastOne (roots k) := by
      intro hk
      exact hi ((boundarySlot_eq_last roots i).mp
        (h.trans ((boundarySlot_eq_last roots k).mpr hk)))
    have h' : (Fintype.equivFin ι i).castSucc = (Fintype.equivFin ι k).castSucc := by
      simpa only [boundarySlot, hi, hk, ↓reduceIte] using h
    exact (Fintype.equivFin ι).injective (Fin.castSucc_injective _ h')

/-- A prescribed finite family of immediate cones, with at most one
ternary factor, has a monochromatic product after a ray map fixing the
entire old ambient level. Colourings are arbitrary functions on the actual
selected target words; no stabilization assumption is an input. -/
theorem boundary_product {j colours : ℕ} (roots : ι → Word)
    (hLength : ∀ i, (roots i).length = j + 1)
    (hInjective : Function.Injective roots)
    (hOne : ∀ i k, LastOne (roots i) → LastOne (roots k) → i = k)
    (colour : (ι → Word) → Fin (colours + 1)) :
    ∃ c : Fin (colours + 1), ∃ g : RayStrongMap,
      FixesThrough j g ∧ ∀ n (x : ι → Word),
        (∀ i, (x i).length = n) →
        (∀ i, ¬ LastOne (roots i) → Binary (x i)) →
        colour (fun i => g.map (roots i ++ x i)) = c := by
  classical
  let slot := boundarySlot roots
  have hSlot := boundarySlot_injective roots hOne
  let lift : Mixed.Tuple (Fintype.card ι) → Fin (colours + 1) :=
    fun x => colour (fun i => roots i ++ x (slot i))
  obtain ⟨c, F, hF⟩ := Mixed.mixed_product lift
  let prescribed (u : Word) : Prop := ∃ i, roots i = u
  let H (u x : Word) : Word :=
    if h : prescribed u then u ++ (F.maps (slot h.choose)).map x else []
  have hH (i : ι) (x : Word) : H (roots i) x = roots i ++ (F.maps (slot i)).map x := by
    have hi : prescribed (roots i) := ⟨i, rfl⟩
    simp only [H, hi, ↓reduceDIte]
    have heq : hi.choose = i := hInjective hi.choose_spec
    rw [heq]
  let L (n : ℕ) := j + 1 + F.level n
  obtain ⟨g, hgBelow, hgOn, _⟩ := graft_binary_ternary RayStrongMap.identity (j + 1) L
    (by intro a b hab; dsimp [L]; exact Nat.add_lt_add_left (F.level_strict hab) _)
    (by simp [L, RayStrongMap.identity]) prescribed LastOne H
    (by intro u hu hp hlast; exact Or.inr hlast)
    (by
      intro u hu hp x hx
      obtain ⟨i, rfl⟩ := hp
      rw [hH, List.length_append, hLength i, F.length_map])
    (by
      intro u hu hp x a hx
      obtain ⟨i, rfl⟩ := hp
      obtain ⟨p, hp, hb⟩ := (F.maps (slot i)).step x a
      refine ⟨p, ?_, hb⟩
      rw [hH, hH, hp]
      simp only [List.append_assoc])
    (by
      intro u hu hp
      obtain ⟨i, rfl⟩ := hp
      refine ⟨(F.maps (slot i)).map [], ?_, ?_⟩
      · rw [hH]; rfl
      · intro hn
        apply F.binary_roots
        exact fun heq => hn ((boundarySlot_eq_last roots i).mp heq))
  refine ⟨c, g, ?_, ?_⟩
  · intro s hs
    have h := hgBelow s (by omega)
    exact h
  · intro n x hxLength hxBinary
    let X (k : Fin (Fintype.card ι + 1)) : Word :=
      if h : ∃ i, slot i = k then x h.choose else List.replicate n 0
    have hX (i : ι) : X (slot i) = x i := by
      have hi : ∃ k, slot k = slot i := ⟨i, rfl⟩
      simp only [X, hi, ↓reduceDIte]
      have heq : hi.choose = i := hSlot hi.choose_spec
      rw [heq]
    have hAdmissible : Mixed.AdmissibleAt (Fintype.card ι) n X := by
      constructor
      · intro k
        dsimp [X]
        split_ifs with h
        · exact hxLength h.choose
        · simp
      · intro k hk
        dsimp [X]
        split_ifs with h
        · apply hxBinary h.choose
          intro hlast
          apply hk
          rw [← h.choose_spec]
          exact (boundarySlot_eq_last roots h.choose).mpr hlast
        · simp [Binary]
    have hMono := hF n X hAdmissible
    change colour (fun i => roots i ++ (F.maps (slot i)).map (X (slot i))) = c at hMono
    suffices heq : (fun i => g.map (roots i ++ x i)) =
        (fun i => roots i ++ (F.maps (slot i)).map (X (slot i))) by
      rw [heq]
      exact hMono
    funext i
    rw [hX]
    have hdomain : LastOne (roots i) ∨ Binary (x i) := by
      by_cases h : LastOne (roots i)
      · exact Or.inl h
      · exact Or.inr (hxBinary i h)
    exact (hgOn (roots i) (hLength i) ⟨i, rfl⟩ (x i) hdomain).trans (hH i (x i))

end AllThoseBigRamsey.Pseudotree.RayMilliken
