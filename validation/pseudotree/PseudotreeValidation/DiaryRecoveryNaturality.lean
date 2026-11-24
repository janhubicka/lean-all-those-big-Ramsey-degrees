import PseudotreeValidation.DiaryRecoveryTurns

/-! Projection and the literal normalized coding set are invariant under
ray-preserving maps. The proof transports the explicit sorted levels. -/

namespace AllThoseBigRamsey.Pseudotree.DiaryRecovery

open RayEmbeddings DiaryNormalization LevelProjection

theorem sort_image (L : Finset ℕ) (K : ℕ → ℕ) (hK : StrictMono K) :
    (L.image K).sort (· ≤ ·) = (L.sort (· ≤ ·)).map K := by
  let e : ℕ ↪ ℕ := ⟨K, hK.injective⟩
  have h := Finset.map_sort e L (· ≤ ·) (· ≤ ·) (fun _ _ _ _ => hK.le_iff_le.symm)
  rw [Finset.map_eq_image] at h
  exact h.symm

private theorem idxOf_map_injective (K : ℕ → ℕ) (hK : Function.Injective K)
    (xs : List ℕ) (j : ℕ) : (xs.map K).idxOf (K j) = xs.idxOf j := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x = j
    · subst x
      simp
    · have h' : K x ≠ K j := fun heq => h (hK heq)
      simp [h, h', ih]

theorem rank_image (L : Finset ℕ) (K : ℕ → ℕ) (hK : StrictMono K) (j : ℕ) :
    rank (L.image K) (K j) = rank L j := by
  rw [rank, sort_image L K hK]
  exact idxOf_map_injective K hK.injective _ j

theorem schedule_image (L : Finset ℕ) (K : ℕ → ℕ) (hK : StrictMono K)
    (i : ℕ) (hi : i < L.card) : schedule (L.image K) i = K (schedule L i) := by
  have hcard : (L.image K).card = L.card := Finset.card_image_of_injective _ hK.injective
  rw [schedule_at (by omega), schedule_at hi, Finset.orderEmbOfFin_apply,
    Finset.orderEmbOfFin_apply]
  simp only [sort_image L K hK, Fin.getElem_fin, List.getElem_map]

theorem project_image (f : RayStrongMap) (L : Finset ℕ) (hL : L.Nonempty)
    (w : Word) (hw : w.length ∈ L) (j : ℕ) (hj : j ≤ rank L w.length) :
    project (schedule (L.image f.level)) (f.map w) j = project (schedule L) w j := by
  have hf : StrictMono f.level := fun _ _ h => f.level_strict h
  apply List.ext_getElem
  · simp only [project_length]
  · intro i hi hi'
    have hij : i < j := by simpa only [project_length] using hi
    have hiRank : i < rank L w.length := lt_of_lt_of_le hij hj
    have hiCard : i < L.card := lt_trans hiRank (rank_lt hw)
    have hiLength : schedule L i < w.length := by
      have h := schedule_strict hL hiRank
      simpa only [schedule_rank hw] using h
    rw [project_get _ _ hij, project_get _ _ hij, schedule_image L f.level hf i hiCard,
      map_get f w _ hiLength]

/-- The actual explicitly normalized word set is unchanged by a total
ray-preserving strong map. This has no diary, chain, sparse-copy, or
extraction hypothesis. -/
theorem codes_image (f : RayStrongMap) (C : Finset Word) (v : Word) :
    codes (C.image f.map) (f.map v) = codes C v := by
  classical
  have hf : StrictMono f.level := fun _ _ h => f.level_strict h
  unfold codes
  rw [selected_image, Finset.image_image]
  apply Finset.image_congr
  intro w hw
  dsimp only [Function.comp_def]
  rw [f.length_map, rank_image _ _ hf]
  exact project_image f (selected C v) (selected_nonempty ⟨w, hw⟩ v) w
    (essential_subset_selected C v (length_mem_essential hw)) _ le_rfl

/-- The normalized prefix tree is invariant as well. -/
theorem nodes_image (f : RayStrongMap) (C : Finset Word) (v : Word) :
    nodes (C.image f.map) (f.map v) = nodes C v := by
  unfold nodes
  rw [codes_image]

end AllThoseBigRamsey.Pseudotree.DiaryRecovery
