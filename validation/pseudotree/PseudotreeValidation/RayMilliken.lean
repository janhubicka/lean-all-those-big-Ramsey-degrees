import PseudotreeValidation.RayMillikenFibre
import PseudotreeValidation.RayMillikenFusion

/-!
# Restricted ray-preserving finite-tree canonization

This is the manuscript's restricted Milliken lemma, for the actual finite
maps on a nonempty finite prefix tree, with at most one incoming `1` at each
source level. The proof uses the unconditional mixed product, the actual
boundary graft, finite batching, fusion, and induction on finite height.
-/

namespace AllThoseBigRamsey.Pseudotree.RayMilliken

open RayEmbeddings

private def prepend (w : Word) : RayStrongMap where
  map s := w ++ s
  level n := w.length + n
  level_strict := fun h => Nat.add_lt_add_left h _
  length_map := fun s => List.length_append
  step s a := ⟨[], by simp only [List.append_assoc], fun _ => binary_nil⟩

private theorem height_one_nodes (F : Shape) (hF : F.height = 1) (s : F.Node) : s.val = [] := by
  have h := F.length_lt_height s.val s.property
  apply List.length_eq_zero_iff.mp
  omega

/-- The one-node case is exactly the one-ternary-factor mixed theorem. -/
theorem canonize_height_one (F : Shape) (hF : F.height = 1) {colours : ℕ}
    (colour : Embedding F → Fin (colours + 1)) :
    ∃ c : Fin (colours + 1), ∃ g : RayStrongMap,
      ∀ e : Embedding F, colour (Embedding.comp g e) = c := by
  classical
  let root : F.Node := ⟨[], F.root_mem⟩
  let lift (x : Mixed.Tuple 0) := colour (Embedding.ofTotal F (prepend (x (Fin.last 0))))
  obtain ⟨c, g, hg⟩ := Mixed.mixed_product lift
  refine ⟨c, g.maps (Fin.last 0), ?_⟩
  intro e
  have hmono := hg (e root).length (fun _ => e root)
    ⟨fun _ => rfl, fun i hi => False.elim (hi (Fin.ext (by omega)))⟩
  change colour (Embedding.ofTotal F (prepend ((g.maps (Fin.last 0)).map (e root)))) = c at hmono
  suffices heq : Embedding.comp (g.maps (Fin.last 0)) e =
      Embedding.ofTotal F (prepend ((g.maps (Fin.last 0)).map (e root))) by
    rw [heq]
    exact hmono
  apply Embedding.ext
  funext s
  have hs : s = root := Subtype.ext (height_one_nodes F hF s)
  subst s
  simp only [Embedding.comp_apply, Embedding.ofTotal, prepend, root, List.append_nil]

/-- Every finite colouring of actual embeddings of the finite prefix tree
is monochromatic below a total ray-preserving strong map. No canonization,
stability, extension, density, or fibre-homogeneity premise is assumed. -/
theorem restricted_milliken (F : Shape) {colours : ℕ}
    (colour : Embedding F → Fin (colours + 1)) :
    ∃ c : Fin (colours + 1), ∃ g : RayStrongMap,
      ∀ e : Embedding F, colour (Embedding.comp g e) = c := by
  classical
  generalize hheight : F.height = N
  induction N using Nat.strong_induction_on generalizing F with
  | h N ih =>
    by_cases hone : F.height = 1
    · exact canonize_height_one F hone colour
    have hpos := F.height_pos
    let h := F.height - 1
    have hh : 0 < h := by dsimp [h]; omega
    have hF : F.height = h + 1 := by dsimp [h]; omega
    let G := F.truncate h hh
    let inclusion := F.truncate_subset h hh
    obtain ⟨g, hg⟩ := all_fibres_fusion inclusion
      (fun χ e' j he' => by
        obtain ⟨f, hf, hc⟩ := homogenize_fibre F h hh hF χ e'
        exact ⟨f, he' ▸ hf, hc⟩) colour
    let liftEmbedding (e' : Embedding G) : Embedding F := Embedding.ofTotal F e'.realizer
    have hsection (e' : Embedding G) : (liftEmbedding e').restrict G inclusion = e' := by
      apply Embedding.ext
      funext s
      exact e'.realizer_agrees s
    let lift (e' : Embedding G) := induced colour g (liftEmbedding e')
    have hlift (e : Embedding F) : induced colour g e = lift (e.restrict G inclusion) := by
      exact hg (e.restrict G inclusion) e (liftEmbedding (e.restrict G inclusion)) rfl (hsection _)
    have hG : G.height = h := F.truncate_height h hh (by omega)
    obtain ⟨c, f, hf⟩ := ih G.height (by rw [hG]; omega) G lift rfl
    refine ⟨c, g.comp f, ?_⟩
    intro e
    change induced colour (g.comp f) e = c
    rw [← induced_comp]
    change induced colour g (Embedding.comp f e) = c
    rw [hlift, Embedding.restrict_comp]
    exact hf (e.restrict G inclusion)

end AllThoseBigRamsey.Pseudotree.RayMilliken
