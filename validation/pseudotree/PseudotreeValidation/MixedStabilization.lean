import PseudotreeValidation.MixedBase
import PseudotreeValidation.MixedFusion
import PseudotreeValidation.WordStrongMaps
import Mathlib.Data.Fintype.Vector

/-!
# Actual binary-ray stabilization by Halpern–Läuchli and fusion

At each source level, apply ordinary binary product HL to all boundary rays
at once, using a finite vector colour indexed by boundary choices.  The
checked boundary grafting theorem extends those infinitely prescribed rays.
Earlier stable levels survive each subsequent refinement, so a coherent
limit is stable at every level. Stability is a conclusion of this module.
-/

namespace AllThoseBigRamsey.Pseudotree.Mixed

open RayEmbeddings WordTrees

def encodeBinary (s : List BinaryLetter) : Word := s.map Subtype.val

theorem encodeBinary_injective : Function.Injective encodeBinary := by
  exact List.map_injective_iff.mpr Subtype.val_injective

theorem encodeBinary_binary (s : List BinaryLetter) : Binary (encodeBinary s) := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact b.property

noncomputable def decodeBinary : Word → List BinaryLetter := Function.invFun encodeBinary

@[simp] theorem decodeBinary_encode (s : List BinaryLetter) :
    decodeBinary (encodeBinary s) = s :=
  Function.leftInverse_invFun encodeBinary_injective s

theorem encodeBinary_decode {s : Word} (hs : Binary s) :
    encodeBinary (decodeBinary s) = s := by
  obtain ⟨t, ht⟩ := (binary_tail_range s).mpr hs
  change encodeBinary t = s at ht
  rw [← ht, decodeBinary_encode]

theorem decodeBinary_length {s : Word} (hs : Binary s) :
    (decodeBinary s).length = s.length := by
  have h := congrArg List.length (encodeBinary_decode hs)
  simpa only [encodeBinary, List.length_map] using h

@[simp] theorem decodeBinary_nil : decodeBinary [] = [] := by
  exact decodeBinary_encode []

theorem decodeBinary_snoc {s : Word} {a : Fin 3} (hs : Binary s) (ha : a ≠ 1) :
    decodeBinary (s ++ [a]) = decodeBinary s ++ [⟨a, ha⟩] := by
  apply encodeBinary_injective
  rw [encodeBinary_decode ((binary_append s [a]).mpr ⟨hs, by simp [Binary, ha]⟩)]
  simp only [encodeBinary, List.map_append, List.map_cons, List.map_nil]
  rw [show (decodeBinary s).map Subtype.val = s from encodeBinary_decode hs]

theorem binary_drop {s : Word} (hs : Binary s) (j : ℕ) : Binary (s.drop j) :=
  fun _ ha => hs _ (List.mem_of_mem_drop ha)

private theorem boundary_map_step (u : Word) (f : StrongWordMap BinaryLetter)
    (x : Word) (a : Fin 3) (hxa : Binary (x ++ [a])) :
    ∃ p : Word,
      u ++ encodeBinary (f.map (decodeBinary (x ++ [a]))) =
        (u ++ encodeBinary (f.map (decodeBinary x))) ++ a :: p ∧
      (a ≠ 1 → Binary p) := by
  have hx := ((binary_append x [a]).mp hxa).1
  have ha : a ≠ 1 := hxa a (by simp)
  obtain ⟨p, hp⟩ := f.step (decodeBinary x) ⟨a, ha⟩
  refine ⟨encodeBinary p, ?_, fun _ => encodeBinary_binary p⟩
  rw [decodeBinary_snoc hx ha, ← hp]
  simp [encodeBinary, List.append_assoc]

/-- One honest fusion step: a finite vector colouring on all boundary rays
is homogenized by binary HL and then grafted into actual ray-preserving maps. -/
theorem exists_stabilizing_step {m colors : ℕ} [NeZero colors]
    (colour : Tuple m → Fin colors) (j : ℕ) :
    ∃ G : Embedding m,
      (∀ i s, s.length < j → (G.maps i).map s = s) ∧
      StableAt (induced colour G) j := by
  classical
  let V := List.Vector (Fin 3) j
  let I := Fin (m + 1) × V
  let C := (Fin (m + 1) → V) → Fin colors
  let encode : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let _ : NeZero (Fintype.card C) := ⟨by
    have hpos : 0 < Fintype.card C := Fintype.card_pos
    omega⟩
  let vectorColour : (I → List BinaryLetter) → Fin (Fintype.card C) := fun x =>
    encode (fun v => colour (fun i => (v i).val ++ encodeBinary (x (i, v i))))
  obtain ⟨c, M, f, hM, hLevels, hMono⟩ :=
    wordStrongMapsHL BinaryLetter I (Fintype.card C) vectorColour
  let H (i : Fin (m + 1)) (u x : Word) : Word :=
    if hu : u.length = j then
      u ++ encodeBinary ((f (i, ⟨u, hu⟩)).map (decodeBinary x)) else []
  have hG (i : Fin (m + 1)) : ∃ g : RayStrongMap,
      (∀ s, s.length < j → g.map s = s) ∧
      (∀ u, u.length = j → ∀ x, Binary x → g.map (u ++ x) = H i u x) ∧
      g.level = spliceLevels RayStrongMap.identity j (fun n => j + M n) := by
    obtain ⟨g, hg, hpres, hlevel⟩ := graft_binary_ternary RayStrongMap.identity j
      (fun n => j + M n) (fun {_ _} h => Nat.add_lt_add_left (hM h) j) (by simp [RayStrongMap.identity])
      (fun _ => True) (fun _ => False) (H i) (by simp)
      (by
        intro u hu _ x hx
        have hx' : Binary x := hx.resolve_left id
        simp only [H, hu, ↓reduceDIte, List.length_append, encodeBinary, List.length_map,
          (f (i, ⟨u, hu⟩)).length_map, hLevels, decodeBinary_length hx'])
      (by
        intro u hu _ x a hx
        have hx' : Binary (x ++ [a]) := hx.resolve_left id
        simpa only [H, hu, ↓reduceDIte] using boundary_map_step u (f (i, ⟨u, hu⟩)) x a hx')
      (by
        intro u hu _
        refine ⟨encodeBinary ((f (i, ⟨u, hu⟩)).map []), ?_, fun _ => encodeBinary_binary _⟩
        simp [H, hu, RayStrongMap.identity])
    exact ⟨g, hg, fun u hu x hx => hpres u hu trivial x (Or.inr hx), hlevel⟩
  choose g hfix hpres hlevel using hG
  let G : Embedding m := {
    maps := g
    level := spliceLevels RayStrongMap.identity j (fun n => j + M n)
    synchronized := hlevel
    binary_roots := by
      intro i _
      by_cases hj : j = 0
      · have h := hpres i [] (by simpa using hj.symm) [] binary_nil
        simp only [List.nil_append, H, List.length_nil, hj, ↓reduceDIte,
          decodeBinary_nil] at h
        rw [h]
        exact encodeBinary_binary _
      · rw [hfix i [] (by simp; omega)]
        exact binary_nil }
  refine ⟨G, hfix, ?_⟩
  intro n hjn x hx hlast
  have htail (i : Fin (m + 1)) : Binary ((x i).drop j) := by
    by_cases hi : i = Fin.last m
    · simpa only [hi] using hlast
    · exact binary_drop (hx.2 i hi) j
  let v : Fin (m + 1) → V := fun i =>
    ⟨(x i).take j, List.length_take_of_le (by rw [hx.1]; exact hjn)⟩
  let tail : Fin (m + 1) → List BinaryLetter := fun i => decodeBinary ((x i).drop j)
  have htaillen (i : Fin (m + 1)) : (tail i).length = n - j := by
    rw [decodeBinary_length (htail i), List.length_drop, hx.1]
  have h₁ := hMono (n - j) (fun p : I => tail p.1) (fun p => htaillen p.1)
  have h₀ := hMono 0 (fun _ : I => []) (by simp)
  have hvec :
      (fun w : Fin (m + 1) → V => colour (fun i => (w i).val ++
        encodeBinary ((f (i, w i)).map (tail i)))) =
      (fun w : Fin (m + 1) → V => colour (fun i => (w i).val ++
        encodeBinary ((f (i, w i)).map []))) :=
    encode.injective (h₁.trans h₀.symm)
  have heq := congrFun hvec v
  have hmap (i : Fin (m + 1)) : (G.maps i).map (x i) =
      (v i).val ++ encodeBinary ((f (i, v i)).map (tail i)) := by
    have h := hpres i (v i).val (v i).property ((x i).drop j) (htail i)
    simp only [H, (v i).property, ↓reduceDIte] at h
    simpa only [v, List.take_append_drop] using h
  have hmap₀ (i : Fin (m + 1)) : (G.maps i).map ((x i).take j) =
      (v i).val ++ encodeBinary ((f (i, v i)).map []) := by
    have h := hpres i (v i).val (v i).property [] binary_nil
    simpa only [List.append_nil, H, (v i).property, ↓reduceDIte, decodeBinary_nil] using h
  change colour (fun i => (G.maps i).map (x i)) =
    colour (fun i => (G.maps i).map ((x i).take j))
  simpa only [hmap, hmap₀] using heq

private theorem binary_tail_after_fixed_prefix (f : RayStrongMap) (j : ℕ)
    (hfix : ∀ s : Word, s.length ≤ j → f.map s = s)
    (x : Word) (hjx : j ≤ x.length) (hb : Binary (x.drop j)) :
    (f.map x).take j = x.take j ∧ Binary ((f.map x).drop j) := by
  have hlen : (x.take j).length = j := List.length_take_of_le hjx
  obtain ⟨p, hp, hpb⟩ := f.map_append (x.take j) (x.drop j)
  rw [List.take_append_drop, hfix _ hlen.le] at hp
  rw [hp, List.take_left' hlen, List.drop_left' hlen]
  exact ⟨rfl, hpb hb⟩

/-- A later synchronized ray refinement fixing a stable level preserves
that level's stability. The proof uses binary-tail preservation, not a
closure assumption on the colouring. -/
theorem StableAt.induced_of_fixes {m : ℕ} {κ : Type} {colour : Tuple m → κ}
    {j : ℕ} (hstable : StableAt colour j) (G : Embedding m)
    (hfix : ∀ i s, s.length ≤ j → (G.maps i).map s = s) :
    StableAt (induced colour G) j := by
  intro n hjn x hx hlast
  have hlevelj : G.level j = j := by
    have h := congrArg List.length (hfix (Fin.last m) (List.replicate j 0) (by simp))
    simpa only [G.length_map, List.length_replicate] using h
  have hbound : j ≤ G.level n := by
    have h := G.level_strict.monotone hjn
    rwa [hlevelj] at h
  have htail (i : Fin (m + 1)) : Binary ((x i).drop j) := by
    by_cases hi : i = Fin.last m
    · simpa only [hi] using hlast
    · exact binary_drop (hx.2 i hi) j
  have hprops (i : Fin (m + 1)) :
      ((G.maps i).map (x i)).take j = (x i).take j ∧
      Binary (((G.maps i).map (x i)).drop j) :=
    binary_tail_after_fixed_prefix (G.maps i) j (hfix i) (x i)
      (by rw [hx.1]; exact hjn) (htail i)
  have h := hstable (G.level n) hbound (G.applyTuple x) (G.admissible_image hx)
    (hprops (Fin.last m)).2
  have htup : (fun i => (G.applyTuple x i).take j) = (fun i => (x i).take j) :=
    funext (fun i => (hprops i).1)
  have hfixed : G.applyTuple (fun i => (x i).take j) = (fun i => (x i).take j) := by
    funext i
    exact hfix i _ (List.length_take_le _ _)
  change colour (G.applyTuple x) = colour (G.applyTuple (fun i => (x i).take j))
  rwa [htup, ← hfixed] at h

noncomputable def stabilizingStep {m colors : ℕ} [NeZero colors]
    (colour : Tuple m → Fin colors) (j : ℕ) : Embedding m :=
  (exists_stabilizing_step colour j).choose

theorem stabilizingStep_fixes {m colors : ℕ} [NeZero colors]
    (colour : Tuple m → Fin colors) (j : ℕ) :
    ∀ i s, s.length < j → ((stabilizingStep colour j).maps i).map s = s :=
  (exists_stabilizing_step colour j).choose_spec.1

theorem stabilizingStep_stable {m colors : ℕ} [NeZero colors]
    (colour : Tuple m → Fin colors) (j : ℕ) :
    StableAt (induced colour (stabilizingStep colour j)) j :=
  (exists_stabilizing_step colour j).choose_spec.2

/-- The actual successive colour-dependent refinements. -/
noncomputable def stabilizingStages {m colors : ℕ} [NeZero colors]
    (colour : Tuple m → Fin colors) : ℕ → Embedding m
  | 0 => stabilizingStep colour 0
  | n + 1 => (stabilizingStages colour n).comp
      (stabilizingStep (induced colour (stabilizingStages colour n)) (n + 1))

/-- Every previously treated level remains stable at all later stages. -/
theorem stabilizingStages_stable {m colors : ℕ} [NeZero colors]
    (colour : Tuple m → Fin colors) (n j : ℕ) (hjn : j ≤ n) :
    StableAt (induced colour (stabilizingStages colour n)) j := by
  induction n generalizing j with
  | zero =>
      have hj : j = 0 := by omega
      subst j
      exact stabilizingStep_stable colour 0
  | succ n ih =>
      change StableAt
        (induced (induced colour (stabilizingStages colour n))
          (stabilizingStep (induced colour (stabilizingStages colour n)) (n + 1))) j
      by_cases hj : j = n + 1
      · subst j
        exact stabilizingStep_stable _ _
      · have hjn' : j ≤ n := by omega
        apply (ih j hjn').induced_of_fixes
        intro i s hs
        exact stabilizingStep_fixes _ (n + 1) i s (by omega)

/-- The refinement sequence is genuinely coherent on its protected levels. -/
theorem stabilizingStages_coherent {m colors : ℕ} [NeZero colors]
    (colour : Tuple m → Fin colors) :
    ∀ a b, a ≤ b → ∀ i s, s.length ≤ a →
      ((stabilizingStages colour b).maps i).map s =
        ((stabilizingStages colour a).maps i).map s := by
  intro a b hab i s hs
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      change ((stabilizingStages colour b).maps i).map
        (((stabilizingStep (induced colour (stabilizingStages colour b)) (b + 1)).maps i).map s) = _
      rw [stabilizingStep_fixes _ (b + 1) i s (by omega)]
      exact ih

/-- The actual preliminary fusion in the manuscript: the induced colouring
is stable along all binary continuations of its ternary coordinate. No
stability, fusion, or Ramsey conclusion is assumed in this theorem. -/
theorem exists_rayStable_embedding {m colors : ℕ} [NeZero colors]
    (colour : Tuple m → Fin colors) :
    ∃ F : Embedding m, RayStable (induced colour F) := by
  let F := stabilizingStages colour
  have hF : Embedding.Coherent F := stabilizingStages_coherent colour
  exact ⟨Embedding.limit F hF,
    Embedding.rayStable_limit colour F hF (stabilizingStages_stable colour)⟩

end AllThoseBigRamsey.Pseudotree.Mixed
