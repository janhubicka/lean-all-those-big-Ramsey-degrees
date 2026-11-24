import PseudotreeValidation.WordStrongMaps

/-!
# Synchronized strong word maps for different alphabets

We transport refinements of the common-root wedge components back to their
original ambient trees, preserving every strong-subtree clause.  Applying
the proved product HL theorem and then the word labelling construction gives
the ordinary letter-preserving map statement for heterogeneous factors.
-/

namespace AllThoseBigRamsey.Pseudotree

open Milliken Milliken.GeneralTree

namespace WedgeStrongPullback

variable {d : ℕ} (T : Fin d → AmbientTree) (hd : 0 < d) (i : Fin d)

theorem embed_injective : Function.Injective (WedgeNode.embed T i) := by
  intro x y h
  exact le_antisymm
    ((WedgeNode.embed_le_embed_iff T i x y).mp h.le)
    ((WedgeNode.embed_le_embed_iff T i y x).mp h.symm.le)

include hd in
theorem embed_covBy {x y : T i} (hxy : x ⋖ y) :
    WedgeNode.embed T i x ⋖ WedgeNode.embed T i y := by
  constructor
  · exact lt_of_le_of_ne ((WedgeNode.embed_le_embed_iff T i x y).mpr hxy.le)
      (fun h => hxy.ne (embed_injective T i h))
  · intro z hxz hzy
    have h₁ := (WedgeNode.ambientTree T hd).level_lt hxz
    have h₂ := (WedgeNode.ambientTree T hd).level_lt hzy
    rw [WedgeNode.ambient_level_embed T hd i x] at h₁
    rw [WedgeNode.ambient_level_embed T hd i y] at h₂
    have hstep := (T i).level_covBy hxy
    omega

variable (S : StrongSubtree (WedgeNode.ambientTree T hd))
    (hS : S.Refines (WedgeNode.componentStrong T hd i))

include hS

theorem levels_pos (n : ℕ) : 0 < S.levels n := by
  obtain ⟨z, hz⟩ := S.sourceLevel_nonempty n
  obtain ⟨x, hx⟩ := WedgeNode.exists_embed_of_mem_componentStrong T hd i z (hS hz.1)
  have hl := hz.2
  rw [← hx, WedgeNode.ambient_level_embed T hd i x] at hl
  omega

theorem level_iff (n : ℕ) (x : T i) :
    (WedgeNode.ambientTree T hd).level (WedgeNode.embed T i x) = S.levels n ↔
      (T i).level x = S.levels n - 1 := by
  rw [WedgeNode.ambient_level_embed]
  have hpos := levels_pos T hd i S hS n
  omega

private noncomputable def root : T i :=
  (WedgeNode.exists_embed_of_mem_componentStrong T hd i S.root (hS S.root_mem)).choose

private theorem embed_root : WedgeNode.embed T i (root T hd i S hS) = S.root :=
  (WedgeNode.exists_embed_of_mem_componentStrong T hd i S.root (hS S.root_mem)).choose_spec

/-- Pull a strong refinement of one wedge component back to its original
tree. The added common root accounts for precisely one level of shift. -/
noncomputable def strong : StrongSubtree (T i) where
  carrier x := WedgeNode.embed T i x ∈ S.carrier
  levels n := S.levels n - 1
  levels_strictMono := by
    intro m n hmn
    change S.levels m - 1 < S.levels n - 1
    have h := S.levels_strictMono hmn
    have hm := levels_pos T hd i S hS m
    have hn := levels_pos T hd i S hS n
    omega
  root := root T hd i S hS
  root_mem := by
    change WedgeNode.embed T i (root T hd i S hS) ∈ S.carrier
    rw [embed_root]
    exact S.root_mem
  root_level := by
    apply (level_iff T hd i S hS 0 _).mp
    rw [embed_root]
    exact S.root_level
  root_below := by
    intro x hx
    apply (WedgeNode.embed_le_embed_iff T i _ x).mp
    rw [embed_root]
    exact S.root_below _ hx
  carrier_levels := by
    intro x hx
    obtain ⟨n, hn⟩ := S.carrier_levels _ hx
    exact ⟨n, (level_iff T hd i S hS n x).mp hn⟩
  predecessor_exists := by
    intro n z hz hzlevel
    obtain ⟨p, hp, hpl, hpz⟩ := S.predecessor_exists n (WedgeNode.embed T i z) hz
      ((level_iff T hd i S hS (n + 1) z).mpr hzlevel)
    obtain ⟨x, hx⟩ := WedgeNode.exists_embed_of_mem_componentStrong T hd i p (hS hp)
    rw [← hx] at hp hpl hpz
    exact ⟨x, hp, (level_iff T hd i S hS n x).mp hpl,
      (WedgeNode.embed_le_embed_iff T i x z).mp hpz⟩
  successor_unique := by
    intro n x hx hxlevel y hxy
    obtain ⟨z, hz, huniq⟩ := S.successor_unique n (WedgeNode.embed T i x) hx
      ((level_iff T hd i S hS n x).mpr hxlevel) (WedgeNode.embed T i y)
      (embed_covBy T hd i hxy)
    obtain ⟨w, hw⟩ := WedgeNode.exists_embed_of_mem_componentStrong T hd i z (hS hz.1)
    refine ⟨w, ?_, ?_⟩
    · rw [← hw] at hz
      exact ⟨hz.1, (level_iff T hd i S hS (n + 1) w).mp hz.2.1,
        (WedgeNode.embed_le_embed_iff T i y w).mp hz.2.2⟩
    · intro v hv
      apply embed_injective T i
      exact (huniq (WedgeNode.embed T i v)
        ⟨hv.1, (level_iff T hd i S hS (n + 1) v).mpr hv.2.1,
          (WedgeNode.embed_le_embed_iff T i y v).mpr hv.2.2⟩).trans hw.symm

theorem strong_sourceLevel_iff (n : ℕ) (x : T i) :
    x ∈ (strong T hd i S hS).sourceLevel n ↔
      WedgeNode.embed T i x ∈ S.sourceLevel n := by
  change (WedgeNode.embed T i x ∈ S.carrier ∧ (T i).level x = S.levels n - 1) ↔
    (WedgeNode.embed T i x ∈ S.carrier ∧
      (WedgeNode.ambientTree T hd).level (WedgeNode.embed T i x) = S.levels n)
  exact and_congr_right (fun _ => (level_iff T hd i S hS n x).symm)

end WedgeStrongPullback

/-- Ordinary strong-product HL for genuinely different ambient trees, with
all nodes transported back from the common-root wedge. -/
theorem heterogeneousStrongProductHL
    (d : ℕ) (hd : 0 < d) (T : Fin d → AmbientTree)
    (colors : ℕ) [NeZero colors] (colour : (∀ i, T i) → Fin colors) :
    ∃ c : Fin colors, ∃ L : ℕ → ℕ, ∃ F : (i : Fin d) → StrongSubtree (T i),
      StrictMono L ∧ (∀ i, (F i).levels = L) ∧
      ∀ k (x : ∀ i, T i), (∀ i, x i ∈ (F i).sourceLevel k) → colour x = c := by
  classical
  let U := WedgeNode.ambientTree T hd
  let P := WedgeNode.componentStrong T hd
  let decode (i : Fin d) : U → T i := Function.invFun (WedgeNode.embed T i)
  have hdecode (i : Fin d) (x : T i) : decode i (WedgeNode.embed T i x) = x :=
    Function.leftInverse_invFun (WedgeStrongPullback.embed_injective T i) x
  obtain ⟨c, M, F, hM, hF, hMono⟩ := generalProductHL_unconditional U d colors P
    (fun n => n + 1) (WedgeNode.componentStrong_levels T hd)
    (fun x => colour (fun i => decode i (x i)))
  have hpos (n : ℕ) : 0 < M n := by
    have h := WedgeStrongPullback.levels_pos T hd ⟨0, hd⟩ (F ⟨0, hd⟩) (hF ⟨0, hd⟩).1 n
    rwa [(hF ⟨0, hd⟩).2] at h
  refine ⟨c, (fun n => M n - 1),
    (fun i => WedgeStrongPullback.strong T hd i (F i) (hF i).1), ?_, ?_, ?_⟩
  · intro m n hmn
    change M m - 1 < M n - 1
    have h := hM hmn
    have hm := hpos m
    have hn := hpos n
    omega
  · intro i
    funext n
    change (F i).levels n - 1 = M n - 1
    rw [(hF i).2]
  · intro k x hx
    have hnodes : ∀ i, WedgeNode.embed T i (x i) ∈ (F i).sourceLevel k := by
      intro i
      exact (WedgeStrongPullback.strong_sourceLevel_iff T hd i (F i) (hF i).1 k (x i)).mp (hx i)
    have h := hMono k (fun i => WedgeNode.embed T i (x i)) hnodes
    simpa only [hdecode] using h

namespace WordTrees

/-- HL for any positive finite family of finite nonempty alphabets, stated
with synchronized letter-preserving maps on the actual words. -/
theorem heterogeneousWordStrongMapsHL
    (d : ℕ) (hd : 0 < d) (A : Fin d → Type)
    [∀ i, Finite (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (colors : ℕ) [NeZero colors] (colour : (∀ i, List (A i)) → Fin colors) :
    ∃ c : Fin colors, ∃ L : ℕ → ℕ, ∃ f : (i : Fin d) → StrongWordMap (A i),
      StrictMono L ∧ (∀ i, (f i).level = L) ∧
      ∀ k (x : ∀ i, List (A i)), (∀ i, (x i).length = k) →
        colour (fun i => (f i).map (x i)) = c := by
  obtain ⟨c, L, F, hL, hF, hMono⟩ := heterogeneousStrongProductHL d hd
    (fun i => ambientTree (A i)) colors (fun x => colour (fun i => (x i).letters))
  refine ⟨c, L, (fun i => toWordStrongMap (F i)), hL, hF, ?_⟩
  intro k x hx
  apply hMono k (fun i => ⟨subtreeWordMap (F i) (x i)⟩)
  intro i
  change (⟨subtreeWordMap (F i) (x i)⟩ : Node (A i)) ∈ (F i).sourceLevel k
  rw [← hx i]
  exact subtreeWordMap_onLevel (F i) (x i)

/-- Rooted heterogeneous version, with the common level map expressed in
the original absolute word lengths. -/
theorem rootedHeterogeneousWordStrongMapsHL
    (d : ℕ) (hd : 0 < d) (A : Fin d → Type)
    [∀ i, Finite (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (root : (i : Fin d) → List (A i)) (r : ℕ) (hroot : ∀ i, (root i).length = r)
    (colors : ℕ) [NeZero colors] (colour : (∀ i, List (A i)) → Fin colors) :
    ∃ c : Fin colors, ∃ L : ℕ → ℕ, ∃ f : (i : Fin d) → StrongWordMap (A i),
      StrictMono L ∧ (∀ i, (f i).level = L) ∧
      (∀ i s, root i <+: (f i).map s) ∧
      ∀ k (x : ∀ i, List (A i)), (∀ i, (x i).length = k) →
        colour (fun i => (f i).map (x i)) = c := by
  obtain ⟨c, L, f, hL, hLevels, hMono⟩ := heterogeneousWordStrongMapsHL d hd A colors
    (fun x => colour (fun i => root i ++ x i))
  refine ⟨c, (fun n => r + L n), (fun i => (f i).prepend (root i)),
    (fun _ _ h => Nat.add_lt_add_left (hL h) r), ?_, ?_, ?_⟩
  · intro i
    funext n
    change (root i).length + (f i).level n = r + L n
    rw [hroot, hLevels]
  · intro i s
    exact List.prefix_append _ _
  · exact hMono

/-- The manuscript's actual binary-ray/ternary-cone factors, with arbitrary
original ternary roots of a common length. These are ordinary strong maps:
the theorem does not assert preservation of all internal pseudotree rays in
a ternary factor. -/
theorem rayConeStrongMapsHL
    (d : ℕ) (hd : 0 < d) (binary : Fin d → Bool)
    (root : Fin d → List (Fin 3)) (r : ℕ) (hroot : ∀ i, (root i).length = r)
    (colors : ℕ) [NeZero colors] (colour : (Fin d → List (Fin 3)) → Fin colors) :
    ∃ c : Fin colors, ∃ L : ℕ → ℕ,
      ∃ f : (i : Fin d) → List (FactorLetter (binary i)) → List (Fin 3),
        StrictMono L ∧
        (∀ i, Function.Injective (f i)) ∧
        (∀ i s, f i s ∈ Set.range (place (binary i) (root i))) ∧
        (∀ i s, (f i s).length = L s.length) ∧
        (∀ i s a, f i s ++ [letterValue (binary i) a] <+: f i (s ++ [a])) ∧
        ∀ k (x : ∀ i, List (FactorLetter (binary i))),
          (∀ i, (x i).length = k) → colour (fun i => f i (x i)) = c := by
  obtain ⟨c, L, f, hL, hLevels, hMono⟩ := heterogeneousWordStrongMapsHL d hd
    (fun i => FactorLetter (binary i)) colors
    (fun x => colour (fun i => place (binary i) (root i) (x i)))
  refine ⟨c, (fun n => r + L n),
    (fun i s => place (binary i) (root i) ((f i).map s)),
    (fun _ _ h => Nat.add_lt_add_left (hL h) r), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (place_injective (binary i) (root i)).comp (f i).injective
  · intro i s
    exact Set.mem_range_self _
  · intro i s
    rw [place_length, hroot, (f i).length_map, hLevels]
  · intro i s a
    obtain ⟨p, hp⟩ := (f i).step s a
    refine ⟨p.map (letterValue (binary i)), ?_⟩
    have h := congrArg (fun t : List (FactorLetter (binary i)) =>
      root i ++ t.map (letterValue (binary i))) hp
    simpa only [place, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc] using h
  · exact hMono

end WordTrees
end AllThoseBigRamsey.Pseudotree
