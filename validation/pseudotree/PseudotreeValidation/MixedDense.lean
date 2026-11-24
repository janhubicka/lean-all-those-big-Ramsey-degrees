import PseudotreeValidation.MixedBase
import Mathlib.Data.List.OfFn

/-! Dense-matrix construction after binary-ray stabilization. -/

namespace AllThoseBigRamsey.Pseudotree.Mixed

open RayEmbeddings

def Allowed {m : ℕ} (i : Fin (m + 1)) (s : Word) : Prop :=
  i = Fin.last m ∨ Binary s

private theorem allowed_iff_factor {m : ℕ} (i : Fin (m + 1)) (s : Word) :
    Allowed i s ↔ s ∈ Set.range (WordTrees.place (decide (i ≠ Fin.last m)) []) := by
  generalize hdec : decide (i ≠ Fin.last m) = b
  cases b with
  | false =>
    have hi : i = Fin.last m := by simpa using of_decide_eq_false hdec
    simp only [Set.mem_range]
    rw [WordTrees.ternary_place_range]
    simp [Allowed, hi]
  | true =>
    have hi : i ≠ Fin.last m := of_decide_eq_true hdec
    simp only [Set.mem_range]
    rw [WordTrees.binary_place_range]
    simp [Allowed, hi, Binary]

/-- Precisely the fixed-base dense-matrix conclusion supplied by HL. -/
structure DenseInput {m : ℕ} {κ : Type} (colour : Tuple m → κ) (base : Tuple m) (c : κ) : Prop where
  base_allowed : ∀ i, Allowed i (base i)
  choose : ∀ D : Fin (m + 1) → Finset Word,
    (∀ i, ∀ x ∈ D i, Allowed i x ∧ base i <+: x) →
    ∀ N : ℕ, ∃ l : ℕ, N ≤ l ∧ ∃ X : Fin (m + 1) → Set Word,
      (∀ i, ∀ x ∈ X i, Allowed i x ∧ x.length = l) ∧
      (∀ i, ∀ x ∈ D i, ∃ y ∈ X i, x <+: y) ∧
      ∀ x : Tuple m, (∀ i, x i ∈ X i) → colour x = c

theorem exists_denseInput (m n : ℕ) (colour : Tuple m → Fin (n + 1)) :
    ∃ base : Tuple m, ∃ c : Fin (n + 1), DenseInput colour base c := by
  classical
  obtain ⟨base, hbase, c, hall⟩ := WordTrees.rayConeDenseMatrices
    (m + 1) (by omega) (fun i => decide (i ≠ Fin.last m)) (fun _ => [])
    0 (by simp) n colour
  refine ⟨base, c, ⟨?_, ?_⟩⟩
  · intro i
    exact (allowed_iff_factor i (base i)).mpr (hbase i)
  · intro D hD N
    have hD' : ∀ i, ∀ x ∈ D i,
        x ∈ Set.range (WordTrees.place (decide (i ≠ Fin.last m)) []) ∧ base i <+: x := by
      intro i x hx
      exact ⟨(allowed_iff_factor i x).mp (hD i x hx).1, (hD i x hx).2⟩
    obtain ⟨l, hNl, X, hX, hDom, hMono⟩ := hall D hD' N
    refine ⟨l, hNl, X, ?_, hDom, hMono⟩
    intro i x hx
    exact ⟨(allowed_iff_factor i x).mpr (hX i x hx).1, (hX i x hx).2⟩

def Good {m : ℕ} {κ : Type} (colour : Tuple m → κ) (base : Tuple m) (c : κ)
    (r : ℕ) (F : Embedding m) : Prop :=
  (∀ i, base i <+: (F.maps i).map []) ∧
  (∀ k, k ≤ r → ∀ x : Tuple m, AdmissibleAt m k x → induced colour F x = c)

private def prependMap (y : Word) : RayStrongMap where
  map s := y ++ s
  level n := y.length + n
  level_strict := fun h => Nat.add_lt_add_left h _
  length_map s := List.length_append
  step s a := ⟨[], by simp, fun _ => binary_nil⟩

theorem dense_initial {m : ℕ} {κ : Type} {colour : Tuple m → κ} {base : Tuple m} {c : κ}
    (hD : DenseInput colour base c) : ∃ F : Embedding m, Good colour base c 0 F := by
  classical
  obtain ⟨l, _, X, hX, hDom, hMono⟩ := hD.choose (fun i => {base i})
    (by intro i x hx; simp only [Finset.mem_singleton] at hx; subst x
        exact ⟨hD.base_allowed i, List.prefix_rfl⟩) 0
  have hall : ∀ i, ∃ y ∈ X i, base i <+: y := fun i => hDom i (base i) (by simp)
  choose y hy hbase using hall
  let F : Embedding m := {
    maps := fun i => prependMap (y i)
    level := fun n => l + n
    synchronized := by intro i; funext n; exact congrArg (· + n) (hX i (y i) (hy i)).2
    binary_roots := by
      intro i hi
      simpa only [prependMap, List.append_nil] using (hX i (y i) (hy i)).1.resolve_left hi }
  refine ⟨F, ?_, ?_⟩
  · intro i
    simpa only [F, prependMap, List.append_nil] using hbase i
  · intro k hk x hx
    have hk0 : k = 0 := by omega
    have hempty : ∀ i, x i = [] := fun i => List.length_eq_zero_iff.mp ((hx.1 i).trans hk0)
    have heq : F.applyTuple x = y := by
      funext i
      simp only [Embedding.applyTuple, F, prependMap, hempty, List.append_nil]
    change colour (F.applyTuple x) = c
    rw [heq]
    exact hMono y hy

private def levelWords (r : ℕ) : Finset Word :=
  Finset.univ.image (List.ofFn : (Fin r → Fin 3) → Word)

private theorem mem_levelWords (r : ℕ) (s : Word) : s ∈ levelWords r ↔ s.length = r := by
  classical
  constructor
  · intro hs
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hs
    exact List.length_ofFn
  · intro hs
    subst r
    exact Finset.mem_image.mpr ⟨s.get, Finset.mem_univ _, List.ofFn_get s⟩

def NeedsMatrix {m : ℕ} (i : Fin (m + 1)) (s : Word) (a : Fin 3) : Prop :=
  if i = Fin.last m then a = 1 else Binary (s ++ [a])

/-- The finite matrix selection used in one genuine construction step.
The other new ternary edges are filled with binary zeros. -/
structure NextLevel {m : ℕ} {κ : Type} (colour : Tuple m → κ) (c : κ)
    (F : Embedding m) (r : ℕ) where
  level : ℕ
  gt : F.level r < level
  matrix : Fin (m + 1) → Set Word
  next : Fin (m + 1) → Word → Fin 3 → Word
  length : ∀ i s a, s.length = r → (next i s a).length = level
  step : ∀ i s a, s.length = r → ∃ p : Word,
    next i s a = (F.maps i).map s ++ a :: p ∧ (a ≠ 1 → Binary p)
  selected : ∀ i s a, s.length = r → NeedsMatrix i s a → next i s a ∈ matrix i
  unselected : ∀ i s a, s.length = r → ¬ NeedsMatrix i s a →
    next i s a = (F.maps i).map s ++ a :: List.replicate (level - F.level r - 1) 0
  monochrome : ∀ x : Tuple m, (∀ i, x i ∈ matrix i) → colour x = c

private noncomputable def demands {m : ℕ} (F : Embedding m) (r : ℕ)
    (i : Fin (m + 1)) : Finset Word := by
  classical
  exact (((levelWords r).product (Finset.univ : Finset (Fin 3))).filter
    (fun p => NeedsMatrix i p.1 p.2)).image
      (fun p => (F.maps i).map p.1 ++ [p.2])

private theorem mem_demands {m : ℕ} (F : Embedding m) (r : ℕ)
    (i : Fin (m + 1)) (s : Word) (a : Fin 3)
    (hs : s.length = r) (ha : NeedsMatrix i s a) :
    (F.maps i).map s ++ [a] ∈ demands F r i := by
  classical
  exact Finset.mem_image.mpr ⟨(s, a), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨(mem_levelWords r s).mpr hs, Finset.mem_univ _⟩, ha⟩, rfl⟩

private theorem demands_allowed {m : ℕ} {κ : Type} {colour : Tuple m → κ}
    {base : Tuple m} {c : κ} {r : ℕ} {F : Embedding m}
    (hF : Good colour base c r F) (i : Fin (m + 1)) (x : Word)
    (hx : x ∈ demands F r i) : Allowed i x ∧ base i <+: x := by
  classical
  obtain ⟨⟨s, a⟩, hp, rfl⟩ := Finset.mem_image.mp hx
  have hneed : NeedsMatrix i s a := (Finset.mem_filter.mp hp).2
  constructor
  · by_cases hi : i = Fin.last m
    · exact Or.inl hi
    · have hbin : Binary (s ++ [a]) := by simpa [NeedsMatrix, hi] using hneed
      have hs := (binary_append s [a]).mp hbin
      exact Or.inr ((binary_append _ _).mpr ⟨F.map_binary i hi s hs.1, hs.2⟩)
  · obtain ⟨p, hp, _⟩ := (F.maps i).map_append [] s
    have hprefix : (F.maps i).map [] <+: (F.maps i).map s :=
      ⟨p, by simpa using hp.symm⟩
    exact (hF.1 i).trans (hprefix.trans (List.prefix_append _ _))

/-- The required next level is obtained from the proved dense-matrix HL
theorem, with no monochromatic ray-map existence hypothesis. -/
theorem exists_nextLevel {m : ℕ} {κ : Type} {colour : Tuple m → κ}
    {base : Tuple m} {c : κ} {r : ℕ} {F : Embedding m}
    (hD : DenseInput colour base c) (hF : Good colour base c r F) :
    Nonempty (NextLevel colour c F r) := by
  classical
  obtain ⟨l, hlevel, X, hX, hDom, hMono⟩ :=
    hD.choose (demands F r) (demands_allowed hF) (F.level r + 1)
  have hlt : F.level r < l := by omega
  have hex : ∀ i s a, s.length = r → NeedsMatrix i s a →
      ∃ y ∈ X i, (F.maps i).map s ++ [a] <+: y := by
    intro i s a hs ha
    exact hDom i _ (mem_demands F r i s a hs ha)
  let next (i : Fin (m + 1)) (s : Word) (a : Fin 3) : Word :=
    if h : s.length = r ∧ NeedsMatrix i s a then
      (hex i s a h.1 h.2).choose
    else (F.maps i).map s ++ a :: List.replicate (l - F.level r - 1) 0
  have hselected (i : Fin (m + 1)) (s : Word) (a : Fin 3)
      (hs : s.length = r) (ha : NeedsMatrix i s a) :
      next i s a ∈ X i ∧ (F.maps i).map s ++ [a] <+: next i s a := by
    dsimp [next]
    rw [dite_eq_left ⟨hs, ha⟩]
    exact (hex i s a hs ha).choose_spec
  have hdefault (i : Fin (m + 1)) (s : Word) (a : Fin 3)
      (ha : ¬ NeedsMatrix i s a) :
      next i s a = (F.maps i).map s ++ a :: List.replicate (l - F.level r - 1) 0 := by
    simp [next, ha]
  refine ⟨⟨l, hlt, X, next, ?_, ?_, ?_, ?_, hMono⟩⟩
  · intro i s a hs
    by_cases ha : NeedsMatrix i s a
    · exact (hX i _ (hselected i s a hs ha).1).2
    · rw [hdefault i s a ha]
      simp only [List.length_append, List.length_cons, List.length_replicate, F.length_map, hs]
      omega
  · intro i s a hs
    by_cases hneed : NeedsMatrix i s a
    · obtain ⟨p, hp⟩ := (hselected i s a hs hneed).2
      have heq : next i s a = (F.maps i).map s ++ a :: p := by
        simpa only [List.append_assoc, List.singleton_append] using hp.symm
      refine ⟨p, heq, ?_⟩
      intro ha
      have hi : i ≠ Fin.last m := by
        intro hi
        have heq : a = 1 := by simpa [NeedsMatrix, hi] using hneed
        exact ha heq
      have hb : Binary (next i s a) :=
        (hX i _ (hselected i s a hs hneed).1).1.resolve_left hi
      rw [heq] at hb
      exact (binary_cons a p).mp ((binary_append _ _).mp hb).2 |>.2
    · refine ⟨List.replicate (l - F.level r - 1) 0, hdefault i s a hneed, ?_⟩
      intro _ z hz
      have hz' : z = 0 := List.eq_of_mem_replicate hz
      subst z
      decide
  · intro i s a hs ha
    exact (hselected i s a hs ha).1
  · intro i s a _ ha
    exact hdefault i s a ha

end AllThoseBigRamsey.Pseudotree.Mixed
