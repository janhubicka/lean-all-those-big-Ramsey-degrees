import PseudotreeValidation.DiaryNormalization

/-! Literal word and essential-level transport under actual ray maps. -/

namespace AllThoseBigRamsey.Pseudotree.DiaryRecovery

open RayEmbeddings DiaryNormalization

theorem map_prefix (f : RayStrongMap) {s t : Word} (hp : s.IsPrefix t) :
    (f.map s).IsPrefix (f.map t) := by
  obtain ⟨u, rfl⟩ := hp
  obtain ⟨v, hv, _⟩ := f.map_append s u
  exact ⟨v, hv.symm⟩

theorem map_take (f : RayStrongMap) (w : Word) (k : ℕ) (hk : k ≤ w.length) :
    f.map (w.take k) = (f.map w).take (f.level k) := by
  have hp := map_prefix f (List.take_prefix k w)
  have hlen : (f.map (w.take k)).length = f.level k := by
    rw [f.length_map, List.length_take, Nat.min_eq_left hk]
  simpa only [hlen] using List.prefix_iff_eq_take.mp hp

theorem map_get (f : RayStrongMap) (w : Word) (k : ℕ) (hk : k < w.length) :
    (f.map w)[f.level k]? = w[k]? := by
  have hform : w = w.take k ++ w[k] :: w.drop (k+1) := by
    simpa only [List.drop_eq_getElem_cons hk] using (List.take_append_drop k w).symm
  obtain ⟨p, hp⟩ := f.map_append_cons (w.take k) w[k] (w.drop (k+1))
  rw [← hform] at hp
  have hlen : (f.map (w.take k)).length = f.level k := by
    rw [f.length_map, List.length_take, Nat.min_eq_left hk.le]
  rw [hp, ← hlen]
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, List.getElem?_eq_getElem hk]

def FirstFork (s t : Word) (k : ℕ) : Prop :=
  k < s.length ∧ k < t.length ∧ s.take k = t.take k ∧ s[k]? ≠ t[k]?

theorem firstFork_unique {s t : Word} {j k : ℕ} (hj : FirstFork s t j) (hk : FirstFork s t k) :
    j = k := by
  have hnot {a b : ℕ} (ha : FirstFork s t a) (hb : FirstFork s t b) : ¬ a < b := by
    intro hab
    apply ha.2.2.2
    have h := congrArg (fun w : Word => w[a]?) hb.2.2.1
    simpa only [List.getElem?_take, hab, ↓reduceIte] using h
  have h₁ := hnot hj hk
  have h₂ := hnot hk hj
  omega

theorem firstFork_not_prefix {s t : Word} {k : ℕ} (h : FirstFork s t k) : ¬ s.IsPrefix t := by
  rintro ⟨u, rfl⟩
  exact h.2.2.2 (List.getElem?_append_left h.1).symm

theorem firstFork_symm {s t : Word} {k : ℕ} (h : FirstFork s t k) : FirstFork t s k :=
  ⟨h.2.1, h.1, h.2.2.1.symm, Ne.symm h.2.2.2⟩

theorem firstFork_of_split (p u v : Word) (a b : Fin 3) (hab : a ≠ b) :
    FirstFork (p ++ a :: u) (p ++ b :: v) p.length := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · simp only [List.take_append_length]
  · simpa only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, ne_eq, Option.some.injEq] using hab

private theorem words_cases (s t : Word) :
    s.IsPrefix t ∨ t.IsPrefix s ∨ ∃ p a b u v,
      s = p ++ a :: u ∧ t = p ++ b :: v ∧ a ≠ b := by
  induction s generalizing t with
  | nil => exact Or.inl (by simp)
  | cons a s ih =>
    cases t with
    | nil => exact Or.inr (Or.inl (by simp))
    | cons b t =>
      by_cases hab : a = b
      · subst b
        rcases ih t with h | h | ⟨p, c, d, u, v, hs, ht, hcd⟩
        · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩)
        · exact Or.inr (Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h⟩))
        · exact Or.inr (Or.inr ⟨a :: p, c, d, u, v, by simp [hs], by simp [ht], hcd⟩)
      · exact Or.inr (Or.inr ⟨[], a, b, s, t, rfl, rfl, hab⟩)

theorem firstFork_map (f : RayStrongMap) {s t : Word} {k : ℕ} (hk : FirstFork s t k) :
    FirstFork (f.map s) (f.map t) (f.level k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [f.length_map]
    exact f.level_strict hk.1
  · rw [f.length_map]
    exact f.level_strict hk.2.1
  · rw [← map_take f s k hk.1.le, ← map_take f t k hk.2.1.le, hk.2.2.1]
  · rw [map_get f s k hk.1, map_get f t k hk.2.1]
    exact hk.2.2.2

theorem firstFork_map_iff (f : RayStrongMap) (s t : Word) (j : ℕ) :
    FirstFork (f.map s) (f.map t) j ↔ ∃ k, FirstFork s t k ∧ j = f.level k := by
  constructor
  · intro hj
    rcases words_cases s t with hp | hp | ⟨p, a, b, u, v, rfl, rfl, hab⟩
    · exact False.elim (firstFork_not_prefix hj (map_prefix f hp))
    · exact False.elim (firstFork_not_prefix (firstFork_symm hj) (map_prefix f hp))
    · have hk := firstFork_of_split p u v a b hab
      exact ⟨p.length, hk, firstFork_unique hj (firstFork_map f hk)⟩
  · rintro ⟨k, hk, rfl⟩
    exact firstFork_map f hk

theorem forkAt_image (f : RayStrongMap) (C : Finset Word) (j : ℕ) :
    ForkAt (C.image f.map) j ↔ ∃ k, ForkAt C k ∧ j = f.level k := by
  classical
  constructor
  · rintro ⟨s, hs, t, ht, hst⟩
    obtain ⟨s, hcs, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t, hct, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨k, hk, hj⟩ := (firstFork_map_iff f s t j).mp hst
    exact ⟨k, ⟨s, hcs, t, hct, hk⟩, hj⟩
  · rintro ⟨k, ⟨s, hs, t, ht, hk⟩, rfl⟩
    exact ⟨f.map s, Finset.mem_image.mpr ⟨s, hs, rfl⟩,
      f.map t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, firstFork_map f hk⟩

/-- End levels and genuine first forks transport exactly, with no extra
essential levels created inside padding. -/
theorem essential_image (f : RayStrongMap) (C : Finset Word) :
    essential (C.image f.map) = (essential C).image f.level := by
  classical
  ext j
  rw [mem_essential_iff, Finset.mem_image]
  constructor
  · rintro (⟨w, hw, hj⟩ | hj)
    · obtain ⟨w, hcw, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨w.length, length_mem_essential hcw, by simpa only [f.length_map] using hj⟩
    · obtain ⟨k, hk, hj⟩ := (forkAt_image f C j).mp hj
      exact ⟨k, fork_mem_essential hk, hj.symm⟩
  · rintro ⟨k, hk, rfl⟩
    rcases mem_essential_iff.mp hk with ⟨w, hw, rfl⟩ | hk
    · exact Or.inl ⟨f.map w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, f.length_map w⟩
    · exact Or.inr ((forkAt_image f C (f.level k)).mpr ⟨k, hk, rfl⟩)

/-- A target position between two retained levels belongs to a unique
source edge interval. This uses finite bounds, not an Archimedean axiom. -/
theorem level_interval (f : RayStrongMap) {p q j : ℕ}
    (hlo : f.level p ≤ j) (hhi : j < f.level q) :
    ∃ i, p ≤ i ∧ i < q ∧ f.level i ≤ j ∧ j < f.level (i+1) := by
  classical
  have hex : ∃ r, r ≤ q ∧ j < f.level r := ⟨q, le_rfl, hhi⟩
  let r := Nat.find hex
  have hr : r ≤ q ∧ j < f.level r := Nat.find_spec hex
  have hp : p < r := by
    by_contra h
    have hle : r ≤ p := Nat.le_of_not_gt h
    have hm := (show StrictMono f.level from fun _ _ h => f.level_strict h).monotone hle
    omega
  refine ⟨r-1, by omega, by omega, ?_, ?_⟩
  · by_contra h
    have hj : j < f.level (r-1) := Nat.lt_of_not_ge h
    exact Nat.find_min hex (by omega : r-1 < r) ⟨by omega, hj⟩
  · have heq : r-1+1 = r := by omega
    rw [heq]
    exact hr.2

/-- Any 1 in a mapped edge interval must originate at a source 1-edge;
0- and 2-edge padding is binary by the actual ray-map definition. -/
theorem one_edge_origin (f : RayStrongMap) (w : Word) {i j : ℕ}
    (hi : i < w.length) (hlo : f.level i ≤ j) (hhi : j < f.level (i+1))
    (hone : (f.map w)[j]? = some 1) : w[i]? = some 1 := by
  have hshort : (w.take i ++ [w[i]]) = w.take (i+1) := List.take_append_getElem hi
  obtain ⟨pad, hp, hbin⟩ := f.step (w.take i) w[i]
  rw [hshort, map_take f w (i+1) (by omega)] at hp
  have hlen : (f.map (w.take i)).length = f.level i := by
    rw [f.length_map, List.length_take, Nat.min_eq_left hi.le]
  have hget := congrArg (fun s : Word => s[j]?) hp
  rw [List.getElem?_take, ite_eq_left hhi, hone] at hget
  by_contra hsource
  have hsource' : w[i] ≠ 1 := by
    intro h
    apply hsource
    simp only [List.getElem?_eq_getElem hi, h]
  have htail : Binary (w[i] :: pad) := (binary_cons _ _).mpr ⟨hsource', hbin hsource'⟩
  rw [List.getElem?_append_right (by omega), hlen] at hget
  have hmem : (1 : Fin 3) ∈ w[i] :: pad := List.mem_of_getElem? hget.symm
  exact htail 1 hmem rfl

end AllThoseBigRamsey.Pseudotree.DiaryRecovery
