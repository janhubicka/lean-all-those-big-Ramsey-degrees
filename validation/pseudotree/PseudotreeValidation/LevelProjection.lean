import PseudotreeValidation.DiaryLex
import AllThoseBigRamsey.Pseudotree.RayExtension

/-!
# Projection to selected levels

Selecting all first-disagreement levels makes the inverse prefix map well
 defined. A concrete no-1 gap condition then makes it ray-preserving. These
are word lemmas used by sparse-chain extraction, without any assumed diary
representation or Ramsey conclusion.
-/

namespace AllThoseBigRamsey.Pseudotree.LevelProjection

open RayEmbeddings

/-- Read the first `j` selected coordinates, with irrelevant out-of-bounds
coordinates filled by 0. Every theorem below supplies the needed bounds. -/
def project (K : Nat → Nat) (w : Word) (j : Nat) : Word :=
  List.ofFn (fun i : Fin j => (w[K i.val]?).getD 0)

@[simp] theorem project_length (K : Nat → Nat) (w : Word) (j : Nat) :
    (project K w j).length = j := by simp [project]

@[simp] theorem project_zero (K : Nat → Nat) (w : Word) : project K w 0 = [] := rfl

@[simp] theorem project_get (K : Nat → Nat) (w : Word) {i j : Nat} (hi : i < j) :
    (project K w j)[i]'(by simpa using hi) = (w[K i]?).getD 0 := by simp [project]

theorem project_succ (K : Nat → Nat) (w : Word) (j : Nat) :
    project K w (j+1) = project K w j ++ [(w[K j]?).getD 0] := by
  simp only [project, List.ofFn_succ_last]
  rfl

@[simp] theorem project_take (K : Nat → Nat) (w : Word) {i j : Nat} (hij : i ≤ j) :
    (project K w j).take i = project K w i := by
  apply List.ext_getElem
  · simp [hij]
  · intro k hk hk'
    simp [project]

/-- A first disagreement before `j`, formulated without choosing a longest
common-prefix object. -/
theorem first_difference {s t : Word} {j : Nat}
    (hs : j ≤ s.length) (ht : j ≤ t.length) (hne : s.take j ≠ t.take j) :
    ∃ k, k < j ∧ s.take k = t.take k ∧ s[k]? ≠ t[k]? := by
  induction j generalizing s t with
  | zero => simp at hne
  | succ j ih =>
      cases s with
      | nil => simp at hs
      | cons a s =>
        cases t with
        | nil => simp at ht
        | cons b t =>
          by_cases hab : a = b
          · subst b
            have hne' : s.take j ≠ t.take j := by simpa using hne
            obtain ⟨k, hk, hp, hd⟩ := ih (by simpa using hs) (by simpa using ht) hne'
            exact ⟨k+1, by omega, by simpa using hp, by simpa using hd⟩
          · exact ⟨0, by omega, rfl, by simpa using hab⟩

/-- All branching levels of the given coding set are selected. This is a
finite combinatorial condition, not an assumption about a projected diary. -/
def Separates (C : Set Word) (K : Nat → Nat) : Prop :=
  ∀ s ∈ C, ∀ t ∈ C, ∀ k, k < s.length → k < t.length →
    s.take k = t.take k → s[k]? ≠ t[k]? → ∃ i, K i = k

theorem take_eq_of_project_eq {C : Set Word} {K : Nat → Nat}
    (hK : StrictMono K) (hsep : Separates C K) {s t : Word} {j : Nat}
    (hs : s ∈ C) (ht : t ∈ C) (hslen : K j ≤ s.length) (htlen : K j ≤ t.length)
    (heq : project K s j = project K t j) : s.take (K j) = t.take (K j) := by
  by_contra hne
  obtain ⟨k, hkj, hp, hd⟩ := first_difference hslen htlen hne
  have hks : k < s.length := lt_of_lt_of_le hkj hslen
  have hkt : k < t.length := lt_of_lt_of_le hkj htlen
  obtain ⟨i, hi⟩ := hsep s hs t ht k hks hkt hp hd
  have hij : i < j := hK.lt_iff_lt.mp (by simpa [hi] using hkj)
  have hval := congrArg (fun v : Word => v[i]?.getD 0) heq
  have hsget : s[k]?.getD 0 = s[k] := by simp [hks]
  have htget : t[k]?.getD 0 = t[k] := by simp [hkt]
  have helem : s[k] = t[k] := by simpa [project, hij, hi, hks, hkt] using hval
  exact hd (by simpa [hks, hkt] using congrArg some helem)

/-- Conversely equal original prefixes have equal selected prefixes. -/
theorem project_eq_of_take_eq {K : Nat → Nat} (hK : StrictMono K)
    {s t : Word} {j : Nat} (heq : s.take (K j) = t.take (K j)) :
    project K s j = project K t j := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hij : i < j := by simpa using hi
    have hik : K i < K j := hK hij
    have h := congrArg (fun v : Word => v[K i]?) heq
    have h' : s[K i]? = t[K i]? := by simpa [List.getElem?_take, hik] using h
    simp only [project_get K s hij, project_get K t hij, h']

/-- No unrecorded 1 can lie in the gap of an edge whose first letter is
binary. This is exactly the ray-preserving padding condition. -/
def BinaryGaps (C : Set Word) (K : Nat → Nat) : Prop :=
  ∀ w ∈ C, ∀ j, K (j+1) ≤ w.length → w[K j]? ≠ some 1 →
    ∀ k, K j < k → k < K (j+1) → w[k]? ≠ some 1

/-- The normalized prefix domain, defined directly from selected coordinates. -/
def Domain (C : Set Word) (K : Nat → Nat) (s : Word) : Prop :=
  ∃ w ∈ C, K s.length ≤ w.length ∧ project K w s.length = s

theorem domain_root {C : Set Word} {K : Nat → Nat}
    (hne : ∃ w ∈ C, K 0 ≤ w.length) : Domain C K [] := by
  obtain ⟨w, hw, hlen⟩ := hne
  exact ⟨w, hw, hlen, project_zero K w⟩

theorem domain_project {C : Set Word} {K : Nat → Nat} {w : Word} {j : Nat}
    (hw : w ∈ C) (hlen : K j ≤ w.length) : Domain C K (project K w j) := by
  simpa only [Domain, project_length] using (show ∃ v ∈ C,
    K j ≤ v.length ∧ project K v j = project K w j from ⟨w, hw, hlen, rfl⟩)

theorem domain_prefix_closed {C : Set Word} {K : Nat → Nat} (hK : StrictMono K)
    (s t : Word) (hst : Domain C K (s ++ t)) : Domain C K s := by
  obtain ⟨w, hw, hlen, heq⟩ := hst
  refine ⟨w, hw, le_trans (hK.monotone ?_) hlen, ?_⟩
  · simp
  · have h := congrArg (List.take s.length) heq
    simpa only [project_take K w (by simp : s.length ≤ (s ++ t).length),
      List.take_left] using h

/-- Choose an original prefix; separation proves that the choice is
irrelevant on the domain. -/
noncomputable def inverse (C : Set Word) (K : Nat → Nat) (s : Word) : Word := by
  classical
  exact if h : Domain C K s then (Classical.choose h).take (K s.length) else []

theorem inverse_eq {C : Set Word} {K : Nat → Nat} (hK : StrictMono K)
    (hsep : Separates C K) {s w : Word} (hw : w ∈ C)
    (hlen : K s.length ≤ w.length) (heq : project K w s.length = s) :
    inverse C K s = w.take (K s.length) := by
  have hd : Domain C K s := ⟨w, hw, hlen, heq⟩
  rw [inverse, dite_eq_left hd]
  obtain ⟨hv, hvlen, hveq⟩ := Classical.choose_spec hd
  exact take_eq_of_project_eq hK hsep hv hw hvlen hlen (hveq.trans heq.symm)

theorem inverse_project {C : Set Word} {K : Nat → Nat} (hK : StrictMono K)
    (hsep : Separates C K) {w : Word} {j : Nat} (hw : w ∈ C) (hlen : K j ≤ w.length) :
    inverse C K (project K w j) = w.take (K j) := by
  simpa only [project_length] using inverse_eq (s := project K w j) hK hsep hw
    (by simpa only [project_length] using hlen) (by simp)

theorem take_edge (w : Word) {i j : Nat} (hij : i < j) (hj : j ≤ w.length) :
    w.take j = w.take i ++ w[i]'(lt_of_lt_of_le hij hj) ::
      (w.drop (i+1)).take (j-i-1) := by
  have harith : j = (i+1) + (j-i-1) := by omega
  conv_lhs => rw [harith, List.take_add]
  rw [← List.take_append_getElem (lt_of_lt_of_le hij hj)]
  simp only [List.append_assoc, List.singleton_append]

theorem inverse_step {C : Set Word} {K : Nat → Nat} (hK : StrictMono K)
    (hsep : Separates C K) (hgap : BinaryGaps C K) (s : Word) (a : Fin 3)
    (hdom : Domain C K (s ++ [a])) :
    ∃ padding : Word, inverse C K (s ++ [a]) = inverse C K s ++ a :: padding ∧
      (a ≠ 1 → Binary padding) := by
  obtain ⟨w, hw, hlen, heq⟩ := hdom
  have hlen' : K (s.length+1) ≤ w.length := by simpa using hlen
  have hj : K s.length < w.length := lt_of_lt_of_le (hK (Nat.lt_succ_self _)) hlen'
  have hp : project K w s.length = s := by
    have h := congrArg (List.take s.length) heq
    simpa only [project_take K w (by simp : s.length ≤ (s ++ [a]).length),
      List.take_left] using h
  have ha : w[K s.length] = a := by
    have h' : [w[K s.length]] = [a] := List.append_cancel_left (by
      simpa only [List.length_append, List.length_singleton, project_succ, hp,
        List.getElem?_eq_getElem hj, Option.getD_some] using heq)
    exact List.singleton_inj.mp h'
  refine ⟨(w.drop (K s.length+1)).take (K (s.length+1)-K s.length-1), ?_, ?_⟩
  · rw [inverse_eq hK hsep hw hlen heq,
      inverse_eq hK hsep hw (Nat.le_of_lt hj) hp]
    simpa only [List.length_append, List.length_singleton, ha] using
      take_edge w (hK (Nat.lt_succ_self s.length)) hlen'
  · intro ha1 b hb heq1
    subst b
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hb
    have hib : i < K (s.length+1)-K s.length-1 :=
      lt_of_lt_of_le hi (List.length_take_le _ _)
    have hidx : K s.length+1+i < K (s.length+1) := by omega
    have hidxw : K s.length+1+i < w.length := lt_of_lt_of_le hidx hlen'
    have hw1 : w[K s.length+1+i]? = some 1 := by
      rw [List.getElem?_eq_getElem hidxw]
      simpa only [List.getElem_take, List.getElem_drop] using congrArg some hget
    exact hgap w hw s.length hlen'
      (by simpa [hj, ha] using ha1) _ (by omega) hidx hw1

/-- Concrete inverse prefixes yield an actual ray-preserving partial strong
map. No injectivity or realization is assumed; both follow from the local
word conditions proved above. -/
noncomputable def prefixRayMap {C : Set Word} {K : Nat → Nat} (hK : StrictMono K)
    (hsep : Separates C K) (hgap : BinaryGaps C K)
    (hne : ∃ w ∈ C, K 0 ≤ w.length) : PrefixRayMap (Domain C K) where
  root_mem := domain_root hne
  prefix_closed := domain_prefix_closed hK
  map := inverse C K
  level := K
  level_strict := fun h => hK h
  length_map := by
    intro s hs
    obtain ⟨w, hw, hlen, heq⟩ := hs
    rw [inverse_eq hK hsep hw hlen heq, List.length_take, Nat.min_eq_left hlen]
  step := inverse_step hK hsep hgap

/-- The completed total map sends every normalized code back to its original
word, provided the coding level itself was selected. -/
theorem completion_project {C : Set Word} {K : Nat → Nat} (hK : StrictMono K)
    (hsep : Separates C K) (hgap : BinaryGaps C K)
    (hne : ∃ w ∈ C, K 0 ≤ w.length) {w : Word} {j : Nat}
    (hw : w ∈ C) (hlen : K j = w.length) :
    (prefixRayMap hK hsep hgap hne).completion.map (project K w j) = w := by
  rw [PrefixRayMap.completion_agrees _ _ (domain_project hw hlen.le)]
  change inverse C K (project K w j) = w
  rw [inverse_project hK hsep hw hlen.le, hlen, List.take_length]

end AllThoseBigRamsey.Pseudotree.LevelProjection
