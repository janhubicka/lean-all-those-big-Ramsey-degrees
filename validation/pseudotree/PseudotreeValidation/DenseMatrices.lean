import Milliken.GeneralTree.UnconditionalHLAPI

/-!
# Finite-colour dense-level-matrix Halpern–Läuchli

The imported library proves binary sparse finite HL and binary fixed-base
density. The pseudotree argument uses an arbitrary finite colour set. We
perform only the finite-colour reduction and the fixed-base/fixed-colour
extraction here; the substantive HL theorem is imported with its proof.
-/

namespace AllThoseBigRamsey.Pseudotree

open Milliken Milliken.GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Finite-colour sparse finite HL, obtained by eliminating the last colour
with the proved binary sparse dichotomy. -/
theorem finiteColourSparseHL
    (P : Fin d → StrongSubtree U)
    (hHDHL : HasHeterogeneousHDHL P)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (hunbounded : ∀ r, ∃ q, r ≤ levels q) :
    ∀ n : ℕ, ∃ l : ℕ, ∀ M : HeterogeneousMatrix P,
      M.DenseAt l → ∀ colour : (Fin d → U) → Fin (n + 1),
        ∃ a : Fin (n + 1), ∃ N : HeterogeneousMatrix P,
          HeterogeneousSparseSomewhereDense P levels N ∧
          N.carrier ⊆ M.carrier ∧
          ∀ x ∈ N.carrier, colour x = a := by
  classical
  intro n
  induction n with
  | zero =>
      refine ⟨levels 1, ?_⟩
      intro M hM colour
      let base : HeterogeneousLevelTuple P (levels 0) :=
        Classical.choice inferInstance
      refine ⟨0, M, ?_, Set.Subset.rfl, ?_⟩
      · refine ⟨0, base, ?_⟩
        intro i x hx _
        exact hM i x hx
      · intro x _
        exact Fin.eq_zero _
  | succ n ih =>
      obtain ⟨l0, hfinite⟩ := ih
      obtain ⟨l, hbinary⟩ := heterogeneousSparseFiniteHL_of_hdhl
        P hHDHL (Nat.zero_lt_succ l0) hlevels hunbounded
      refine ⟨l, ?_⟩
      intro M hM colour
      let last : Fin (n + 2) := Fin.last (n + 1)
      let K0 : Set (Fin d → U) := {x | colour x ≠ last}
      rcases hbinary M hM K0 with hlast | hrest
      · obtain ⟨N, hNsparse, hNsub⟩ := hlast
        refine ⟨last, N, hNsparse, (fun x hx => (hNsub hx).1), ?_⟩
        intro x hx
        by_contra hne
        exact (hNsub hx).2 hne
      · obtain ⟨M0, hM0dense, hM0sub⟩ := hrest
        let reduced : (Fin d → U) → Fin (n + 1) := fun x =>
          if h : colour x = last then 0 else
            ⟨(colour x).val, by
              have hlt := (colour x).isLt
              have hne : (colour x).val ≠ n + 1 := by
                intro hv
                apply h
                apply Fin.ext
                simpa [last] using hv
              omega⟩
        obtain ⟨a, N, hNsparse, hNsub, hmono⟩ :=
          hfinite M0 (M0.denseAt_of_le (Nat.le_succ l0) hM0dense) reduced
        refine ⟨a.castSucc, N, hNsparse, ?_, ?_⟩
        · intro x hx
          exact (hM0sub (hNsub hx)).1
        · intro x hx
          have hnotLast : colour x ≠ last := (hM0sub (hNsub hx)).2
          have hcast : (reduced x).castSucc = colour x := by
            apply Fin.ext
            simp [reduced, hnotLast]
          exact hcast.symm.trans (congrArg Fin.castSucc (hmono x hx))

/-- A monochromatic matrix on one common source level, dense at q above
a fixed base. The colour is initially allowed to depend on q. -/
def FiniteLevelMonochromaticAbove
    (P : Fin d → StrongSubtree U) {colors : ℕ}
    (colour : (Fin d → U) → Fin colors)
    (base : Fin d → U) (q : ℕ) : Prop :=
  ∃ a : Fin colors, ∃ M : HeterogeneousMatrix P, ∃ l : ℕ,
    M.OnLevel l ∧ M.DenseAbove base q ∧
      ∀ x ∈ M.carrier, colour x = a

/-- Todorčević's forbidden-density-scale argument, now for any positive
finite number of colours. -/
theorem finiteColourFixedBase
    (P : Fin d → StrongSubtree U)
    (hHDHL : HasHeterogeneousHDHL P) (n : ℕ)
    (colour : (Fin d → U) → Fin (n + 1)) :
    ∃ k : ℕ, ∃ base : HeterogeneousLevelTuple P k,
      ∀ q, FiniteLevelMonochromaticAbove P colour base.1 q := by
  classical
  by_contra hfail
  have hbad : ∀ k : ℕ, ∀ base : HeterogeneousLevelTuple P k,
      ∃ q, ¬ FiniteLevelMonochromaticAbove P colour base.1 q := by
    intro k base
    by_contra hall
    push Not at hall
    exact hfail ⟨k, base, hall⟩
  let bad : (k : ℕ) → HeterogeneousLevelTuple P k → ℕ :=
    fun k base => Classical.choose (hbad k base)
  have hbad_spec (k : ℕ) (base : HeterogeneousLevelTuple P k) :
      ¬ FiniteLevelMonochromaticAbove P colour base.1 (bad k base) :=
    Classical.choose_spec (hbad k base)
  let (k : ℕ) : Fintype (HeterogeneousLevelTuple P k) := Fintype.ofFinite _
  let next (k : ℕ) : ℕ := max (k + 1) (1 + Finset.univ.sup (bad k))
  have hnext (k : ℕ) : k < next k := by
    have h := Nat.le_max_left (k + 1) (1 + Finset.univ.sup (bad k))
    dsimp [next]
    omega
  have hbad_lt_next (k : ℕ) (base : HeterogeneousLevelTuple P k) :
      bad k base < next k := by
    have hs : bad k base ≤ Finset.univ.sup (bad k) :=
      Finset.le_sup (f := bad k) (Finset.mem_univ base)
    dsimp [next]
    omega
  let levels : ℕ → ℕ := Nat.rec 0 (fun _ previous => next previous)
  have hlevels : StrictMono levels := by
    apply strictMono_nat_of_lt_succ
    intro p
    exact hnext (levels p)
  have hdiag : ∀ p, p ≤ levels p := hlevels.id_le
  obtain ⟨l, hfinite⟩ := finiteColourSparseHL P hHDHL levels hlevels
    (fun r => ⟨r, hdiag r⟩) n
  let Full : HeterogeneousMatrix P := HeterogeneousMatrix.fullLevel P l
  obtain ⟨a, N, ⟨p, base, hDense⟩, hsub, hmono⟩ :=
    hfinite Full (HeterogeneousMatrix.fullLevel_denseAt P l) colour
  have hnonempty : ∀ i, (N.coord i).Nonempty := by
    intro i
    obtain ⟨z, hz, hbasez⟩ := (P i).exists_sourceLevel_descendant
      (hlevels (Nat.lt_succ_self p)).le (base.2 i)
    obtain ⟨w, hw, _⟩ := hDense i z hz hbasez
    exact ⟨w, hw⟩
  have hOn : N.OnLevel l :=
    N.onLevel_of_carrier_subset_of_coord_nonempty Full hsub
      (HeterogeneousMatrix.fullLevel_onLevel P l) hnonempty
  have hbound : bad (levels p) base < levels (p + 1) :=
    hbad_lt_next (levels p) base
  have hLow : N.DenseAbove base.1 (bad (levels p) base) :=
    N.denseAbove_of_le base.1 hbound.le hDense
  exact hbad_spec (levels p) base ⟨a, N, l, hOn, hLow, hmono⟩

/-- The finite-colour dense-level-matrix form used in the pseudotree note.
The supporting source level can exceed any independent lower bound m.
The ambient factors need only be pruned and locally finite. -/
theorem finiteColourDenseMatrices
    (U : AmbientTree) (d : ℕ) (hd : 0 < d)
    (P : Fin d → StrongSubtree U) (n : ℕ)
    (colour : (Fin d → U) → Fin (n + 1)) :
    ∃ k : ℕ, ∃ base : HeterogeneousLevelTuple P k,
      ∃ a : Fin (n + 1), ∀ q m : ℕ,
        ∃ l : ℕ, m ≤ l ∧
          ∃ M : HeterogeneousMatrix P,
            M.OnLevel l ∧ M.DenseAbove base.1 q ∧
            ∀ x ∈ M.carrier, colour x = a := by
  classical
  obtain ⟨k, base, hall⟩ := finiteColourFixedBase P
    (heterogeneousHDHL_unconditional d hd U P) n colour
  choose c M l hOn hDense hMono using hall
  obtain ⟨a, hInfiniteFibre⟩ := Finite.exists_infinite_fiber c
  have hInfinite : (c ⁻¹' {a}).Infinite :=
    Set.infinite_coe_iff.mp hInfiniteFibre
  refine ⟨k, base, a, ?_⟩
  intro q m
  obtain ⟨r, hrmem, hr⟩ := hInfinite.exists_gt (max k (max q m))
  have hkr : k ≤ r := by omega
  have hqr : q ≤ r := by omega
  have hmr : m ≤ r := by omega
  have hrl : r ≤ l r :=
    heterogeneous_support_ge_of_onLevel_denseAbove
      P hd base hkr (M r) (hOn r) (hDense r)
  refine ⟨l r, hmr.trans hrl, M r, hOn r,
    (M r).denseAbove_of_le base.1 hqr (hDense r), ?_⟩
  intro x hx
  have hca : c r = a := by simpa using hrmem
  exact (hMono r x hx).trans hca

/-- The finite-demand formulation of the preceding theorem: every finite
family of nodes above the fixed base is dominated by a monochromatic
matrix supported arbitrarily high. This is the quantifier pattern of
part (i) of the note's Halpern–Läuchli statement. -/
theorem finiteDemandDenseMatrices
    (U : AmbientTree) (d : ℕ) (hd : 0 < d)
    (P : Fin d → StrongSubtree U) (n : ℕ)
    (colour : (Fin d → U) → Fin (n + 1)) :
    ∃ k : ℕ, ∃ base : HeterogeneousLevelTuple P k,
      ∃ a : Fin (n + 1), ∀ F : Fin d → Finset U,
        (∀ i, ∀ x ∈ F i, x ∈ (P i).carrier ∧ base.1 i ≤ x) →
        ∀ m : ℕ, ∃ l : ℕ, m ≤ l ∧
          ∃ M : HeterogeneousMatrix P,
            M.OnLevel l ∧
            (∀ i, ∀ x ∈ F i, ∃ y ∈ M.coord i, x ≤ y) ∧
            ∀ x ∈ M.carrier, colour x = a := by
  classical
  obtain ⟨k, base, a, hall⟩ := finiteColourDenseMatrices U d hd P n colour
  refine ⟨k, base, a, ?_⟩
  intro F hF m
  let q : ℕ := Finset.univ.sup (fun i => (F i).sup U.level)
  obtain ⟨l, hml, M, hOn, hDense, hMono⟩ := hall q m
  refine ⟨l, hml, M, hOn, ?_, hMono⟩
  intro i x hx
  obtain ⟨hcar, hbase⟩ := hF i x hx
  obtain ⟨j, hj⟩ := (P i).carrier_levels x hcar
  have hjq : j ≤ q := by
    have hjlevel : j ≤ U.level x := by
      rw [hj]
      exact (P i).levels_strictMono.id_le j
    have hxbound : U.level x ≤ (F i).sup U.level :=
      Finset.le_sup (f := U.level) hx
    have hibound : (F i).sup U.level ≤ q :=
      Finset.le_sup (f := fun i => (F i).sup U.level) (Finset.mem_univ i)
    exact hjlevel.trans (hxbound.trans hibound)
  obtain ⟨z, hz, hxz⟩ :=
    (P i).exists_sourceLevel_descendant hjq ⟨hcar, hj⟩
  obtain ⟨y, hy, hzy⟩ := hDense i z hz (hbase.trans hxz)
  exact ⟨y, hy, hxz.trans hzy⟩

end AllThoseBigRamsey.Pseudotree
