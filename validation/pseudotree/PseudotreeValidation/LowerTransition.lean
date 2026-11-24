import PseudotreeValidation.LowerStep
import PseudotreeValidation.LowerParents

/-! Synchronizing the genuine geometric candidates into a one-level step. -/

namespace AllThoseBigRamsey.Pseudotree.LowerRealization

open LowerGeometry
open scoped FirstOrder

/-- Finite simultaneous refinement turns the actual rational candidate copies
at the children into synchronized next-level prefixes. -/
theorem step_of_root_choices {D : PaperDiary n}
    {f : TernaryModel ↪[language] TernaryModel} {j height : Nat}
    (P : Layer D f j) (T : PaperTreeAxioms D.nodes D.codes height)
    (H : RootChoices P) : Nonempty (Step P) := by
  classical
  have hchoice : ∀ v : Level D (j + 1), ∃ Q : RayCopy,
      Set.range Q.embedding ⊆ Set.range f ∧ ∀ q, ∃ b : List TernaryLetter,
        fromBlocks (Q q) = H.roots (parent T v) ++ RayMapModel.toLetter (last v) :: b ∧
        (last v ≠ 1 → .one ∉ b) := by
    intro v
    exact H.children (parent T v) (last v) (parent_child_mem T v)
  choose Q hQinside hQtail using hchoice
  obtain ⟨L, hL, R, p, hstem, hsub, hlen, hp, hroot⟩ := finite_common_prefix Q H.level
  have htail : ∀ v : Level D (j + 1), ∃ b : List TernaryLetter,
      p v = H.roots (parent T v) ++ RayMapModel.toLetter (last v) :: b ∧
      (last v ≠ 1 → .one ∉ b) := by
    intro v
    obtain ⟨q, hq⟩ := hsub v ⟨0, rfl⟩
    obtain ⟨b, hb, hbinary⟩ := hQtail v q
    have hpre : p v <+: H.roots (parent T v) ++ RayMapModel.toLetter (last v) :: b := by
      rw [← hb, hq]
      exact hp v 0
    have hfirst : H.roots (parent T v) ++ [RayMapModel.toLetter (last v)] <+: p v := by
      exact List.prefix_of_prefix_length_le ⟨b, by simp⟩ hpre (by
        rw [List.length_append, H.length, List.length_singleton, hlen]
        omega)
    obtain ⟨tail, htail⟩ := hfirst
    refine ⟨tail, by simpa only [List.append_assoc, List.singleton_append] using htail.symm, ?_⟩
    intro hlast
    have hsubtail : tail <+: b := by
      apply (List.prefix_append_right_inj
        (H.roots (parent T v) ++ [RayMapModel.toLetter (last v)])).mp
      rw [htail]
      simpa only [List.append_assoc, List.singleton_append] using hpre
    exact fun hmem => hbinary hlast (hsubtail.subset hmem)
  have hedge : ∀ u a (ha : child u.val a ∈ D.nodes),
      ∃ b : List TernaryLetter,
        p (childNode u a ha) = H.roots u ++ RayMapModel.toLetter a :: b ∧
        (a ≠ 1 → .one ∉ b) := by
    intro u a ha
    simpa only [parent_childNode, last_childNode T] using htail (childNode u a ha)
  let next : Layer D f (j + 1) := {
    bound := L
    copies := R
    prefixes := p
    prefix_length := hlen
    common_prefix := hp
    root_short := hroot
    inside := fun v => (hsub v).trans (hQinside v)
    ordered := ordered_children T H.roots H.level H.length H.ordered p (by
      intro u a ha
      obtain ⟨b, hb, _⟩ := hedge u a ha
      exact ⟨b, by simpa only [List.append_assoc, List.singleton_append] using hb.symm⟩)
  }
  exact ⟨⟨next, H.level, H.lower, hL, H.roots, H.length, H.binary, H.coding, hedge⟩⟩

/-- A genuine step exists at every level of every raw paper diary, inside
every functional self-copy whose range lies in the actual sparse set. -/
theorem exists_step {D : PaperDiary n}
    {f : TernaryModel ↪[language] TernaryModel} {j height : Nat}
    (T : PaperTreeAxioms D.nodes D.codes height) (hj : j < height)
    (hsparse : ∀ x ∈ Set.range f, Sparse.InSparse (fromBlocks x))
    (P : Layer D f j) : Nonempty (Step P) := by
  obtain ⟨kind, c, LP⟩ := T.level j hj
  obtain ⟨H⟩ := root_choices P hsparse LP
  exact step_of_root_choices P T H

end AllThoseBigRamsey.Pseudotree.LowerRealization
