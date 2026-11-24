import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic

/-!
# Least-enumeration profiles in meet-trees

This file uses the actual functional meet operation of a `SemilatticeInf`.
`System` supplies a surjective enumeration and the meet-tree condition that
predecessors of a common upper bound are comparable. The label and profile
are the literal definitions from the incomparable-elements proof in the note.
-/
namespace AllThoseBigRamsey.Pseudotree.Profiles

structure System (α : Type*) [SemilatticeInf α] where
  enumerate : ℕ → α
  onto : Function.Surjective enumerate
  predecessors : ∀ {x y z : α}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x

variable {α : Type*} [SemilatticeInf α]

namespace System

variable (E : System α)

private theorem exists_above (a : α) : ∃ i, a ≤ E.enumerate i := by
  obtain ⟨i, rfl⟩ := E.onto a
  exact ⟨i, le_rfl⟩

/-- The least index of an enumerated upper bound. -/
noncomputable def label (a : α) : ℕ := by
  classical
  exact Nat.find (E.exists_above a)

theorem label_spec (a : α) : a ≤ E.enumerate (E.label a) := by
  classical
  exact Nat.find_spec (E.exists_above a)

theorem label_le_of_le_enumerate {a : α} {i : ℕ} (ha : a ≤ E.enumerate i) :
    E.label a ≤ i := by
  classical
  exact Nat.find_min' (E.exists_above a) ha

theorem label_monotone : Monotone E.label := by
  intro a b hab
  exact E.label_le_of_le_enumerate (hab.trans (E.label_spec b))

/-- The finite set of labels of all predecessors of `a`. The range bound is
proved redundant in `mem_profile_iff`; it makes the finiteness constructive. -/
noncomputable def profile (a : α) : Finset ℕ := by
  classical
  exact (Finset.range (E.label a + 1)).filter (fun i => ∃ x, x ≤ a ∧ E.label x = i)

theorem mem_profile_iff {a : α} {i : ℕ} :
    i ∈ E.profile a ↔ ∃ x, x ≤ a ∧ E.label x = i := by
  classical
  simp only [profile, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · rintro ⟨x, hx, heq⟩
    have hb := E.label_monotone hx
    exact ⟨by omega, x, hx, heq⟩

theorem label_mem_profile (a : α) : E.label a ∈ E.profile a :=
  E.mem_profile_iff.mpr ⟨a, le_rfl, rfl⟩

theorem profile_nonempty (a : α) : (E.profile a).Nonempty :=
  ⟨E.label a, E.label_mem_profile a⟩

theorem mem_profile_le {a : α} {i : ℕ} (hi : i ∈ E.profile a) : i ≤ E.label a := by
  obtain ⟨x, hx, rfl⟩ := E.mem_profile_iff.mp hi
  exact E.label_monotone hx

theorem profile_subset_range (a : α) : E.profile a ⊆ Finset.range (E.label a + 1) := by
  intro i hi
  exact Finset.mem_range.mpr (by have := E.mem_profile_le hi; omega)

theorem profile_monotone {a b : α} (hab : a ≤ b) : E.profile a ⊆ E.profile b := by
  intro i hi
  obtain ⟨x, hx, hlabel⟩ := E.mem_profile_iff.mp hi
  exact E.mem_profile_iff.mpr ⟨x, hx.trans hab, hlabel⟩

/-- The greatest profile value is exactly the least-upper-enumeration label. -/
theorem profile_max (a : α) : (E.profile a).max' (E.profile_nonempty a) = E.label a := by
  apply le_antisymm
  · exact Finset.max'_le _ _ _ (fun _ hi => E.mem_profile_le hi)
  · exact Finset.le_max' _ _ (E.label_mem_profile a)

/-- Each label fibre is linearly ordered in the ambient meet-tree. -/
theorem label_fibre_chain {a b : α} (hab : E.label a = E.label b) : a ≤ b ∨ b ≤ a := by
  apply E.predecessors (E.label_spec a)
  simpa [hab] using E.label_spec b

theorem profile_eq_label_eq {a b : α} (hab : E.profile a = E.profile b) :
    E.label a = E.label b := by
  apply le_antisymm
  · exact E.mem_profile_le (hab ▸ E.label_mem_profile a)
  · exact E.mem_profile_le (hab.symm ▸ E.label_mem_profile b)

/-- Incomparable points have different labels and different finite profiles. -/
theorem incomparable_distinct {a b : α} (hab : ¬a ≤ b) (hba : ¬b ≤ a) :
    E.label a ≠ E.label b ∧ E.profile a ≠ E.profile b := by
  have hl : E.label a ≠ E.label b := by
    intro he
    exact (E.label_fibre_chain he).elim hab hba
  exact ⟨hl, fun hp => hl (E.profile_eq_label_eq hp)⟩

theorem profile_constant_between {u x a : α} (hux : u ≤ x) (hxa : x ≤ a)
    (heq : E.profile u = E.profile a) : E.profile x = E.profile a := by
  apply Finset.Subset.antisymm (E.profile_monotone hxa)
  rw [← heq]
  exact E.profile_monotone hux

include E in
/-- Moving farther along a branch above a strict meet does not change that meet. -/
theorem inf_eq_of_above_branch {z b a : α} (hzb : z ≤ b) (hza : z ⊓ a < z) :
    b ⊓ a = z ⊓ a := by
  apply le_antisymm
  · rcases E.predecessors hzb (inf_le_left : b ⊓ a ≤ b) with h | h
    · have hle : z ≤ a := h.trans inf_le_right
      have he : z ⊓ a = z := inf_eq_left.mpr hle
      exact False.elim (hza.ne he)
    · exact le_inf h inf_le_right
  · exact le_inf (inf_le_left.trans hzb) inf_le_right

/-- A finite subset appears as a repeated profile inside `S`. -/
def Repeated (S : Set α) (s : Finset ℕ) : Prop :=
  ∃ u ∈ S, ∃ a ∈ S, u < a ∧ E.profile u = s ∧ E.profile a = s

/-- Concrete geometric conditions used in the paper's proof. There are no
profile, colouring, or no-isolation conclusions among these assumptions. -/
structure RichSubset (_E : System α) (S : Set α) : Prop where
  nonempty : S.Nonempty
  above : ∀ y ∈ S, ∃ w ∈ S, y < w
  intervals : ∀ {y w}, y ∈ S → w ∈ S → y < w →
    Set.Infinite {x | x ∈ S ∧ y < x ∧ x < w}
  branching : ∀ {x a}, x ∈ S → a ∈ S → x < a →
    ∃ z ∈ S, x < z ∧ z ⊓ a = x

/-- The geometric conditions hold on every meet-preserving embedded copy of
a densely ordered branching meet-tree without maximal points. -/
theorem richSubset_range [Nonempty α] [DenselyOrdered α] [NoMaxOrder α]
    (hbranch : ∀ {x a : α}, x < a → ∃ z, x < z ∧ z ⊓ a = x)
    (f : α ↪o α) (hinf : ∀ x y, f (x ⊓ y) = f x ⊓ f y) :
    E.RichSubset (Set.range f) := by
  constructor
  · obtain ⟨a⟩ := ‹Nonempty α›
    exact ⟨f a, a, rfl⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨w, hw⟩ := exists_gt y
    exact ⟨f w, ⟨w, rfl⟩, f.strictMono hw⟩
  · rintro _ _ ⟨y, rfl⟩ ⟨w, rfl⟩ hyw
    have hI := Set.Ioo_infinite (f.lt_iff_lt.mp hyw)
    have hIm := hI.image f.injective.injOn
    apply hIm.mono
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, f.strictMono hx.1, f.strictMono hx.2⟩
  · rintro _ _ ⟨x, rfl⟩ ⟨a, rfl⟩ hxa
    obtain ⟨z, hxz, hza⟩ := hbranch (f.lt_iff_lt.mp hxa)
    exact ⟨f z, ⟨z, rfl⟩, f.strictMono hxz, by rw [← hinf, hza]⟩

/-- Finitely many profiles on an infinite interval force a repeated profile
above every point of the subset. -/
theorem repeated_above {S : Set α} (hS : E.RichSubset S) {y : α} (hy : y ∈ S) :
    ∃ a ∈ S, y < a ∧ E.Repeated S (E.profile a) := by
  classical
  obtain ⟨w, hw, hyw⟩ := hS.above y hy
  have hI := hS.intervals hy hw hyw
  have hmap : Set.MapsTo E.profile {x | x ∈ S ∧ y < x ∧ x < w}
      (↑(E.profile w).powerset : Set (Finset ℕ)) := by
    intro x hx
    exact Finset.mem_powerset.mpr (E.profile_monotone hx.2.2.le)
  obtain ⟨p, hp, q, hq, hpq, heq⟩ :=
    hI.exists_ne_map_eq_of_mapsTo hmap (E.profile w).powerset.finite_toSet
  rcases E.predecessors hp.2.2.le hq.2.2.le with hpq' | hqp'
  · refine ⟨q, hq.1, hq.2.1, p, hp.1, q, hq.1, ?_, heq, rfl⟩
    exact lt_of_le_of_ne hpq' hpq
  · refine ⟨p, hp.1, hp.2.1, q, hq.1, p, hp.1, ?_, heq.symm, rfl⟩
    exact lt_of_le_of_ne hqp' hpq.symm

theorem repeated_nonempty {S : Set α} (hS : E.RichSubset S) :
    ∃ s, E.Repeated S s := by
  obtain ⟨y, hy⟩ := hS.nonempty
  obtain ⟨a, _, _, ha⟩ := E.repeated_above hS hy
  exact ⟨E.profile a, ha⟩

theorem repeated_fin_nonempty {S : Set α} {s : Finset ℕ} (hs : E.Repeated S s) :
    s.Nonempty := by
  obtain ⟨_, _, a, _, _, _, ha⟩ := hs
  simpa [ha] using E.profile_nonempty a

/-- The finitely many branch points at which labels at most `N` can leave the
chain ending at `a`. This replaces the longer pairwise-fibre avoidance argument. -/
noncomputable def barriers (a : α) (N : ℕ) : Finset α := by
  classical
  exact (Finset.range (N + 1)).image (fun i => a ⊓ E.enumerate i)

/-- Above a branch point outside the finite barrier set, every newly entered
node has enumeration label greater than the cutoff. -/
theorem label_gt_of_avoids_barriers {a b x q : α} {N : ℕ}
    (hx : x ∉ E.barriers a N) (hba : b ⊓ a = x)
    (hxq : x < q) (hqb : q ≤ b) : N < E.label q := by
  classical
  have hxa : x ≤ a := by rw [← hba]; exact inf_le_right
  have hqa : q ⊓ a = x := by
    apply le_antisymm
    · calc q ⊓ a ≤ b ⊓ a := inf_le_inf_right a hqb
           _ = x := hba
    · exact le_inf hxq.le hxa
  by_contra hn
  have hn' : E.label q ≤ N := by omega
  have hqa' : q ⊓ a < q := by simpa [hqa] using hxq
  have he : E.enumerate (E.label q) ⊓ a = x :=
    (E.inf_eq_of_above_branch (E.label_spec q) hqa').trans hqa
  apply hx
  apply Finset.mem_image.mpr
  refine ⟨E.label q, Finset.mem_range.mpr (by omega), ?_⟩
  simpa [inf_comm] using he

/-- The repeated-profile family has arbitrarily distant proper end-extensions.
This is the actual no-isolated-points construction, derived from infinite
intervals and branching rather than assumed as a profile hypothesis. -/
theorem repeated_endExtension {S : Set α} (hS : E.RichSubset S)
    {s : Finset ℕ} (hs : E.Repeated S s) (N : ℕ) :
    ∃ t, E.Repeated S t ∧ s ⊂ t ∧ ∀ i ∈ t, i ∉ s → N < i := by
  classical
  obtain ⟨u, hu, a, ha, hua, hpu, hpa⟩ := hs
  have hI := hS.intervals hu ha hua
  obtain ⟨x, hxI, hxB⟩ := (hI.sdiff (E.barriers a N).finite_toSet).nonempty
  obtain ⟨hx, hux, hxa⟩ := hxI
  obtain ⟨z, hz, hxz, hza⟩ := hS.branching hx ha hxa
  obtain ⟨b, hb, hzb, hrep⟩ := E.repeated_above hS hz
  have hxb : x < b := hxz.trans hzb
  have hba : b ⊓ a = x :=
    (E.inf_eq_of_above_branch hzb.le (by simpa [hza] using hxz)).trans hza
  have hpx : E.profile x = s :=
    (E.profile_constant_between hux.le hxa.le (hpu.trans hpa.symm)).trans hpa
  have hsub : s ⊆ E.profile b := by
    rw [← hpx]
    exact E.profile_monotone hxb.le
  have hnot_ab : ¬a ≤ b := by
    intro h
    have he : b ⊓ a = a := inf_eq_right.mpr h
    have : x = a := hba.symm.trans he
    exact hxa.ne this
  have hnot_ba : ¬b ≤ a := by
    intro h
    have he : b ⊓ a = b := inf_eq_left.mpr h
    have : x = b := hba.symm.trans he
    exact hxb.ne this
  have hne : s ≠ E.profile b := by
    rw [← hpa]
    exact (E.incomparable_distinct hnot_ab hnot_ba).2
  refine ⟨E.profile b, hrep, Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩, ?_⟩
  intro i hi hni
  obtain ⟨q, hqb, hqi⟩ := E.mem_profile_iff.mp hi
  rcases E.predecessors hqb hxb.le with hqx | hxq
  · have hi' : i ∈ E.profile x := E.mem_profile_iff.mpr ⟨q, hqx, hqi⟩
    exact False.elim (hni (hpx ▸ hi'))
  · rcases lt_or_eq_of_le hxq with hxq | heq
    · simpa [hqi] using E.label_gt_of_avoids_barriers hxB hba hxq hqb
    · have hi' : i ∈ E.profile x := E.mem_profile_iff.mpr ⟨q, heq.ge, hqi⟩
      exact False.elim (hni (hpx ▸ hi'))

/-- Equivalent finite-initial-segment formulation, directly usable for the
product topology on FIN or a characteristic-word translation. -/
theorem repeated_agrees_below {S : Set α} (hS : E.RichSubset S)
    {s : Finset ℕ} (hs : E.Repeated S s) (N : ℕ) :
    ∃ t, E.Repeated S t ∧ s ⊂ t ∧
      ∀ i, i ≤ N → (i ∈ t ↔ i ∈ s) := by
  obtain ⟨t, ht, hst, hnew⟩ := E.repeated_endExtension hS hs N
  refine ⟨t, ht, hst, ?_⟩
  intro i hi
  constructor
  · intro hit
    by_contra hnot
    have := hnew i hit hnot
    omega
  · intro his
    exact hst.subset his

end System
end AllThoseBigRamsey.Pseudotree.Profiles
