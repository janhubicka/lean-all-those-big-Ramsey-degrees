import Std

/-!
# Uniform repair of triangle rules

The colour rule is constructed on an arbitrary type set Q, before any
continuation is chosen. No finiteness of Q or bound on the base size is used.
The bridge to relational full-type maps is a separate manuscript argument.
-/
namespace AllThoseBigRamsey.TriangleRepair

universe u v w

structure RepairSystem (C : Type u) (T : C → C → C → Prop) where
  repair : C → C → C → C
  valid : ∀ s x h, T s x (repair s x h)
  fixed : ∀ s x h, T s x h → repair s x h = h
  pairs : ∀ s x y h k d, T x y d → T h k d →
    T (repair s x h) (repair s y k) d

variable {C : Type u} {B : Type v} {Q : Type w}
variable {T : C → C → C → Prop}

/-- Correct the rule at one base vertex. -/
def step (R : RepairSystem C T) (s : B → C) (q : Q → B → C)
    (b : B) (h : Q → C) : Q → C :=
  fun x => R.repair (s b) (q x b) (h x)

/-- A finite list specifies the order in which base vertices are processed. -/
def run (R : RepairSystem C T) (s : B → C) (q : Q → B → C) :
    List B → (Q → C) → Q → C
  | [], h => h
  | b :: bs, h => run R s q bs (step R s q b h)

/-- Every already admissible protected value is unchanged. -/
theorem run_fixed (R : RepairSystem C T) (s : B → C) (q : Q → B → C)
    (bs : List B) (h : Q → C) (x : Q)
    (hx : ∀ b ∈ bs, T (s b) (q x b) (h x)) :
    run R s q bs h x = h x := by
  induction bs generalizing h with
  | nil => rfl
  | cons b bs ih =>
    have hb : step R s q b h x = h x :=
      R.fixed _ _ _ (hx b (List.mem_cons_self))
    have ht : ∀ c ∈ bs, T (s c) (q x c) (step R s q b h x) := by
      intro c hc
      rw [hb]
      exact hx c (List.mem_cons_of_mem b hc)
    exact (ih (step R s q b h) ht).trans hb

/-- All allowed future-pair colours remain allowed at every stage. -/
theorem run_pairs (R : RepairSystem C T) (s : B → C) (q : Q → B → C)
    (P : Q → Q → C → Prop)
    (profile : ∀ x y d, P x y d → ∀ b, T (q x b) (q y b) d)
    (bs : List B) (h : Q → C)
    (hh : ∀ x y d, P x y d → T (h x) (h y) d) :
    ∀ x y d, P x y d → T (run R s q bs h x) (run R s q bs h y) d := by
  induction bs generalizing h with
  | nil => exact hh
  | cons b bs ih =>
    apply ih (step R s q b h)
    intro x y d hd
    exact R.pairs _ _ _ _ _ _ (profile x y d hd b) (hh x y d hd)

variable (rotate : ∀ a b c, T a b c → T c a b)
variable (R : RepairSystem C T) (s : B → C) (q : Q → B → C)
variable (edge : B → B → C)
variable (base : ∀ b c, b ≠ c → T (s b) (edge b c) (s c))
variable (profile : ∀ x b c, b ≠ c → T (q x b) (edge b c) (q x c))

def AtAnchor (T : C → C → C → Prop) (s : B → C) (q : Q → B → C) (h : Q → C) (c : B) : Prop :=
  ∀ x, T (h x) (s c) (q x c)

include rotate edge base profile

/-- Correcting b cannot undo a previously correct anchor c. -/
theorem step_anchor (b c : B) (h : Q → C) (hc : AtAnchor T s q h c) :
    AtAnchor T s q (step R s q b h) c := by
  classical
  intro x
  by_cases he : b = c
  · subst c
    exact rotate _ _ _ (R.valid _ _ _)
  · have hp := R.pairs (s b) (q x b) (edge b c) (h x) (s c) (q x c)
      (profile x b c he) (hc x)
    rw [R.fixed _ _ _ (base b c he)] at hp
    exact hp

theorem run_anchor (bs : List B) (h : Q → C) (c : B)
    (hc : AtAnchor T s q h c) : AtAnchor T s q (run R s q bs h) c := by
  induction bs generalizing h with
  | nil => exact hc
  | cons b bs ih =>
    apply ih (step R s q b h)
    exact step_anchor rotate R s q edge base profile b c h hc

/-- Every anchor occurring in the list is correct at the end. -/
theorem run_covers (bs : List B) (h : Q → C) (c : B) (hc : c ∈ bs) :
    AtAnchor T s q (run R s q bs h) c := by
  induction bs generalizing h with
  | nil => cases hc
  | cons b bs ih =>
    rcases List.mem_cons.mp hc with he | ht
    · subst c
      apply run_anchor rotate R s q edge base profile bs (step R s q b h) b
      intro x
      exact rotate _ _ _ (R.valid _ _ _)
    · exact ih (step R s q b h) ht

/-- The actual simultaneous-choice invariant: all anchors, all possible future
pairs, and all protected values, without quantifying over a chosen continuation. -/
theorem uniform_choice (P : Q → Q → C → Prop)
    (pairsProfile : ∀ x y d, P x y d → ∀ b, T (q x b) (q y b) d)
    (bs : List B) (covers : ∀ b, b ∈ bs) (h : Q → C)
    (seed : ∀ x y d, P x y d → T (h x) (h y) d)
    (marked : Q → Prop)
    (protectedValid : ∀ x, marked x → ∀ b, T (s b) (q x b) (h x)) :
    (∀ b, AtAnchor T s q (run R s q bs h) b) ∧
    (∀ x y d, P x y d → T (run R s q bs h x) (run R s q bs h y) d) ∧
    (∀ x, marked x → run R s q bs h x = h x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    exact run_covers rotate R s q edge base profile bs h b (covers b)
  · exact run_pairs R s q P pairsProfile bs h seed
  · intro x hx
    exact run_fixed R s q bs h x (fun b _ => protectedValid x hx b)

end AllThoseBigRamsey.TriangleRepair
