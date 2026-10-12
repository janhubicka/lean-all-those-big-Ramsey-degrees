import Std

/-!
# Anchored uniform repair for asymmetric pair types

T a b c is the triangle with labels 01=a, 12=b, 02=c. An involution
reverses pair labels. One fixed source anchor supplies a compatible seed.
The theorem processes any finite list of additional anchors on an arbitrary
type set, before choosing a continuation. The relational bridge is separate.
-/
namespace AllThoseBigRamsey.DirectedTriangleRepair

universe u v w

structure LocalLaws {C : Type u} (T : C → C → C → Prop)
    (r : C → C → C → C) : Prop where
  valid : ∀ s a h, T s a (r s a h)
  fixed : ∀ s a h, T s a h → r s a h = h
  pairs : ∀ s a a' h h' t, T a t a' → T h t h' →
    T (r s a h) t (r s a' h')

/-- u=v-to-root, v=root-to-anchor, w=v-to-anchor;
p=root-to-future, q=anchor-to-future, h=old v-to-future. -/
structure AnchoredLaws {C : Type u} (T : C → C → C → Prop)
    (r : C → C → C → C → C → C → C) : Prop where
  valid : ∀ u v w p q h, T u v w → T v q p → T u p h →
    T u p (r u v w p q h) ∧ T w q (r u v w p q h)
  fixed : ∀ u v w p q h, T u v w → T v q p → T u p h →
    T w q h → r u v w p q h = h
  pairs : ∀ u v w p q h p' q' h' t,
    T u v w → T v q p → T u p h → T v q' p' → T u p' h' →
    T p t p' → T q t q' → T h t h' →
    T (r u v w p q h) t (r u v w p' q' h')

structure Problem (C : Type u) (B : Type v) (Q : Type w) where
  T : C → C → C → Prop
  rev : C → C
  involution : ∀ c, rev (rev c) = c
  swapLast : ∀ a b c, T a b c → T c (rev b) a
  root : C
  rootBase : B → C
  newBase : B → C
  profileRoot : Q → C
  profile : Q → B → C
  edge : B → B → C
  possiblePair : Q → Q → C → Prop
  baseRoot : ∀ b, T root (rootBase b) (newBase b)
  typeRoot : ∀ x b, T (rootBase b) (profile x b) (profileRoot x)
  basePair : ∀ b c, b ≠ c → T (newBase b) (edge b c) (newBase c)
  rootBasePair : ∀ b c, b ≠ c → T (rootBase b) (edge b c) (rootBase c)
  typeBasePair : ∀ x b c, b ≠ c → T (edge b c) (profile x c) (profile x b)
  pairRoot : ∀ x y t, possiblePair x y t → T (profileRoot x) t (profileRoot y)
  pairBase : ∀ x y t, possiblePair x y t → ∀ b, T (profile x b) t (profile y b)

namespace Problem
variable {C : Type u} {B : Type v} {Q : Type w}
variable (D : Problem C B Q) (r : C → C → C → C → C → C → C)
variable (laws : AnchoredLaws D.T r)

def Root (h : Q → C) : Prop := ∀ x, D.T D.root (D.profileRoot x) (h x)
def Pairs (h : Q → C) : Prop :=
  ∀ x y t, D.possiblePair x y t → D.T (h x) t (h y)
def At (h : Q → C) (b : B) : Prop := ∀ x, D.T (D.newBase b) (D.profile x b) (h x)

def step (b : B) (h : Q → C) : Q → C :=
  fun x => r D.root (D.rootBase b) (D.newBase b)
    (D.profileRoot x) (D.profile x b) (h x)

theorem step_root (b : B) (h : Q → C) (hr : D.Root h) :
    D.Root (D.step r b h) := by
  intro x
  exact (laws.valid _ _ _ _ _ _ (D.baseRoot b) (D.typeRoot x b) (hr x)).1

theorem step_at (b : B) (h : Q → C) (hr : D.Root h) :
    D.At (D.step r b h) b := by
  intro x
  exact (laws.valid _ _ _ _ _ _ (D.baseRoot b) (D.typeRoot x b) (hr x)).2

theorem step_pairs (b : B) (h : Q → C) (hr : D.Root h) (hp : D.Pairs h) :
    D.Pairs (D.step r b h) := by
  intro x y t ht
  exact laws.pairs _ _ _ _ _ _ _ _ _ _ (D.baseRoot b)
    (D.typeRoot x b) (hr x) (D.typeRoot y b) (hr y)
    (D.pairRoot x y t ht) (D.pairBase x y t ht b) (hp x y t ht)

theorem step_preserves_at (b c : B) (h : Q → C)
    (hr : D.Root h) (hc : D.At h c) : D.At (D.step r b h) c := by
  classical
  by_cases he : b = c
  · subst c
    exact D.step_at r laws b h hr
  · intro x
    have fix := laws.fixed D.root (D.rootBase b) (D.newBase b)
      (D.rootBase c) (D.edge b c) (D.newBase c)
      (D.baseRoot b) (D.rootBasePair b c he) (D.baseRoot c) (D.basePair b c he)
    have hp := laws.pairs D.root (D.rootBase b) (D.newBase b)
      (D.profileRoot x) (D.profile x b) (h x)
      (D.rootBase c) (D.edge b c) (D.newBase c) (D.rev (D.profile x c))
      (D.baseRoot b) (D.typeRoot x b) (hr x)
      (D.rootBasePair b c he) (D.baseRoot c)
      (D.swapLast _ _ _ (D.typeRoot x c))
      (D.swapLast _ _ _ (D.typeBasePair x b c he))
      (D.swapLast _ _ _ (hc x))
    rw [fix] at hp
    have out := D.swapLast _ _ _ hp
    rw [D.involution] at out
    exact out

def run : List B → (Q → C) → Q → C
  | [], h => h
  | b :: bs, h => D.run r bs (D.step r b h)

theorem run_root (bs : List B) (h : Q → C) (hr : D.Root h) :
    D.Root (D.run r bs h) := by
  induction bs generalizing h with
  | nil => exact hr
  | cons b bs ih => exact ih (D.step r b h) (D.step_root r laws b h hr)

theorem run_pairs (bs : List B) (h : Q → C) (hr : D.Root h) (hp : D.Pairs h) :
    D.Pairs (D.run r bs h) := by
  induction bs generalizing h with
  | nil => exact hp
  | cons b bs ih =>
    exact ih (D.step r b h) (D.step_root r laws b h hr) (D.step_pairs r laws b h hr hp)

theorem run_preserves_at (bs : List B) (h : Q → C) (hr : D.Root h)
    (c : B) (hc : D.At h c) : D.At (D.run r bs h) c := by
  induction bs generalizing h with
  | nil => exact hc
  | cons b bs ih =>
    exact ih (D.step r b h) (D.step_root r laws b h hr)
      (D.step_preserves_at r laws b c h hr hc)

theorem run_covers (bs : List B) (h : Q → C) (hr : D.Root h)
    (c : B) (hc : c ∈ bs) : D.At (D.run r bs h) c := by
  induction bs generalizing h with
  | nil => cases hc
  | cons b bs ih =>
    rcases List.mem_cons.mp hc with he | ht
    · subst c
      exact D.run_preserves_at r laws bs (D.step r b h)
        (D.step_root r laws b h hr) b (D.step_at r laws b h hr)
    · exact ih (D.step r b h) (D.step_root r laws b h hr) ht

theorem run_fixed (bs : List B) (h : Q → C) (hr : D.Root h) (x : Q)
    (hx : ∀ b ∈ bs, D.T (D.newBase b) (D.profile x b) (h x)) :
    D.run r bs h x = h x := by
  induction bs generalizing h with
  | nil => rfl
  | cons b bs ih =>
    have hb : D.step r b h x = h x := laws.fixed _ _ _ _ _ _
      (D.baseRoot b) (D.typeRoot x b) (hr x) (hx b List.mem_cons_self)
    have ht : ∀ c ∈ bs, D.T (D.newBase c) (D.profile x c) (D.step r b h x) := by
      intro c hc
      rw [hb]
      exact hx c (List.mem_cons_of_mem b hc)
    exact (ih (D.step r b h) (D.step_root r laws b h hr) ht).trans hb

/-- One rule works at every anchor, with no bound on the base or type set. -/
theorem uniform_choice (bs : List B) (covers : ∀ b, b ∈ bs)
    (h : Q → C) (hr : D.Root h) (hp : D.Pairs h) :
    D.Root (D.run r bs h) ∧ D.Pairs (D.run r bs h) ∧
    (∀ b, D.At (D.run r bs h) b) ∧
    (∀ x, (∀ b, D.T (D.newBase b) (D.profile x b) (h x)) →
      D.run r bs h x = h x) := by
  exact ⟨D.run_root r laws bs h hr, D.run_pairs r laws bs h hr hp,
    fun b => D.run_covers r laws bs h hr b (covers b),
    fun x hx => D.run_fixed r laws bs h hr x (fun b _ => hx b)⟩

end Problem
end AllThoseBigRamsey.DirectedTriangleRepair
