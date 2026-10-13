import Std

/-!
# Canonical socle induction

A finite, nonempty list of locally admissible solutions is ordered once.
Taking its head yields a deterministic extension depending only on the socle
and the previously chosen completion. This verifies the prefix/compatibility
part of the transfer. It does not establish the local TRAP premises.
-/
namespace AllThoseBigRamsey.CanonicalSocle

universe u v w

structure FiniteProblem (Output : Type v) where
  options : List Output
  nonempty : options ≠ []

def FiniteProblem.choose {Output : Type v} (P : FiniteProblem Output) : Output :=
  P.options.head P.nonempty

theorem FiniteProblem.choose_mem {Output : Type v} (P : FiniteProblem Output) :
    P.choose ∈ P.options := by
  cases P with
  | mk options nonempty =>
    cases options with
    | nil => contradiction
    | cons a tail => simp [FiniteProblem.choose]

/-- At a socle, allowable outputs are a finite nonempty list. The list may
depend on the source history and on the already completed output history. -/
structure Scheme (Input : Type u) (Output : Type v) where
  options : List Input → List Output → Input → List Output
  nonempty : ∀ xs ys a, options xs ys a ≠ []

namespace Scheme
variable {Input : Type u} {Output : Type v} (S : Scheme Input Output)

def select (xs : List Input) (ys : List Output) (a : Input) : Output :=
  (S.options xs ys a).head (S.nonempty xs ys a)

def step (s : List Input × List Output) (a : Input) : List Input × List Output :=
  (s.1 ++ [a], s.2 ++ [S.select s.1 s.2 a])

def state (xs : List Input) : List Input × List Output :=
  xs.foldl S.step ([], [])

def complete (xs : List Input) : List Output := (S.state xs).2

def Prefix {α : Type w} (xs ys : List α) : Prop := ∃ rest, ys = xs ++ rest

theorem prefix_refl {α : Type w} (xs : List α) : Prefix xs xs := by
  exact ⟨[], by simp⟩

theorem prefix_trans {α : Type w} {xs ys zs : List α}
    (h : Prefix xs ys) (g : Prefix ys zs) : Prefix xs zs := by
  rcases h with ⟨a, rfl⟩
  rcases g with ⟨b, rfl⟩
  exact ⟨a ++ b, by simp [List.append_assoc]⟩

private theorem foldl_prefix (s : List Input × List Output) (tail : List Input) :
    Prefix s.2 ((tail.foldl S.step s).2) := by
  induction tail generalizing s with
  | nil => exact prefix_refl s.2
  | cons a rest ih =>
    have h : Prefix s.2 (S.step s a).2 :=
      ⟨[S.select s.1 s.2 a], rfl⟩
    exact prefix_trans h (ih (S.step s a))

/-- A canonical extension of a longer socle retains every earlier output. -/
theorem complete_append_prefix (xs tail : List Input) :
    Prefix (S.complete xs) (S.complete (xs ++ tail)) := by
  simpa [complete, state, List.foldl_append] using
    (S.foldl_prefix (S.state xs) tail)

private theorem foldl_input (s : List Input × List Output) (tail : List Input) :
    (tail.foldl S.step s).1 = s.1 ++ tail := by
  induction tail generalizing s with
  | nil => simp
  | cons a rest ih =>
    simpa [step, List.append_assoc] using (ih (S.step s a))

theorem state_input (xs : List Input) : (S.state xs).1 = xs := by
  simpa [state] using (S.foldl_input ([], []) xs)

structure TypeNode (Label : Type w) (α : Type u) where
  socle : List α
  typeData : Label

def TypeNode.Compatible {Label : Type w} {α : Type u}
    (p q : TypeNode Label α) : Prop := p.socle = q.socle

def liftNode {Label : Type w} (p : TypeNode Label Input) : TypeNode Label Output :=
  ⟨S.complete p.socle, p.typeData⟩

theorem preserves_compatibility {Label : Type w} {p q : TypeNode Label Input}
    (h : p.Compatible q) : (S.liftNode p).Compatible (S.liftNode q) := by
  exact congrArg S.complete h

/-- A decoder is additional faithful coding data; TRAP does not imply it. -/
def Faithful (decode : Output → Input) : Prop :=
  ∀ xs ys a, decode (S.select xs ys a) = a

private theorem foldl_decode (decode : Output → Input) (h : S.Faithful decode)
    (s : List Input × List Output) (tail : List Input)
    (hs : s.2.map decode = s.1) :
    ((tail.foldl S.step s).2).map decode = (tail.foldl S.step s).1 := by
  induction tail generalizing s with
  | nil => exact hs
  | cons a rest ih =>
    apply ih (S.step s a)
    have hv : decode (S.select s.1 s.2 a) = a := h _ _ _
    simp [step, List.map_append, hs, hv]

theorem decode_complete (decode : Output → Input) (h : S.Faithful decode)
    (xs : List Input) : (S.complete xs).map decode = xs := by
  have hp := S.foldl_decode decode h ([], []) xs (by simp)
  calc
    (S.complete xs).map decode = (S.state xs).1 := hp
    _ = xs := S.state_input xs

theorem map_prefix {α : Type w} {β : Type u} (f : α → β)
    {xs ys : List α} (h : Prefix xs ys) : Prefix (xs.map f) (ys.map f) := by
  rcases h with ⟨tail, rfl⟩
  exact ⟨tail.map f, by simp [List.map_append]⟩

/-- Reflection needs a decoder, not merely a first-solution choice. -/
theorem reflects_prefix_of_faithful (decode : Output → Input)
    (hfaith : S.Faithful decode) {xs ys : List Input}
    (h : Prefix (S.complete xs) (S.complete ys)) : Prefix xs ys := by
  have h' := map_prefix decode h
  simpa only [S.decode_complete decode hfaith] using h'

end Scheme

/-- The visible composite is independent of how an amalgamation solution
is filled in outside the prescribed image. -/
theorem visible_independent {A : Type u} {B : Type v} {C : Type w}
    (F : A → B) (G H : B → C)
    (h : ∀ a, G (F a) = H (F a)) :
    (fun a => G (F a)) = (fun a => H (F a)) := funext h

end AllThoseBigRamsey.CanonicalSocle
