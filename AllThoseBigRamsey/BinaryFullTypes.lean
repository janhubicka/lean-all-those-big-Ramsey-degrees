import AllThoseBigRamsey.FullTypes

/-! Reconstruction of a full binary type from its singleton restrictions and
its whole future diagram. Unary and diagonal information is not discarded. -/
namespace AllThoseBigRamsey

namespace RelStructure

theorem ext_rel {L : Language} {α : Type} {A B : RelStructure L α}
    (h : ∀ R q, A.rel R q ↔ B.rel R q) : A = B := by
  cases A with
  | mk a =>
    cases B with
    | mk b =>
      have hab : a = b := funext (fun R => funext (fun q => propext (h R q)))
      cases hab
      rfl
end RelStructure

namespace FullType

theorem ext_diagram {L : Language} {α : Type} {A : RelStructure L α}
    {k : Nat} {p q : FullType A k}
    (h : ∀ R t, p.diagram.rel R t ↔ q.diagram.rel R t) : p = q := by
  have hd : p.diagram = q.diagram := RelStructure.ext_rel h
  cases p
  cases q
  cases hd
  rfl

/-- Complete information on the future tuple, including internal relations. -/
def futureDiagram {L : Language} {α : Type} {A : RelStructure L α}
    {k : Nat} (p : FullType A k) : RelStructure L (Fin k) :=
  p.diagram.pullback Sum.inr

private theorem fin_two_cover {n : Nat} (hn : n ≤ 2)
    (i j t : Fin n) (hij : i ≠ j) : t = i ∨ t = j := by
  by_cases hi : t = i
  · exact Or.inl hi
  · right
    apply Fin.ext
    have hival := i.isLt
    have hjval := j.isLt
    have htval := t.isLt
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hti : t.val ≠ i.val := fun h => hi (Fin.ext h)
    omega

/-- Two full types are equal if their future diagrams and all singleton
restrictions agree. This is false if the future-diagram premise is dropped. -/
theorem binary_ext {L : Language} (binary : ∀ R, L.arity R ≤ 2)
    {α : Type} {A : RelStructure L α} {k : Nat} {p q : FullType A k}
    (single : ∀ j : Fin k,
      p.restrict (fun _ : Fin 1 => j) = q.restrict (fun _ : Fin 1 => j))
    (future : p.futureDiagram = q.futureDiagram) : p = q := by
  classical
  apply ext_diagram
  intro R t
  by_cases ht : ∃ j : Fin k, ∃ i, t i = Sum.inr j
  · obtain ⟨j, i, hi⟩ := ht
    by_cases hb : ∃ a : α, ∃ b, t b = Sum.inl a
    · obtain ⟨a, b, hb⟩ := hb
      have hib : i ≠ b := by
        intro heq
        have h := hi
        rw [heq, hb] at h
        cases h
      have hj : ∀ d u, t d = Sum.inr u → u = j := by
        intro d u hu
        rcases fin_two_cover (binary R) i b d hib with hd | hd
        · rw [hd, hi] at hu
          exact (Sum.inr.inj hu).symm
        · rw [hd, hb] at hu
          cases hu
      let small : Fin (L.arity R) → Sum α (Fin 1) := fun d =>
        match t d with
        | .inl x => .inl x
        | .inr _ => .inr 0
      have hnames : (fun d => Sum.map (fun x : α => x) (fun _ : Fin 1 => j) (small d)) = t := by
        funext d
        dsimp [small]
        cases hd : t d with
        | inl x => rfl
        | inr u =>
          have hu := hj d u hd
          cases hu
          rfl
      have heq := congrArg (fun z : FullType A 1 => z.diagram.rel R small) (single j)
      have he : p.diagram.rel R t = q.diagram.rel R t := by
        change p.diagram.rel R (fun d => Sum.map (fun x => x) (fun _ : Fin 1 => j) (small d)) =
          q.diagram.rel R (fun d => Sum.map (fun x => x) (fun _ : Fin 1 => j) (small d)) at heq
        simpa only [hnames] using heq
      exact Iff.of_eq he
    · have noBase : ∀ d a, t d ≠ Sum.inl a := by
        intro d a h
        exact hb ⟨a, d, h⟩
      let names : Fin (L.arity R) → Fin k := fun d =>
        match hd : t d with
        | .inl a => False.elim (noBase d a hd)
        | .inr j => j
      have hnames : (fun d => Sum.inr (names d)) = t := by
        funext d
        dsimp [names]
        cases hd : t d with
        | inl a => exact False.elim (noBase d a hd)
        | inr j => rfl
      have heq := congrArg (fun z : RelStructure L (Fin k) => z.rel R names) future
      change p.diagram.rel R (fun d => Sum.inr (names d)) =
        q.diagram.rel R (fun d => Sum.inr (names d)) at heq
      exact Iff.of_eq (by simpa only [hnames] using heq)
  · have noFuture : ∀ d j, t d ≠ Sum.inr j := by
      intro d j h
      exact ht ⟨j, d, h⟩
    let names : Fin (L.arity R) → α := fun d =>
      match hd : t d with
      | .inl a => a
      | .inr j => False.elim (noFuture d j hd)
    have hnames : (fun d => Sum.inl (names d)) = t := by
      funext d
      dsimp [names]
      cases hd : t d with
      | inl a => rfl
      | inr j => exact False.elim (noFuture d j hd)
    have hp := p.over_base R names
    have hq := q.over_base R names
    rw [hnames] at hp hq
    exact hp.trans hq.symm
end FullType
end AllThoseBigRamsey
