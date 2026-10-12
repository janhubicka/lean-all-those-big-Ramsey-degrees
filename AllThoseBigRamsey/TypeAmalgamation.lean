import AllThoseBigRamsey.FullTypeMaps

/-! Concrete finite-base continuation and full n-type amalgamation interfaces.
A single total map on types is chosen before the quantifier over continuations.
The predicates below do not assert that any particular class has amalgamation. -/
namespace AllThoseBigRamsey

/-- A finite base appears as the exact initial segment of an enumerated structure. -/
structure Continuation {L : Language} {a : Nat} (A : RelStructure L (Fin a)) where
  ambient : EnumeratedStructure L
  base : OrderedEmbedding (EnumeratedStructure.ofFin A) ambient
  base_index : ∀ x : Fin a, ambient.index (base.toFun x) = x.val

namespace Continuation
variable {L : Language} {a b c n : Nat}
variable {A : RelStructure L (Fin a)} {B : RelStructure L (Fin b)}
variable {C : RelStructure L (Fin c)}

/-- The base range is the whole finite prefix, not just an embedded substructure. -/
theorem mem_prefix (D : Continuation A) (x : D.ambient.Carrier)
    (hx : D.ambient.index x < a) :
    ∃ i : Fin a, D.base.toFun i = x := by
  refine ⟨⟨D.ambient.index x, hx⟩, ?_⟩
  apply D.ambient.enumeration.injective
  exact D.base_index _

/-- Strictly increasing tuples entirely beyond the finite base. -/
def FutureTuple (D : Continuation A) {k : Nat}
    (s : Fin k → D.ambient.Carrier) : Prop :=
  (∀ i, a ≤ D.ambient.index (s i)) ∧
  (∀ i j, i.val < j.val → D.ambient.index (s i) < D.ambient.index (s j))

/-- The formal names used by a future tuple denote distinct actual vertices. -/
theorem future_evaluate_injective (D : Continuation A) {k : Nat}
    {s : Fin k → D.ambient.Carrier} (hs : D.FutureTuple s)
    {x y : Sum (Fin a) (Fin k)}
    (h : evaluate D.base.toFun s x = evaluate D.base.toFun s y) : x = y := by
  cases x with
  | inl b =>
    cases y with
    | inl c => exact congrArg Sum.inl (D.base.injective h)
    | inr j =>
      have heq := congrArg D.ambient.index h
      change D.ambient.index (D.base.toFun b) = D.ambient.index (s j) at heq
      rw [D.base_index] at heq
      have hj := hs.1 j
      have hb := b.isLt
      omega
  | inr i =>
    cases y with
    | inl b =>
      have heq := congrArg D.ambient.index h
      change D.ambient.index (s i) = D.ambient.index (D.base.toFun b) at heq
      rw [D.base_index] at heq
      have hi := hs.1 i
      have hb := b.isLt
      omega
    | inr j =>
      have heq := congrArg D.ambient.index h
      change D.ambient.index (s i) = D.ambient.index (s j) at heq
      have hv : i.val = j.val := by
        by_cases hij : i.val < j.val
        · have hh := hs.2 i j hij
          omega
        by_cases hji : j.val < i.val
        · have hh := hs.2 j i hji
          omega
        omega
      exact congrArg Sum.inr (Fin.ext hv)

/-- The full diagram of the base and tuple. The FutureTuple hypotheses give
its realised-type interpretation, including disjointness and distinctness. -/
def typeOf (D : Continuation A) {k : Nat}
    (s : Fin k → D.ambient.Carrier) : FullType A k where
  diagram := D.ambient.relStructure.pullback (evaluate D.base.toFun s)
  over_base := fun R t => (D.base.map_rel R t).symm

/-- Equality is required on every prescribed full type, not just membership
in an image. No additional vertices are silently identified. -/
structure Approximates
    (F : FullTypeMap n (EnumeratedStructure.ofFin A) (EnumeratedStructure.ofFin B))
    (D : Continuation A) (E : Continuation B)
    (h : OrderedEmbedding D.ambient E.ambient) : Prop where
  on_base : ∀ i, h.toFun (D.base.toFun i) = E.base.toFun (F.base.toFun i)
  beyond_base : ∀ x, a ≤ D.ambient.index x → b ≤ E.ambient.index (h.toFun x)
  on_types : ∀ k hk (s : Fin k → D.ambient.Carrier), D.FutureTuple s →
    E.typeOf (fun i => h.toFun (s i)) = F.onType k hk (D.typeOf s)

namespace Approximates

theorem map_future
    {F : FullTypeMap n (EnumeratedStructure.ofFin A) (EnumeratedStructure.ofFin B)}
    {D : Continuation A} {E : Continuation B} {h : OrderedEmbedding D.ambient E.ambient}
    (hh : Approximates F D E h) {k : Nat} {s : Fin k → D.ambient.Carrier}
    (hs : D.FutureTuple s) : E.FutureTuple (fun i => h.toFun (s i)) :=
  ⟨fun i => hh.beyond_base (s i) (hs.1 i),
    fun i j hij => h.increasing (hs.2 i j hij)⟩

theorem id (D : Continuation A) (n : Nat) :
    Approximates (FullTypeMap.id (EnumeratedStructure.ofFin A) n) D D
      (OrderedEmbedding.id D.ambient) where
  on_base := fun _ => rfl
  beyond_base := fun _ hx => hx
  on_types := fun _ _ _ _ => rfl

theorem comp
    {F : FullTypeMap n (EnumeratedStructure.ofFin A) (EnumeratedStructure.ofFin B)}
    {G : FullTypeMap n (EnumeratedStructure.ofFin B) (EnumeratedStructure.ofFin C)}
    {D : Continuation A} {E : Continuation B} {V : Continuation C}
    {h : OrderedEmbedding D.ambient E.ambient} {g : OrderedEmbedding E.ambient V.ambient}
    (hh : Approximates F D E h) (hg : Approximates G E V g) :
    Approximates (FullTypeMap.comp G F) D V (OrderedEmbedding.comp g h) where
  on_base := by
    intro i
    change g.toFun (h.toFun (D.base.toFun i)) =
      V.base.toFun (G.base.toFun (F.base.toFun i))
    rw [hh.on_base, hg.on_base]
  beyond_base := fun x hx => hg.beyond_base _ (hh.beyond_base x hx)
  on_types := by
    intro k hk s hs
    change V.typeOf (fun i => g.toFun (h.toFun (s i))) =
      G.onType k hk (F.onType k hk (D.typeOf s))
    rw [hg.on_types k hk _ (hh.map_future hs), hh.on_types k hk s hs]
end Approximates
end Continuation

/-- Unrestricted uniform continuation property, separate from class membership. -/
def TypeRespectingMap {L : Language} {a b n : Nat}
    {A : RelStructure L (Fin a)} {B : RelStructure L (Fin b)}
    (F : FullTypeMap n (EnumeratedStructure.ofFin A) (EnumeratedStructure.ofFin B)) : Prop :=
  ∀ D : Continuation A, ∃ E : Continuation B,
    ∃ h : OrderedEmbedding D.ambient E.ambient,
      NTypeRespecting n h ∧ Continuation.Approximates F D E h

/-- `K` is evaluated on enumerated finite or countable structures. For a finite
age the application uses its finite/countable age closure here. -/
def ClassTypeRespectingMap {L : Language} (K : EnumeratedStructure L → Prop)
    {a b n : Nat} {A : RelStructure L (Fin a)} {B : RelStructure L (Fin b)}
    (F : FullTypeMap n (EnumeratedStructure.ofFin A) (EnumeratedStructure.ofFin B)) : Prop :=
  TypeRespectingMap F ∧
  ∀ D : Continuation A, K D.ambient → ∃ E : Continuation B,
    ∃ h : OrderedEmbedding D.ambient E.ambient,
      K E.ambient ∧ NTypeRespecting n h ∧ Continuation.Approximates F D E h

namespace TypeRespectingMap
variable {L : Language} {a b c n : Nat}
variable {A : RelStructure L (Fin a)} {B : RelStructure L (Fin b)}
variable {C : RelStructure L (Fin c)}

theorem id (A : RelStructure L (Fin a)) (n : Nat) :
    TypeRespectingMap (FullTypeMap.id (EnumeratedStructure.ofFin A) n) := by
  intro D
  exact ⟨D, OrderedEmbedding.id D.ambient, NTypeRespecting.id D.ambient n,
    Continuation.Approximates.id D n⟩

theorem comp
    {F : FullTypeMap n (EnumeratedStructure.ofFin A) (EnumeratedStructure.ofFin B)}
    {G : FullTypeMap n (EnumeratedStructure.ofFin B) (EnumeratedStructure.ofFin C)}
    (hf : TypeRespectingMap F) (hg : TypeRespectingMap G) :
    TypeRespectingMap (FullTypeMap.comp G F) := by
  intro D
  obtain ⟨E, f, hft, hfa⟩ := hf D
  obtain ⟨V, g, hgt, hga⟩ := hg E
  exact ⟨V, OrderedEmbedding.comp g f, NTypeRespecting.comp hft hgt, hfa.comp hga⟩
end TypeRespectingMap

namespace ClassTypeRespectingMap
variable {L : Language} {a b c n : Nat} {K : EnumeratedStructure L → Prop}
variable {A : RelStructure L (Fin a)} {B : RelStructure L (Fin b)}
variable {C : RelStructure L (Fin c)}

theorem id (K : EnumeratedStructure L → Prop) (A : RelStructure L (Fin a)) (n : Nat) :
    ClassTypeRespectingMap K (FullTypeMap.id (EnumeratedStructure.ofFin A) n) := by
  refine ⟨TypeRespectingMap.id A n, ?_⟩
  intro D hD
  exact ⟨D, OrderedEmbedding.id D.ambient, hD, NTypeRespecting.id D.ambient n,
    Continuation.Approximates.id D n⟩

theorem comp
    {F : FullTypeMap n (EnumeratedStructure.ofFin A) (EnumeratedStructure.ofFin B)}
    {G : FullTypeMap n (EnumeratedStructure.ofFin B) (EnumeratedStructure.ofFin C)}
    (hf : ClassTypeRespectingMap K F) (hg : ClassTypeRespectingMap K G) :
    ClassTypeRespectingMap K (FullTypeMap.comp G F) := by
  refine ⟨TypeRespectingMap.comp hf.1 hg.1, ?_⟩
  intro D hD
  obtain ⟨E, f, hE, hft, hfa⟩ := hf.2 D hD
  obtain ⟨V, g, hV, hgt, hga⟩ := hg.2 E hE
  exact ⟨V, OrderedEmbedding.comp g f, hV, NTypeRespecting.comp hft hgt, hfa.comp hga⟩
end ClassTypeRespectingMap

/-- Literal extension by one new final vertex. -/
def ExtendsByLast {L : Language} {b : Nat}
    (B : RelStructure L (Fin b)) (B' : RelStructure L (Fin (b+1))) : Prop :=
  ∀ R t, B.rel R t ↔ B'.rel R (fun i => (t i).castSucc)

/-- The requested full n-type-respecting amalgamation property, with all
continuation quantifiers inside the predicate on the single chosen map H. -/
def NTypeRespectingAmalgamation {L : Language}
    (K : EnumeratedStructure L → Prop) (n : Nat) : Prop :=
  ∀ a b (A : RelStructure L (Fin a)) (B : RelStructure L (Fin b))
    (B' : RelStructure L (Fin (b+1))),
    K (EnumeratedStructure.ofFin A) → K (EnumeratedStructure.ofFin B) →
    K (EnumeratedStructure.ofFin B') → ExtendsByLast B B' →
    ∀ (F : FullTypeMap n (EnumeratedStructure.ofFin A) (EnumeratedStructure.ofFin B))
      (F' : FullTypeMap n (EnumeratedStructure.ofFin A) (EnumeratedStructure.ofFin B'))
      (G : FullTypeMap n (EnumeratedStructure.ofFin B) (EnumeratedStructure.ofFin B')),
      ClassTypeRespectingMap K F → ClassTypeRespectingMap K F' →
      TypeRespectingMap G → (∀ i, G.base.toFun i = i.castSucc) →
      FullTypeMap.comp G F = F' →
      ∃ H : FullTypeMap n (EnumeratedStructure.ofFin B) (EnumeratedStructure.ofFin B'),
        ClassTypeRespectingMap K H ∧ (∀ i, H.base.toFun i = i.castSucc) ∧
        FullTypeMap.comp H F = F'

/-- The maximum arity is the same checked parameter used for embeddings. -/
def TypeRespectingAmalgamation {L : Language}
    (K : EnumeratedStructure L → Prop) (r : MaximumArity L) : Prop :=
  NTypeRespectingAmalgamation K (r.value - 1)
end AllThoseBigRamsey
