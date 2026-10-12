import AllThoseBigRamsey.DirectedTriangleRepair

/-!
# Certificates for all triangle classes of oriented graphs

Pair labels: 0 is forward, 1 backward, 2 absent. Triangle coordinates are
(01,12,02). The seven orbits, in bit order, are transitive tournament,
cyclic tournament, directed path, in-star, out-star, single arc, empty.
All 128 palettes are tested. Sixteen pass the genuine small-amalgamation
condition, fifteen have local repairs, and palette 37 has anchored repairs.
All closed checks use kernel `decide`; no solver output is trusted.
-/
namespace AllThoseBigRamsey.DirectedTriangleCertificates

set_option maxSynthPendingDepth 1000

abbrev Colour := Fin 3

def reverse (a : Colour) : Colour :=
  if a = 0 then 1 else if a = 1 then 0 else 2

def orbit (a b c : Colour) : Nat :=
  match 9 * a.val + 3 * b.val + c.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 0 | 5 => 3
  | 6 => 4 | 7 => 2 | 8 => 5 | 9 => 0 | 10 => 0 | 11 => 4
  | 12 => 1 | 13 => 0 | 14 => 2 | 15 => 2 | 16 => 3 | 17 => 5
  | 18 => 3 | 19 => 2 | 20 => 5 | 21 => 2 | 22 => 4 | 23 => 5
  | 24 => 5 | 25 => 5 | _ => 6

def Triangle (palette : Fin 128) (a b c : Colour) : Prop :=
  palette.val.testBit (orbit a b c) = true

instance (palette : Fin 128) (a b c : Colour) : Decidable (Triangle palette a b c) := by
  unfold Triangle
  infer_instance

def SmallSAP (palette : Fin 128) : Prop :=
  (∀ a b : Colour, ∃ t : Colour, Triangle palette a t b) ∧
  (∀ edge p₀ p₁ q₀ q₁ : Colour,
    Triangle palette edge p₁ p₀ → Triangle palette edge q₁ q₀ →
    ∃ t : Colour, Triangle palette p₀ t q₀ ∧ Triangle palette p₁ t q₁) ∧
  (∀ ab ac bc p₀ p₁ p₂ q₀ q₁ q₂ : Colour,
    Triangle palette ab bc ac →
    Triangle palette ab p₁ p₀ → Triangle palette ac p₂ p₀ → Triangle palette bc p₂ p₁ →
    Triangle palette ab q₁ q₀ → Triangle palette ac q₂ q₀ → Triangle palette bc q₂ q₁ →
    ∃ t : Colour, Triangle palette p₀ t q₀ ∧ Triangle palette p₁ t q₁ ∧
      Triangle palette p₂ t q₂)

def Listed (palette : Fin 128) : Prop :=
  palette.val ∈ [33, 35, 37, 63, 89, 90, 91, 92, 95, 97, 99, 121, 124, 125, 126, 127]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_classification : ∀ palette : Fin 128, SmallSAP palette ↔ Listed palette := by
  unfold SmallSAP Listed Triangle
  decide

theorem reverse_reverse : ∀ a : Colour, reverse (reverse a) = a := by decide

theorem swap_last : ∀ palette : Fin 128, ∀ a b c : Colour,
    Triangle palette a b c → Triangle palette c (reverse b) a := by
  unfold Triangle
  decide

def localData (palette : Fin 128) : Nat :=
  match palette.val with
  | 33 => 1129710783834 | 35 => 1129705469427 | 63 => 1075404773523
  | 89 => 7479346398579 | 90 => 7479339588409 | 91 => 7479341084172
  | 92 => 7375768648442 | 95 => 7375765892682 | 97 => 6213442440492
  | 99 => 6213437126085 | 121 => 6181243846506 | 124 => 6159139185941
  | 125 => 6159137493066 | 126 => 6159138123056 | 127 => 6159136430181
  | _ => 0

def localRepair (palette : Fin 128) (s a h : Colour) : Colour :=
  ⟨(localData palette / 3 ^ (9 * s.val + 3 * a.val + h.val)) % 3,
    Nat.mod_lt _ (by decide)⟩

def LocalChecks (palette : Fin 128) : Prop :=
  (∀ s a h : Colour, Triangle palette s a (localRepair palette s a h)) ∧
  (∀ s a h : Colour, Triangle palette s a h → localRepair palette s a h = h) ∧
  (∀ s a a' h h' t : Colour, Triangle palette a t a' → Triangle palette h t h' →
    Triangle palette (localRepair palette s a h) t (localRepair palette s a' h'))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem local_certificates : ∀ palette : Fin 128,
    Listed palette → palette.val ≠ 37 → LocalChecks palette := by
  unfold Listed LocalChecks Triangle
  decide

theorem local_laws (palette : Fin 128) (hp : SmallSAP palette) (he : palette.val ≠ 37) :
    DirectedTriangleRepair.LocalLaws (Triangle palette) (localRepair palette) := by
  have h := local_certificates palette ((small_classification palette).mp hp) he
  exact ⟨h.1, h.2.1, h.2.2⟩

def anchoredData (u v w : Colour) : Nat :=
  match 9 * u.val + 3 * v.val + w.val with
  | 0 => 5940377347806 | 2 => 3397333315268 | 3 => 6056546113458
  | 4 => 6997978490742 | 7 => 224316535842 | 8 => 259227433080
  | 9 => 5655872002842 | 10 => 5084087190798 | 13 => 5292950117178
  | 14 => 188299527772 | 15 => 7275371238 | 17 => 196207369848
  | 19 => 1431171192 | 20 => 848847858006 | 21 => 1161099575160
  | 23 => 847298577810 | 24 => 31668407676 | 25 => 43261972668
  | _ => 0

def anchoredRepair (u v w p q h : Colour) : Colour :=
  ⟨(anchoredData u v w / 3 ^ (9 * p.val + 3 * q.val + h.val)) % 3,
    Nat.mod_lt _ (by decide)⟩

abbrev ExceptionalTriangle := Triangle (⟨37, by decide⟩ : Fin 128)

def AnchoredChecks : Prop :=
  (∀ u v w p q h : Colour,
    ExceptionalTriangle u v w → ExceptionalTriangle v q p → ExceptionalTriangle u p h →
    ExceptionalTriangle u p (anchoredRepair u v w p q h) ∧
    ExceptionalTriangle w q (anchoredRepair u v w p q h)) ∧
  (∀ u v w p q h : Colour,
    ExceptionalTriangle u v w → ExceptionalTriangle v q p → ExceptionalTriangle u p h →
    ExceptionalTriangle w q h → anchoredRepair u v w p q h = h) ∧
  (∀ u v w p q h p' q' h' t : Colour,
    ExceptionalTriangle u v w → ExceptionalTriangle v q p → ExceptionalTriangle u p h →
    ExceptionalTriangle v q' p' → ExceptionalTriangle u p' h' →
    ExceptionalTriangle p t p' → ExceptionalTriangle q t q' → ExceptionalTriangle h t h' →
    ExceptionalTriangle (anchoredRepair u v w p q h) t (anchoredRepair u v w p' q' h'))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem anchored_certificate : AnchoredChecks := by
  unfold AnchoredChecks ExceptionalTriangle Triangle
  decide

theorem anchored_laws : DirectedTriangleRepair.AnchoredLaws ExceptionalTriangle anchoredRepair :=
  ⟨anchored_certificate.1, anchored_certificate.2.1, anchored_certificate.2.2⟩

/-- An incomparable pair cannot share any prescribed profile at a new base point.
Thus the exceptional class has no admissible empty-to-nonempty type map. -/
theorem no_empty_rule : ∀ h : Colour, ¬ ExceptionalTriangle h 2 h := by
  unfold ExceptionalTriangle Triangle
  decide

/-- The strict relation encoded by the three oriented pair labels. -/
def relation (a b c : Colour) (i j : Fin 3) : Prop :=
  (i = 0 ∧ j = 1 ∧ a = 0) ∨ (i = 1 ∧ j = 0 ∧ a = 1) ∨
  (i = 1 ∧ j = 2 ∧ b = 0) ∨ (i = 2 ∧ j = 1 ∧ b = 1) ∨
  (i = 0 ∧ j = 2 ∧ c = 0) ∨ (i = 2 ∧ j = 0 ∧ c = 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem poset_triangle_iff : ∀ a b c : Colour,
    Triangle ⟨121, by decide⟩ a b c ↔
    ∀ i j k : Fin 3, relation a b c i j → relation a b c j k → relation a b c i k := by
  unfold Triangle relation
  decide

end AllThoseBigRamsey.DirectedTriangleCertificates
