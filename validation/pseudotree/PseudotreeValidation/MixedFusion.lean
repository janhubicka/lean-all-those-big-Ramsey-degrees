import PseudotreeValidation.MixedBase

/-!
# Coherent limits of synchronized binary/ternary maps

The local limit is constructed coordinate by coordinate from the proved
ray-map limit. Synchronization and binary roots are preserved. The finite
stage predicates in the choice lemma are arbitrary; the actual stabilization
and monochromatic successor steps are proved separately from HL.
-/

namespace AllThoseBigRamsey.Pseudotree.Mixed

open RayEmbeddings

variable {m : ℕ} {κ : Type}

/-- `G` agrees with the preceding approximation `F` through level `r`. -/
def FixesThrough (F G : Embedding m) (r : ℕ) : Prop :=
  ∀ i s, s.length ≤ r → (G.maps i).map s = (F.maps i).map s

namespace Embedding

def Coherent (F : ℕ → Embedding m) : Prop :=
  ∀ i j, i ≤ j → ∀ k (s : Word), s.length ≤ i →
    ((F j).maps k).map s = ((F i).maps k).map s

theorem coherent_of_successive (F : ℕ → Embedding m)
    (hstep : ∀ n, FixesThrough (F n) (F (n + 1)) n) : Coherent F := by
  intro i j hij k s hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => rfl
  | succ d ih =>
    calc
      ((F (i + (d + 1))).maps k).map s = ((F (i + d)).maps k).map s := by
        exact hstep (i + d) k s (by omega)
      _ = ((F i).maps k).map s := ih (by omega)

theorem maps_coherent (F : ℕ → Embedding m) (hF : Coherent F) (k : Fin (m + 1)) :
    RayStrongMap.Coherent (fun n => (F n).maps k) :=
  fun i j hij s hs => hF i j hij k s hs

/-- The actual synchronized limit; no new fusion principle is assumed. -/
def limit (F : ℕ → Embedding m) (hF : Coherent F) : Embedding m where
  maps k := RayStrongMap.limit (fun n => (F n).maps k) (maps_coherent F hF k)
  level n := (F n).level n
  synchronized k := by
    funext n
    change ((F n).maps k).level n = (F n).level n
    rw [(F n).synchronized]
  binary_roots k hk := (F 0).binary_roots k hk

theorem limit_agrees (F : ℕ → Embedding m) (hF : Coherent F)
    (n : ℕ) (i : Fin (m + 1)) (s : Word) (hs : s.length ≤ n) :
    ((limit F hF).maps i).map s = ((F n).maps i).map s :=
  RayStrongMap.limit_agrees (fun k => (F k).maps i) (maps_coherent F hF i) n s hs

theorem limit_applyTuple_agrees (F : ℕ → Embedding m) (hF : Coherent F)
    (n : ℕ) (x : Tuple m) (hx : ∀ i, (x i).length ≤ n) :
    (limit F hF).applyTuple x = (F n).applyTuple x := by
  funext i
  exact limit_agrees F hF n i (x i) (hx i)

theorem monochromatic_limit (colour : Tuple m → κ) (c : κ)
    (F : ℕ → Embedding m) (hF : Coherent F)
    (hmono : ∀ n k, k ≤ n → ∀ x : Tuple m, AdmissibleAt m k x →
      induced colour (F n) x = c) : Monochromatic colour (limit F hF) c := by
  intro n x hx
  change colour ((limit F hF).applyTuple x) = c
  rw [limit_applyTuple_agrees F hF n x (fun i => Nat.le_of_eq (hx.1 i))]
  exact hmono n n (Nat.le_refl _) x hx

/-- Stabilization at every previously treated source level passes to the
limit, since both tuples in its equality are finite. -/
theorem rayStable_limit (colour : Tuple m → κ) (F : ℕ → Embedding m)
    (hF : Coherent F)
    (hstable : ∀ n j, j ≤ n → StableAt (induced colour (F n)) j) :
    RayStable (induced colour (limit F hF)) := by
  intro j n hjn x hx hbin
  change colour ((limit F hF).applyTuple x) =
    colour ((limit F hF).applyTuple (fun i => (x i).take j))
  rw [limit_applyTuple_agrees F hF n x (fun i => Nat.le_of_eq (hx.1 i))]
  rw [limit_applyTuple_agrees F hF n (fun i => (x i).take j) (by
    intro i
    simp only [List.length_take, hx.1 i]
    exact Nat.min_le_right _ _)]
  exact hstable n j hjn n hjn x hx hbin

end Embedding

/-- Dependent choice assembles genuinely proved finite extension steps into
a coherent sequence. The state invariant may record fixed roots, colours,
or any additional finite conditions needed by an application. -/
theorem exists_coherent_sequence (P : ℕ → Embedding m → Prop)
    (hzero : ∃ F, P 0 F)
    (hstep : ∀ n F, P n F → ∃ G, P (n + 1) G ∧ FixesThrough F G n) :
    ∃ F : ℕ → Embedding m, (∀ n, P n (F n)) ∧ Embedding.Coherent F := by
  classical
  obtain ⟨Fzero, hFzero⟩ := hzero
  let step (n : ℕ) (F : {F : Embedding m // P n F}) :
      {G : Embedding m // P (n + 1) G ∧ FixesThrough F.val G n} :=
    ⟨(hstep n F.val F.property).choose, (hstep n F.val F.property).choose_spec⟩
  let seq : (n : ℕ) → {F : Embedding m // P n F} :=
    Nat.rec ⟨Fzero, hFzero⟩ (fun n F => ⟨(step n F).val, (step n F).property.1⟩)
  refine ⟨fun n => (seq n).val, (fun n => (seq n).property), ?_⟩
  apply Embedding.coherent_of_successive
  intro n
  exact (step n (seq n)).property.2

theorem monochromatic_of_successive_steps (colour : Tuple m → κ) (c : κ)
    (P : ℕ → Embedding m → Prop) (hzero : ∃ F, P 0 F)
    (hstep : ∀ n F, P n F → ∃ G, P (n + 1) G ∧ FixesThrough F G n)
    (hmono : ∀ n F, P n F → ∀ k, k ≤ n → ∀ x : Tuple m,
      AdmissibleAt m k x → induced colour F x = c) :
    ∃ F : Embedding m, Monochromatic colour F c := by
  obtain ⟨F, hP, hF⟩ := exists_coherent_sequence P hzero hstep
  exact ⟨Embedding.limit F hF,
    Embedding.monochromatic_limit colour c F hF (fun n => hmono n (F n) (hP n))⟩

end AllThoseBigRamsey.Pseudotree.Mixed
