import PseudotreeValidation.FiniteExtensions
import PseudotreeValidation.WordModelMathlib

/-!
# The concrete model is the Fraïssé limit of finite binary meet-trees

The class below is specified independently of the concrete model: its members
are finite structures whose symbols interpret a semilattice with linearly
ordered predecessor sets and at most two upward cones.  We prove the exact age
equality and then use the already checked finite-extension/back-and-forth
argument to obtain mathlib's native `IsFraisseLimit` statement.
-/

namespace AllThoseBigRamsey.Pseudotree

open FirstOrder
open scoped FirstOrder

instance : Countable (Σ n, language.Functions n) :=
  Function.Injective.countable (f := fun _ : Σ n, language.Functions n => ()) (by
    rintro ⟨_, f⟩ ⟨_, g⟩ _
    cases f
    cases g
    rfl)

/-- An intrinsic, finite-structure definition of the age in the manuscript. -/
def finiteBinaryClass : Set (CategoryTheory.Bundled.{u} language.Structure) :=
  {S | Finite S ∧ ∃ i : SemilatticeInf S,
    letI := i
    MeetsInterpreted S ∧
      (∀ {x y z : S}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x) ∧
      BinaryBranching S}

section Pullback

variable {A : Type u} [language.Structure A]
    {B : Type v} [SemilatticeInf B] [language.Structure B] [MeetsInterpreted B]

/-- Pull the semilattice on the image back to an arbitrary language structure. -/
noncomputable abbrev semilatticeOfEmbedding (f : A ↪[language] B) : SemilatticeInf A :=
  f.equivRange.toEquiv.semilatticeInf

theorem meetsInterpreted_of_embedding (f : A ↪[language] B) :
    @MeetsInterpreted A (semilatticeOfEmbedding f) _ := by
  letI := semilatticeOfEmbedding f
  constructor
  · intro x
    apply f.equivRange.injective
    calc
      _ = FirstOrder.Language.Structure.funMap (L := language) MeetFunction.meet
          (f.equivRange ∘ x) := f.equivRange.map_fun MeetFunction.meet x
      _ = f.equivRange (x 0) ⊓ f.equivRange (x 1) := by
          simp only [MeetsInterpreted.meet_eq, Function.comp_apply]
      _ = _ := by
        change f.equivRange (x 0) ⊓ f.equivRange (x 1) =
          f.equivRange (f.equivRange.symm (f.equivRange (x 0) ⊓ f.equivRange (x 1)))
        exact (f.equivRange.apply_symm_apply _).symm
  · intro x
    have h := f.equivRange.map_rel OrderRelation.le x
    change FirstOrder.Language.Structure.RelMap (L := language) OrderRelation.le x ↔
      f.equivRange (x 0) ≤ f.equivRange (x 1)
    simpa only [MeetsInterpreted.order_iff, Function.comp_apply] using h.symm

end Pullback

section Age

variable {α : Type u} [LinearOrder α] [NoMinOrder α] [NoMaxOrder α]
    [DenselyOrdered α] [Nonempty α]

/-- All finitely generated substructures of the model are finite, and the
model realizes every finite binary meet-tree. -/
theorem RayTree.age_eq_finiteBinaryClass :
    language.age (RayTree α) = finiteBinaryClass := by
  ext S
  constructor
  · rintro ⟨hfg, ⟨f⟩⟩
    have hrange := hfg.range f.toHom
    obtain ⟨X, hX, hXrange⟩ := FirstOrder.Language.Substructure.fg_def.mp hrange
    have hrangeFinite := finite_meet_closure RayTree.le_or_ge_of_le_common hX
    rw [hXrange] at hrangeFinite
    letI : Finite f.toHom.range := hrangeFinite.to_subtype
    have hSfinite : Finite S := Finite.of_injective f.equivRange f.equivRange.injective
    letI := semilatticeOfEmbedding f
    letI := meetsInterpreted_of_embedding f
    refine ⟨hSfinite, inferInstance, inferInstance, ?_, ?_⟩
    · intro x y z hx hy
      have hx' : f x ≤ f z := (embedding_le_iff f x z).2 hx
      have hy' : f y ≤ f z := (embedding_le_iff f y z).2 hy
      rcases RayTree.le_or_ge_of_le_common hx' hy' with h | h
      · exact Or.inl ((embedding_le_iff f x y).1 h)
      · exact Or.inr ((embedding_le_iff f y x).1 h)
    · intro s x y z hx hy hz
      have h := RayTree.binaryBranching (f s) (f x) (f y) (f z)
        ((embedding_lt_iff f s x).2 hx)
        ((embedding_lt_iff f s y).2 hy)
        ((embedding_lt_iff f s z).2 hz)
      simpa only [← embedding_map_inf, embedding_lt_iff] using h
  · rintro ⟨hfinite, i, hinterpreted, htree, hbinary⟩
    letI := hfinite
    letI := i
    letI := hinterpreted
    exact ⟨FirstOrder.Language.Structure.FG.of_finite,
      finite_universal htree hbinary⟩

/-- This is the native model-theoretic identification, not an assumption about
the proposed coding model. -/
theorem RayTree.isFraisseLimit [Countable α] :
    language.IsFraisseLimit finiteBinaryClass (RayTree α) where
  ultrahomogeneous := RayTree.isUltrahomogeneous
  age := RayTree.age_eq_finiteBinaryClass

end Age

/-- The literal ternary coding, in its explicitly equivalent block form, is
the countable homogeneous binary pseudotree from the manuscript. -/
theorem ternaryModel_isFraisseLimit :
    language.IsFraisseLimit finiteBinaryClass TernaryModel :=
  RayTree.isFraisseLimit

/-- Heredity, joint embedding, and amalgamation also follow from the concrete
construction, without assuming the Fraïssé class axioms. -/
theorem finiteBinaryClass_isFraisse :
    FirstOrder.Language.IsFraisse finiteBinaryClass.{0} :=
  ternaryModel_isFraisseLimit.isFraisse

/-- The coding model is isomorphic to any other countable Fraïssé limit of
the independently defined finite binary meet-tree class. -/
theorem ternaryModel_unique {M : Type} [language.Structure M] [Countable M]
    (hM : language.IsFraisseLimit finiteBinaryClass M) :
    Nonempty (TernaryModel ≃[language] M) :=
  ternaryModel_isFraisseLimit.nonempty_equiv hM

end AllThoseBigRamsey.Pseudotree
