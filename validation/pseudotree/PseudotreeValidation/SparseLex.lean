import AllThoseBigRamsey.Pseudotree.SparseFrontier
import AllThoseBigRamsey.Pseudotree.RayMapModel
import PseudotreeValidation.DiaryLex

/-! Exact identification of the sparse construction's Boolean lexicographic
comparison with the diary alphabet's literal list order. -/

namespace AllThoseBigRamsey.Pseudotree.Sparse

@[simp] theorem rank_toLetter (a : Fin 3) : rank (RayMapModel.toLetter a) = a.val := by
  fin_cases a <;> rfl

theorem lexLess_fin_iff (s t : DiaryWord) :
    lexLess (s.map RayMapModel.toLetter) (t.map RayMapModel.toLetter) = true ↔ s < t := by
  induction s generalizing t with
  | nil => cases t <;> simp [lexLess]
  | cons a s ih =>
    cases t with
    | nil => simp [lexLess]
    | cons b t =>
      change lexLess (RayMapModel.toLetter a :: s.map RayMapModel.toLetter)
        (RayMapModel.toLetter b :: t.map RayMapModel.toLetter) = true ↔
          List.Lex (· < ·) (a :: s) (b :: t)
      rw [List.cons_lex_cons_iff]
      simp only [lexLess, rank_toLetter]
      by_cases hab : a = b
      · subst b
        simp only [↓reduceIte, lt_self_iff_false, true_and, false_or]
        exact ih t
      · have hval : a.val ≠ b.val := fun h => hab (Fin.ext h)
        simp only [hval, ↓reduceIte, decide_eq_true_eq, hab, false_and, or_false, Fin.lt_def]

theorem lexLess_iff_fin (s t : Word) :
    lexLess s t = true ↔ s.map RayMapModel.toFin < t.map RayMapModel.toFin := by
  have h := lexLess_fin_iff (s.map RayMapModel.toFin) (t.map RayMapModel.toFin)
  simpa [List.map_map, Function.comp_def] using h

@[simp] theorem lexLess_self (s : Word) : lexLess s s = false := by
  have hn : lexLess s s ≠ true := fun h => lt_irrefl _ ((lexLess_iff_fin s s).mp h)
  exact Bool.eq_false_of_not_eq_true hn

theorem lexLess_asymm {s t : Word} (h : lexLess s t = true) : lexLess t s = false := by
  have hs := (lexLess_iff_fin s t).mp h
  have hn : lexLess t s ≠ true := fun ht => not_lt_of_gt hs ((lexLess_iff_fin t s).mp ht)
  exact Bool.eq_false_of_not_eq_true hn

theorem lexLess_trans {s t u : Word} (hst : lexLess s t = true) (htu : lexLess t u = true) :
    lexLess s u = true :=
  (lexLess_iff_fin s u).mpr (lt_trans ((lexLess_iff_fin s t).mp hst) ((lexLess_iff_fin t u).mp htu))

end AllThoseBigRamsey.Pseudotree.Sparse
