import PseudotreeValidation.SparseChainGeometry
import PseudotreeValidation.SparseLex

/-! Finite prefixes of the maximum branch are lexicographically leftmost. -/

namespace AllThoseBigRamsey.Pseudotree.Sparse

private theorem lex_take_le {s t : DiaryWord} (h : s < t) (j : Nat) :
    s.take j ≤ t.take j := by
  induction j generalizing s t with
  | zero => simp
  | succ j ih =>
    cases h with
    | nil => exact le_of_lt List.Lex.nil
    | rel hab => exact le_of_lt (List.Lex.rel hab)
    | cons htail =>
      rcases lt_or_eq_of_le (ih htail) with hlt | heq
      · exact le_of_lt (List.Lex.cons hlt)
      · simp only [List.take_succ_cons, heq]
        exact le_refl _

/-- The corrected leftmost assertion at each common prefix level. A shorter
coding word may itself precede the maximum in full lexicographic order, so
the prefix length is bounded by both words as in the extraction proof. -/
theorem fin_prefix_leftmost {w v : DiaryWord}
    (hw : InSparse (w.map RayMapModel.toLetter))
    (hv : InSparse (v.map RayMapModel.toLetter))
    (hbelow : DiaryChains.model w ≤ DiaryChains.model v)
    (j : Nat) (hjw : j ≤ w.length) (_hjv : j ≤ v.length) : v.take j ≤ w.take j := by
  have hb : wordBelow (w.map RayMapModel.toLetter) (v.map RayMapModel.toLetter) :=
    (wordBelow_iff_toBlocks_le _ _).mpr hbelow
  rcases below_spine hw hv hb with hp | ⟨p, s, t, hwform, hvform, _hno⟩
  · have hpf : w.IsPrefix v := by
      have hh := hp.map RayMapModel.toFin
      simpa [List.map_map, Function.comp_def] using hh
    obtain ⟨tail, htail⟩ := hpf
    rw [← htail, List.take_append_of_le_length hjw]
  · have hlex : lexLess (v.map RayMapModel.toLetter) (w.map RayMapModel.toLetter) = true := by
      rw [hwform, hvform, lexLess_common_prefix]
      rfl
    exact lex_take_le ((lexLess_fin_iff v w).mp hlex) j

end AllThoseBigRamsey.Pseudotree.Sparse
