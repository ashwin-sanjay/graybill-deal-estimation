import GD.Module0671


















open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0869

noncomputable section

open _root_.GD.N0232.N0719.N1007



def d009833 {I : Type*} (shape : I → ℝ) (deleted : Finset I) : ℝ :=
  ∑ i ∈ deleted, (shape i + 1 / 2)


theorem d009834 {I : Type*} [DecidableEq I]
    (shape : I → ℝ) (left right : Finset I)
    (hdisjoint : Disjoint left right) :
    _root_.GD.N0232.N0719.N0869.d009833 shape (left ∪ right) =
      _root_.GD.N0232.N0719.N0869.d009833 shape left + _root_.GD.N0232.N0719.N0869.d009833 shape right := by
  unfold _root_.GD.N0232.N0719.N0869.d009833
  rw [Finset.sum_union hdisjoint]



theorem d009835
    {I : Type*} [DecidableEq I]
    (shape : I → ℝ) (deleted : Finset I) :
    _root_.GD.N0232.N0719.N0869.d009833 shape deleted =
      _root_.GD.N0232.N0719.N1007.d009816 shape deleted := by
  unfold _root_.GD.N0232.N0719.N0869.d009833 _root_.GD.N0232.N0719.N1007.d009816
  simp_rw [Finset.sum_add_distrib]
  simp
  ring


theorem d009836 {I : Type*} [DecidableEq I]
    (shape : I → ℝ) (left right : Finset I)
    (hdisjoint : Disjoint left right) :
    _root_.GD.N0232.N0719.N1007.d009816 shape (left ∪ right) =
      _root_.GD.N0232.N0719.N1007.d009816 shape left +
        _root_.GD.N0232.N0719.N1007.d009816 shape right := by
  unfold _root_.GD.N0232.N0719.N1007.d009816
  rw [Finset.sum_union hdisjoint, Finset.card_union_of_disjoint hdisjoint]
  push_cast
  ring



theorem d009837
    {I : Type*} [DecidableEq I]
    (shape : I → ℝ) (child parent : Finset I)
    (hsub : child ⊆ parent) :
    _root_.GD.N0232.N0719.N1007.d009816 shape child +
        _root_.GD.N0232.N0719.N0869.d009833 shape (parent \ child) =
      _root_.GD.N0232.N0719.N1007.d009816 shape parent := by
  have hdisjoint : Disjoint (parent \ child) child :=
    Finset.sdiff_disjoint
  have hunion : parent \ child ∪ child = parent :=
    Finset.sdiff_union_of_subset hsub
  rw [_root_.GD.N0232.N0719.N0869.d009835]
  have hadd := _root_.GD.N0232.N0719.N0869.d009836
    shape (parent \ child) child hdisjoint
  rw [hunion] at hadd
  linarith




theorem d009838
    {I : Type*} [DecidableEq I]
    (shape : I → ℝ) (child parent : Finset I)
    (hsub : child ⊆ parent) (commonPower : ℝ) :
    _root_.GD.N0232.N0719.N1007.d009817 commonPower
        (_root_.GD.N0232.N0719.N1007.d009816 shape child) =
      _root_.GD.N0232.N0719.N1007.d009817 commonPower
          (_root_.GD.N0232.N0719.N1007.d009816 shape parent) +
        _root_.GD.N0232.N0719.N0869.d009833 shape (parent \ child) := by
  have horder := _root_.GD.N0232.N0719.N0869.d009837
    shape child parent hsub
  unfold _root_.GD.N0232.N0719.N1007.d009817
  linarith


theorem d009839
    {I : Type*} [DecidableEq I]
    (shape : I → ℝ) (child middle parent : Finset I)
    (hchild : child ⊆ middle) (hmiddle : middle ⊆ parent)
    (commonPower : ℝ) :
    _root_.GD.N0232.N0719.N0869.d009833 shape (parent \ child) =
      _root_.GD.N0232.N0719.N0869.d009833 shape (parent \ middle) +
        _root_.GD.N0232.N0719.N0869.d009833 shape (middle \ child) := by
  have hcp : child ⊆ parent := hchild.trans hmiddle
  have hwhole := _root_.GD.N0232.N0719.N0869.d009838
    shape child parent hcp commonPower
  have hupper := _root_.GD.N0232.N0719.N0869.d009838
    shape middle parent hmiddle commonPower
  have hlower := _root_.GD.N0232.N0719.N0869.d009838
    shape child middle hchild commonPower
  linarith



theorem d009840
    {I : Type*} [DecidableEq I]
    (shape : I → ℝ) (child parent : Finset I)
    (hsub : child ⊆ parent) (commonPower : ℝ) :
    (_root_.GD.N0232.N0719.N1007.d009817 commonPower
          (_root_.GD.N0232.N0719.N1007.d009816 shape child) -
        _root_.GD.N0232.N0719.N1007.d009817 commonPower
          (_root_.GD.N0232.N0719.N1007.d009816 shape parent)) -
      (∑ i ∈ parent \ child, shape i) =
        ((parent \ child).card : ℝ) / 2 := by
  rw [_root_.GD.N0232.N0719.N0869.d009838 shape child parent hsub commonPower]
  unfold _root_.GD.N0232.N0719.N0869.d009833
  simp_rw [Finset.sum_add_distrib]
  simp
  ring


theorem d009841
    {I : Type*} [DecidableEq I]
    (shape : I → ℝ) (child parent : Finset I)
    (hsub : child ⊆ parent) (commonPower : ℝ) :
    (_root_.GD.N0232.N0719.N1007.d009817 commonPower
          (_root_.GD.N0232.N0719.N1007.d009816 shape child) -
        _root_.GD.N0232.N0719.N1007.d009817 commonPower
          (_root_.GD.N0232.N0719.N1007.d009816 shape parent)) -
      (∑ i ∈ parent \ child, shape i) =
        ((parent.card : ℝ) - (child.card : ℝ)) / 2 := by
  rw [_root_.GD.N0232.N0719.N0869.d009840 shape child parent hsub commonPower]
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hcardReal :
      ((parent \ child).card : ℝ) + (child.card : ℝ) =
        (parent.card : ℝ) := by
    exact_mod_cast hcard
  linarith



theorem d009842
    {I : Type*} (shape : I → ℝ) (i j : I) :
    (shape i + 1 / 2) + (shape j + 1 / 2) =
      (shape j + 1 / 2) + (shape i + 1 / 2) := by
  ring

end

end N0869
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0869.d009837
#print axioms _root_.GD.N0232.N0719.N0869.d009838
#print axioms _root_.GD.N0232.N0719.N0869.d009839
#print axioms _root_.GD.N0232.N0719.N0869.d009840
#print axioms _root_.GD.N0232.N0719.N0869.d009841
