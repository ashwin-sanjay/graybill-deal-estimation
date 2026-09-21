import GD.Module0672






















open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0906

noncomputable section

open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0719.N1007
open _root_.GD.N0232.N0719.N0869






theorem d009843
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 1 ≤ sizes i) (face : Finset (Fin k)) :
    _root_.GD.N0232.N0719.N1007.d009816 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face =
      ∑ i ∈ face, (sizes i : ℝ) / 2 := by
  unfold _root_.GD.N0232.N0719.N1007.d009816 _root_.GD.N0232.N0719.N0954.d009355
  rw [show (face.card : ℝ) / 2 =
      ∑ _i ∈ face, (1 : ℝ) / 2 by simp [div_eq_mul_inv]]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hcast : (((sizes i - 1 : ℕ) : ℝ) + 1) = sizes i := by
    exact_mod_cast Nat.sub_add_cancel (hsizes i)
  linarith



theorem d009844
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 1 ≤ sizes i) (deleted : Finset (Fin k)) :
    _root_.GD.N0232.N0719.N0869.d009833 (_root_.GD.N0232.N0719.N0954.d009355 sizes) deleted =
      ∑ i ∈ deleted, (sizes i : ℝ) / 2 := by
  rw [_root_.GD.N0232.N0719.N0869.d009835]
  exact _root_.GD.N0232.N0719.N0906.d009843 sizes hsizes deleted



theorem d009845
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 1 ≤ sizes i)
    (face : Finset (Fin k)) {i : Fin k} (hi : i ∈ face)
    (commonPower : ℝ) :
    _root_.GD.N0232.N0719.N1007.d009817 commonPower
        (_root_.GD.N0232.N0719.N1007.d009816 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (face.erase i)) =
      _root_.GD.N0232.N0719.N1007.d009817 commonPower
          (_root_.GD.N0232.N0719.N1007.d009816 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face) +
        (sizes i : ℝ) / 2 := by
  rw [_root_.GD.N0232.N0719.N1007.d009821 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face hi commonPower]
  unfold _root_.GD.N0232.N0719.N0954.d009355
  have hcast : (((sizes i - 1 : ℕ) : ℝ) + 1) = sizes i := by
    exact_mod_cast Nat.sub_add_cancel (hsizes i)
  linarith



theorem d009846
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 1 ≤ sizes i)
    (child parent : Finset (Fin k)) (hsub : child ⊆ parent)
    (commonPower : ℝ) :
    _root_.GD.N0232.N0719.N1007.d009817 commonPower
        (_root_.GD.N0232.N0719.N1007.d009816 (_root_.GD.N0232.N0719.N0954.d009355 sizes) child) =
      _root_.GD.N0232.N0719.N1007.d009817 commonPower
          (_root_.GD.N0232.N0719.N1007.d009816 (_root_.GD.N0232.N0719.N0954.d009355 sizes) parent) +
        ∑ i ∈ parent \ child, (sizes i : ℝ) / 2 := by
  rw [_root_.GD.N0232.N0719.N0869.d009838
    (_root_.GD.N0232.N0719.N0954.d009355 sizes) child parent hsub commonPower,
    _root_.GD.N0232.N0719.N0906.d009844 sizes hsizes]





def d009847
    {I : Type*} (shape : I → ℝ) (face : Finset I) (s : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1007.d009816 shape face + s - 3 / 2


def d009848
    {I : Type*} (shape : I → ℝ) (face : Finset I)
    (s dilation : ℝ) : ℝ :=
  (dilation ^ 2) ^ (-_root_.GD.N0232.N0719.N0906.d009847 shape face s)



theorem d009849
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 1 ≤ sizes i)
    (face : Finset (Fin k)) {i : Fin k} (hi : i ∈ face)
    (s : ℝ) :
    _root_.GD.N0232.N0719.N0906.d009847 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (face.erase i) s =
      _root_.GD.N0232.N0719.N0906.d009847 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face s -
        (sizes i : ℝ) / 2 := by
  unfold _root_.GD.N0232.N0719.N0906.d009847
  rw [_root_.GD.N0232.N0719.N0906.d009843 sizes hsizes,
    _root_.GD.N0232.N0719.N0906.d009843 sizes hsizes]
  have hsum := Finset.sum_erase_add
    (s := face) (f := fun j ↦ (sizes j : ℝ) / 2) hi
  linarith


theorem d009850
    {dilation : ℝ} (hpos : 0 < dilation) (hne : dilation ≠ 1) :
    dilation ^ 2 ≠ 1 := by
  intro hsquare
  have : dilation = 1 ∨ dilation = -1 :=
    sq_eq_one_iff.mp hsquare
  rcases this with h | h
  · exact hne h
  · linarith






theorem d009851
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (face : Finset (Fin k)) {i : Fin k} (hi : i ∈ face)
    (s dilation : ℝ) (hdilation : 0 < dilation)
    (hdilation_ne : dilation ≠ 1) :
    _root_.GD.N0232.N0719.N0906.d009848 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (face.erase i) s dilation ≠
      _root_.GD.N0232.N0719.N0906.d009848 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face s dilation := by
  intro hcharacter
  have hbasePos : 0 < dilation ^ 2 := sq_pos_of_pos hdilation
  have hbaseNe : dilation ^ 2 ≠ 1 :=
    _root_.GD.N0232.N0719.N0906.d009850 hdilation hdilation_ne
  have hexponents :
      -_root_.GD.N0232.N0719.N0906.d009847 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (face.erase i) s =
        -_root_.GD.N0232.N0719.N0906.d009847 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face s :=
    (Real.rpow_right_inj hbasePos hbaseNe).mp hcharacter
  have hpower := _root_.GD.N0232.N0719.N0906.d009849
    sizes (fun i ↦ (hsizes i).trans' (by omega)) face hi s
  have hsizePos : 0 < (sizes i : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hsizes i))
  linarith



theorem d009852
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 1 ≤ sizes i)
    (face : Finset (Fin k)) {i : Fin k} (hi : i ∈ face)
    (s : ℝ) :
    _root_.GD.N0232.N0719.N0906.d009847 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (face.erase i)
        (s + (sizes i : ℝ) / 2) =
      _root_.GD.N0232.N0719.N0906.d009847 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face s := by
  rw [_root_.GD.N0232.N0719.N0906.d009849 sizes hsizes face hi]
  unfold _root_.GD.N0232.N0719.N0906.d009847
  ring



theorem d009853
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 1 ≤ sizes i)
    (face : Finset (Fin k)) {i : Fin k} (hi : i ∈ face)
    (s dilation : ℝ) :
    _root_.GD.N0232.N0719.N0906.d009848 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (face.erase i)
        (s + (sizes i : ℝ) / 2) dilation =
      _root_.GD.N0232.N0719.N0906.d009848 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face s dilation := by
  unfold _root_.GD.N0232.N0719.N0906.d009848
  rw [_root_.GD.N0232.N0719.N0906.d009852 sizes hsizes face hi]









theorem d009854
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (face : Finset (Fin k)) {i : Fin k} (hi : i ∈ face)
    (s dilation massChild massParent actionChild actionParent : ℝ)
    (hdilation : 0 < dilation) (hdilation_ne : dilation ≠ 1)
    (hmassChild : massChild ≠ 0) (hmassParent : massParent ≠ 0)
    (haction : actionChild ≠ actionParent) :
    ¬ ((_root_.GD.N0232.N0719.N0906.d009848 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (face.erase i) s dilation *
          massChild * actionChild +
        _root_.GD.N0232.N0719.N0906.d009848 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face s dilation *
          massParent * actionParent) * (massChild + massParent) =
      (massChild * actionChild + massParent * actionParent) *
        (_root_.GD.N0232.N0719.N0906.d009848 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (face.erase i) s dilation *
            massChild +
          _root_.GD.N0232.N0719.N0906.d009848 (_root_.GD.N0232.N0719.N0954.d009355 sizes) face s dilation *
            massParent)) := by
  intro hposterior
  have hcharacters := _root_.GD.N0232.N0719.N1007.d009832
    hmassChild hmassParent haction hposterior
  exact (_root_.GD.N0232.N0719.N0906.d009851
    sizes hsizes face hi s dilation hdilation hdilation_ne) hcharacters

end

end N0906
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0906.d009843
#print axioms _root_.GD.N0232.N0719.N0906.d009846
#print axioms _root_.GD.N0232.N0719.N0906.d009851
#print axioms _root_.GD.N0232.N0719.N0906.d009853
#print axioms _root_.GD.N0232.N0719.N0906.d009854
