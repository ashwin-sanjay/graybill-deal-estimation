import GD.Module0644






























open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N1007

noncomputable section

variable {J : Type*} [Fintype J]

open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0931




def d009816 {I : Type*}
    (shape : I → ℝ) (face : Finset I) : ℝ :=
  ∑ i ∈ face, shape i + (face.card : ℝ) / 2



def d009817 (commonPower order : ℝ) : ℝ :=
  commonPower + 3 / 2 - order


theorem d009818
    (commonPower order : ℝ) :
    order + _root_.GD.N0232.N0719.N1007.d009817 commonPower order - 3 / 2 = commonPower := by
  unfold _root_.GD.N0232.N0719.N1007.d009817
  ring



theorem d009819
    {I : Type*} (shape : I → ℝ) (face : Finset I)
    (commonPower : ℝ) :
    _root_.GD.N0232.N0719.N1007.d009816 shape face +
        _root_.GD.N0232.N0719.N1007.d009817 commonPower
          (_root_.GD.N0232.N0719.N1007.d009816 shape face) - 3 / 2 = commonPower := by
  exact _root_.GD.N0232.N0719.N1007.d009818
    commonPower (_root_.GD.N0232.N0719.N1007.d009816 shape face)



theorem d009820
    {I : Type*} [DecidableEq I]
    (shape : I → ℝ) (face : Finset I) {i : I} (hi : i ∈ face) :
    _root_.GD.N0232.N0719.N1007.d009816 shape (face.erase i) =
      _root_.GD.N0232.N0719.N1007.d009816 shape face - (shape i + 1 / 2) := by
  have hsum := Finset.sum_erase_add (s := face) (f := shape) hi
  have hcardNat : (face.erase i).card + 1 = face.card :=
    Finset.card_erase_add_one hi
  have hcardReal :
      ((face.erase i).card : ℝ) + 1 = (face.card : ℝ) := by
    exact_mod_cast hcardNat
  unfold _root_.GD.N0232.N0719.N1007.d009816
  linarith




theorem d009821
    {I : Type*} [DecidableEq I]
    (shape : I → ℝ) (face : Finset I) {i : I} (hi : i ∈ face)
    (commonPower : ℝ) :
    _root_.GD.N0232.N0719.N1007.d009817 commonPower
        (_root_.GD.N0232.N0719.N1007.d009816 shape (face.erase i)) =
      _root_.GD.N0232.N0719.N1007.d009817 commonPower
          (_root_.GD.N0232.N0719.N1007.d009816 shape face) + (shape i + 1 / 2) := by
  rw [_root_.GD.N0232.N0719.N1007.d009820 shape face hi]
  unfold _root_.GD.N0232.N0719.N1007.d009817
  ring





theorem d009822
    {I : Type*} [DecidableEq I]
    (shape : I → ℝ) (face : Finset I) {i : I} (hi : i ∈ face)
    (commonPower : ℝ) :
    (_root_.GD.N0232.N0719.N1007.d009817 commonPower
        (_root_.GD.N0232.N0719.N1007.d009816 shape (face.erase i)) -
      _root_.GD.N0232.N0719.N1007.d009817 commonPower
        (_root_.GD.N0232.N0719.N1007.d009816 shape face)) - shape i = 1 / 2 := by
  rw [_root_.GD.N0232.N0719.N1007.d009821 shape face hi commonPower]
  ring



theorem d009823
    {I : Type*} [Fintype I]
    (shape : I → ℝ) (commonPower : ℝ) :
    _root_.GD.N0232.N0719.N0928.d009415 shape
        (_root_.GD.N0232.N0719.N1007.d009817 commonPower (_root_.GD.N0232.N0719.N0928.d009408 shape)) =
      commonPower := by
  unfold _root_.GD.N0232.N0719.N0928.d009415
  exact _root_.GD.N0232.N0719.N1007.d009818
    commonPower (_root_.GD.N0232.N0719.N0928.d009408 shape)



theorem d009824
    {I : Type*} [Fintype I]
    (shape : I → ℝ) (commonPower dilation : ℝ) :
    _root_.GD.N0232.N0719.N0931.d009450 shape
        (_root_.GD.N0232.N0719.N1007.d009817 commonPower (_root_.GD.N0232.N0719.N0928.d009408 shape))
        dilation =
      (dilation ^ 2) ^ (-commonPower) := by
  unfold _root_.GD.N0232.N0719.N0931.d009450
  rw [_root_.GD.N0232.N0719.N1007.d009823 shape commonPower]



theorem d009825
    {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (shape₁ : I₁ → ℝ) (shape₂ : I₂ → ℝ)
    (commonPower dilation : ℝ) :
    _root_.GD.N0232.N0719.N0931.d009450 shape₁
        (_root_.GD.N0232.N0719.N1007.d009817 commonPower (_root_.GD.N0232.N0719.N0928.d009408 shape₁))
        dilation =
      _root_.GD.N0232.N0719.N0931.d009450 shape₂
        (_root_.GD.N0232.N0719.N1007.d009817 commonPower (_root_.GD.N0232.N0719.N0928.d009408 shape₂))
        dilation := by
  rw [_root_.GD.N0232.N0719.N1007.d009824, _root_.GD.N0232.N0719.N1007.d009824]


def d009826
    (weight evidence : J → ℝ) : ℝ :=
  ∑ j, weight j * evidence j


def d009827
    (weight evidence action : J → ℝ) : ℝ :=
  ∑ j, weight j * evidence j * action j


def d009828
    (weight evidence action : J → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1007.d009827 weight evidence action /
    _root_.GD.N0232.N0719.N1007.d009826 weight evidence


theorem d009829
    (weight evidence : J → ℝ) (character : ℝ) :
    _root_.GD.N0232.N0719.N1007.d009826 weight (fun j ↦ character * evidence j) =
      character * _root_.GD.N0232.N0719.N1007.d009826 weight evidence := by
  unfold _root_.GD.N0232.N0719.N1007.d009826
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring




theorem d009830
    (weight evidence action : J → ℝ)
    (character shift dilation : ℝ)
    (hcharacter : character ≠ 0)
    (hdenom : _root_.GD.N0232.N0719.N1007.d009826 weight evidence ≠ 0) :
    _root_.GD.N0232.N0719.N1007.d009828 weight
        (fun j ↦ character * evidence j)
        (fun j ↦ shift + dilation * action j) =
      shift + dilation * _root_.GD.N0232.N0719.N1007.d009828 weight evidence action := by
  have hdenom' :
      _root_.GD.N0232.N0719.N1007.d009826 weight (fun j ↦ character * evidence j) ≠ 0 := by
    rw [_root_.GD.N0232.N0719.N1007.d009829]
    exact mul_ne_zero hcharacter hdenom
  have hsumdenom : (∑ j, weight j * evidence j) ≠ 0 := by
    simpa [_root_.GD.N0232.N0719.N1007.d009826] using hdenom
  unfold _root_.GD.N0232.N0719.N1007.d009828 _root_.GD.N0232.N0719.N1007.d009827
  rw [_root_.GD.N0232.N0719.N1007.d009829]
  have hnum :
      (∑ j, weight j * (character * evidence j) *
          (shift + dilation * action j)) =
        character *
          (shift * (∑ j, weight j * evidence j) +
            dilation * (∑ j, weight j * evidence j * action j)) := by
    calc
      (∑ j, weight j * (character * evidence j) *
          (shift + dilation * action j)) =
          ∑ j, ((character * shift) * (weight j * evidence j) +
            (character * dilation) *
              (weight j * evidence j * action j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (character * shift) * (∑ j, weight j * evidence j) +
          (character * dilation) *
            (∑ j, weight j * evidence j * action j) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = _ := by ring
  rw [hnum]
  unfold _root_.GD.N0232.N0719.N1007.d009826
  field_simp [hcharacter, hsumdenom]





theorem d009831
    (mass₁ mass₂ action₁ action₂ character₁ character₂ : ℝ) :
    (character₁ * mass₁ * action₁ +
        character₂ * mass₂ * action₂) * (mass₁ + mass₂) -
      (mass₁ * action₁ + mass₂ * action₂) *
        (character₁ * mass₁ + character₂ * mass₂) =
      mass₁ * mass₂ * (character₁ - character₂) *
        (action₁ - action₂) := by
  ring



theorem d009832
    {mass₁ mass₂ action₁ action₂ character₁ character₂ : ℝ}
    (hmass₁ : mass₁ ≠ 0) (hmass₂ : mass₂ ≠ 0)
    (haction : action₁ ≠ action₂)
    (hposterior :
      (character₁ * mass₁ * action₁ +
          character₂ * mass₂ * action₂) * (mass₁ + mass₂) =
        (mass₁ * action₁ + mass₂ * action₂) *
          (character₁ * mass₁ + character₂ * mass₂)) :
    character₁ = character₂ := by
  have hzero :
      mass₁ * mass₂ * (character₁ - character₂) *
          (action₁ - action₂) = 0 := by
    rw [← _root_.GD.N0232.N0719.N1007.d009831]
    exact sub_eq_zero.mpr hposterior
  rcases mul_eq_zero.mp hzero with hleft | hact
  · rcases mul_eq_zero.mp hleft with hmass | hchar
    · exact False.elim ((mul_ne_zero hmass₁ hmass₂) hmass)
    · exact sub_eq_zero.mp hchar
  · exact False.elim (haction (sub_eq_zero.mp hact))

end

end N1007
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N1007.d009818
#print axioms _root_.GD.N0232.N0719.N1007.d009821
#print axioms _root_.GD.N0232.N0719.N1007.d009822
#print axioms _root_.GD.N0232.N0719.N1007.d009825
#print axioms _root_.GD.N0232.N0719.N1007.d009830
#print axioms _root_.GD.N0232.N0719.N1007.d009832
