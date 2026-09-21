import GD.Module0033
import GD.Module0224

























open scoped BigOperators

namespace GD
namespace N0233
namespace N0725

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0619
open _root_.GD.N0233.N0726

variable {Omega iota : Type*} [MeasurableSpace Omega]
variable [Fintype iota] [DecidableEq iota]


def d003180
    (weight : iota → ℝ) (likelihood : iota → Omega → ℝ)
    (omega : Omega) : Option iota → ℝ :=
  fun s ↦ _root_.GD.N0230.N0619.d000381 weight s * _root_.GD.N0230.N0619.d000382 likelihood omega s


theorem d003181
    (weight : iota → ℝ) (likelihood : iota → Omega → ℝ)
    (omega : Omega) :
    _root_.GD.N0233.N0726.d003174 (_root_.GD.N0233.N0725.d003180 weight likelihood omega) =
      _root_.GD.N0230.N0617.d000163 weight likelihood omega := by
  unfold _root_.GD.N0233.N0726.d003174 _root_.GD.N0233.N0725.d003180
  exact _root_.GD.N0230.N0619.d000391 weight likelihood omega


theorem d003182
    (weight : iota → ℝ) (likelihood : iota → Omega → ℝ)
    (center : iota → ℝ) (omega : Omega) :
    _root_.GD.N0233.N0726.d003175 (_root_.GD.N0233.N0725.d003180 weight likelihood omega)
        (_root_.GD.N0230.N0619.d000383 center) =
      _root_.GD.N0230.N0617.d000164 weight likelihood center omega := by
  unfold _root_.GD.N0233.N0726.d003175 _root_.GD.N0233.N0725.d003180 _root_.GD.N0230.N0617.d000164
  rw [Fintype.sum_option]
  simp [_root_.GD.N0230.N0619.d000381, _root_.GD.N0230.N0619.d000382, _root_.GD.N0230.N0619.d000383]



theorem d003183
    (weight : iota → ℝ) (likelihood : iota → Omega → ℝ)
    (center : iota → ℝ) (omega : Omega) :
    _root_.GD.N0233.N0726.d003176 (_root_.GD.N0233.N0725.d003180 weight likelihood omega)
        (_root_.GD.N0230.N0619.d000383 center) =
      _root_.GD.N0230.N0617.d000166 weight likelihood center omega := by
  unfold _root_.GD.N0233.N0726.d003176 _root_.GD.N0230.N0617.d000166
  rw [_root_.GD.N0233.N0725.d003182,
    _root_.GD.N0233.N0725.d003181]



theorem d003184
    (weight : iota → ℝ) (likelihood : iota → Omega → ℝ)
    (center : iota → ℝ) (omega : Omega)
    (hmass : _root_.GD.N0230.N0617.d000163 weight likelihood omega ≠ 0) :
    _root_.GD.N0233.N0726.d003177
        (_root_.GD.N0233.N0725.d003180 weight likelihood omega)
        (_root_.GD.N0230.N0619.d000383 center) (_root_.GD.N0230.N0619.d000383 center) =
      _root_.GD.N0230.N0617.d000165 weight likelihood center omega -
        _root_.GD.N0230.N0617.d000167 weight likelihood center omega := by
  unfold _root_.GD.N0233.N0726.d003177
  rw [show
    _root_.GD.N0233.N0726.d003176 (_root_.GD.N0233.N0725.d003180 weight likelihood omega)
        (_root_.GD.N0230.N0619.d000383 center) =
      _root_.GD.N0230.N0617.d000166 weight likelihood center omega from
        _root_.GD.N0233.N0725.d003183
          weight likelihood center omega]
  unfold _root_.GD.N0233.N0725.d003180
  rw [Fintype.sum_option]
  simp only [_root_.GD.N0230.N0619.d000381, _root_.GD.N0230.N0619.d000382, _root_.GD.N0230.N0619.d000383, sub_zero,
    zero_mul, mul_zero, zero_add]
  calc
    (∑ i,
        weight i * likelihood i omega *
          (center i - _root_.GD.N0230.N0617.d000166 weight likelihood center omega) *
            center i) =
        ∑ i,
          (weight i * likelihood i omega * center i ^ 2 -
            _root_.GD.N0230.N0617.d000166 weight likelihood center omega *
              (weight i * likelihood i omega * center i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ =
        _root_.GD.N0230.N0617.d000165 weight likelihood center omega -
          _root_.GD.N0230.N0617.d000166 weight likelihood center omega *
            _root_.GD.N0230.N0617.d000164 weight likelihood center omega := by
      unfold _root_.GD.N0230.N0617.d000165 _root_.GD.N0230.N0617.d000164
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _root_.GD.N0230.N0617.d000165 weight likelihood center omega -
          _root_.GD.N0230.N0617.d000167 weight likelihood center omega := by
      unfold _root_.GD.N0230.N0617.d000166 _root_.GD.N0230.N0617.d000167
      field_simp [hmass]



theorem d003185
    (weight : iota → ℝ) (likelihood : iota → Omega → ℝ)
    (center : iota → ℝ) (omega : Omega)
    (hmass : _root_.GD.N0230.N0617.d000163 weight likelihood omega ≠ 0) :
    _root_.GD.N0230.N0617.d000163 weight likelihood omega *
        (_root_.GD.N0230.N0617.d000165 weight likelihood center omega -
          _root_.GD.N0230.N0617.d000167 weight likelihood center omega) =
      _root_.GD.N0233.N0726.d003178
        (_root_.GD.N0233.N0725.d003180 weight likelihood omega)
        (_root_.GD.N0230.N0619.d000383 center) (_root_.GD.N0230.N0619.d000383 center) := by
  rw [← _root_.GD.N0233.N0725.d003181 weight likelihood omega,
    ← _root_.GD.N0233.N0725.d003184
      weight likelihood center omega hmass]
  exact _root_.GD.N0233.N0726.d003179
    (_root_.GD.N0233.N0725.d003180 weight likelihood omega)
    (_root_.GD.N0230.N0619.d000383 center) (_root_.GD.N0230.N0619.d000383 center)
    (by simpa [_root_.GD.N0233.N0725.d003181] using hmass)


theorem d003186
    (weight : iota → ℝ) (likelihood : iota → Omega → ℝ)
    (center : iota → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i omega, 0 ≤ likelihood i omega)
    (omega : Omega) :
    _root_.GD.N0233.N0726.d003178
        (_root_.GD.N0233.N0725.d003180 weight likelihood omega)
        (_root_.GD.N0230.N0619.d000383 center) (_root_.GD.N0230.N0619.d000383 center) =
      _root_.GD.N0230.N0617.d000163 weight likelihood omega ^ 2 *
        _root_.GD.N0230.N0619.d000386 weight likelihood center omega := by
  have hmass : _root_.GD.N0230.N0617.d000163 weight likelihood omega ≠ 0 :=
    (_root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood omega).ne'
  rw [← _root_.GD.N0233.N0725.d003185
    weight likelihood center omega hmass]
  rw [_root_.GD.N0230.N0619.d000401
    weight likelihood center hweight hlikelihood omega]
  ring



theorem d003187
    (weight : iota → ℝ) (likelihood : iota → Omega → ℝ)
    (center : iota → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i omega, 0 ≤ likelihood i omega)
    (omega : Omega) :
    _root_.GD.N0233.N0726.d003178
        (_root_.GD.N0233.N0725.d003180 weight likelihood omega)
        (_root_.GD.N0230.N0619.d000383 center) (_root_.GD.N0230.N0619.d000383 center) =
      (1 / 2 : ℝ) * _root_.GD.N0230.N0617.d000163 weight likelihood omega ^ 2 *
        _root_.GD.N0230.N0619.d000387 weight likelihood center omega := by
  rw [_root_.GD.N0233.N0725.d003186
    weight likelihood center hweight hlikelihood omega]
  rw [_root_.GD.N0230.N0619.d000399
    weight likelihood center hweight hlikelihood omega]
  ring




theorem d003188
    (weight : iota → ℝ) (likelihood : iota → Omega → ℝ)
    (center : iota → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i omega, 0 ≤ likelihood i omega)
    (omega : Omega) (decision : ℝ) :
    _root_.GD.N0230.N0617.d000163 weight likelihood omega *
        _root_.GD.N0230.N0619.d000388 weight likelihood center omega decision =
      _root_.GD.N0230.N0619.d000389
          weight likelihood center omega decision +
        (_root_.GD.N0230.N0617.d000165 weight likelihood center omega -
          _root_.GD.N0230.N0617.d000167 weight likelihood center omega) := by
  have hmass : _root_.GD.N0230.N0617.d000163 weight likelihood omega ≠ 0 :=
    (_root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood omega).ne'
  rw [_root_.GD.N0230.N0619.d000403
    weight likelihood center hweight hlikelihood omega decision]
  rw [_root_.GD.N0230.N0619.d000395
    weight likelihood center omega decision hmass]
  rw [_root_.GD.N0230.N0619.d000401
    weight likelihood center hweight hlikelihood omega]
  ring





theorem d003189
    (weight : iota → ℝ) (likelihood : iota → Omega → ℝ)
    (center : iota → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hlikelihood : ∀ i omega, 0 ≤ likelihood i omega)
    (omega : Omega) (decision : ℝ) :
    _root_.GD.N0230.N0617.d000163 weight likelihood omega ^ 2 *
        _root_.GD.N0230.N0619.d000388 weight likelihood center omega decision =
      _root_.GD.N0230.N0617.d000163 weight likelihood omega *
          _root_.GD.N0230.N0619.d000389
            weight likelihood center omega decision +
        _root_.GD.N0233.N0726.d003178
          (_root_.GD.N0233.N0725.d003180 weight likelihood omega)
          (_root_.GD.N0230.N0619.d000383 center) (_root_.GD.N0230.N0619.d000383 center) := by
  have hmass : _root_.GD.N0230.N0617.d000163 weight likelihood omega ≠ 0 :=
    (_root_.GD.N0230.N0617.d000169 weight likelihood hweight hlikelihood omega).ne'
  rw [_root_.GD.N0230.N0619.d000403
    weight likelihood center hweight hlikelihood omega decision]
  rw [_root_.GD.N0230.N0619.d000395
    weight likelihood center omega decision hmass]
  rw [_root_.GD.N0233.N0725.d003186
    weight likelihood center hweight hlikelihood omega]
  ring









section FirewallWitnesses

local instance d003190 : MeasurableSpace PUnit := ⊤

private def d003191 : PUnit → ℝ := fun _ ↦ 1

private def d003192 : PUnit → PUnit → ℝ := fun _ _ ↦ 1

private def d003193 : PUnit → ℝ := fun _ ↦ 0

private def d003194 : PUnit → ℝ := fun _ ↦ 1

@[simp]
private theorem d003195 :
    _root_.GD.N0230.N0617.d000163 _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192 PUnit.unit = 2 := by
  simp [_root_.GD.N0230.N0617.d000163, _root_.GD.N0233.N0725.d003191, _root_.GD.N0233.N0725.d003192]
  norm_num

@[simp]
private theorem d003196 :
    _root_.GD.N0230.N0617.d000164 _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192 _root_.GD.N0233.N0725.d003194
        PUnit.unit = 1 := by
  simp [_root_.GD.N0230.N0617.d000164, _root_.GD.N0233.N0725.d003191, _root_.GD.N0233.N0725.d003192, _root_.GD.N0233.N0725.d003194]

@[simp]
private theorem d003197 :
    _root_.GD.N0230.N0617.d000164 _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192 _root_.GD.N0233.N0725.d003193
        PUnit.unit = 0 := by
  simp [_root_.GD.N0230.N0617.d000164, _root_.GD.N0233.N0725.d003191, _root_.GD.N0233.N0725.d003192, _root_.GD.N0233.N0725.d003193]

@[simp]
private theorem d003198 :
    _root_.GD.N0230.N0617.d000165 _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192
          _root_.GD.N0233.N0725.d003194 PUnit.unit -
        _root_.GD.N0230.N0617.d000167 _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192 _root_.GD.N0233.N0725.d003194
          PUnit.unit = 1 / 2 := by
  simp [_root_.GD.N0230.N0617.d000165, _root_.GD.N0230.N0617.d000167, _root_.GD.N0230.N0617.d000164,
    _root_.GD.N0230.N0617.d000163, _root_.GD.N0233.N0725.d003191, _root_.GD.N0233.N0725.d003192, _root_.GD.N0233.N0725.d003194]
  norm_num

@[simp]
private theorem d003199 :
    _root_.GD.N0230.N0617.d000165 _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192
          _root_.GD.N0233.N0725.d003193 PUnit.unit -
        _root_.GD.N0230.N0617.d000167 _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192 _root_.GD.N0233.N0725.d003193
          PUnit.unit = 0 := by
  simp [_root_.GD.N0230.N0617.d000165, _root_.GD.N0230.N0617.d000167, _root_.GD.N0230.N0617.d000164,
    _root_.GD.N0230.N0617.d000163, _root_.GD.N0233.N0725.d003191, _root_.GD.N0233.N0725.d003192, _root_.GD.N0233.N0725.d003193]




theorem d003200 :
    _root_.GD.N0230.N0619.d000389 _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192
        _root_.GD.N0233.N0725.d003194 PUnit.unit (1 / 2) = 0 ∧
      0 < _root_.GD.N0233.N0726.d003178
        (_root_.GD.N0233.N0725.d003180 _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192 PUnit.unit)
        (_root_.GD.N0230.N0619.d000383 _root_.GD.N0233.N0725.d003194)
        (_root_.GD.N0230.N0619.d000383 _root_.GD.N0233.N0725.d003194) := by
  constructor
  · unfold _root_.GD.N0230.N0619.d000389
    rw [_root_.GD.N0233.N0725.d003195, _root_.GD.N0233.N0725.d003196]
    norm_num
  · have henergy :=
      _root_.GD.N0233.N0725.d003185
        _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192 _root_.GD.N0233.N0725.d003194 PUnit.unit
        (by rw [_root_.GD.N0233.N0725.d003195]; norm_num)
    rw [_root_.GD.N0233.N0725.d003195, _root_.GD.N0233.N0725.d003198] at henergy
    norm_num at henergy
    calc
      0 < (1 : ℝ) := by norm_num
      _ = _root_.GD.N0233.N0726.d003178
          (_root_.GD.N0233.N0725.d003180 _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192 PUnit.unit)
          (_root_.GD.N0230.N0619.d000383 _root_.GD.N0233.N0725.d003194)
          (_root_.GD.N0230.N0619.d000383 _root_.GD.N0233.N0725.d003194) := henergy




theorem d003201 :
    _root_.GD.N0233.N0726.d003178
        (_root_.GD.N0233.N0725.d003180 _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192 PUnit.unit)
        (_root_.GD.N0230.N0619.d000383 _root_.GD.N0233.N0725.d003193)
        (_root_.GD.N0230.N0619.d000383 _root_.GD.N0233.N0725.d003193) = 0 ∧
      0 < _root_.GD.N0230.N0619.d000389 _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192
        _root_.GD.N0233.N0725.d003193 PUnit.unit 1 := by
  constructor
  · have henergy :=
      _root_.GD.N0233.N0725.d003185
        _root_.GD.N0233.N0725.d003191 _root_.GD.N0233.N0725.d003192 _root_.GD.N0233.N0725.d003193 PUnit.unit
        (by rw [_root_.GD.N0233.N0725.d003195]; norm_num)
    rw [_root_.GD.N0233.N0725.d003195, _root_.GD.N0233.N0725.d003199] at henergy
    norm_num at henergy
    exact henergy.symm
  · unfold _root_.GD.N0230.N0619.d000389
    rw [_root_.GD.N0233.N0725.d003195, _root_.GD.N0233.N0725.d003197]
    norm_num

end FirewallWitnesses

end

end N0725
end N0233
end GD

#print axioms _root_.GD.N0233.N0725.d003185
#print axioms _root_.GD.N0233.N0725.d003187
#print axioms _root_.GD.N0233.N0725.d003188
#print axioms _root_.GD.N0233.N0725.d003189
#print axioms _root_.GD.N0233.N0725.d003200
#print axioms _root_.GD.N0233.N0725.d003201
