import GD.Module1652
import GD.Module0532








set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set

namespace GD.N0101.N0363
noncomputable section

open _root_.GD.N0101.N0397 _root_.GD.N0101.N0362
open _root_.GD.N0213.N0526
open _root_.GD.N0208.N0455

def d028128 (r₀ r₁ : ℝ) (β : _root_.GD.N0101.N0362.d007943) : _root_.GD.N0101.N0362.d007943 :=
  _root_.GD.N0101.N0397.d028118.symm (_root_.GD.N0213.N0526.d028101 r₀ r₁ (_root_.GD.N0101.N0397.d028118 β))

@[simp] theorem d028129 (r₀ r₁ : ℝ) (β : _root_.GD.N0101.N0362.d007943) :
    _root_.GD.N0101.N0363.d028128 r₀ r₁ β 0 = (r₁ / r₀) * β 1 := rfl

@[simp] theorem d028130 (r₀ r₁ : ℝ) (β : _root_.GD.N0101.N0362.d007943) :
    _root_.GD.N0101.N0363.d028128 r₀ r₁ β 1 = (r₀ / r₁) * β 0 := rfl

@[fun_prop] theorem d028131 (r₀ r₁ : ℝ) : Measurable (_root_.GD.N0101.N0363.d028128 r₀ r₁) :=
  _root_.GD.N0101.N0397.d028118.symm.measurable.comp ((_root_.GD.N0213.N0526.d028102 r₀ r₁).comp _root_.GD.N0101.N0397.d028118.measurable)

theorem d028132 {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    {β : _root_.GD.N0101.N0362.d007943} (hβ : β ∈ _root_.GD.N0101.N0362.d007944) : _root_.GD.N0101.N0363.d028128 r₀ r₁ β ∈ _root_.GD.N0101.N0362.d007944 := by
  change ∀ i, 0 < _root_.GD.N0101.N0363.d028128 r₀ r₁ β i
  intro i
  fin_cases i
  · exact mul_pos (div_pos h₁ h₀) (hβ 1)
  · exact mul_pos (div_pos h₀ h₁) (hβ 0)

theorem d028133 {r₀ r₁ : ℝ} (h₀ : r₀ ≠ 0) (h₁ : r₁ ≠ 0) :
    Function.Involutive (_root_.GD.N0101.N0363.d028128 r₀ r₁) := by
  intro β
  unfold _root_.GD.N0101.N0363.d028128
  rw [_root_.GD.N0101.N0397.d028118.apply_symm_apply, _root_.GD.N0213.N0526.d028103 h₀ h₁, _root_.GD.N0101.N0397.d028118.symm_apply_apply]

theorem d028134 {r₀ r₁ : ℝ} (h₀ : r₀ ≠ 0) (h₁ : r₁ ≠ 0) (β : _root_.GD.N0101.N0362.d007943) :
    _root_.GD.N0101.N0363.d028128 r₀ r₁ β 0 * _root_.GD.N0101.N0363.d028128 r₀ r₁ β 1 = β 0 * β 1 :=
  _root_.GD.N0213.N0526.d028104 h₀ h₁ (_root_.GD.N0101.N0397.d028118 β)

theorem d028135 {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    {β : _root_.GD.N0101.N0362.d007943} (hβ : β ∈ _root_.GD.N0101.N0362.d007944) :
    _root_.GD.N0101.N0362.d007945 (_root_.GD.N0101.N0363.d028128 r₀ r₁ β) = _root_.GD.N0101.N0362.d007945 β := by
  rw [_root_.GD.N0101.N0362.d007951 (_root_.GD.N0101.N0363.d028132 h₀ h₁ hβ),
    _root_.GD.N0101.N0362.d007951 hβ, _root_.GD.N0101.N0363.d028134 h₀.ne' h₁.ne']

theorem d028136 {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    {β : _root_.GD.N0101.N0362.d007943} (hβ : β ∈ _root_.GD.N0101.N0362.d007944) :
    _root_.GD.N0101.N0362.d007946 (_root_.GD.N0101.N0363.d028128 r₀ r₁ β) = Real.log (r₁ / r₀) - _root_.GD.N0101.N0362.d007946 β := by
  unfold _root_.GD.N0101.N0362.d007946
  rw [_root_.GD.N0101.N0363.d028129, _root_.GD.N0101.N0363.d028130,
    Real.log_mul (div_ne_zero h₁.ne' h₀.ne') (hβ 1).ne',
    Real.log_mul (div_ne_zero h₀.ne' h₁.ne') (hβ 0).ne']
  simp only [Real.log_div h₁.ne' h₀.ne', Real.log_div h₀.ne' h₁.ne']
  ring

def d028137 (β t : _root_.GD.N0101.N0362.d007943) : _root_.GD.N0101.N0362.d007943 := fun i => β i * t i

theorem d028138 {β t : _root_.GD.N0101.N0362.d007943} (hβ : β ∈ _root_.GD.N0101.N0362.d007944) (ht : t ∈ _root_.GD.N0101.N0362.d007944) :
    _root_.GD.N0101.N0363.d028137 β t ∈ _root_.GD.N0101.N0362.d007944 := fun i => mul_pos (hβ i) (ht i)



theorem d028139 {a : ℝ} (ha : 0 < a) {β t : _root_.GD.N0101.N0362.d007943}
    (hβ : β ∈ _root_.GD.N0101.N0362.d007944) (ht : t ∈ _root_.GD.N0101.N0362.d007944) :
    _root_.GD.N0101.N0362.d007946 (_root_.GD.N0101.N0363.d028128 (a * t 0) (a * t 1) β) =
      _root_.GD.N0101.N0362.d007946 β - Real.log (_root_.GD.N0101.N0363.d028137 β t 0 / _root_.GD.N0101.N0363.d028137 β t 1) := by
  rw [_root_.GD.N0101.N0363.d028136 (mul_pos ha (ht 0)) (mul_pos ha (ht 1)) hβ]
  unfold _root_.GD.N0101.N0363.d028137 _root_.GD.N0101.N0362.d007946
  rw [Real.log_div (mul_ne_zero ha.ne' (ht 1).ne') (mul_ne_zero ha.ne' (ht 0).ne'),
    Real.log_div (mul_ne_zero (hβ 0).ne' (ht 0).ne')
      (mul_ne_zero (hβ 1).ne' (ht 1).ne'),
    Real.log_mul ha.ne' (ht 1).ne', Real.log_mul ha.ne' (ht 0).ne',
    Real.log_mul (hβ 0).ne' (ht 0).ne', Real.log_mul (hβ 1).ne' (ht 1).ne']
  ring

theorem d028140 (N : ℝ) {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    {β : _root_.GD.N0101.N0362.d007943} (hβ : β ∈ _root_.GD.N0101.N0362.d007944) :
    _root_.GD.N0101.N0362.d007947 N (_root_.GD.N0101.N0363.d028128 r₀ r₁ β) =
      _root_.GD.N0208.N0455.d007937 N (_root_.GD.N0101.N0362.d007945 β) * _root_.GD.N0208.N0455.d007937 N (Real.log (r₁ / r₀) - _root_.GD.N0101.N0362.d007946 β) := by
  rw [_root_.GD.N0101.N0362.d007947, if_pos (_root_.GD.N0101.N0363.d028132 h₀ h₁ hβ),
    _root_.GD.N0101.N0363.d028135 h₀ h₁ hβ, _root_.GD.N0101.N0363.d028136 h₀ h₁ hβ]

theorem d028141 (N : ℝ) {a : ℝ} (ha : 0 < a)
    {β t : _root_.GD.N0101.N0362.d007943} (hβ : β ∈ _root_.GD.N0101.N0362.d007944) (ht : t ∈ _root_.GD.N0101.N0362.d007944) :
    _root_.GD.N0101.N0362.d007947 N (_root_.GD.N0101.N0363.d028128 (a * t 0) (a * t 1) β) =
      _root_.GD.N0208.N0455.d007937 N (_root_.GD.N0101.N0362.d007945 β) *
        _root_.GD.N0208.N0455.d007937 N (_root_.GD.N0101.N0362.d007946 β - Real.log (_root_.GD.N0101.N0363.d028137 β t 0 / _root_.GD.N0101.N0363.d028137 β t 1)) := by
  rw [_root_.GD.N0101.N0362.d007947, if_pos (_root_.GD.N0101.N0363.d028132 (mul_pos ha (ht 0)) (mul_pos ha (ht 1)) hβ),
    _root_.GD.N0101.N0363.d028135 (mul_pos ha (ht 0)) (mul_pos ha (ht 1)) hβ,
    _root_.GD.N0101.N0363.d028139 ha hβ ht]



theorem d028142 (N : ℝ) {a : ℝ} (ha : 0 < a)
    {β t : _root_.GD.N0101.N0362.d007943} (hβ : β ∈ _root_.GD.N0101.N0362.d007944) (ht : t ∈ _root_.GD.N0101.N0362.d007944) :
    (_root_.GD.N0101.N0362.d007947 N β - _root_.GD.N0101.N0362.d007947 N (_root_.GD.N0101.N0363.d028128 (a * t 0) (a * t 1) β)) ^ 2 =
      _root_.GD.N0208.N0455.d007937 N (_root_.GD.N0101.N0362.d007945 β) ^ 2 *
        (_root_.GD.N0208.N0455.d007937 N (_root_.GD.N0101.N0362.d007946 β) -
          _root_.GD.N0208.N0455.d007937 N (_root_.GD.N0101.N0362.d007946 β - Real.log (_root_.GD.N0101.N0363.d028137 β t 0 / _root_.GD.N0101.N0363.d028137 β t 1))) ^ 2 := by
  rw [_root_.GD.N0101.N0363.d028141 N ha hβ ht, _root_.GD.N0101.N0362.d007947, if_pos hβ]
  ring

end
end GD.N0101.N0363

#print axioms _root_.GD.N0101.N0363.d028132
#print axioms _root_.GD.N0101.N0363.d028133
#print axioms _root_.GD.N0101.N0363.d028135
#print axioms _root_.GD.N0101.N0363.d028136
#print axioms _root_.GD.N0101.N0363.d028139
#print axioms _root_.GD.N0101.N0363.d028141
#print axioms _root_.GD.N0101.N0363.d028142
