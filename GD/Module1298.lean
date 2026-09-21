import GD.Module1285
import GD.Module0185



















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0106.N0428.N0765.N1627
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1611
open _root_.GD.N0106.N0428.N0765.N1606 hiding d012618
open _root_.GD.N0106.N0428.N0765.N1607 hiding d012638
open _root_.GD.N0106.N0428.N0765.N1610 hiding d020743
open _root_.GD.N0106.N0428.N0765.N1529 hiding d020796
open _root_.GD.N0235
open _root_.GD.N0228.N0547.N0791
open _root_.GD.N0232.N0720.N1249

abbrev d021078 := Fin 3 → ℝ
abbrev d021079 := ℝ × (ℝ × ℝ)


def d021080 (p : _root_.GD.N0106.N0428.N0765.N1627.d021078) : _root_.GD.N0106.N0428.N0765.N1627.d021078 := ![p 0, p 2, p 1]

def d021081 : _root_.GD.N0106.N0428.N0765.N1627.d021079 → _root_.GD.N0106.N0428.N0765.N1627.d021079 := Prod.map id Prod.swap

@[fun_prop] theorem d021082 : Measurable _root_.GD.N0106.N0428.N0765.N1627.d021080 := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp [_root_.GD.N0106.N0428.N0765.N1627.d021080] <;> fun_prop

@[fun_prop] theorem d021083 : Measurable _root_.GD.N0106.N0428.N0765.N1627.d021081 := by
  unfold _root_.GD.N0106.N0428.N0765.N1627.d021081
  fun_prop

theorem d021084 : Function.Involutive _root_.GD.N0106.N0428.N0765.N1627.d021080 := by
  intro p
  funext i
  fin_cases i <;> simp [_root_.GD.N0106.N0428.N0765.N1627.d021080]

theorem d021085 (p : _root_.GD.N0106.N0428.N0765.N1627.d021079) :
    _root_.GD.N0228.N0547.N0791.d012866 (_root_.GD.N0106.N0428.N0765.N1627.d021081 p) = _root_.GD.N0106.N0428.N0765.N1627.d021080 (_root_.GD.N0228.N0547.N0791.d012866 p) := by
  funext i
  fin_cases i <;>
    simp [_root_.GD.N0228.N0547.N0791.d012866, _root_.GD.N0106.N0428.N0765.N1627.d021081, _root_.GD.N0228.N0547.N0791.d012864, _root_.GD.N0106.N0428.N0765.N1627.d021080, add_comm]


theorem d021086 :
    _root_.GD.N0106.N0428.N0765.N1633.d014079.map _root_.GD.N0106.N0428.N0765.N1627.d021081 = _root_.GD.N0106.N0428.N0765.N1633.d014079 := by
  letI : IsProbabilityMeasure (gammaMeasure ((3 : ℝ) / 2) ((1 : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure (gammaMeasure 5 ((1 : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  unfold _root_.GD.N0106.N0428.N0765.N1633.d014079 _root_.GD.N0106.N0428.N0765.N1627.d021081
  rw [← Measure.map_prod_map _ _ measurable_id _root_.measurable_swap,
    Measure.map_id, Measure.prod_swap]

theorem d021087 :
    _root_.GD.N0106.N0428.N0765.N1633.d014079.map _root_.GD.N0228.N0547.N0791.d012866 = _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
  _root_.GD.N0228.N0547.N0791.d012873 (by norm_num) (by norm_num) (by norm_num) (by norm_num)


theorem d021088 : _root_.GD.N0106.N0428.N0765.N1529.d020798.map _root_.GD.N0106.N0428.N0765.N1627.d021080 = _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  calc
    _root_.GD.N0106.N0428.N0765.N1529.d020798.map _root_.GD.N0106.N0428.N0765.N1627.d021080 = (_root_.GD.N0106.N0428.N0765.N1633.d014079.map _root_.GD.N0228.N0547.N0791.d012866).map _root_.GD.N0106.N0428.N0765.N1627.d021080 := by
      rw [_root_.GD.N0106.N0428.N0765.N1627.d021087]
    _ = _root_.GD.N0106.N0428.N0765.N1633.d014079.map (_root_.GD.N0106.N0428.N0765.N1627.d021080 ∘ _root_.GD.N0228.N0547.N0791.d012866) :=
      Measure.map_map _root_.GD.N0106.N0428.N0765.N1627.d021082 _root_.GD.N0228.N0547.N0791.d012867
    _ = _root_.GD.N0106.N0428.N0765.N1633.d014079.map (_root_.GD.N0228.N0547.N0791.d012866 ∘ _root_.GD.N0106.N0428.N0765.N1627.d021081) := by
      congr 1
      funext p
      exact (_root_.GD.N0106.N0428.N0765.N1627.d021085 p).symm
    _ = (_root_.GD.N0106.N0428.N0765.N1633.d014079.map _root_.GD.N0106.N0428.N0765.N1627.d021081).map _root_.GD.N0228.N0547.N0791.d012866 :=
      (Measure.map_map _root_.GD.N0228.N0547.N0791.d012867 _root_.GD.N0106.N0428.N0765.N1627.d021083).symm
    _ = _root_.GD.N0106.N0428.N0765.N1529.d020798 := by rw [_root_.GD.N0106.N0428.N0765.N1627.d021086, _root_.GD.N0106.N0428.N0765.N1627.d021087]


theorem d021089 (location eta : ℝ) (heta : 0 < eta) :
    (_root_.GD.N0106.N0428.N0765.N1633.d014078 location eta).map (_root_.GD.N0106.N0428.N0765.N1627.d021080 ∘ _root_.GD.N0106.N0428.N0765.N1633.d014080 eta) =
      _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  rw [← Measure.map_map _root_.GD.N0106.N0428.N0765.N1627.d021082 (_root_.GD.N0106.N0428.N0765.N1633.d014085 eta),
    _root_.GD.N0106.N0428.N0765.N1633.d014101 location eta heta]
  exact _root_.GD.N0106.N0428.N0765.N1627.d021088

theorem d021090 :
    ∀ᵐ p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798, 0 ≤ p 0 ∧ 0 < p 1 ∧ 0 < p 2 := by
  rw [← _root_.GD.N0106.N0428.N0765.N1627.d021087]
  apply (ae_map_iff _root_.GD.N0228.N0547.N0791.d012867.aemeasurable ?_).2
  · filter_upwards [_root_.GD.N0228.N0547.N0791.d012871 (by norm_num : (0 : ℝ) < 3 / 2)
      (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5)
      (by norm_num : (0 : ℝ) < 1 / 2)] with p hp
    have htotal : 0 < _root_.GD.N0228.N0547.N0791.d012864 p := add_pos hp.1 (add_pos hp.2.1 hp.2.2)
    change 0 ≤ p.1 / _root_.GD.N0228.N0547.N0791.d012864 p ∧
      0 < p.2.1 / _root_.GD.N0228.N0547.N0791.d012864 p ∧ 0 < p.2.2 / _root_.GD.N0228.N0547.N0791.d012864 p
    exact ⟨div_nonneg hp.1.le htotal.le,
      div_pos hp.2.1 htotal, div_pos hp.2.2 htotal⟩
  · exact (measurableSet_le measurable_const (measurable_pi_apply 0)).inter
      ((measurableSet_lt measurable_const (measurable_pi_apply 1)).inter
        (measurableSet_lt measurable_const (measurable_pi_apply 2)))

theorem d021091 (f : _root_.GD.N0106.N0428.N0765.N1627.d021078 → ℝ) (hf : Measurable f) :
    (∫ p, f (_root_.GD.N0106.N0428.N0765.N1627.d021080 p) ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) = ∫ p, f p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  have h := integral_map _root_.GD.N0106.N0428.N0765.N1627.d021082.aemeasurable hf.aestronglyMeasurable
    (μ := _root_.GD.N0106.N0428.N0765.N1529.d020798)
  rw [_root_.GD.N0106.N0428.N0765.N1627.d021088] at h
  exact h.symm


theorem d021092 (eta : ℝ) (heta : 0 < eta) :
    (1 + eta) / 11 = eta * ((1 + eta⁻¹) / 11) := by
  field_simp [heta.ne']
  <;> ring

theorem d021093 (eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1607.d012678 eta⁻¹ = 1 - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta := by
  unfold _root_.GD.N0106.N0428.N0765.N1607.d012678
  field_simp [heta.ne', (by positivity : (1 + eta : ℝ) ≠ 0),
    (by positivity : (1 + eta⁻¹ : ℝ) ≠ 0)]
  <;> ring

theorem d021094 (eta : ℝ) (heta : 0 < eta) (p : _root_.GD.N0106.N0428.N0765.N1627.d021078)
    (hp : 0 ≤ p 0 ∧ 0 < p 1 ∧ 0 < p 2) :
    _root_.GD.N0106.N0428.N0765.N1529.d020799 eta⁻¹ (_root_.GD.N0106.N0428.N0765.N1627.d021080 p) = 1 - _root_.GD.N0106.N0428.N0765.N1529.d020799 eta p := by
  change _root_.GD.N0106.N0428.N0765.N1534.d005330 eta⁻¹ (p 0) (p 2) (p 1) =
    1 - _root_.GD.N0106.N0428.N0765.N1534.d005330 eta (p 0) (p 1) (p 2)
  exact _root_.GD.N0106.N0428.N0765.N1534.d005346 heta hp.1 hp.2.1 hp.2.2

theorem d021095 (eta : ℝ) (heta : 0 < eta) (p : _root_.GD.N0106.N0428.N0765.N1627.d021078)
    (hp : 0 ≤ p 0 ∧ 0 < p 1 ∧ 0 < p 2) :
    _root_.GD.N0106.N0428.N0765.N1529.d020800 eta⁻¹ (_root_.GD.N0106.N0428.N0765.N1627.d021080 p) = 1 - _root_.GD.N0106.N0428.N0765.N1529.d020800 eta p := by
  change p 2 / (p 2 + eta⁻¹ * p 1) = 1 - p 1 / (p 1 + eta * p 2)
  have hd : p 1 + eta * p 2 ≠ 0 := (add_pos hp.2.1 (mul_pos heta hp.2.2)).ne'
  have hden : p 2 + eta⁻¹ * p 1 = eta⁻¹ * (p 1 + eta * p 2) := by
    calc
      p 2 + eta⁻¹ * p 1 = eta⁻¹ * p 1 + (eta⁻¹ * eta) * p 2 := by
        rw [inv_mul_cancel₀ heta.ne', one_mul, add_comm]
      _ = eta⁻¹ * (p 1 + eta * p 2) := by ring
  rw [hden, div_mul_eq_div_div, div_inv_eq_mul]
  apply eq_sub_iff_add_eq.mpr
  rw [← add_div,
    show p 2 * eta + p 1 = p 1 + eta * p 2 by ring,
    div_self hd]

theorem d021096 (eta : ℝ) (heta : 0 < eta) (p : _root_.GD.N0106.N0428.N0765.N1627.d021078)
    (hp : 0 ≤ p 0 ∧ 0 < p 1 ∧ 0 < p 2) :
    _root_.GD.N0106.N0428.N0765.N1529.d020801 eta⁻¹ (_root_.GD.N0106.N0428.N0765.N1627.d021080 p) = _root_.GD.N0106.N0428.N0765.N1529.d020801 eta p := by
  change 10 * (1 + eta⁻¹) * p 0 / (p 2 + eta⁻¹ * p 1) =
    10 * (1 + eta) * p 0 / (p 1 + eta * p 2)
  have hd : p 1 + eta * p 2 ≠ 0 := (add_pos hp.2.1 (mul_pos heta hp.2.2)).ne'
  have hden : p 2 + eta⁻¹ * p 1 = eta⁻¹ * (p 1 + eta * p 2) := by
    calc
      p 2 + eta⁻¹ * p 1 = eta⁻¹ * p 1 + (eta⁻¹ * eta) * p 2 := by
        rw [inv_mul_cancel₀ heta.ne', one_mul, add_comm]
      _ = eta⁻¹ * (p 1 + eta * p 2) := by ring
  have hnum : (1 + eta⁻¹) * eta = 1 + eta := by
    rw [add_mul, one_mul, inv_mul_cancel₀ heta.ne']
    ring
  rw [hden, div_mul_eq_div_div, div_inv_eq_mul]
  apply (div_left_inj' hd).2
  calc
    10 * (1 + eta⁻¹) * p 0 * eta = 10 * p 0 * ((1 + eta⁻¹) * eta) := by ring
    _ = 10 * (1 + eta) * p 0 := by rw [hnum]; ring

theorem d021097 (eta : ℝ) (heta : 0 < eta) (p : _root_.GD.N0106.N0428.N0765.N1627.d021078)
    (hp : 0 ≤ p 0 ∧ 0 < p 1 ∧ 0 < p 2) :
    _root_.GD.N0106.N0428.N0765.N1529.d020802 eta⁻¹ (_root_.GD.N0106.N0428.N0765.N1627.d021080 p) = _root_.GD.N0106.N0428.N0765.N1529.d020802 eta p := by
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020802
  rw [_root_.GD.N0106.N0428.N0765.N1627.d021095 eta heta p hp, _root_.GD.N0106.N0428.N0765.N1627.d021094 eta heta p hp,
    _root_.GD.N0106.N0428.N0765.N1627.d021093 eta heta]
  ring


def d021098 (k : Fin 5) : Fin 5 → ℝ :=
  ![![1, 0, 0, 0, 0], ![-1 / 2, 1, 0, 0, 0], ![1 / 4, -1, 1, 0, 0],
    ![-1 / 8, 3 / 4, -3 / 2, 1, 0], ![1 / 16, -1 / 2, 3 / 2, -2, 1]] k

theorem d021099 (k : Fin 5) (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002197 k.val h = ∑ a : Fin 5, _root_.GD.N0106.N0428.N0765.N1627.d021098 k a * _root_.GD.N0106.N0428.N0765.N1607.d012644 a h := by
  fin_cases k <;>
    norm_num [_root_.GD.N0106.N0428.N0765.N1627.d021098, _root_.GD.N0232.N0720.N1249.d002197, _root_.GD.N0106.N0428.N0765.N1607.d012644, Fin.sum_univ_succ] <;> ring

def d021100 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (h z : ℝ) : ℝ :=
  if j.2 = 1 then _root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 h * z else -_root_.GD.N0106.N0428.N0765.N1607.d012644 j.1 h

def d021101 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (h z : ℝ) : ℝ :=
  if j.2 = 1 then _root_.GD.N0232.N0720.N1249.d002197 j.1.val h * z else -_root_.GD.N0232.N0720.N1249.d002197 j.1.val h

def d021102 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (p : _root_.GD.N0106.N0428.N0765.N1627.d021078) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1627.d021101 j (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p) (_root_.GD.N0106.N0428.N0765.N1529.d020801 eta p)

def d021103 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (x : _root_.GD.N0106.N0428.N0765.N1611.d012588) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1627.d021101 j (_root_.GD.N0106.N0428.N0765.N1607.d012641 x) (_root_.GD.N0106.N0428.N0765.N1607.d012642 x)

def d021104 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (p : _root_.GD.N0106.N0428.N0765.N1627.d021078) : ℝ :=
  (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1627.d021102 j eta p


def d021105 (location eta : ℝ) (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) : ℝ :=
  ∫ x, _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1627.d021103 j x
    ∂_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta

theorem d021106 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (h z r : ℝ) :
    r * _root_.GD.N0106.N0428.N0765.N1627.d021101 j h z =
      ∑ a : Fin 5, _root_.GD.N0106.N0428.N0765.N1627.d021098 j.1 a * (r * _root_.GD.N0106.N0428.N0765.N1627.d021100 (a, j.2) h z) := by
  by_cases hj : j.2 = 1
  · simp only [_root_.GD.N0106.N0428.N0765.N1627.d021101, _root_.GD.N0106.N0428.N0765.N1627.d021100, hj, if_pos]
    rw [_root_.GD.N0106.N0428.N0765.N1627.d021099, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  · simp only [_root_.GD.N0106.N0428.N0765.N1627.d021101, _root_.GD.N0106.N0428.N0765.N1627.d021100, hj, if_false]
    rw [_root_.GD.N0106.N0428.N0765.N1627.d021099, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring

theorem d021107 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (p : _root_.GD.N0106.N0428.N0765.N1627.d021078) :
    _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta p =
      ∑ a : Fin 5, _root_.GD.N0106.N0428.N0765.N1627.d021098 j.1 a * _root_.GD.N0106.N0428.N0765.N1529.d020804 (a, j.2) eta p := by
  exact _root_.GD.N0106.N0428.N0765.N1627.d021106 j (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p) (_root_.GD.N0106.N0428.N0765.N1529.d020801 eta p)
    (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta p - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta)

@[fun_prop] theorem d021108 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1627.d021104 j eta) := by
  have hfun : _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta =
      fun p => ∑ a : Fin 5, _root_.GD.N0106.N0428.N0765.N1627.d021098 j.1 a * _root_.GD.N0106.N0428.N0765.N1529.d020804 (a, j.2) eta p :=
    funext (_root_.GD.N0106.N0428.N0765.N1627.d021107 j eta)
  rw [hfun]
  fun_prop

theorem d021109 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (heta : 0 < eta) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1627.d021104 j eta) _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  have hfun : _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta =
      fun p => ∑ a : Fin 5, _root_.GD.N0106.N0428.N0765.N1627.d021098 j.1 a * _root_.GD.N0106.N0428.N0765.N1529.d020804 (a, j.2) eta p :=
    funext (_root_.GD.N0106.N0428.N0765.N1627.d021107 j eta)
  rw [hfun]
  exact integrable_finsetSum _ fun a _ =>
    (_root_.GD.N0106.N0428.N0765.N1529.d020830 (a, j.2) eta heta).const_mul (_root_.GD.N0106.N0428.N0765.N1627.d021098 j.1 a)

theorem d021110 (eta : ℝ) (j : _root_.GD.N0106.N0428.N0765.N1607.d012643)
    (x : _root_.GD.N0106.N0428.N0765.N1611.d012588) :
    _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1627.d021103 j x =
      ∑ a : Fin 5, _root_.GD.N0106.N0428.N0765.N1627.d021098 j.1 a *
        (_root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1607.d012645 (a, j.2) x) := by
  exact _root_.GD.N0106.N0428.N0765.N1627.d021106 j (_root_.GD.N0106.N0428.N0765.N1607.d012641 x) (_root_.GD.N0106.N0428.N0765.N1607.d012642 x)
    (_root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta))

theorem d021111 (location eta : ℝ) (heta : 0 < eta) (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 * (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) *
      _root_.GD.N0106.N0428.N0765.N1627.d021103 j x) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta) := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1627.d021110 eta j]
  exact integrable_finsetSum _ fun a _ =>
    (_root_.GD.N0106.N0428.N0765.N1607.d012682 location eta heta (a, j.2)).const_mul (_root_.GD.N0106.N0428.N0765.N1627.d021098 j.1 a)

theorem d021112 (location eta : ℝ) (heta : 0 < eta) (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    _root_.GD.N0106.N0428.N0765.N1627.d021105 location eta j =
      ∑ a : Fin 5, _root_.GD.N0106.N0428.N0765.N1627.d021098 j.1 a * _root_.GD.N0106.N0428.N0765.N1607.d012683 location eta (a, j.2) := by
  unfold _root_.GD.N0106.N0428.N0765.N1627.d021105
  simp_rw [_root_.GD.N0106.N0428.N0765.N1627.d021110 eta j]
  rw [integral_finsetSum _ fun a _ =>
    (_root_.GD.N0106.N0428.N0765.N1607.d012682 location eta heta (a, j.2)).const_mul (_root_.GD.N0106.N0428.N0765.N1627.d021098 j.1 a)]
  simp only [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1607.d012683]

theorem d021113 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (heta : 0 < eta) :
    (∫ p, _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) =
      ∑ a : Fin 5, _root_.GD.N0106.N0428.N0765.N1627.d021098 j.1 a * ∫ p, _root_.GD.N0106.N0428.N0765.N1529.d020804 (a, j.2) eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1627.d021107 j eta]
  rw [integral_finsetSum _ fun a _ =>
    (_root_.GD.N0106.N0428.N0765.N1529.d020830 (a, j.2) eta heta).const_mul (_root_.GD.N0106.N0428.N0765.N1627.d021098 j.1 a)]
  simp_rw [integral_const_mul]


theorem d021114 (location eta : ℝ) (heta : 0 < eta) (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    _root_.GD.N0106.N0428.N0765.N1627.d021105 location eta j =
      ((1 + eta) / 11) * ∫ p, _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  rw [_root_.GD.N0106.N0428.N0765.N1627.d021112 location eta heta j,
    _root_.GD.N0106.N0428.N0765.N1627.d021113 j eta heta, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020833 location eta heta (a, j.2)]
  ring


theorem d021115 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (heta : 0 < eta)
    (p : _root_.GD.N0106.N0428.N0765.N1627.d021078) (hp : 0 ≤ p 0 ∧ 0 < p 1 ∧ 0 < p 2) :
    _root_.GD.N0106.N0428.N0765.N1627.d021102 j eta⁻¹ (_root_.GD.N0106.N0428.N0765.N1627.d021080 p) =
      (-1 : ℝ) ^ j.1.val * _root_.GD.N0106.N0428.N0765.N1627.d021102 j eta p := by
  unfold _root_.GD.N0106.N0428.N0765.N1627.d021102 _root_.GD.N0106.N0428.N0765.N1627.d021101
  rw [_root_.GD.N0106.N0428.N0765.N1627.d021094 eta heta p hp, _root_.GD.N0106.N0428.N0765.N1627.d021096 eta heta p hp]
  simp only [_root_.GD.N0232.N0720.N1249.d002198]
  split_ifs <;> ring

theorem d021116 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (heta : 0 < eta)
    (p : _root_.GD.N0106.N0428.N0765.N1627.d021078) (hp : 0 ≤ p 0 ∧ 0 < p 1 ∧ 0 < p 2) :
    _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta⁻¹ (_root_.GD.N0106.N0428.N0765.N1627.d021080 p) =
      -((-1 : ℝ) ^ j.1.val) * _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta p := by
  unfold _root_.GD.N0106.N0428.N0765.N1627.d021104
  rw [_root_.GD.N0106.N0428.N0765.N1627.d021094 eta heta p hp, _root_.GD.N0106.N0428.N0765.N1627.d021093 eta heta,
    _root_.GD.N0106.N0428.N0765.N1627.d021115 j eta heta p hp]
  ring

theorem d021117 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    (-((-1 : ℝ) ^ j.1.val)) * (-((-1 : ℝ) ^ j.1.val)) = 1 := by
  rw [neg_mul_neg, ← mul_pow]
  norm_num

theorem d021118 (eta : ℝ) (heta : 0 < eta) :
    (∫ p, _root_.GD.N0106.N0428.N0765.N1529.d020802 eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) = ∫ p, _root_.GD.N0106.N0428.N0765.N1529.d020802 eta⁻¹ p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  calc
    (∫ p, _root_.GD.N0106.N0428.N0765.N1529.d020802 eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) =
        ∫ p, _root_.GD.N0106.N0428.N0765.N1529.d020802 eta⁻¹ (_root_.GD.N0106.N0428.N0765.N1627.d021080 p) ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0106.N0428.N0765.N1627.d021090] with p hp
      exact (_root_.GD.N0106.N0428.N0765.N1627.d021097 eta heta p hp).symm
    _ = ∫ p, _root_.GD.N0106.N0428.N0765.N1529.d020802 eta⁻¹ p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 :=
      _root_.GD.N0106.N0428.N0765.N1627.d021091 _ (_root_.GD.N0106.N0428.N0765.N1529.d020812 eta⁻¹)

theorem d021119 (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) (eta : ℝ) (heta : 0 < eta) :
    (∫ p, _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) =
      -((-1 : ℝ) ^ j.1.val) * ∫ p, _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta⁻¹ p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  calc
    (∫ p, _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) =
        ∫ p, -((-1 : ℝ) ^ j.1.val) * _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta⁻¹ (_root_.GD.N0106.N0428.N0765.N1627.d021080 p)
          ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0106.N0428.N0765.N1627.d021090] with p hp
      rw [_root_.GD.N0106.N0428.N0765.N1627.d021116 j eta heta p hp,
        ← mul_assoc, _root_.GD.N0106.N0428.N0765.N1627.d021117, one_mul]
    _ = -((-1 : ℝ) ^ j.1.val) *
        ∫ p, _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta⁻¹ (_root_.GD.N0106.N0428.N0765.N1627.d021080 p) ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := integral_const_mul _ _
    _ = -((-1 : ℝ) ^ j.1.val) * ∫ p, _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta⁻¹ p ∂_root_.GD.N0106.N0428.N0765.N1529.d020798 := by
      rw [_root_.GD.N0106.N0428.N0765.N1627.d021091 _ (_root_.GD.N0106.N0428.N0765.N1627.d021108 j eta⁻¹)]


def d021120 (location eta : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11)) -
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593


theorem d021121 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1627.d021120 location eta = eta * _root_.GD.N0106.N0428.N0765.N1627.d021120 location eta⁻¹ := by
  unfold _root_.GD.N0106.N0428.N0765.N1627.d021120
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020832 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1529.d020832 location eta⁻¹ (inv_pos.mpr heta),
    _root_.GD.N0106.N0428.N0765.N1627.d021118 eta heta, _root_.GD.N0106.N0428.N0765.N1627.d021092 eta heta]
  ring


theorem d021122 (location eta : ℝ) (heta : 0 < eta)
    (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    _root_.GD.N0106.N0428.N0765.N1627.d021105 location eta j =
      -((-1 : ℝ) ^ j.1.val) * eta * _root_.GD.N0106.N0428.N0765.N1627.d021105 location eta⁻¹ j := by
  rw [_root_.GD.N0106.N0428.N0765.N1627.d021114 location eta heta j,
    _root_.GD.N0106.N0428.N0765.N1627.d021114 location eta⁻¹ (inv_pos.mpr heta) j,
    _root_.GD.N0106.N0428.N0765.N1627.d021119 j eta heta,
    _root_.GD.N0106.N0428.N0765.N1627.d021092 eta heta]
  ring


theorem d021123 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1627.d021120 location eta = eta * _root_.GD.N0106.N0428.N0765.N1627.d021120 location eta⁻¹ ∧
      (∀ j : _root_.GD.N0106.N0428.N0765.N1607.d012643, Integrable (fun x => _root_.GD.N0106.N0428.N0765.N1611.d012591 x ^ 2 *
        (_root_.GD.N0106.N0428.N0765.N1607.d012641 x - _root_.GD.N0106.N0428.N0765.N1607.d012678 eta) * _root_.GD.N0106.N0428.N0765.N1627.d021103 j x) (_root_.GD.N0106.N0428.N0765.N1607.d012639 location eta)) ∧
      ∀ j : _root_.GD.N0106.N0428.N0765.N1607.d012643, _root_.GD.N0106.N0428.N0765.N1627.d021105 location eta j =
        -((-1 : ℝ) ^ j.1.val) * eta * _root_.GD.N0106.N0428.N0765.N1627.d021105 location eta⁻¹ j :=
  ⟨_root_.GD.N0106.N0428.N0765.N1627.d021121 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1627.d021111 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1627.d021122 location eta heta⟩

end
end GD.N0106.N0428.N0765.N1627

#print axioms _root_.GD.N0106.N0428.N0765.N1627.d021086
#print axioms _root_.GD.N0106.N0428.N0765.N1627.d021088
#print axioms _root_.GD.N0106.N0428.N0765.N1627.d021089
#print axioms _root_.GD.N0106.N0428.N0765.N1627.d021099
#print axioms _root_.GD.N0106.N0428.N0765.N1627.d021114
#print axioms _root_.GD.N0106.N0428.N0765.N1627.d021115
#print axioms _root_.GD.N0106.N0428.N0765.N1627.d021116
#print axioms _root_.GD.N0106.N0428.N0765.N1627.d021121
#print axioms _root_.GD.N0106.N0428.N0765.N1627.d021122
#print axioms _root_.GD.N0106.N0428.N0765.N1627.d021123
