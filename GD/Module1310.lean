import GD.Module1301
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts











set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0106.N0428.N0765.N1663
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1538

def d021403 (e x : ℝ) : ℝ := 1 - x + e * x

def d021404 (e x : ℝ) : ℝ := e * x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x

def d021405 (e x : ℝ) : ℝ := e / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 2

theorem d021406 {e x : ℝ} (he : 0 < e) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < _root_.GD.N0106.N0428.N0765.N1663.d021403 e x := by
  unfold _root_.GD.N0106.N0428.N0765.N1663.d021403
  rcases lt_or_eq_of_le hx.2 with h | rfl
  · exact add_pos_of_pos_of_nonneg (sub_pos.mpr h) (mul_nonneg he.le hx.1)
  · simpa using he

theorem d021407 {e x : ℝ} (he : 0 < e)
    (hx : x ∈ Icc (0 : ℝ) 1) : _root_.GD.N0106.N0428.N0765.N1663.d021404 e x ∈ Icc (0 : ℝ) 1 := by
  have hD := _root_.GD.N0106.N0428.N0765.N1663.d021406 he hx
  constructor
  · exact div_nonneg (mul_nonneg he.le hx.1) hD.le
  · apply (div_le_one hD).mpr
    dsimp [_root_.GD.N0106.N0428.N0765.N1663.d021403]
    linarith [hx.2]

theorem d021408 {e x : ℝ} (he : 0 < e)
    (hx : x ∈ Ioo (0 : ℝ) 1) : _root_.GD.N0106.N0428.N0765.N1663.d021404 e x ∈ Ioo (0 : ℝ) 1 := by
  have hD := _root_.GD.N0106.N0428.N0765.N1663.d021406 he (Ioo_subset_Icc_self hx)
  constructor
  · exact div_pos (mul_pos he hx.1) hD
  · apply (div_lt_one hD).mpr
    dsimp [_root_.GD.N0106.N0428.N0765.N1663.d021403]
    linarith [hx.2]

@[simp] theorem d021409 (e : ℝ) : _root_.GD.N0106.N0428.N0765.N1663.d021404 e 0 = 0 := by
  simp [_root_.GD.N0106.N0428.N0765.N1663.d021404, _root_.GD.N0106.N0428.N0765.N1663.d021403]

@[simp] theorem d021410 {e : ℝ} (he : 0 < e) : _root_.GD.N0106.N0428.N0765.N1663.d021404 e 1 = 1 := by
  simp [_root_.GD.N0106.N0428.N0765.N1663.d021404, _root_.GD.N0106.N0428.N0765.N1663.d021403, he.ne']

theorem d021411 {e x : ℝ} (he : 0 < e)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    1 - _root_.GD.N0106.N0428.N0765.N1663.d021404 e x = (1 - x) / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x := by
  have hD := (_root_.GD.N0106.N0428.N0765.N1663.d021406 he hx).ne'
  unfold _root_.GD.N0106.N0428.N0765.N1663.d021404
  field_simp
  simp [_root_.GD.N0106.N0428.N0765.N1663.d021403]

theorem d021412 {e x : ℝ} (he : 0 < e)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1663.d021404 e x * (1 - _root_.GD.N0106.N0428.N0765.N1663.d021404 e x) = _root_.GD.N0106.N0428.N0765.N1663.d021405 e x * (x * (1 - x)) := by
  rw [_root_.GD.N0106.N0428.N0765.N1663.d021411 he hx]
  unfold _root_.GD.N0106.N0428.N0765.N1663.d021404 _root_.GD.N0106.N0428.N0765.N1663.d021405
  ring

theorem d021413 {e x : ℝ} (he : 0 < e) :
    e⁻¹ * _root_.GD.N0106.N0428.N0765.N1663.d021404 e x = x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x := by
  unfold _root_.GD.N0106.N0428.N0765.N1663.d021404
  rw [← mul_div_assoc, inv_mul_cancel_left₀ he.ne']

theorem d021414 {e x : ℝ} (he : 0 < e) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < _root_.GD.N0106.N0428.N0765.N1663.d021405 e x :=
  div_pos he (sq_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1663.d021406 he hx))

theorem d021415 {e x : ℝ} (he : 0 < e)
    (hx : x ∈ Icc (0 : ℝ) 1) : HasDerivAt (_root_.GD.N0106.N0428.N0765.N1663.d021404 e) (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x) x := by
  have hD := (_root_.GD.N0106.N0428.N0765.N1663.d021406 he hx).ne'
  have hn := (hasDerivAt_id x).const_mul e
  have hd := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
    ((hasDerivAt_id x).const_mul e)
  apply (hn.div hd hD).congr_deriv
  change (e * 1 * (1 - x + e * x) - e * x * (0 - 1 + e * 1)) /
    (1 - x + e * x) ^ 2 = e / (1 - x + e * x) ^ 2
  ring

theorem d021416 {e : ℝ} (he : 0 < e) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1663.d021405 e) (Icc (0 : ℝ) 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1663.d021405
  apply continuousOn_const.div
  · exact (show ContinuousOn (_root_.GD.N0106.N0428.N0765.N1663.d021403 e) (Icc (0 : ℝ) 1) by
      unfold _root_.GD.N0106.N0428.N0765.N1663.d021403
      fun_prop).pow 2
  · intro x hx
    exact pow_ne_zero 2 (_root_.GD.N0106.N0428.N0765.N1663.d021406 he hx).ne'


theorem d021417 {e : ℝ} (he : 0 < e) (g : ℝ → ℂ)
    (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    (∫ x in (0 : ℝ)..1, (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x : ℂ) * g (_root_.GD.N0106.N0428.N0765.N1663.d021404 e x)) =
      ∫ l in (0 : ℝ)..1, g l := by
  have hder : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (_root_.GD.N0106.N0428.N0765.N1663.d021404 e) (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x) x := by
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    exact _root_.GD.N0106.N0428.N0765.N1663.d021415 he hx
  have hj : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1663.d021405 e) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact _root_.GD.N0106.N0428.N0765.N1663.d021416 he
  have hmap : _root_.GD.N0106.N0428.N0765.N1663.d021404 e '' uIcc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [uIcc_of_le zero_le_one] at hx
    exact _root_.GD.N0106.N0428.N0765.N1663.d021407 he hx
  simpa only [Function.comp_apply, Complex.real_smul, _root_.GD.N0106.N0428.N0765.N1663.d021409,
    _root_.GD.N0106.N0428.N0765.N1663.d021410 he] using
    (intervalIntegral.integral_deriv_smul_comp' hder hj (hg.mono hmap))


def d021418 (e a b α β x : ℝ) : ℂ :=
  (Complex.exp ((b : ℂ) + (β : ℂ) * Complex.I) * (1 - (x : ℂ)) + (x : ℂ)) *
      ((1 - (x : ℂ)) + (e : ℂ) * (x : ℂ)) +
    (1 + (e : ℂ)) * Complex.exp ((a : ℂ) + (α : ℂ) * Complex.I) *
      (1 + Complex.exp ((b : ℂ) + (β : ℂ) * Complex.I)) *
      (x : ℂ) * (1 - (x : ℂ))


theorem d021419 {e x : ℝ} (he : 0 < e) (hx : x ∈ Icc (0 : ℝ) 1)
    (a b α β : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1538.d021210 e a b α β (_root_.GD.N0106.N0428.N0765.N1663.d021404 e x) =
      (_root_.GD.N0106.N0428.N0765.N1663.d021405 e x : ℂ) * _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x := by
  have hD : (_root_.GD.N0106.N0428.N0765.N1663.d021403 e x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (_root_.GD.N0106.N0428.N0765.N1663.d021406 he hx).ne'
  rw [_root_.GD.N0106.N0428.N0765.N1538.d021211]
  unfold _root_.GD.N0106.N0428.N0765.N1663.d021404 _root_.GD.N0106.N0428.N0765.N1663.d021405 _root_.GD.N0106.N0428.N0765.N1663.d021418
  push_cast
  field_simp [hD]
  simp only [_root_.GD.N0106.N0428.N0765.N1663.d021403, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_one]
  ring

theorem d021420 {e x : ℝ} (he : 0 < e) (hx : x ∈ Icc (0 : ℝ) 1)
    (a b α β : ℝ) (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x ≠ 0 := by
  intro hz
  have h := _root_.GD.N0106.N0428.N0765.N1538.d021220 he a b α β (_root_.GD.N0106.N0428.N0765.N1663.d021407 he hx) hw
  rw [_root_.GD.N0106.N0428.N0765.N1663.d021419 he hx a b α β, hz, mul_zero] at h
  exact h rfl


theorem d021421 {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z ≠ 0) (q : ℂ) :
    ((c : ℂ) * z) ^ q = (c : ℂ) ^ q * z ^ q := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hcC hz),
    Complex.cpow_def_of_ne_zero hcC, Complex.cpow_def_of_ne_zero hz,
    Complex.log_ofReal_mul hc hz, ← Complex.ofReal_log hc.le, add_mul, Complex.exp_add]

end
end GD.N0106.N0428.N0765.N1663

#print axioms _root_.GD.N0106.N0428.N0765.N1663.d021415
#print axioms _root_.GD.N0106.N0428.N0765.N1663.d021417
#print axioms _root_.GD.N0106.N0428.N0765.N1663.d021419
#print axioms _root_.GD.N0106.N0428.N0765.N1663.d021420
#print axioms _root_.GD.N0106.N0428.N0765.N1663.d021421
