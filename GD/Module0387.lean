import GD.Module0359
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic



























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set intervalIntegral

namespace GD.N0106.N0428.N0765.N1679
open _root_.GD.N0106.N0428.N0765.N1534
noncomputable section


def d005880 (r x : ℝ) : ℝ := r + (1 - 2 * r) * x

def d005881 (x : ℝ) : ℝ := x * (1 - x)

def d005882 (r x : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1679.d005881 x / _root_.GD.N0106.N0428.N0765.N1679.d005880 r x

def d005883 (r x : ℝ) : ℝ := r * (1 - x) / _root_.GD.N0106.N0428.N0765.N1679.d005880 r x

def d005884 (r : ℝ) : ℝ := Real.sqrt (r * (1 - r))

def d005885 (r : ℝ) : ℝ := r / (_root_.GD.N0106.N0428.N0765.N1679.d005884 r + r)

def d005886 (r x : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1679.d005880 r x ^ 2 / (r * (1 - r))

def d005887 (r L x : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1679.d005881 x ^ ((9 : ℝ) / 2) * (_root_.GD.N0106.N0428.N0765.N1679.d005880 r x + L * _root_.GD.N0106.N0428.N0765.N1679.d005881 x) ^ (-((21 : ℝ) / 2))

def d005888 (r L : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..1, x * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x) / ∫ x in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x

section Algebra
variable {r : ℝ}

theorem d005889 {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1679.d005881 x :=
  mul_nonneg hx.1 (sub_nonneg.mpr hx.2)

theorem d005890 (hr0 : 0 < r) (hr1 : r < 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 < _root_.GD.N0106.N0428.N0765.N1679.d005880 r x := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005880
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]
    simpa using hr0
  · nlinarith [mul_pos (sub_pos.mpr hr1) h, mul_nonneg hr0.le (sub_nonneg.mpr hx.2)]

theorem d005891 (hr0 : 0 < r) (hr1 : r < 1) : 0 < r * (1 - r) := mul_pos hr0 (sub_pos.mpr hr1)

theorem d005892 (hr0 : 0 < r) (hr1 : r < 1) : 0 < _root_.GD.N0106.N0428.N0765.N1679.d005884 r := Real.sqrt_pos.mpr (_root_.GD.N0106.N0428.N0765.N1679.d005891 hr0 hr1)

theorem d005893 (hr0 : 0 < r) (hr1 : r < 1) : _root_.GD.N0106.N0428.N0765.N1679.d005884 r ^ 2 = r * (1 - r) :=
  Real.sq_sqrt (_root_.GD.N0106.N0428.N0765.N1679.d005891 hr0 hr1).le

theorem d005894 {x : ℝ} (hx : _root_.GD.N0106.N0428.N0765.N1679.d005880 r x ≠ 0) : _root_.GD.N0106.N0428.N0765.N1679.d005880 r (_root_.GD.N0106.N0428.N0765.N1679.d005883 r x) = r * (1 - r) / _root_.GD.N0106.N0428.N0765.N1679.d005880 r x := by
  have hx' : r + (1 - 2 * r) * x ≠ 0 := hx
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005883 _root_.GD.N0106.N0428.N0765.N1679.d005880
  rw [eq_div_iff hx', add_mul, mul_assoc, div_mul_cancel₀ _ hx']
  ring

theorem d005895 {x : ℝ} (hx : _root_.GD.N0106.N0428.N0765.N1679.d005880 r x ≠ 0) : _root_.GD.N0106.N0428.N0765.N1679.d005881 (_root_.GD.N0106.N0428.N0765.N1679.d005883 r x) = r * (1 - r) * _root_.GD.N0106.N0428.N0765.N1679.d005881 x / _root_.GD.N0106.N0428.N0765.N1679.d005880 r x ^ 2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005881 _root_.GD.N0106.N0428.N0765.N1679.d005883
  field_simp
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005880
  ring

theorem d005896 (hr0 : 0 < r) (hr1 : r < 1) {x : ℝ} (hx : _root_.GD.N0106.N0428.N0765.N1679.d005880 r x ≠ 0) : _root_.GD.N0106.N0428.N0765.N1679.d005882 r (_root_.GD.N0106.N0428.N0765.N1679.d005883 r x) = _root_.GD.N0106.N0428.N0765.N1679.d005882 r x := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005882
  rw [_root_.GD.N0106.N0428.N0765.N1679.d005894 hx, _root_.GD.N0106.N0428.N0765.N1679.d005895 hx]
  have h1 : (1 - r) ≠ 0 := by linarith
  have h2 : r ≠ 0 := hr0.ne'
  field_simp

theorem d005897 (hr0 : 0 < r) : _root_.GD.N0106.N0428.N0765.N1679.d005883 r 0 = 1 := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005883 _root_.GD.N0106.N0428.N0765.N1679.d005880
  simp [hr0.ne']

theorem d005898 (hr0 : 0 < r) (hr1 : r < 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1679.d005883 r x ∈ Icc (0 : ℝ) 1 := by
  have hc := _root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hx
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005883
  constructor
  · exact div_nonneg (mul_nonneg hr0.le (sub_nonneg.mpr hx.2)) hc.le
  · rw [div_le_one hc]
    unfold _root_.GD.N0106.N0428.N0765.N1679.d005880
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) hx.1]

theorem d005899 {x : ℝ} (hx : _root_.GD.N0106.N0428.N0765.N1679.d005880 r x ≠ 0) :
    HasDerivAt (_root_.GD.N0106.N0428.N0765.N1679.d005883 r) (-(r * (1 - r)) / _root_.GD.N0106.N0428.N0765.N1679.d005880 r x ^ 2) x := by
  have hu : HasDerivAt (fun y : ℝ => r * (1 - y)) (-r) x := by
    have h := ((hasDerivAt_id x).const_sub 1).const_mul r
    simpa using h
  have hv : HasDerivAt (_root_.GD.N0106.N0428.N0765.N1679.d005880 r) (1 - 2 * r) x := by
    have h := ((hasDerivAt_id x).const_mul (1 - 2 * r)).const_add r
    exact h.congr_deriv (mul_one _)
  refine (hu.div hv hx).congr_deriv ?_
  rw [div_eq_div_iff (pow_ne_zero 2 hx) (pow_ne_zero 2 hx)]
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005880
  ring

theorem d005900 (r : ℝ) : Continuous (_root_.GD.N0106.N0428.N0765.N1679.d005880 r) := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005880
  fun_prop

theorem d005901 : Continuous _root_.GD.N0106.N0428.N0765.N1679.d005881 := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005881
  fun_prop

theorem d005902 (hr0 : 0 < r) (hr1 : r < 1) : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1679.d005883 r) (Icc 0 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005883
  exact (by fun_prop : Continuous fun x : ℝ => r * (1 - x)).continuousOn.div
    (_root_.GD.N0106.N0428.N0765.N1679.d005900 r).continuousOn (fun x hx => (_root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hx).ne')

theorem d005903 (hr0 : 0 < r) (hr1 : r < 1) : _root_.GD.N0106.N0428.N0765.N1679.d005885 r ∈ Ioo (0 : ℝ) 1 := by
  have hs := _root_.GD.N0106.N0428.N0765.N1679.d005892 hr0 hr1
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005885
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]
    linarith

theorem d005904 (hr0 : 0 < r) (hr1 : r < 1) : _root_.GD.N0106.N0428.N0765.N1679.d005880 r (_root_.GD.N0106.N0428.N0765.N1679.d005885 r) = _root_.GD.N0106.N0428.N0765.N1679.d005884 r := by
  have hs := _root_.GD.N0106.N0428.N0765.N1679.d005892 hr0 hr1
  have hsq := _root_.GD.N0106.N0428.N0765.N1679.d005893 hr0 hr1
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005880 _root_.GD.N0106.N0428.N0765.N1679.d005885
  field_simp
  nlinarith [hsq]

theorem d005905 (hr0 : 0 < r) (hr1 : r < 1) : _root_.GD.N0106.N0428.N0765.N1679.d005883 r (_root_.GD.N0106.N0428.N0765.N1679.d005885 r) = _root_.GD.N0106.N0428.N0765.N1679.d005885 r := by
  have hs := _root_.GD.N0106.N0428.N0765.N1679.d005892 hr0 hr1
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005883
  rw [_root_.GD.N0106.N0428.N0765.N1679.d005904 hr0 hr1]
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005885
  field_simp
  ring

theorem d005906 (hr0 : 0 < r) (hr1 : r < 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 < _root_.GD.N0106.N0428.N0765.N1679.d005886 r x := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005886
  exact div_pos (pow_pos (_root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hx) 2) (_root_.GD.N0106.N0428.N0765.N1679.d005891 hr0 hr1)

theorem d005907 (hr0 : 0 < r) (hr1 : r < 1) {L : ℝ} (hL : 0 ≤ L) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < _root_.GD.N0106.N0428.N0765.N1679.d005880 r x + L * _root_.GD.N0106.N0428.N0765.N1679.d005881 x :=
  add_pos_of_pos_of_nonneg (_root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hx) (mul_nonneg hL (_root_.GD.N0106.N0428.N0765.N1679.d005889 hx))

theorem d005908 (hr0 : 0 < r) (hr1 : r < 1) {L : ℝ} (hL : 0 ≤ L) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x :=
  mul_nonneg (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1679.d005889 hx) _) (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1679.d005907 hr0 hr1 hL hx).le _)

theorem d005909 (hr0 : 0 < r) (hr1 : r < 1) {L : ℝ} (hL : 0 ≤ L) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x :=
  mul_pos (Real.rpow_pos_of_pos (mul_pos hx.1 (sub_pos.mpr hx.2)) _)
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1679.d005907 hr0 hr1 hL (Ioo_subset_Icc_self hx)) _)

theorem d005910 (hr0 : 0 < r) (hr1 : r < 1) {L : ℝ} (hL : 0 ≤ L) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1679.d005887 r L) (Icc 0 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005887
  apply ContinuousOn.mul
  · exact ((Real.continuous_rpow_const (by norm_num)).comp _root_.GD.N0106.N0428.N0765.N1679.d005901).continuousOn
  · exact ContinuousOn.rpow_const (by unfold _root_.GD.N0106.N0428.N0765.N1679.d005880 _root_.GD.N0106.N0428.N0765.N1679.d005881; fun_prop)
      (fun x hx => Or.inl (_root_.GD.N0106.N0428.N0765.N1679.d005907 hr0 hr1 hL hx).ne')



theorem d005911 (hr0 : 0 < r) (hr1 : r < 1) {L : ℝ} (hL : 0 ≤ L) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0765.N1679.d005887 r L (_root_.GD.N0106.N0428.N0765.N1679.d005883 r x) * (r * (1 - r) / _root_.GD.N0106.N0428.N0765.N1679.d005880 r x ^ 2) = _root_.GD.N0106.N0428.N0765.N1679.d005886 r x ^ 5 * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x := by
  have hc := _root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hx
  have hrr := _root_.GD.N0106.N0428.N0765.N1679.d005891 hr0 hr1
  set a := r * (1 - r) / _root_.GD.N0106.N0428.N0765.N1679.d005880 r x ^ 2 with ha
  have hapos : 0 < a := div_pos hrr (pow_pos hc 2)
  have hhr : _root_.GD.N0106.N0428.N0765.N1679.d005881 (_root_.GD.N0106.N0428.N0765.N1679.d005883 r x) = a * _root_.GD.N0106.N0428.N0765.N1679.d005881 x := by
    rw [_root_.GD.N0106.N0428.N0765.N1679.d005895 hc.ne', ha]
    ring
  have hbr : _root_.GD.N0106.N0428.N0765.N1679.d005880 r (_root_.GD.N0106.N0428.N0765.N1679.d005883 r x) + L * _root_.GD.N0106.N0428.N0765.N1679.d005881 (_root_.GD.N0106.N0428.N0765.N1679.d005883 r x) = a * (_root_.GD.N0106.N0428.N0765.N1679.d005880 r x + L * _root_.GD.N0106.N0428.N0765.N1679.d005881 x) := by
    rw [_root_.GD.N0106.N0428.N0765.N1679.d005894 hc.ne', _root_.GD.N0106.N0428.N0765.N1679.d005895 hc.ne', ha]
    field_simp
  have hz : _root_.GD.N0106.N0428.N0765.N1679.d005886 r x = a⁻¹ := by
    rw [ha, _root_.GD.N0106.N0428.N0765.N1679.d005886, inv_div]
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005887
  rw [hbr, hhr, Real.mul_rpow hapos.le (_root_.GD.N0106.N0428.N0765.N1679.d005889 hx),
    Real.mul_rpow hapos.le (_root_.GD.N0106.N0428.N0765.N1679.d005907 hr0 hr1 hL hx).le, hz]
  have e : a ^ ((9 : ℝ) / 2) * a ^ (-((21 : ℝ) / 2)) * a = a⁻¹ ^ 5 := by
    have e1 : a ^ ((9 : ℝ) / 2) * a ^ (-((21 : ℝ) / 2)) * a
        = a ^ ((9 : ℝ) / 2 + -((21 : ℝ) / 2) + 1) := by
      rw [Real.rpow_add hapos, Real.rpow_add hapos, Real.rpow_one]
    rw [e1, show (9 : ℝ) / 2 + -((21 : ℝ) / 2) + 1 = -((5 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hapos.le, Real.rpow_natCast, inv_pow]
  calc a ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1679.d005881 x ^ ((9 : ℝ) / 2) *
        (a ^ (-((21 : ℝ) / 2)) * (_root_.GD.N0106.N0428.N0765.N1679.d005880 r x + L * _root_.GD.N0106.N0428.N0765.N1679.d005881 x) ^ (-((21 : ℝ) / 2))) * a
      = (a ^ ((9 : ℝ) / 2) * a ^ (-((21 : ℝ) / 2)) * a) *
        (_root_.GD.N0106.N0428.N0765.N1679.d005881 x ^ ((9 : ℝ) / 2) * (_root_.GD.N0106.N0428.N0765.N1679.d005880 r x + L * _root_.GD.N0106.N0428.N0765.N1679.d005881 x) ^ (-((21 : ℝ) / 2))) := by ring
    _ = a⁻¹ ^ 5 * (_root_.GD.N0106.N0428.N0765.N1679.d005881 x ^ ((9 : ℝ) / 2) * (_root_.GD.N0106.N0428.N0765.N1679.d005880 r x + L * _root_.GD.N0106.N0428.N0765.N1679.d005881 x) ^ (-((21 : ℝ) / 2))) := by rw [e]

end Algebra

section Reflection
variable {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
include hr0 hr1


theorem d005912 {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) :
    ∫ x in _root_.GD.N0106.N0428.N0765.N1679.d005885 r..1, g x = ∫ u in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, g (_root_.GD.N0106.N0428.N0765.N1679.d005883 r u) * (r * (1 - r) / _root_.GD.N0106.N0428.N0765.N1679.d005880 r u ^ 2) := by
  have hstar := _root_.GD.N0106.N0428.N0765.N1679.d005903 hr0 hr1
  have hsub : uIcc (0 : ℝ) (_root_.GD.N0106.N0428.N0765.N1679.d005885 r) ⊆ Icc 0 1 := by
    rw [uIcc_of_le hstar.1.le]
    exact Icc_subset_Icc le_rfl hstar.2.le
  have h := integral_comp_mul_deriv' (a := (0 : ℝ)) (b := _root_.GD.N0106.N0428.N0765.N1679.d005885 r) (f := _root_.GD.N0106.N0428.N0765.N1679.d005883 r)
    (f' := fun u => -(r * (1 - r)) / _root_.GD.N0106.N0428.N0765.N1679.d005880 r u ^ 2) (g := g)
    (fun u hu => _root_.GD.N0106.N0428.N0765.N1679.d005899 (_root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 (hsub hu)).ne')
    (by
      apply ContinuousOn.div continuousOn_const ((_root_.GD.N0106.N0428.N0765.N1679.d005900 r).continuousOn.pow 2)
      intro u hu
      exact pow_ne_zero 2 (_root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 (hsub hu)).ne')
    (by
      refine hg.mono ?_
      rintro _ ⟨u, hu, rfl⟩
      exact _root_.GD.N0106.N0428.N0765.N1679.d005898 hr0 hr1 (hsub hu))
  rw [_root_.GD.N0106.N0428.N0765.N1679.d005897 hr0, _root_.GD.N0106.N0428.N0765.N1679.d005905 hr0 hr1, integral_symm (_root_.GD.N0106.N0428.N0765.N1679.d005885 r) 1] at h
  have h2 : (∫ x in _root_.GD.N0106.N0428.N0765.N1679.d005885 r..1, g x)
      = -∫ u in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, (g ∘ _root_.GD.N0106.N0428.N0765.N1679.d005883 r) u * (-(r * (1 - r)) / _root_.GD.N0106.N0428.N0765.N1679.d005880 r u ^ 2) := by
    linarith [h]
  rw [h2, ← intervalIntegral.integral_neg]
  congr 1
  funext u
  simp only [Function.comp]
  ring


theorem d005913 {L : ℝ} (hL : 0 ≤ L) {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc 0 1)) :
    ∫ x in (0 : ℝ)..1, φ x * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x
      = ∫ x in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, (φ x + φ (_root_.GD.N0106.N0428.N0765.N1679.d005883 r x) * _root_.GD.N0106.N0428.N0765.N1679.d005886 r x ^ 5) * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x := by
  have hstar := _root_.GD.N0106.N0428.N0765.N1679.d005903 hr0 hr1
  have hcont : ContinuousOn (fun x => φ x * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x) (Icc 0 1) :=
    hφ.mul (_root_.GD.N0106.N0428.N0765.N1679.d005910 hr0 hr1 hL)
  have hi1 : IntervalIntegrable (fun x => φ x * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x) volume 0 (_root_.GD.N0106.N0428.N0765.N1679.d005885 r) :=
    (hcont.mono (Icc_subset_Icc le_rfl hstar.2.le)).intervalIntegrable_of_Icc hstar.1.le
  have hi2 : IntervalIntegrable (fun x => φ x * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x) volume (_root_.GD.N0106.N0428.N0765.N1679.d005885 r) 1 :=
    (hcont.mono (Icc_subset_Icc hstar.1.le le_rfl)).intervalIntegrable_of_Icc hstar.2.le
  rw [← integral_add_adjacent_intervals hi1 hi2, _root_.GD.N0106.N0428.N0765.N1679.d005912 hr0 hr1 hcont]
  have hsub : ∀ x ∈ uIcc (0 : ℝ) (_root_.GD.N0106.N0428.N0765.N1679.d005885 r), x ∈ Icc (0 : ℝ) 1 := by
    intro x hx
    rw [uIcc_of_le hstar.1.le] at hx
    exact Icc_subset_Icc le_rfl hstar.2.le hx
  have hmaps : MapsTo (_root_.GD.N0106.N0428.N0765.N1679.d005883 r) (Icc 0 1) (Icc 0 1) := fun x hx => _root_.GD.N0106.N0428.N0765.N1679.d005898 hr0 hr1 hx
  have hc3 : ContinuousOn (fun u => φ (_root_.GD.N0106.N0428.N0765.N1679.d005883 r u) * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L (_root_.GD.N0106.N0428.N0765.N1679.d005883 r u) *
      (r * (1 - r) / _root_.GD.N0106.N0428.N0765.N1679.d005880 r u ^ 2)) (Icc 0 1) := by
    refine ((hφ.comp (_root_.GD.N0106.N0428.N0765.N1679.d005902 hr0 hr1) hmaps).mul
      ((_root_.GD.N0106.N0428.N0765.N1679.d005910 hr0 hr1 hL).comp (_root_.GD.N0106.N0428.N0765.N1679.d005902 hr0 hr1) hmaps)).mul ?_
    exact continuousOn_const.div ((_root_.GD.N0106.N0428.N0765.N1679.d005900 r).continuousOn.pow 2)
      (fun u hu => pow_ne_zero 2 (_root_.GD.N0106.N0428.N0765.N1679.d005890 hr0 hr1 hu).ne')
  have hi3 : IntervalIntegrable (fun u => φ (_root_.GD.N0106.N0428.N0765.N1679.d005883 r u) * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L (_root_.GD.N0106.N0428.N0765.N1679.d005883 r u) *
      (r * (1 - r) / _root_.GD.N0106.N0428.N0765.N1679.d005880 r u ^ 2)) volume 0 (_root_.GD.N0106.N0428.N0765.N1679.d005885 r) :=
    (hc3.mono (Icc_subset_Icc le_rfl hstar.2.le)).intervalIntegrable_of_Icc hstar.1.le
  rw [← integral_add hi1 hi3]
  apply integral_congr
  intro x hx
  have hx' := hsub x hx
  show φ x * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x + φ (_root_.GD.N0106.N0428.N0765.N1679.d005883 r x) * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L (_root_.GD.N0106.N0428.N0765.N1679.d005883 r x) * (r * (1 - r) / _root_.GD.N0106.N0428.N0765.N1679.d005880 r x ^ 2)
    = (φ x + φ (_root_.GD.N0106.N0428.N0765.N1679.d005883 r x) * _root_.GD.N0106.N0428.N0765.N1679.d005886 r x ^ 5) * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x
  rw [mul_assoc (φ (_root_.GD.N0106.N0428.N0765.N1679.d005883 r x)), _root_.GD.N0106.N0428.N0765.N1679.d005911 hr0 hr1 hL hx']
  ring


theorem d005914 {L : ℝ} (hL : 0 ≤ L) :
    _root_.GD.N0106.N0428.N0765.N1679.d005888 r L
      = (∫ x in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, (x + _root_.GD.N0106.N0428.N0765.N1679.d005883 r x * _root_.GD.N0106.N0428.N0765.N1679.d005886 r x ^ 5) * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x) /
          ∫ x in (0 : ℝ).._root_.GD.N0106.N0428.N0765.N1679.d005885 r, (1 + _root_.GD.N0106.N0428.N0765.N1679.d005886 r x ^ 5) * _root_.GD.N0106.N0428.N0765.N1679.d005887 r L x := by
  unfold _root_.GD.N0106.N0428.N0765.N1679.d005888
  have h0 := _root_.GD.N0106.N0428.N0765.N1679.d005913 hr0 hr1 hL (φ := fun x => x) continuousOn_id
  have h2 := _root_.GD.N0106.N0428.N0765.N1679.d005913 hr0 hr1 hL (φ := fun _ => (1 : ℝ)) continuousOn_const
  simp only [one_mul] at h2
  rw [h0, h2]

end Reflection

section Identification


theorem d005915 {η u v w : ℝ} (hη : 0 < η) (hu : 0 ≤ u) (hv : 0 < v)
    (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w = _root_.GD.N0106.N0428.N0765.N1679.d005888 (v / (v + η * w)) ((1 + η) * u / (v + η * w)) := by
  have hS : 0 < v + η * w := by positivity
  set S := v + η * w with hSdef
  have hC : ∀ l ∈ Icc (0 : ℝ) 1, _root_.GD.N0106.N0428.N0765.N1534.d005328 η u v w l
      = S * (_root_.GD.N0106.N0428.N0765.N1679.d005880 (v / S) l + (1 + η) * u / S * _root_.GD.N0106.N0428.N0765.N1679.d005881 l) := by
    intro l _
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005328 _root_.GD.N0106.N0428.N0765.N1679.d005880 _root_.GD.N0106.N0428.N0765.N1679.d005881
    field_simp
    ring
  have hk : ∀ l ∈ Icc (0 : ℝ) 1, _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w l
      = S ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1679.d005887 (v / S) ((1 + η) * u / S) l := by
    intro l hl
    have hr0 : 0 < v / S := div_pos hv hS
    have hr1 : v / S < 1 := by rw [div_lt_one hS]; nlinarith [mul_pos hη hw]
    have hL : 0 ≤ (1 + η) * u / S := by positivity
    unfold _root_.GD.N0106.N0428.N0765.N1534.d005329 _root_.GD.N0106.N0428.N0765.N1679.d005887
    rw [hC l hl, Real.mul_rpow hS.le (_root_.GD.N0106.N0428.N0765.N1679.d005907 hr0 hr1 hL hl).le]
    unfold _root_.GD.N0106.N0428.N0765.N1679.d005881
    ring
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005330 _root_.GD.N0106.N0428.N0765.N1679.d005888
  have hne : S ^ (-((21 : ℝ) / 2)) ≠ 0 := (Real.rpow_pos_of_pos hS _).ne'
  have hnum : (∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w l)
      = S ^ (-((21 : ℝ) / 2)) * ∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1679.d005887 (v / S) ((1 + η) * u / S) l := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro l hl
    rw [uIcc_of_le zero_le_one] at hl
    show l * _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w l = S ^ (-((21 : ℝ) / 2)) * (l * _root_.GD.N0106.N0428.N0765.N1679.d005887 (v / S) ((1 + η) * u / S) l)
    rw [hk l hl]
    ring
  have hden : (∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w l)
      = S ^ (-((21 : ℝ) / 2)) * ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1679.d005887 (v / S) ((1 + η) * u / S) l := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro l hl
    rw [uIcc_of_le zero_le_one] at hl
    exact hk l hl
  rw [hnum, hden, mul_div_mul_left _ _ hne]

end Identification

end
end GD.N0106.N0428.N0765.N1679
