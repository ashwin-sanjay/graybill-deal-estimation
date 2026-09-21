import GD.Module1311
import Mathlib.MeasureTheory.Integral.DominatedConvergence













set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set Filter Topology

namespace GD.N0106.N0428.N0765.N1526
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1663 _root_.GD.N0106.N0428.N0765.N1672

def d021431 (e b x : ℝ) : ℝ := Real.exp b * (1 - x) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x
def d021432 (e x : ℝ) : ℝ := x * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x
def d021433 (e a x : ℝ) : ℝ := (1 + e) * Real.exp a * x * (1 - x)
def d021434 (e a b x : ℝ) : ℝ := (1 + e) * Real.exp a * Real.exp b * x * (1 - x)
def d021435 (e a b x : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1526.d021431 e b x + _root_.GD.N0106.N0428.N0765.N1526.d021432 e x + _root_.GD.N0106.N0428.N0765.N1526.d021433 e a x + _root_.GD.N0106.N0428.N0765.N1526.d021434 e a b x

theorem d021436 {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Icc (0 : ℝ) 1) : 1 - x ≤ _root_.GD.N0106.N0428.N0765.N1663.d021403 e x := by
  unfold _root_.GD.N0106.N0428.N0765.N1663.d021403
  linarith [mul_nonneg he hx.1]

theorem d021437 {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1663.d021403 e x :=
  (sub_nonneg.mpr hx.2).trans (_root_.GD.N0106.N0428.N0765.N1526.d021436 he hx)

theorem d021438 {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Icc (0 : ℝ) 1) (a b : ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1526.d021431 e b x ∧ 0 ≤ _root_.GD.N0106.N0428.N0765.N1526.d021432 e x ∧ 0 ≤ _root_.GD.N0106.N0428.N0765.N1526.d021433 e a x ∧ 0 ≤ _root_.GD.N0106.N0428.N0765.N1526.d021434 e a b x := by
  have hD := _root_.GD.N0106.N0428.N0765.N1526.d021437 he hx
  have hm := sub_nonneg.mpr hx.2
  have hx0 := hx.1
  have h1 : 0 ≤ 1 + e := by linarith
  dsimp [_root_.GD.N0106.N0428.N0765.N1526.d021431, _root_.GD.N0106.N0428.N0765.N1526.d021432, _root_.GD.N0106.N0428.N0765.N1526.d021433, _root_.GD.N0106.N0428.N0765.N1526.d021434]
  exact ⟨mul_nonneg (mul_nonneg (Real.exp_pos b).le hm) hD,
    mul_nonneg hx0 hD,
    mul_nonneg (mul_nonneg (mul_nonneg h1 (Real.exp_pos a).le) hx0) hm,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 (Real.exp_pos a).le)
      (Real.exp_pos b).le) hx0) hm⟩

theorem d021439 (e a b α β x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x =
      _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1526.d021431 e b x) β + _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1526.d021432 e x) 0 +
        _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1526.d021433 e a x) α + _root_.GD.N0106.N0428.N0765.N1538.d021186 (_root_.GD.N0106.N0428.N0765.N1526.d021434 e a b x) (α + β) := by
  unfold _root_.GD.N0106.N0428.N0765.N1663.d021418 _root_.GD.N0106.N0428.N0765.N1538.d021186 _root_.GD.N0106.N0428.N0765.N1526.d021431 _root_.GD.N0106.N0428.N0765.N1526.d021432 _root_.GD.N0106.N0428.N0765.N1526.d021433 _root_.GD.N0106.N0428.N0765.N1526.d021434 _root_.GD.N0106.N0428.N0765.N1663.d021403
  push_cast
  simp only [add_mul, Complex.exp_add, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    mul_one, Complex.ofReal_exp]
  ring

theorem d021440 {e x : ℝ} (he : 0 ≤ e) (hx : x ∈ Icc (0 : ℝ) 1) (a b : ℝ) :
    min (Real.exp b) 1 * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ≤ _root_.GD.N0106.N0428.N0765.N1526.d021435 e a b x := by
  have hD := _root_.GD.N0106.N0428.N0765.N1526.d021437 he hx
  have hm := sub_nonneg.mpr hx.2
  have hB := min_le_left (Real.exp b) (1 : ℝ)
  have h1 := min_le_right (Real.exp b) (1 : ℝ)
  have hlin : min (Real.exp b) 1 ≤ Real.exp b * (1 - x) + x := by
    have hBm := mul_le_mul_of_nonneg_right hB hm
    have h1x := mul_le_mul_of_nonneg_right h1 hx.1
    nlinarith
  obtain ⟨_, _, h3, h4⟩ := _root_.GD.N0106.N0428.N0765.N1526.d021438 he hx a b
  have hscaled := mul_le_mul_of_nonneg_right hlin hD
  unfold _root_.GD.N0106.N0428.N0765.N1526.d021435 _root_.GD.N0106.N0428.N0765.N1526.d021431 _root_.GD.N0106.N0428.N0765.N1526.d021432 at *
  nlinarith


theorem d021441 {e x : ℝ} (he : 0 ≤ e) (hx : x ∈ Icc (0 : ℝ) 1)
    (a b α β θ w : ℝ) (hw : w ≤ Real.pi)
    (hβ : |β - θ| ≤ w) (h0 : |0 - θ| ≤ w)
    (hα : |α - θ| ≤ w) (hsum : |α + β - θ| ≤ w) :
    Real.cos w * _root_.GD.N0106.N0428.N0765.N1526.d021435 e a b x ≤
      (Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x).re := by
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GD.N0106.N0428.N0765.N1526.d021438 he hx a b
  have e1 := _root_.GD.N0106.N0428.N0765.N1538.d021190 h1 hβ hw
  have e2 := _root_.GD.N0106.N0428.N0765.N1538.d021190 h2 h0 hw
  have e3 := _root_.GD.N0106.N0428.N0765.N1538.d021190 h3 hα hw
  have e4 := _root_.GD.N0106.N0428.N0765.N1538.d021190 h4 hsum hw
  rw [_root_.GD.N0106.N0428.N0765.N1526.d021439]
  unfold _root_.GD.N0106.N0428.N0765.N1526.d021435
  simp only [mul_add, Complex.add_re]
  linarith

def d021442 (b α β : ℝ) : ℝ :=
  Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * min (Real.exp b) 1

def d021443 (b α β : ℝ) : ℝ := _root_.GD.N0106.N0428.N0765.N1526.d021442 b α β ^ (-((21 : ℝ) / 2))

theorem d021444 (b α β : ℝ) (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    0 < _root_.GD.N0106.N0428.N0765.N1526.d021442 b α β := by
  exact mul_pos (_root_.GD.N0106.N0428.N0765.N1538.d021219 hw) (lt_min (Real.exp_pos b) zero_lt_one)

theorem d021445 {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Icc (0 : ℝ) 1) (a b α β : ℝ) (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1526.d021442 b α β * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ≤ ‖_root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x‖ := by
  have hrot := _root_.GD.N0106.N0428.N0765.N1526.d021441 he hx a b α β (_root_.GD.N0106.N0428.N0765.N1538.d021191 α β) (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2)
    (by linarith [Real.pi_pos]) (_root_.GD.N0106.N0428.N0765.N1538.d021195 α β) (_root_.GD.N0106.N0428.N0765.N1538.d021196 α β)
    (_root_.GD.N0106.N0428.N0765.N1538.d021197 α β) (_root_.GD.N0106.N0428.N0765.N1538.d021198 α β)
  calc _root_.GD.N0106.N0428.N0765.N1526.d021442 b α β * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x
      = Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * (min (Real.exp b) 1 * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x) := by
        unfold _root_.GD.N0106.N0428.N0765.N1526.d021442
        ring
    _ ≤ Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β / 2) * _root_.GD.N0106.N0428.N0765.N1526.d021435 e a b x :=
      mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1526.d021440 he hx a b) (_root_.GD.N0106.N0428.N0765.N1538.d021219 hw).le
    _ ≤ (_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x).re := hrot
    _ ≤ |(_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x).re| := le_abs_self _
    _ ≤ ‖_root_.GD.N0106.N0428.N0765.N1538.d021215 α β * _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x‖ := Complex.abs_re_le_norm _
    _ = ‖_root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x‖ := by rw [norm_mul, _root_.GD.N0106.N0428.N0765.N1538.d021216, one_mul]



theorem d021446 {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Icc (0 : ℝ) 1) (hD : 0 < _root_.GD.N0106.N0428.N0765.N1663.d021403 e x)
    (a b α β : ℝ) (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x ∈ Complex.slitPlane := by
  have hw0 := _root_.GD.N0106.N0428.N0765.N1538.d021193 α β
  have hwhalf : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi / 2 := by linarith
  have hc : 0 < Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hwhalf⟩
  have hβ : |β - 0| ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β := by
    simpa only [sub_zero, _root_.GD.N0106.N0428.N0765.N1538.d021192] using le_add_of_nonneg_left (abs_nonneg α)
  have hα : |α - 0| ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β := by
    simpa only [sub_zero, _root_.GD.N0106.N0428.N0765.N1538.d021192] using le_add_of_nonneg_right (abs_nonneg β)
  have h0 : |(0 : ℝ) - 0| ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β := by simpa using hw0
  have hs : |α + β - 0| ≤ _root_.GD.N0106.N0428.N0765.N1538.d021192 α β := by simpa [_root_.GD.N0106.N0428.N0765.N1538.d021192] using abs_add_le α β
  have hr := _root_.GD.N0106.N0428.N0765.N1526.d021441 he hx a b α β 0 (_root_.GD.N0106.N0428.N0765.N1538.d021192 α β)
    (by linarith [Real.pi_pos]) hβ h0 hα hs
  have hm : 0 < _root_.GD.N0106.N0428.N0765.N1526.d021435 e a b x :=
    lt_of_lt_of_le (mul_pos (lt_min (Real.exp_pos b) zero_lt_one) hD) (_root_.GD.N0106.N0428.N0765.N1526.d021440 he hx a b)
  simp only [neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] at hr
  exact Complex.mem_slitPlane_iff.mpr (Or.inl ((mul_pos hc hm).trans_le hr))



theorem d021447 {x m D c r : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hm0 : 0 < m) (hm1 : m ≤ 1) (hmD : m ≤ D) (hc : 0 < c)
    (hr0 : 6 ≤ r) (hr1 : r ≤ (21 : ℝ) / 2) :
    (x * m) ^ ((9 : ℝ) / 2) * D ^ r * (c * D) ^ (-((21 : ℝ) / 2)) ≤
      c ^ (-((21 : ℝ) / 2)) := by
  have hD := hm0.trans_le hmD
  have hxm : x * m ≤ m := by nlinarith
  have ht := Real.rpow_le_rpow (mul_nonneg hx0 hm0.le) hxm (by norm_num : (0 : ℝ) ≤ 9 / 2)
  have hneg : r - (21 : ℝ) / 2 ≤ 0 := by linarith
  have hdec := Real.rpow_le_rpow_of_nonpos hm0 hmD hneg
  have hc0 : 0 ≤ c ^ (-((21 : ℝ) / 2)) := (Real.rpow_pos_of_pos hc _).le
  have hmR : m ^ (r - 6) ≤ 1 := Real.rpow_le_one hm0.le hm1 (by linarith)
  calc
    (x * m) ^ ((9 : ℝ) / 2) * D ^ r * (c * D) ^ (-((21 : ℝ) / 2))
      = c ^ (-((21 : ℝ) / 2)) *
          ((x * m) ^ ((9 : ℝ) / 2) * D ^ (r - (21 : ℝ) / 2)) := by
        rw [Real.mul_rpow hc.le hD.le, Real.rpow_sub hD]
        rw [Real.rpow_neg hD.le]
        ring
    _ ≤ c ^ (-((21 : ℝ) / 2)) *
          (m ^ ((9 : ℝ) / 2) * m ^ (r - (21 : ℝ) / 2)) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        exact mul_le_mul ht hdec (Real.rpow_nonneg hD.le _)
          (Real.rpow_nonneg hm0.le _)
    _ = c ^ (-((21 : ℝ) / 2)) * m ^ (r - 6) := by
        rw [← Real.rpow_add hm0]
        congr 2
        ring
    _ ≤ c ^ (-((21 : ℝ) / 2)) * 1 := mul_le_mul_of_nonneg_left hmR hc0
    _ = c ^ (-((21 : ℝ) / 2)) := mul_one _

theorem d021448 {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Icc (0 : ℝ) 1) (a b α β : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1672.d021422 e a b α β x‖ =
      ((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10) *
        ‖_root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x‖ ^ (-((21 : ℝ) / 2)) := by
  have hw : 0 ≤ (x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10 :=
    mul_nonneg (Real.rpow_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) _)
      (pow_nonneg (_root_.GD.N0106.N0428.N0765.N1526.d021437 he hx) _)
  unfold _root_.GD.N0106.N0428.N0765.N1672.d021422
  rw [norm_mul, Complex.norm_of_nonneg hw]
  congr 1
  convert Complex.norm_cpow_real (_root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x) (-((21 : ℝ) / 2)) using 1 <;>
    push_cast <;> rfl


theorem d021449 {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Ioo (0 : ℝ) 1) (a b α β : ℝ) (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1672.d021422 e a b α β x‖ ≤ _root_.GD.N0106.N0428.N0765.N1526.d021443 b α β := by
  have hxc := Ioo_subset_Icc_self hx
  have hx0 : 0 ≤ x := hx.1.le
  have hx1 : x ≤ 1 := hx.2.le
  have hm : 0 < 1 - x := sub_pos.mpr hx.2
  have hD := hm.trans_le (_root_.GD.N0106.N0428.N0765.N1526.d021436 he hxc)
  have hc := _root_.GD.N0106.N0428.N0765.N1526.d021444 b α β hw
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hc hD)
    (_root_.GD.N0106.N0428.N0765.N1526.d021445 he hxc a b α β hw) (by norm_num : -((21 : ℝ) / 2) ≤ 0)
  rw [_root_.GD.N0106.N0428.N0765.N1526.d021448 he hxc]
  calc
    ((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10) *
        ‖_root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x‖ ^ (-((21 : ℝ) / 2))
      ≤ ((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10) *
        (_root_.GD.N0106.N0428.N0765.N1526.d021442 b α β * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x) ^ (-((21 : ℝ) / 2)) := by
          exact mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _root_.GD.N0106.N0428.N0765.N1526.d021443 b α β := by
      simpa only [Real.rpow_ofNat, _root_.GD.N0106.N0428.N0765.N1526.d021443] using
        (_root_.GD.N0106.N0428.N0765.N1526.d021447 hx.1.le hx.2.le hm (by linarith) (_root_.GD.N0106.N0428.N0765.N1526.d021436 he hxc)
          hc (r := 10) (by norm_num) (by norm_num))

def d021450 (e a b α β x : ℝ) : ℂ :=
  ((x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1672.d021422 e a b α β x

theorem d021451 {e x : ℝ} (he : 0 ≤ e)
    (hx : x ∈ Ioo (0 : ℝ) 1) (a b α β : ℝ) (hw : _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ‖_root_.GD.N0106.N0428.N0765.N1526.d021450 e a b α β x‖ ≤ _root_.GD.N0106.N0428.N0765.N1526.d021443 b α β := by
  have hxc := Ioo_subset_Icc_self hx
  have hx0 : 0 ≤ x := hx.1.le
  have hx1 : x ≤ 1 := hx.2.le
  have hm : 0 < 1 - x := sub_pos.mpr hx.2
  have hD := hm.trans_le (_root_.GD.N0106.N0428.N0765.N1526.d021436 he hxc)
  have hc := _root_.GD.N0106.N0428.N0765.N1526.d021444 b α β hw
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hc hD)
    (_root_.GD.N0106.N0428.N0765.N1526.d021445 he hxc a b α β hw) (by norm_num : -((21 : ℝ) / 2) ≤ 0)
  have hxD : 0 ≤ x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x := div_nonneg hx.1.le hD.le
  unfold _root_.GD.N0106.N0428.N0765.N1526.d021450
  rw [norm_mul, Complex.norm_of_nonneg hxD, _root_.GD.N0106.N0428.N0765.N1526.d021448 he hxc]
  have heq : x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x *
      ((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10) =
        x * ((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 9) := by
    field_simp [hD.ne']
  rw [← mul_assoc, heq, mul_assoc]
  calc
    x * (((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 9) *
        ‖_root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x‖ ^ (-((21 : ℝ) / 2)))
      ≤ x * (((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 9) *
        (_root_.GD.N0106.N0428.N0765.N1526.d021442 b α β * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x) ^ (-((21 : ℝ) / 2))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp (by positivity)) hx.1.le
    _ ≤ x * _root_.GD.N0106.N0428.N0765.N1526.d021443 b α β := by
      apply mul_le_mul_of_nonneg_left _ hx.1.le
      simpa only [Real.rpow_ofNat, _root_.GD.N0106.N0428.N0765.N1526.d021443] using
        (_root_.GD.N0106.N0428.N0765.N1526.d021447 hx.1.le hx.2.le hm (by linarith) (_root_.GD.N0106.N0428.N0765.N1526.d021436 he hxc)
          hc (r := 9) (by norm_num) (by norm_num))
    _ ≤ _root_.GD.N0106.N0428.N0765.N1526.d021443 b α β := by
      have hM : 0 ≤ _root_.GD.N0106.N0428.N0765.N1526.d021443 b α β := (Real.rpow_pos_of_pos hc _).le
      nlinarith [hx.2.le]

theorem d021452 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1672.d021422 e a b α β) (Icc (0 : ℝ) 1) := by
  have hb : Continuous (_root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β) := by unfold _root_.GD.N0106.N0428.N0765.N1663.d021418; fun_prop
  have hweight : Continuous (fun x : ℝ =>
      (((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10 : ℝ) : ℂ)) := by
    have hr := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 9 / 2)).comp
      (show Continuous (fun x : ℝ => x * (1 - x)) by fun_prop)
    exact Complex.continuous_ofReal.comp (hr.mul (by unfold _root_.GD.N0106.N0428.N0765.N1663.d021403; fun_prop))
  exact hweight.continuousOn.mul (hb.continuousOn.cpow_const fun x hx =>
    _root_.GD.N0106.N0428.N0765.N1526.d021446 he.le hx (_root_.GD.N0106.N0428.N0765.N1663.d021406 he hx) a b α β hw)

theorem d021453 {e : ℝ} (he : 0 < e) (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1526.d021450 e a b α β) (Icc (0 : ℝ) 1) := by
  have hdiv : ContinuousOn (fun x => x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x) (Icc (0 : ℝ) 1) := by
    exact continuousOn_id.div (by unfold _root_.GD.N0106.N0428.N0765.N1663.d021403; fun_prop)
      (fun x hx => (_root_.GD.N0106.N0428.N0765.N1663.d021406 he hx).ne')
  exact (Complex.continuous_ofReal.comp_continuousOn hdiv).mul
    (_root_.GD.N0106.N0428.N0765.N1526.d021452 he a b α β hw)

theorem d021454 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (a b α β : ℝ) (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ContinuousAt (fun e => _root_.GD.N0106.N0428.N0765.N1672.d021422 e a b α β x) 0 := by
  have hD : 0 < _root_.GD.N0106.N0428.N0765.N1663.d021403 0 x := by simpa [_root_.GD.N0106.N0428.N0765.N1663.d021403] using sub_pos.mpr hx.2
  have hbase : ContinuousAt (fun e => _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x) 0 := by
    unfold _root_.GD.N0106.N0428.N0765.N1663.d021418
    fun_prop
  have hcp : ContinuousAt (fun e => _root_.GD.N0106.N0428.N0765.N1663.d021418 e a b α β x ^ (-((21 : ℂ) / 2))) 0 :=
    hbase.cpow continuousAt_const
      (_root_.GD.N0106.N0428.N0765.N1526.d021446 le_rfl (Ioo_subset_Icc_self hx) hD a b α β hw)
  have hweight : ContinuousAt (fun e : ℝ =>
      (((x * (1 - x)) ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1663.d021403 e x ^ 10 : ℝ) : ℂ)) 0 := by
    unfold _root_.GD.N0106.N0428.N0765.N1663.d021403
    fun_prop
  exact hweight.mul hcp

theorem d021455 {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (a b α β : ℝ) (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    ContinuousAt (fun e => _root_.GD.N0106.N0428.N0765.N1526.d021450 e a b α β x) 0 := by
  have hD : _root_.GD.N0106.N0428.N0765.N1663.d021403 0 x ≠ 0 := by simpa [_root_.GD.N0106.N0428.N0765.N1663.d021403] using (sub_pos.mpr hx.2).ne'
  have hdiv : ContinuousAt (fun e => x / _root_.GD.N0106.N0428.N0765.N1663.d021403 e x) 0 :=
    continuousAt_const.div (by unfold _root_.GD.N0106.N0428.N0765.N1663.d021403; fun_prop) hD
  exact (Complex.continuous_ofReal.continuousAt.comp hdiv).mul
    (_root_.GD.N0106.N0428.N0765.N1526.d021454 hx a b α β hw)


theorem d021456 (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Tendsto (fun e => _root_.GD.N0106.N0428.N0765.N1672.d021423 e a b α β) (𝓝[>] 0) (𝓝 (_root_.GD.N0106.N0428.N0765.N1672.d021423 0 a b α β)) := by
  unfold _root_.GD.N0106.N0428.N0765.N1672.d021423
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => _root_.GD.N0106.N0428.N0765.N1526.d021443 b α β) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with e he
    have hc := (_root_.GD.N0106.N0428.N0765.N1526.d021452 he a b α β hw).mono Ioc_subset_Icc_self
    simpa only [uIoc_of_le zero_le_one] using hc.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [self_mem_nhdsWithin] with e he
    filter_upwards [volume.ae_ne (1 : ℝ)] with x hx1
    intro hx
    rw [uIoc_of_le zero_le_one] at hx
    exact _root_.GD.N0106.N0428.N0765.N1526.d021449 he.le ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩ a b α β (_root_.GD.N0106.N0428.N0765.N1538.d021233 hw)
  · filter_upwards [volume.ae_ne (1 : ℝ)] with x hx1
    intro hx
    rw [uIoc_of_le zero_le_one] at hx
    exact (_root_.GD.N0106.N0428.N0765.N1526.d021454 ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩ a b α β hw).tendsto.mono_left
      nhdsWithin_le_nhds


theorem d021457 (a b α β : ℝ)
    (hw : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Tendsto (fun e => _root_.GD.N0106.N0428.N0765.N1672.d021424 e a b α β) (𝓝[>] 0) (𝓝 (_root_.GD.N0106.N0428.N0765.N1672.d021424 0 a b α β)) := by
  change Tendsto (fun e => ∫ x in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1526.d021450 e a b α β x)
    (𝓝[>] 0) (𝓝 (∫ x in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1526.d021450 0 a b α β x))
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => _root_.GD.N0106.N0428.N0765.N1526.d021443 b α β) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with e he
    have hc := (_root_.GD.N0106.N0428.N0765.N1526.d021453 he a b α β hw).mono Ioc_subset_Icc_self
    simpa only [uIoc_of_le zero_le_one] using hc.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [self_mem_nhdsWithin] with e he
    filter_upwards [volume.ae_ne (1 : ℝ)] with x hx1
    intro hx
    rw [uIoc_of_le zero_le_one] at hx
    exact _root_.GD.N0106.N0428.N0765.N1526.d021451 he.le ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩ a b α β (_root_.GD.N0106.N0428.N0765.N1538.d021233 hw)
  · filter_upwards [volume.ae_ne (1 : ℝ)] with x hx1
    intro hx
    rw [uIoc_of_le zero_le_one] at hx
    exact (_root_.GD.N0106.N0428.N0765.N1526.d021455 ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩ a b α β hw).tendsto.mono_left
      nhdsWithin_le_nhds

end
end GD.N0106.N0428.N0765.N1526

#print axioms _root_.GD.N0106.N0428.N0765.N1526.d021449
#print axioms _root_.GD.N0106.N0428.N0765.N1526.d021451
#print axioms _root_.GD.N0106.N0428.N0765.N1526.d021456
#print axioms _root_.GD.N0106.N0428.N0765.N1526.d021457
