import GD.Module0371
import GD.Module0364
import GD.Module0368
import GD.Module1784
import GD.Module1762










set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory
open scoped FourierTransform

namespace GD.N0106.N0428.N0765.N1507
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1585 _root_.GD.N0106.N0428.N0765.N1550 _root_.GD.N0106.N0428.N0765.N1613 _root_.GD.N0106.N0428.N0765.N1687

theorem d029669 : IsOpen {z : ℂ | |z.im| < Real.pi / 2} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem d029670 {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {z : ℂ}
    (hz : |z.im| < Real.pi / 2) : DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) z :=
  (_root_.GD.N0106.N0428.N0765.N1585.d005539 hs ht).differentiableAt (_root_.GD.N0106.N0428.N0765.N1507.d029669.mem_nhds hz)

theorem d029671 (y : ℝ) : Continuous fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005473 x y := by
  unfold _root_.GD.N0106.N0428.N0765.N1550.d005473
  fun_prop

theorem d029672 {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {y : ℝ}
    (hy : |y| < Real.pi / 2) : Continuous (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) y) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hz : |(_root_.GD.N0106.N0428.N0765.N1550.d005473 x y).im| < Real.pi / 2 := by
    rw [_root_.GD.N0106.N0428.N0765.N1550.d005477]
    exact hy
  change ContinuousAt (fun u : ℝ => _root_.GD.N0106.N0428.N0765.N1585.d005529 s t (_root_.GD.N0106.N0428.N0765.N1550.d005473 u y)) x
  exact (_root_.GD.N0106.N0428.N0765.N1507.d029670 hs ht hz).continuousAt.comp
    (f := fun u : ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005473 u y) ((_root_.GD.N0106.N0428.N0765.N1507.d029671 y).continuousAt (x := x))


theorem d029673 {s t d : ℝ} (hs : 0 < s) (ht : 0 < t) (hd0 : 0 ≤ d)
    (hd : d < Real.pi / 2) {z : ℂ} (hz : |z.im| ≤ d) :
    ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 s t z‖ ≤ Real.cos (d / 2) ^ (-(s + t)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 s t z.re := by
  have hz' : |z.im| < Real.pi / 2 := lt_of_le_of_lt hz hd
  have h := _root_.GD.N0106.N0428.N0765.N1585.d005536 hs ht hz'
  have hcd : 0 < Real.cos (d / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hcos : Real.cos (d / 2) ≤ Real.cos (z.im / 2) := by
    have habs : Real.cos (z.im / 2) = Real.cos (|z.im| / 2) := by
      rw [← Real.cos_abs (z.im / 2), abs_div, abs_two]
    rw [habs]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
    linarith
  have hpow : Real.cos (z.im / 2) ^ (-(s + t)) ≤ Real.cos (d / 2) ^ (-(s + t)) :=
    Real.rpow_le_rpow_of_nonpos hcd hcos (by linarith)
  calc ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 s t z‖ ≤ Real.cos (z.im / 2) ^ (-(s + t)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 s t z.re := h
    _ ≤ Real.cos (d / 2) ^ (-(s + t)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 s t z.re :=
        mul_le_mul_of_nonneg_right hpow (_root_.GD.N0106.N0428.N0765.N1539.d005375 hs ht _).le

theorem d029674 {s t d : ℝ} (hs : 0 < s) (ht : 0 < t) (hd0 : 0 ≤ d)
    (hd : d < Real.pi / 2) {y : ℝ} (hy : |y| ≤ d) (x : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) y x‖ ≤ Real.cos (d / 2) ^ (-(s + t)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 s t x := by
  have h := _root_.GD.N0106.N0428.N0765.N1507.d029673 hs ht hd0 hd (z := _root_.GD.N0106.N0428.N0765.N1550.d005473 x y) (by rw [_root_.GD.N0106.N0428.N0765.N1550.d005477]; exact hy)
  rw [_root_.GD.N0106.N0428.N0765.N1550.d005476] at h
  exact h

theorem d029675 {s t d : ℝ} (hs : 0 < s) (ht : 0 < t) (hd0 : 0 ≤ d)
    (hd : d < Real.pi / 2) {y : ℝ} (hy : |y| ≤ d) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) y) := by
  refine Integrable.mono'
    ((_root_.GD.N0106.N0428.N0765.N1539.d005379 hs ht).const_mul (Real.cos (d / 2) ^ (-(s + t))))
    (_root_.GD.N0106.N0428.N0765.N1507.d029672 hs ht (lt_of_le_of_lt hy hd)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x => _root_.GD.N0106.N0428.N0765.N1507.d029674 hs ht hd0 hd hy x)

theorem d029676 {s t d : ℝ} (hs : 0 < s) (ht : 0 < t) (hd0 : 0 ≤ d)
    (hd : d < Real.pi / 2) {y : ℝ} (hy : |y| ≤ d) :
    (∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) y x‖) ≤ Real.cos (d / 2) ^ (-(s + t)) := by
  have h1 : (∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) y x‖) ≤
      ∫ x : ℝ, Real.cos (d / 2) ^ (-(s + t)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 s t x :=
    integral_mono (_root_.GD.N0106.N0428.N0765.N1507.d029675 hs ht hd0 hd hy).norm
      ((_root_.GD.N0106.N0428.N0765.N1539.d005379 hs ht).const_mul _) (fun x => _root_.GD.N0106.N0428.N0765.N1507.d029674 hs ht hd0 hd hy x)
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1539.d005380 hs ht, mul_one] at h1
  exact h1



theorem d029677 {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Continuous (_root_.GD.N0106.N0428.N0765.N1539.d005373 s t) := by
  have h0 : |(0 : ℝ)| < Real.pi / 2 := by
    rw [abs_zero]
    positivity
  have hc := _root_.GD.N0106.N0428.N0765.N1507.d029672 hs ht h0
  have heq : _root_.GD.N0106.N0428.N0765.N1539.d005373 s t = fun x => (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) 0 x).re := by
    funext x
    rw [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005478, _root_.GD.N0106.N0428.N0765.N1585.d005530, Complex.ofReal_re]
  rw [heq]
  exact Complex.continuous_re.comp hc

theorem d029678 {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1539.d005373 s t x| ≤ (beta s t)⁻¹ * Real.exp (s * x) := by
  have hB := beta_pos hs ht
  have hP : (1 : ℝ) ≤ (1 + Real.exp x) ^ (s + t) :=
    Real.one_le_rpow (by linarith [Real.exp_pos x]) (by linarith)
  rw [abs_of_pos (_root_.GD.N0106.N0428.N0765.N1539.d005375 hs ht x)]
  unfold _root_.GD.N0106.N0428.N0765.N1539.d005373
  calc Real.exp (s * x) / (beta s t * (1 + Real.exp x) ^ (s + t))
      ≤ Real.exp (s * x) / (beta s t * 1) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (mul_pos hB one_pos)
          (mul_le_mul_of_nonneg_left hP hB.le)
    _ = (beta s t)⁻¹ * Real.exp (s * x) := by rw [mul_one, div_eq_inv_mul]

theorem d029679 {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1539.d005373 s t x| ≤ (beta s t)⁻¹ * Real.exp (-t * x) := by
  have hB := beta_pos hs ht
  have hE : 0 < Real.exp (x * (s + t)) := Real.exp_pos _
  have hP : Real.exp (x * (s + t)) ≤ (1 + Real.exp x) ^ (s + t) := by
    have h := Real.rpow_le_rpow (Real.exp_pos x).le
      (by linarith [Real.exp_pos x] : Real.exp x ≤ 1 + Real.exp x) (by linarith : (0 : ℝ) ≤ s + t)
    rw [← Real.exp_mul] at h
    exact h
  rw [abs_of_pos (_root_.GD.N0106.N0428.N0765.N1539.d005375 hs ht x)]
  unfold _root_.GD.N0106.N0428.N0765.N1539.d005373
  calc Real.exp (s * x) / (beta s t * (1 + Real.exp x) ^ (s + t))
      ≤ Real.exp (s * x) / (beta s t * Real.exp (x * (s + t))) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (mul_pos hB hE)
          (mul_le_mul_of_nonneg_left hP hB.le)
    _ = (beta s t)⁻¹ * Real.exp (-t * x) := by
        rw [show Real.exp (-t * x) = Real.exp (s * x) / Real.exp (x * (s + t)) by
              rw [← Real.exp_sub]; congr 1; ring,
          div_eq_inv_mul, div_eq_inv_mul, mul_inv, mul_assoc]



theorem d029680 {s t d : ℝ} (hs : 0 < s) (ht : 0 < t) (hd0 : 0 ≤ d)
    (hd : d < Real.pi / 2) (xi : ℝ) :
    ‖𝓕 (fun x : ℝ => (_root_.GD.N0106.N0428.N0765.N1539.d005373 s t x : ℂ)) xi‖ ≤
      Real.cos (d / 2) ^ (-(s + t)) * Real.exp (-(2 * Real.pi * d) * |xi|) := by
  have hC : 0 ≤ Real.cos (d / 2) ^ (-(s + t)) := by
    apply Real.rpow_nonneg
    apply (Real.cos_pos_of_mem_Ioo _).le
    constructor <;> linarith [Real.pi_pos]
  have hhol : ∀ z : ℂ, |z.im| ≤ d → DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) z :=
    fun z hz => _root_.GD.N0106.N0428.N0765.N1507.d029670 hs ht (lt_of_le_of_lt hz hd)
  have h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) 0) :=
    _root_.GD.N0106.N0428.N0765.N1507.d029675 hs ht hd0 hd (by rw [abs_zero]; exact hd0)
  have hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) (-d)) :=
    _root_.GD.N0106.N0428.N0765.N1507.d029675 hs ht hd0 hd
      (by simpa only [abs_neg, abs_of_nonneg hd0] using (le_refl d))
  have hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) d) :=
    _root_.GD.N0106.N0428.N0765.N1507.d029675 hs ht hd0 hd
      (by simpa only [abs_of_nonneg hd0] using (le_refl d))
  have hleft : ∀ z : ℂ, |z.im| ≤ d → z.re ≤ 0 →
      ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 s t z‖ ≤ (Real.cos (d / 2) ^ (-(s + t)) * (beta s t)⁻¹) *
        Real.exp (s * z.re) := by
    intro z hz _
    calc ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 s t z‖ ≤ Real.cos (d / 2) ^ (-(s + t)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 s t z.re :=
          _root_.GD.N0106.N0428.N0765.N1507.d029673 hs ht hd0 hd hz
      _ ≤ Real.cos (d / 2) ^ (-(s + t)) * ((beta s t)⁻¹ * Real.exp (s * z.re)) := by
          apply mul_le_mul_of_nonneg_left _ hC
          have := _root_.GD.N0106.N0428.N0765.N1507.d029678 hs ht z.re
          rwa [abs_of_pos (_root_.GD.N0106.N0428.N0765.N1539.d005375 hs ht _)] at this
      _ = (Real.cos (d / 2) ^ (-(s + t)) * (beta s t)⁻¹) * Real.exp (s * z.re) := by ring
  have hright : ∀ z : ℂ, |z.im| ≤ d → 0 ≤ z.re →
      ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 s t z‖ ≤ (Real.cos (d / 2) ^ (-(s + t)) * (beta s t)⁻¹) *
        Real.exp (-t * z.re) := by
    intro z hz _
    calc ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 s t z‖ ≤ Real.cos (d / 2) ^ (-(s + t)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 s t z.re :=
          _root_.GD.N0106.N0428.N0765.N1507.d029673 hs ht hd0 hd hz
      _ ≤ Real.cos (d / 2) ^ (-(s + t)) * ((beta s t)⁻¹ * Real.exp (-t * z.re)) := by
          apply mul_le_mul_of_nonneg_left _ hC
          have := _root_.GD.N0106.N0428.N0765.N1507.d029679 hs ht z.re
          rwa [abs_of_pos (_root_.GD.N0106.N0428.N0765.N1539.d005375 hs ht _)] at this
      _ = (Real.cos (d / 2) ^ (-(s + t)) * (beta s t)⁻¹) * Real.exp (-t * z.re) := by ring
  have hfourier := _root_.GD.N0106.N0428.N0765.N1550.d005490 hd0 hhol h0 hminus hplus hs ht hleft hright xi
  have hreal : (fun x : ℝ => (_root_.GD.N0106.N0428.N0765.N1539.d005373 s t x : ℂ)) = _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) 0 := by
    funext x
    rw [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005478, _root_.GD.N0106.N0428.N0765.N1585.d005530]
  have hheight : |(if 0 ≤ xi then -d else d)| ≤ d := by
    split_ifs <;> simpa only [abs_neg, abs_of_nonneg hd0] using (le_refl d)
  have hboundary := _root_.GD.N0106.N0428.N0765.N1507.d029676 hs ht hd0 hd hheight
  rw [hreal]
  calc ‖𝓕 (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) 0) xi‖
      ≤ Real.exp (-2 * Real.pi * d * |xi|) *
          ∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1585.d005529 s t) (if 0 ≤ xi then -d else d) x‖ := hfourier
    _ ≤ Real.exp (-2 * Real.pi * d * |xi|) * Real.cos (d / 2) ^ (-(s + t)) :=
        mul_le_mul_of_nonneg_left hboundary (Real.exp_pos _).le
    _ = Real.cos (d / 2) ^ (-(s + t)) * Real.exp (-(2 * Real.pi * d) * |xi|) := by
        rw [mul_comm]
        congr 2
        ring



theorem d029681 {s t d h : ℝ} (hs : 0 < s) (ht : 0 < t) (hd : 0 < d)
    (hdpi : d < Real.pi / 2) (hh : 0 < h) (offset : ℝ) :
    |h * (∑' n : ℤ, _root_.GD.N0106.N0428.N0765.N1539.d005373 s t (offset + h * n)) - 1| ≤
      2 * Real.cos (d / 2) ^ (-(s + t)) / (Real.exp (2 * Real.pi * d / h) - 1) := by
  have hk : 0 < 2 * Real.pi * d := by positivity
  have h := _root_.GD.N0106.N0428.N0765.N1613.d005636 (f := _root_.GD.N0106.N0428.N0765.N1539.d005373 s t) (_root_.GD.N0106.N0428.N0765.N1507.d029677 hs ht)
    hs ht hk hh (fun x _ => _root_.GD.N0106.N0428.N0765.N1507.d029678 hs ht x) (fun x _ => _root_.GD.N0106.N0428.N0765.N1507.d029679 hs ht x)
    (fun xi => _root_.GD.N0106.N0428.N0765.N1507.d029680 hs ht hd.le hdpi xi) offset
  rw [_root_.GD.N0106.N0428.N0765.N1539.d005380 hs ht] at h
  exact h


theorem d029682 (a b h c : ℝ) :
    (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b 0 h c k) =
      h * ∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1539.d005373 a b (c + h * k) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1687.d029646, _root_.GD.N0106.N0428.N0765.N1687.d029645, zero_mul, Real.exp_zero, one_mul]
  rw [tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  congr 1
  ring


theorem d029683 {a b d h : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hd : 0 < d) (hdpi : d < Real.pi / 2) (hh : 0 < h) (c : ℝ) :
    (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 a b 0 h c k) ≤
      1 + 2 * Real.cos (d / 2) ^ (-(a + b)) /
        (Real.exp (2 * Real.pi * d / h) - 1) := by
  rw [_root_.GD.N0106.N0428.N0765.N1507.d029682]
  have he := _root_.GD.N0106.N0428.N0765.N1507.d029681 ha hb hd hdpi hh c
  have hu := (abs_le.mp he).2
  linarith


def d029684 (d h : ℝ) : ℝ :=
  2 * Real.cos (d / 2) ^ (-((23 : ℝ) / 2)) /
    (Real.exp (2 * Real.pi * d / h) - 1)


def d029685 (d h : ℝ) : ℝ :=
  2 * Real.cos (d / 2) ^ (-(10 : ℝ)) /
    (Real.exp (2 * Real.pi * d / h) - 1)


theorem d029686 {d h : ℝ} (hd : 0 < d) (hdpi : d < Real.pi / 2)
    (hh : 0 < h) (c : ℝ) :
    (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 (3 / 2) 10 0 h c k) ≤ 1 + _root_.GD.N0106.N0428.N0765.N1507.d029684 d h := by
  have h := _root_.GD.N0106.N0428.N0765.N1507.d029683 (a := (3 : ℝ) / 2) (b := 10)
    (by norm_num) (by norm_num) hd hdpi hh c
  norm_num [_root_.GD.N0106.N0428.N0765.N1507.d029684] at h ⊢
  exact h


theorem d029687 {d h : ℝ} (hd : 0 < d) (hdpi : d < Real.pi / 2)
    (hh : 0 < h) (c : ℝ) :
    (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 5 5 0 h c k) ≤ 1 + _root_.GD.N0106.N0428.N0765.N1507.d029685 d h := by
  have h := _root_.GD.N0106.N0428.N0765.N1507.d029683 (a := (5 : ℝ)) (b := 5)
    (by norm_num) (by norm_num) hd hdpi hh c
  norm_num [_root_.GD.N0106.N0428.N0765.N1507.d029685] at h ⊢
  exact h


theorem d029688 (h c : ℝ) :
    (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 (3 / 2) 10 1 h c k) =
      (1 / 6 : ℝ) * ∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 (5 / 2) 9 0 h c k := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [_root_.GD.N0106.N0428.N0765.N1687.d029646, _root_.GD.N0106.N0428.N0765.N1687.d029645, one_mul, zero_mul, Real.exp_zero,
    _root_.GD.N0106.N0428.N0765.N1512.d029165]
  ring



theorem d029689 {d h : ℝ} (hd : 0 < d) (hdpi : d < Real.pi / 2)
    (hh : 0 < h) (c : ℝ) :
    (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 (3 / 2) 10 1 h c k) ≤ (1 + _root_.GD.N0106.N0428.N0765.N1507.d029684 d h) / 6 := by
  have hm := _root_.GD.N0106.N0428.N0765.N1507.d029683 (a := (5 : ℝ) / 2) (b := 9)
    (by norm_num) (by norm_num) hd hdpi hh c
  have hexponent : -((5 : ℝ) / 2 + 9) = -((23 : ℝ) / 2) := by norm_num
  rw [hexponent] at hm
  change (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1687.d029646 (5 / 2) 9 0 h c k) ≤ 1 + _root_.GD.N0106.N0428.N0765.N1507.d029684 d h at hm
  rw [_root_.GD.N0106.N0428.N0765.N1507.d029688]
  linarith

end
end GD.N0106.N0428.N0765.N1507

#print axioms _root_.GD.N0106.N0428.N0765.N1507.d029681
#print axioms _root_.GD.N0106.N0428.N0765.N1507.d029686
#print axioms _root_.GD.N0106.N0428.N0765.N1507.d029687
#print axioms _root_.GD.N0106.N0428.N0765.N1507.d029689
