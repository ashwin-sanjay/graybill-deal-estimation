import GD.Module1288
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace GD.N0106.N0428.N0765.N1563
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1616

private def d020971 (eta u v w : ℝ) : ℝ := v + eta * w + (1 + eta) * u

def d020972 (eta u v w : ℝ) (z : ℂ) : ℂ :=
  (v : ℂ) + (_root_.GD.N0106.N0428.N0765.N1563.d020971 eta u v w : ℂ) * Complex.exp z +
    (eta * w : ℂ) * (Complex.exp z) ^ 2

def d020973 (a : ℝ) (n : ℕ) (eta u v w : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) * z) * (1 + Complex.exp z) ^ n *
    _root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z ^ ((-21 / 2 : ℝ) : ℂ)

def d020974 (eta u v w : ℝ) (z : ℂ) : ℂ := _root_.GD.N0106.N0428.N0765.N1563.d020973 (11 / 2) 10 eta u v w z
def d020975 (eta u v w : ℝ) (z : ℂ) : ℂ := _root_.GD.N0106.N0428.N0765.N1563.d020973 (13 / 2) 9 eta u v w z

def d020976 (d : ℝ) : Set ℂ := {z | |z.im| < d}

private theorem d020977 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    0 < _root_.GD.N0106.N0428.N0765.N1563.d020971 eta u v w := by
  unfold _root_.GD.N0106.N0428.N0765.N1563.d020971
  have hew : 0 < eta * w := mul_pos heta hw
  have heu : 0 ≤ (1 + eta) * u := mul_nonneg (by linarith) hu
  linarith

theorem d020978 (eta u v w : ℝ) (z : ℂ) :
    _root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z = (v : ℂ) + (_root_.GD.N0106.N0428.N0765.N1563.d020971 eta u v w : ℂ) * Complex.exp z +
      (eta * w : ℂ) * Complex.exp (2 * z) := by
  unfold _root_.GD.N0106.N0428.N0765.N1563.d020972
  rw [show (2 : ℂ) * z = z + z by ring, Complex.exp_add]
  ring

theorem d020979 (eta u v w c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w (c : ℂ) = (_root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1563.d020972 _root_.GD.N0106.N0428.N0765.N1563.d020971 _root_.GD.N0106.N0428.N0765.N1616.d020956
  rw [← Complex.ofReal_exp]
  push_cast
  ring

private theorem d020980 (eta u v w : ℝ) (z : ℂ) :
    (_root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z).re = v + _root_.GD.N0106.N0428.N0765.N1563.d020971 eta u v w * Real.exp z.re * Real.cos z.im +
      eta * w * (Real.exp z.re) ^ 2 *
        ((Real.cos z.im) ^ 2 - (Real.sin z.im) ^ 2) := by
  unfold _root_.GD.N0106.N0428.N0765.N1563.d020972
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.exp_im, pow_two]
  ring

private theorem d020981 (eta u v w : ℝ) (z : ℂ) :
    (_root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z).im =
      (_root_.GD.N0106.N0428.N0765.N1563.d020971 eta u v w * Real.exp z.re +
        2 * eta * w * (Real.exp z.re) ^ 2 * Real.cos z.im) * Real.sin z.im := by
  unfold _root_.GD.N0106.N0428.N0765.N1563.d020972
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.exp_im, pow_two]
  ring

private theorem d020982 {d : ℝ} (hd : d < Real.pi / 2) {z : ℂ}
    (hz : |z.im| ≤ d) : 0 < Real.cos z.im := by
  have h : |z.im| < Real.pi / 2 := lt_of_le_of_lt hz hd
  exact Real.cos_pos_of_mem_Ioo (abs_lt.mp h)

private theorem d020983 {d : ℝ} (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) :
    0 < Real.cos d := by
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith, hd⟩

private theorem d020984 {d : ℝ} (hd0 : 0 ≤ d) (hd : d < Real.pi / 2)
    {z : ℂ} (hz : |z.im| ≤ d) : Real.cos d ≤ Real.cos z.im := by
  have hpi : d ≤ Real.pi := by linarith [Real.pi_pos]
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg z.im) hpi hz
  simpa only [Real.cos_abs] using h

theorem d020985 (eta u v w : ℝ) (z : ℂ) :
    (Complex.exp (((-z.im : ℝ) : ℂ) * Complex.I) * _root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z).re =
      _root_.GD.N0106.N0428.N0765.N1563.d020971 eta u v w * Real.exp z.re +
        Real.cos z.im * (v + eta * w * (Real.exp z.re) ^ 2) := by
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, _root_.GD.N0106.N0428.N0765.N1563.d020980, _root_.GD.N0106.N0428.N0765.N1563.d020981]
  simp only [Real.cos_neg, Real.sin_neg]
  calc
    _ = _root_.GD.N0106.N0428.N0765.N1563.d020971 eta u v w * Real.exp z.re +
        Real.cos z.im * (v + eta * w * (Real.exp z.re) ^ 2) +
        (_root_.GD.N0106.N0428.N0765.N1563.d020971 eta u v w * Real.exp z.re +
          eta * w * (Real.exp z.re) ^ 2 * Real.cos z.im) *
            ((Real.cos z.im) ^ 2 + (Real.sin z.im) ^ 2 - 1) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring

theorem d020986 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) {z : ℂ} (hz : |z.im| ≤ d) :
    Real.cos d * _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w z.re ≤ ‖_root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z‖ := by
  have hb := _root_.GD.N0106.N0428.N0765.N1563.d020977 heta hu hv hw
  have hc := _root_.GD.N0106.N0428.N0765.N1563.d020982 hd hz
  have hcd := _root_.GD.N0106.N0428.N0765.N1563.d020984 hd0 hd hz
  have hr := Real.exp_pos z.re
  have hew := mul_pos heta hw
  have hrot :
      Real.cos z.im * _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w z.re ≤
        (Complex.exp (((-z.im : ℝ) : ℂ) * Complex.I) * _root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z).re := by
    rw [_root_.GD.N0106.N0428.N0765.N1563.d020985]
    change Real.cos z.im *
      (v + _root_.GD.N0106.N0428.N0765.N1563.d020971 eta u v w * Real.exp z.re + eta * w * (Real.exp z.re) ^ 2) ≤ _
    have hcos_le : Real.cos z.im ≤ 1 := Real.cos_le_one _
    have hprod : 0 ≤ (1 - Real.cos z.im) *
        (_root_.GD.N0106.N0428.N0765.N1563.d020971 eta u v w * Real.exp z.re) :=
      mul_nonneg (by linarith) (mul_nonneg hb.le hr.le)
    nlinarith
  calc
    Real.cos d * _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w z.re ≤
        Real.cos z.im * _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w z.re :=
          mul_le_mul_of_nonneg_right hcd (le_of_lt (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw z.re))
    _ ≤ (Complex.exp (((-z.im : ℝ) : ℂ) * Complex.I) * _root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z).re := hrot
    _ ≤ ‖Complex.exp (((-z.im : ℝ) : ℂ) * Complex.I) * _root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z‖ :=
      Complex.re_le_norm _
    _ = ‖_root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z‖ := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem d020987 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) {z : ℂ} (hz : |z.im| ≤ d) :
    _root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hθ : z.im = 0
  · left
    rw [_root_.GD.N0106.N0428.N0765.N1563.d020980, hθ]
    simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero]
    have hb := _root_.GD.N0106.N0428.N0765.N1563.d020977 heta hu hv hw
    have hr := Real.exp_pos z.re
    have hew := mul_pos heta hw
    positivity
  · right
    rw [_root_.GD.N0106.N0428.N0765.N1563.d020981]
    have hb := _root_.GD.N0106.N0428.N0765.N1563.d020977 heta hu hv hw
    have hc := _root_.GD.N0106.N0428.N0765.N1563.d020982 hd hz
    have hr := Real.exp_pos z.re
    have hew := mul_pos heta hw
    have hfactor : 0 < _root_.GD.N0106.N0428.N0765.N1563.d020971 eta u v w * Real.exp z.re +
        2 * eta * w * (Real.exp z.re) ^ 2 * Real.cos z.im := by positivity
    apply mul_ne_zero hfactor.ne'
    rcases lt_or_gt_of_ne hθ with hneg | hpos
    · have hpi : -Real.pi < z.im := by
        have h := (abs_lt.mp (lt_of_le_of_lt hz hd)).1
        linarith [Real.pi_pos]
      exact (Real.sin_neg_of_neg_of_neg_pi_lt hneg hpi).ne
    · have hpi : z.im < Real.pi := by
        have h := (abs_lt.mp (lt_of_le_of_lt hz hd)).2
        linarith [Real.pi_pos]
      exact (Real.sin_pos_of_pos_of_lt_pi hpos hpi).ne'

theorem d020988 (eta u v w : ℝ) :
    Differentiable ℂ (_root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w) := by
  unfold _root_.GD.N0106.N0428.N0765.N1563.d020972
  fun_prop

theorem d020989 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (a : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (_root_.GD.N0106.N0428.N0765.N1563.d020973 a n eta u v w) (_root_.GD.N0106.N0428.N0765.N1563.d020976 d) := by
  intro z hz
  have hzclosed : |z.im| ≤ d := le_of_lt hz
  have hQ : DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w) z := _root_.GD.N0106.N0428.N0765.N1563.d020988 eta u v w z
  have hp := hQ.cpow_const (c := ((-21 / 2 : ℝ) : ℂ))
    (_root_.GD.N0106.N0428.N0765.N1563.d020987 heta hu hv hw hd0 hd hzclosed)
  have hn : DifferentiableAt ℂ
      (fun t : ℂ => Complex.exp ((a : ℂ) * t) * (1 + Complex.exp t) ^ n) z := by
    fun_prop
  unfold _root_.GD.N0106.N0428.N0765.N1563.d020973
  exact (hn.mul hp).differentiableWithinAt

theorem d020990 (a : ℝ) (n : ℕ) (eta u v w c : ℝ)
    (hQ : 0 ≤ _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c) :
    _root_.GD.N0106.N0428.N0765.N1563.d020973 a n eta u v w (c : ℂ) =
      ((Real.exp (a * c) * (1 + Real.exp c) ^ n *
        _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w c ^ (-21 / 2 : ℝ) : ℝ) : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1563.d020973
  have hec : Complex.exp (c : ℂ) = (Real.exp c : ℂ) :=
    (Complex.ofReal_exp c).symm
  have hea : Complex.exp ((a : ℂ) * (c : ℂ)) = (Real.exp (a * c) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
  rw [hea, hec, _root_.GD.N0106.N0428.N0765.N1563.d020979, ← Complex.ofReal_cpow hQ]
  norm_cast

theorem d020991 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w (c : ℂ) = (_root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c : ℂ) := by
  change _root_.GD.N0106.N0428.N0765.N1563.d020973 (11 / 2) 10 eta u v w (c : ℂ) = _
  rw [_root_.GD.N0106.N0428.N0765.N1563.d020990 (11 / 2) 10 eta u v w c
    (le_of_lt (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c))]
  have he : Real.exp ((11 / 2 : ℝ) * c) = Real.exp (11 * c / 2) :=
    congrArg Real.exp (by ring)
  simp only [he, _root_.GD.N0106.N0428.N0765.N1616.d020957, show (-21 / 2 : ℝ) = -(21 / 2) by ring]

theorem d020992 {eta u v w : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w (c : ℂ) = (_root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c : ℂ) := by
  change _root_.GD.N0106.N0428.N0765.N1563.d020973 (13 / 2) 9 eta u v w (c : ℂ) = _
  rw [_root_.GD.N0106.N0428.N0765.N1563.d020990 (13 / 2) 9 eta u v w c
    (le_of_lt (_root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw c))]
  have he : Real.exp ((13 / 2 : ℝ) * c) = Real.exp (13 * c / 2) :=
    congrArg Real.exp (by ring)
  simp only [he, _root_.GD.N0106.N0428.N0765.N1616.d020958, show (-21 / 2 : ℝ) = -(21 / 2) by ring]

theorem d020993 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2)
    (a : ℝ) (n : ℕ) {z : ℂ} (hz : |z.im| ≤ d) :
    ‖_root_.GD.N0106.N0428.N0765.N1563.d020973 a n eta u v w z‖ ≤
      (Real.cos d) ^ (-21 / 2 : ℝ) *
        (Real.exp (a * z.re) * (1 + Real.exp z.re) ^ n *
          _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w z.re ^ (-21 / 2 : ℝ)) := by
  have hc := _root_.GD.N0106.N0428.N0765.N1563.d020983 hd0 hd
  have hq := _root_.GD.N0106.N0428.N0765.N1616.d020959 heta hu hv hw z.re
  have hqn := _root_.GD.N0106.N0428.N0765.N1563.d020986 heta hu hv hw hd0 hd hz
  have hpow := Real.rpow_le_rpow_of_nonpos (mul_pos hc hq) hqn
    (by norm_num : (-21 / 2 : ℝ) ≤ 0)
  have hexp : ‖Complex.exp ((a : ℂ) * z)‖ = Real.exp (a * z.re) := by
    rw [Complex.norm_exp, Complex.re_ofReal_mul]
  have hnum : ‖(1 : ℂ) + Complex.exp z‖ ≤ 1 + Real.exp z.re := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp z‖ := norm_add_le _ _
      _ = _ := by simp [Complex.norm_exp]
  have hpow_num : ‖(1 : ℂ) + Complex.exp z‖ ^ n ≤
      (1 + Real.exp z.re) ^ n := by
    exact pow_le_pow_left₀ (norm_nonneg _) hnum n
  have hfactor :
      (Real.cos d * _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w z.re) ^ (-21 / 2 : ℝ) =
        (Real.cos d) ^ (-21 / 2 : ℝ) *
          _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w z.re ^ (-21 / 2 : ℝ) := by
    exact Real.mul_rpow hc.le hq.le
  unfold _root_.GD.N0106.N0428.N0765.N1563.d020973
  rw [norm_mul, norm_mul, Complex.norm_cpow_real, norm_pow, hexp]
  calc
    Real.exp (a * z.re) * ‖1 + Complex.exp z‖ ^ n *
        ‖_root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z‖ ^ (-21 / 2 : ℝ) ≤
      Real.exp (a * z.re) * (1 + Real.exp z.re) ^ n *
        ‖_root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w z‖ ^ (-21 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hpow_num (Real.exp_pos _).le)
            (Real.rpow_nonneg (norm_nonneg _) _)
    _ ≤
      Real.exp (a * z.re) * (1 + Real.exp z.re) ^ n *
        (Real.cos d * _root_.GD.N0106.N0428.N0765.N1616.d020956 eta u v w z.re) ^ (-21 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (Real.exp_pos _).le (pow_nonneg (by positivity) _))
    _ = _ := by rw [hfactor]; ring

theorem d020994 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2)
    {z : ℂ} (hz : |z.im| ≤ d) :
    ‖_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w z‖ ≤
      ((Real.cos d)⁻¹) ^ (21 / 2 : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w z.re := by
  have h := _root_.GD.N0106.N0428.N0765.N1563.d020993 heta hu hv hw hd0 hd (11 / 2) 10 hz
  simpa [_root_.GD.N0106.N0428.N0765.N1563.d020974, _root_.GD.N0106.N0428.N0765.N1616.d020957, show (-21 / 2 : ℝ) = -(21 / 2) by ring,
    Real.rpow_neg_eq_inv_rpow, show (11 / 2 : ℝ) * z.re =
    11 * z.re / 2 by ring, mul_assoc] using h

theorem d020995 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2)
    {z : ℂ} (hz : |z.im| ≤ d) :
    ‖_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w z‖ ≤
      ((Real.cos d)⁻¹) ^ (21 / 2 : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w z.re := by
  have h := _root_.GD.N0106.N0428.N0765.N1563.d020993 heta hu hv hw hd0 hd (13 / 2) 9 hz
  simpa [_root_.GD.N0106.N0428.N0765.N1563.d020975, _root_.GD.N0106.N0428.N0765.N1616.d020958, show (-21 / 2 : ℝ) = -(21 / 2) by ring,
    Real.rpow_neg_eq_inv_rpow, show (13 / 2 : ℝ) * z.re =
    13 * z.re / 2 by ring, mul_assoc] using h

end
end GD.N0106.N0428.N0765.N1563

#print axioms _root_.GD.N0106.N0428.N0765.N1563.d020978
#print axioms _root_.GD.N0106.N0428.N0765.N1563.d020979
#print axioms _root_.GD.N0106.N0428.N0765.N1563.d020985
#print axioms _root_.GD.N0106.N0428.N0765.N1563.d020986
#print axioms _root_.GD.N0106.N0428.N0765.N1563.d020987
#print axioms _root_.GD.N0106.N0428.N0765.N1563.d020989
#print axioms _root_.GD.N0106.N0428.N0765.N1563.d020991
#print axioms _root_.GD.N0106.N0428.N0765.N1563.d020992
#print axioms _root_.GD.N0106.N0428.N0765.N1563.d020994
#print axioms _root_.GD.N0106.N0428.N0765.N1563.d020995
