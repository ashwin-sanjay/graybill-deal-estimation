import GD.Module1302
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.RealDeriv












set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Metric _root_.GD.N0235

namespace GD.N0106.N0428.N0765.N1523
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1535 _root_.GD.N0106.N0428.N0765.N1536 _root_.GD.N0106.N0428.N0765.N1565 _root_.GD.N0106.N0428.N0765.N1529

theorem d021308 (x : ℝ) :
    closedBall (x : ℂ) ((1 : ℝ) / 7) ⊆ _root_.GD.N0106.N0428.N0765.N1535.d021126 := by
  intro z hz
  exact _root_.GD.N0106.N0428.N0765.N1535.d021164 x (by simpa only [mem_closedBall, dist_eq_norm] using hz)

theorem d021309 (x : ℝ) {z : ℂ}
    (hz : z ∈ closedBall (x : ℂ) ((1 : ℝ) / 7)) : |z.im| ≤ (1 : ℝ) / 7 := by
  have hnorm : ‖z - (x : ℂ)‖ ≤ (1 : ℝ) / 7 := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have him := (Complex.abs_im_le_norm (z - (x : ℂ))).trans hnorm
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using him

theorem d021310 (x : ℝ) {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q)
    {z : ℂ} (hz : z ∈ closedBall (x : ℂ) ((1 : ℝ) / 7)) :
    ‖_root_.GD.N0106.N0428.N0765.N1535.d021136 q z‖ ≤ (41 : ℝ) / 4 := by
  have hs := _root_.GD.N0106.N0428.N0765.N1523.d021308 x hz
  have hsec := (_root_.GD.N0106.N0428.N0765.N1535.d021165 (_root_.GD.N0106.N0428.N0765.N1523.d021309 x hz)).2
  have harg : (21 : ℝ) / 4 * |z.im| = ((21 : ℝ) / 2) * |z.im| / 2 := by ring
  have hh : ‖_root_.GD.N0106.N0428.N0765.N1535.d021133 q z‖ ≤ (3 : ℝ) / 2 := by
    apply (_root_.GD.N0106.N0428.N0765.N1536.d021185 hq hs).trans
    rw [harg]
    exact hsec.le
  have hg : ‖_root_.GD.N0106.N0428.N0765.N1535.d021134 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [_root_.GD.N0106.N0428.N0765.N1565.d021299 hq hs, _root_.GD.N0106.N0428.N0765.N1565.d021300 hs])
  have hho : ‖_root_.GD.N0106.N0428.N0765.N1535.d021133 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z‖ ≤ (5 : ℝ) / 2 :=
    (norm_sub_le _ _).trans (by linarith [_root_.GD.N0106.N0428.N0765.N1565.d021300 hs])
  calc
    ‖_root_.GD.N0106.N0428.N0765.N1535.d021136 q z‖ ≤ ‖(_root_.GD.N0106.N0428.N0765.N1535.d021134 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z) ^ 2‖ + ‖(_root_.GD.N0106.N0428.N0765.N1535.d021133 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z) ^ 2‖ :=
      norm_sub_le _ _
    _ = ‖_root_.GD.N0106.N0428.N0765.N1535.d021134 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z‖ ^ 2 + ‖_root_.GD.N0106.N0428.N0765.N1535.d021133 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z‖ ^ 2 := by
      rw [norm_pow, norm_pow]
    _ ≤ (41 : ℝ) / 4 := by
      nlinarith [norm_nonneg (_root_.GD.N0106.N0428.N0765.N1535.d021134 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z), norm_nonneg (_root_.GD.N0106.N0428.N0765.N1535.d021133 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z)]

theorem d021311 (x : ℝ) {z : ℂ}
    (hz : z ∈ closedBall (x : ℂ) ((1 : ℝ) / 7)) :
    ‖_root_.GD.N0106.N0428.N0765.N1535.d021137 z‖ ≤ (41 : ℝ) / 4 := by
  letI : IsProbabilityMeasure _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    _root_.GD.N0235.d004251 (by norm_num) (by norm_num) (by norm_num)
  have hb : ∀ᵐ q ∂_root_.GD.N0106.N0428.N0765.N1529.d020798, ‖_root_.GD.N0106.N0428.N0765.N1535.d021136 q z‖ ≤ (41 : ℝ) / 4 :=
    _root_.GD.N0106.N0428.N0765.N1627.d021090.mono fun _ hq => _root_.GD.N0106.N0428.N0765.N1523.d021310 x hq hz
  simpa only [_root_.GD.N0106.N0428.N0765.N1535.d021137, probReal_univ, mul_one] using
    (MeasureTheory.norm_integral_le_of_norm_le_const hb)

theorem d021312 (x : ℝ) {z : ℂ}
    (hz : z ∈ closedBall (x : ℂ) ((1 : ℝ) / 7)) : ‖_root_.GD.N0106.N0428.N0765.N1535.d021137 z‖ < 11 :=
  (_root_.GD.N0106.N0428.N0765.N1523.d021311 x hz).trans_lt (by norm_num)

theorem d021313 (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n _root_.GD.N0106.N0428.N0765.N1535.d021137 (x : ℂ)‖ ≤ 11 * (n.factorial : ℝ) * 7 ^ n := by
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0 : ℝ) < 1 / 7)
    (_root_.GD.N0106.N0428.N0765.N1565.d021307.diffContOnCl_ball (_root_.GD.N0106.N0428.N0765.N1523.d021308 x))
    (fun z hz => (_root_.GD.N0106.N0428.N0765.N1523.d021312 x (sphere_subset_closedBall hz)).le)
  calc
    ‖iteratedDeriv n _root_.GD.N0106.N0428.N0765.N1535.d021137 (x : ℂ)‖ ≤ (n.factorial : ℝ) * 11 / ((1 : ℝ) / 7) ^ n := hc
    _ = 11 * (n.factorial : ℝ) * 7 ^ n := by
      rw [div_pow, one_pow, div_div_eq_mul_div, div_one]
      ring

def d021314 (x : ℝ) : ℝ := (_root_.GD.N0106.N0428.N0765.N1535.d021137 (x : ℂ)).re

theorem d021315 (n : ℕ) {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    AnalyticAt ℂ (iteratedDeriv n _root_.GD.N0106.N0428.N0765.N1535.d021137) z := by
  induction n with
  | zero =>
      simpa only [iteratedDeriv_zero] using
        _root_.GD.N0106.N0428.N0765.N1565.d021307.analyticAt (_root_.GD.N0106.N0428.N0765.N1565.d021270.mem_nhds hz)
  | succ n ih =>
      simpa only [iteratedDeriv_succ] using ih.deriv

theorem d021316 (n : ℕ) :
    iteratedDeriv n _root_.GD.N0106.N0428.N0765.N1523.d021314 =
      fun x : ℝ => (iteratedDeriv n _root_.GD.N0106.N0428.N0765.N1535.d021137 (x : ℂ)).re := by
  induction n with
  | zero =>
      simp only [iteratedDeriv_zero]
      rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      rw [iteratedDeriv_succ]
      have h := (_root_.GD.N0106.N0428.N0765.N1523.d021315 n (_root_.GD.N0106.N0428.N0765.N1535.d021138 x)).differentiableAt.hasDerivAt
      exact h.real_of_complex.deriv

theorem d021317 (location : ℝ) :
    (fun x : ℝ => 11 * _root_.GD.N0106.N0428.N0765.N1627.d021120 location (Real.exp x) /
      (1 + Real.exp x)) = _root_.GD.N0106.N0428.N0765.N1523.d021314 := by
  funext x
  rw [_root_.GD.N0106.N0428.N0765.N1523.d021314, _root_.GD.N0106.N0428.N0765.N1535.d021163 location x, Complex.ofReal_re]


theorem d021318 (location : ℝ) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fun y : ℝ => 11 * _root_.GD.N0106.N0428.N0765.N1627.d021120 location (Real.exp y) /
      (1 + Real.exp y)) x| ≤ 11 * (n.factorial : ℝ) * 7 ^ n := by
  rw [_root_.GD.N0106.N0428.N0765.N1523.d021317, _root_.GD.N0106.N0428.N0765.N1523.d021316]
  exact (Complex.abs_re_le_norm _).trans (_root_.GD.N0106.N0428.N0765.N1523.d021313 n x)


theorem d021319 (location : ℝ) :
    DifferentiableOn ℂ _root_.GD.N0106.N0428.N0765.N1535.d021137 _root_.GD.N0106.N0428.N0765.N1535.d021126 ∧
      (∀ x : ℝ, _root_.GD.N0106.N0428.N0765.N1535.d021137 (x : ℂ) =
        ((11 * _root_.GD.N0106.N0428.N0765.N1627.d021120 location (Real.exp x) / (1 + Real.exp x)) : ℝ)) ∧
      (∀ (x : ℝ) (z : ℂ), z ∈ closedBall (x : ℂ) ((1 : ℝ) / 7) →
        ‖_root_.GD.N0106.N0428.N0765.N1535.d021137 z‖ < 11) ∧
      ∀ (n : ℕ) (x : ℝ),
        ‖iteratedDeriv n _root_.GD.N0106.N0428.N0765.N1535.d021137 (x : ℂ)‖ ≤ 11 * (n.factorial : ℝ) * 7 ^ n :=
  ⟨_root_.GD.N0106.N0428.N0765.N1565.d021307, _root_.GD.N0106.N0428.N0765.N1535.d021163 location,
    fun x _ hz => _root_.GD.N0106.N0428.N0765.N1523.d021312 x hz, _root_.GD.N0106.N0428.N0765.N1523.d021313⟩

end
end GD.N0106.N0428.N0765.N1523

#print axioms _root_.GD.N0106.N0428.N0765.N1523.d021310
#print axioms _root_.GD.N0106.N0428.N0765.N1523.d021312
#print axioms _root_.GD.N0106.N0428.N0765.N1523.d021313
#print axioms _root_.GD.N0106.N0428.N0765.N1523.d021316
#print axioms _root_.GD.N0106.N0428.N0765.N1523.d021318
#print axioms _root_.GD.N0106.N0428.N0765.N1523.d021319
