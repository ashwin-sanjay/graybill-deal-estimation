import GD.Module1300
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Normed.Group.Bounded















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal NNReal Topology Interval

namespace GD.N0106.N0428.N0765.N1565
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1535 _root_.GD.N0106.N0428.N0765.N1536 _root_.GD.N0106.N0428.N0765.N1529

def d021262 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) (l : ℝ) : ℂ :=
  ((l * (1 - l)) ^ ((9 : ℝ) / 2) : ℝ) *
    ((-((21 : ℂ) / 2)) * (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z) ^ (-((21 : ℂ) / 2) - 1) *
      (Complex.exp z * (_root_.GD.N0106.N0428.N0765.N1535.d021128 q l : ℂ)))

def d021263 (n : ℕ) (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) : ℂ :=
  ∫ l in (0 : ℝ)..1, (l : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1535.d021130 q z l

def d021264 (n : ℕ) (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) : ℂ :=
  ∫ l in (0 : ℝ)..1, (l : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1565.d021262 q z l

def d021265 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) : ℂ :=
  (_root_.GD.N0106.N0428.N0765.N1565.d021264 1 q z * _root_.GD.N0106.N0428.N0765.N1535.d021131 q z -
    _root_.GD.N0106.N0428.N0765.N1535.d021132 q z * _root_.GD.N0106.N0428.N0765.N1565.d021264 0 q z) / (_root_.GD.N0106.N0428.N0765.N1535.d021131 q z) ^ 2

def d021266 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) : ℂ :=
  (0 * ((q 1 : ℂ) + Complex.exp z * (q 2 : ℂ)) -
    (q 1 : ℂ) * (Complex.exp z * (q 2 : ℂ))) /
    ((q 1 : ℂ) + Complex.exp z * (q 2 : ℂ)) ^ 2

def d021267 (z : ℂ) : ℂ :=
  (0 * (1 + Complex.exp z) - 1 * Complex.exp z) / (1 + Complex.exp z) ^ 2

def d021268 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) : ℂ :=
  (2 * (_root_.GD.N0106.N0428.N0765.N1535.d021134 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z) * (_root_.GD.N0106.N0428.N0765.N1565.d021266 q z - _root_.GD.N0106.N0428.N0765.N1565.d021267 z)) -
    (2 * (_root_.GD.N0106.N0428.N0765.N1535.d021133 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z) * (_root_.GD.N0106.N0428.N0765.N1565.d021265 q z - _root_.GD.N0106.N0428.N0765.N1565.d021267 z))


theorem d021269 (c : ℂ) : Measurable (fun u : ℂ => u ^ c) := by
  simp only [Complex.cpow_def]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    ((Complex.continuous_exp.measurable).comp (Complex.measurable_log.mul_const c))

theorem d021270 : IsOpen _root_.GD.N0106.N0428.N0765.N1535.d021126 := by
  exact isOpen_Iio.preimage (continuous_abs.comp Complex.continuous_im)

theorem d021271 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    HasDerivAt (fun w => _root_.GD.N0106.N0428.N0765.N1535.d021130 q w l) (_root_.GD.N0106.N0428.N0765.N1565.d021262 q z l) z := by
  have hb : HasDerivAt (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l) (Complex.exp z * (_root_.GD.N0106.N0428.N0765.N1535.d021128 q l : ℂ)) z := by
    change HasDerivAt
      (fun w : ℂ => (_root_.GD.N0106.N0428.N0765.N1535.d021127 q l : ℂ) + Complex.exp w * (_root_.GD.N0106.N0428.N0765.N1535.d021128 q l : ℂ))
      (Complex.exp z * (_root_.GD.N0106.N0428.N0765.N1535.d021128 q l : ℂ)) z
    exact ((Complex.hasDerivAt_exp z).mul_const (_root_.GD.N0106.N0428.N0765.N1535.d021128 q l : ℂ)).const_add
      (_root_.GD.N0106.N0428.N0765.N1535.d021127 q l : ℂ)
  exact (hb.cpow_const (_root_.GD.N0106.N0428.N0765.N1535.d021146 hq hl hz)).const_mul _

theorem d021272 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) :
    ContinuousOn (fun p : ℂ × ℝ => _root_.GD.N0106.N0428.N0765.N1565.d021262 q p.1 p.2)
      (_root_.GD.N0106.N0428.N0765.N1535.d021126 ×ˢ Icc (0 : ℝ) 1) := by
  have hw : Continuous (fun p : ℂ × ℝ =>
      (((p.2 * (1 - p.2)) ^ ((9 : ℝ) / 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((Real.continuous_rpow_const (by norm_num)).comp (by fun_prop))
  have hb : Continuous (fun p : ℂ × ℝ => _root_.GD.N0106.N0428.N0765.N1535.d021129 q p.2 p.1) := by
    unfold _root_.GD.N0106.N0428.N0765.N1535.d021129 _root_.GD.N0106.N0428.N0765.N1535.d021127 _root_.GD.N0106.N0428.N0765.N1535.d021128
    fun_prop
  have hc : Continuous (fun p : ℂ × ℝ => (_root_.GD.N0106.N0428.N0765.N1535.d021128 q p.2 : ℂ)) := by
    unfold _root_.GD.N0106.N0428.N0765.N1535.d021128
    fun_prop
  have hp := hb.continuousOn.cpow_const
    (fun p (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126 ×ˢ Icc (0 : ℝ) 1) => _root_.GD.N0106.N0428.N0765.N1535.d021146 hq hp.2 hp.1)
    (b := -((21 : ℂ) / 2) - 1)
  exact hw.continuousOn.mul ((continuousOn_const.mul hp).mul
    ((Complex.continuous_exp.comp continuous_fst).continuousOn.mul hc.continuousOn))

theorem d021273 (n : ℕ) {q : _root_.GD.N0106.N0428.N0765.N1535.d021124}
    (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) :
    ContinuousOn (fun p : ℂ × ℝ => (p.2 : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1565.d021262 q p.1 p.2)
      (_root_.GD.N0106.N0428.N0765.N1535.d021126 ×ˢ Icc (0 : ℝ) 1) :=
  ((Complex.continuous_ofReal.comp continuous_snd).pow n).continuousOn.mul
    (_root_.GD.N0106.N0428.N0765.N1565.d021272 hq)


theorem d021274 (n : ℕ) {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q)
    {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    ∃ r > 0, closedBall z r ⊆ _root_.GD.N0106.N0428.N0765.N1535.d021126 ∧ ∃ C : ℝ,
      ∀ w ∈ closedBall z r, ∀ l ∈ Icc (0 : ℝ) 1,
        ‖(l : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1565.d021262 q w l‖ ≤ C := by
  obtain ⟨r, hr, hs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (_root_.GD.N0106.N0428.N0765.N1565.d021270.mem_nhds hz)
  have hc : IsCompact (closedBall z r ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall z r).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn
    ((_root_.GD.N0106.N0428.N0765.N1565.d021273 n hq).mono
      (fun p hp => ⟨hs hp.1, hp.2⟩))
  exact ⟨r, hr, hs, C, fun w hw l hl => hC (w, l) ⟨hw, hl⟩⟩

theorem d021275 (n : ℕ) {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q)
    {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : HasDerivAt (_root_.GD.N0106.N0428.N0765.N1565.d021263 n q) (_root_.GD.N0106.N0428.N0765.N1565.d021264 n q z) z := by
  obtain ⟨r, hr, hs, C, hC⟩ := _root_.GD.N0106.N0428.N0765.N1565.d021274 n hq hz
  have hcont (w : ℂ) (hw : w ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
      ContinuousOn (fun l : ℝ => (l : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1535.d021130 q w l) (Icc 0 1) :=
    (Complex.continuous_ofReal.pow n).continuousOn.mul (_root_.GD.N0106.N0428.N0765.N1535.d021150 hq hw)
  have hcontD : ContinuousOn (fun l : ℝ => (l : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1565.d021262 q z l)
      (Icc 0 1) :=
    (_root_.GD.N0106.N0428.N0765.N1565.d021273 n hq).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun l hl => ⟨hz, hl⟩)
  have hm : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (fun l : ℝ => (l : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1535.d021130 q w l)
        (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [_root_.GD.N0106.N0428.N0765.N1565.d021270.mem_nhds hz] with w hw
    simpa only [uIoc_of_le zero_le_one] using
      ((hcont w hw).intervalIntegrable_of_Icc zero_le_one).1.aestronglyMeasurable
  have hmD : AEStronglyMeasurable
      (fun l : ℝ => (l : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1565.d021262 q z l)
      (volume.restrict (Ι (0 : ℝ) 1)) := by
    simpa only [uIoc_of_le zero_le_one] using
      (hcontD.intervalIntegrable_of_Icc zero_le_one).1.aestronglyMeasurable
  have hb : ∀ᵐ l : ℝ ∂volume, l ∈ Ι (0 : ℝ) 1 →
      ∀ w ∈ closedBall z r, ‖(l : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1565.d021262 q w l‖ ≤ C := by
    apply ae_of_all
    intro l hl w hw
    have hl' : l ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le zero_le_one] using hl
    exact hC w hw l ⟨hl'.1.le, hl'.2⟩
  have hd : ∀ᵐ l : ℝ ∂volume, l ∈ Ι (0 : ℝ) 1 → ∀ w ∈ closedBall z r,
      HasDerivAt (fun w => (l : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1535.d021130 q w l)
        ((l : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1565.d021262 q w l) w := by
    apply ae_of_all
    intro l hl w hw
    have hl' : l ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hl
    exact (_root_.GD.N0106.N0428.N0765.N1565.d021271 hq ⟨hl'.1.le, hl'.2⟩ (hs hw)).const_mul _
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (closedBall_mem_nhds z hr) hm ((hcont z hz).intervalIntegrable_of_Icc zero_le_one)
    hmD hb (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume 0 1) hd).2

theorem d021276 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : HasDerivAt (_root_.GD.N0106.N0428.N0765.N1535.d021131 q) (_root_.GD.N0106.N0428.N0765.N1565.d021264 0 q z) z := by
  have hm : _root_.GD.N0106.N0428.N0765.N1565.d021263 0 q = _root_.GD.N0106.N0428.N0765.N1535.d021131 q := by
    funext w
    simp only [_root_.GD.N0106.N0428.N0765.N1565.d021263, _root_.GD.N0106.N0428.N0765.N1535.d021131, pow_zero, one_mul]
  rw [← hm]
  exact _root_.GD.N0106.N0428.N0765.N1565.d021275 0 hq hz

theorem d021277 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : HasDerivAt (_root_.GD.N0106.N0428.N0765.N1535.d021132 q) (_root_.GD.N0106.N0428.N0765.N1565.d021264 1 q z) z := by
  have hm : _root_.GD.N0106.N0428.N0765.N1565.d021263 1 q = _root_.GD.N0106.N0428.N0765.N1535.d021132 q := by
    funext w
    simp only [_root_.GD.N0106.N0428.N0765.N1565.d021263, _root_.GD.N0106.N0428.N0765.N1535.d021132, pow_one]
  rw [← hm]
  exact _root_.GD.N0106.N0428.N0765.N1565.d021275 1 hq hz

theorem d021278 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : HasDerivAt (_root_.GD.N0106.N0428.N0765.N1535.d021133 q) (_root_.GD.N0106.N0428.N0765.N1565.d021265 q z) z :=
  (_root_.GD.N0106.N0428.N0765.N1565.d021277 hq hz).div (_root_.GD.N0106.N0428.N0765.N1565.d021276 hq hz)
    (_root_.GD.N0106.N0428.N0765.N1536.d021183 hq hz)

theorem d021279 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) :
    DifferentiableOn ℂ (_root_.GD.N0106.N0428.N0765.N1535.d021133 q) _root_.GD.N0106.N0428.N0765.N1535.d021126 :=
  fun _ hz => (_root_.GD.N0106.N0428.N0765.N1565.d021278 hq hz).differentiableAt.differentiableWithinAt

theorem d021280 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : 0 < ((q 1 : ℂ) + Complex.exp z * (q 2 : ℂ)).re := by
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.exp_re]
  positivity [_root_.GD.N0106.N0428.N0765.N1535.d021140 hz, hq.2.1, hq.2.2]

theorem d021281 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : (q 1 : ℂ) + Complex.exp z * (q 2 : ℂ) ≠ 0 := by
  intro h
  have hp := _root_.GD.N0106.N0428.N0765.N1565.d021280 hq hz
  rw [h, Complex.zero_re] at hp
  exact lt_irrefl _ hp

theorem d021282 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    0 < (1 + Complex.exp z).re := by
  simp only [Complex.add_re, Complex.one_re, Complex.exp_re]
  positivity [_root_.GD.N0106.N0428.N0765.N1535.d021140 hz]

theorem d021283 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    1 + Complex.exp z ≠ 0 := by
  intro h
  have hp := _root_.GD.N0106.N0428.N0765.N1565.d021282 hz
  rw [h, Complex.zero_re] at hp
  exact lt_irrefl _ hp

theorem d021284 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : HasDerivAt (_root_.GD.N0106.N0428.N0765.N1535.d021134 q) (_root_.GD.N0106.N0428.N0765.N1565.d021266 q z) z := by
  exact (hasDerivAt_const z (q 1 : ℂ)).div
    (((Complex.hasDerivAt_exp z).mul_const (q 2 : ℂ)).const_add (q 1 : ℂ))
    (_root_.GD.N0106.N0428.N0765.N1565.d021281 hq hz)

theorem d021285 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    HasDerivAt _root_.GD.N0106.N0428.N0765.N1535.d021135 (_root_.GD.N0106.N0428.N0765.N1565.d021267 z) z :=
  (hasDerivAt_const z (1 : ℂ)).div ((Complex.hasDerivAt_exp z).const_add 1)
    (_root_.GD.N0106.N0428.N0765.N1565.d021283 hz)

theorem d021286 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : HasDerivAt (_root_.GD.N0106.N0428.N0765.N1535.d021136 q) (_root_.GD.N0106.N0428.N0765.N1565.d021268 q z) z := by
  have h := (((_root_.GD.N0106.N0428.N0765.N1565.d021284 hq hz).fun_sub (_root_.GD.N0106.N0428.N0765.N1565.d021285 hz)).fun_pow 2).fun_sub
    (((_root_.GD.N0106.N0428.N0765.N1565.d021278 hq hz).fun_sub (_root_.GD.N0106.N0428.N0765.N1565.d021285 hz)).fun_pow 2)
  change HasDerivAt
    (fun w : ℂ => (_root_.GD.N0106.N0428.N0765.N1535.d021134 q w - _root_.GD.N0106.N0428.N0765.N1535.d021135 w) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1535.d021133 q w - _root_.GD.N0106.N0428.N0765.N1535.d021135 w) ^ 2)
    (_root_.GD.N0106.N0428.N0765.N1565.d021268 q z) z
  simpa only [_root_.GD.N0106.N0428.N0765.N1565.d021268, Nat.cast_ofNat, Nat.reduceSub, pow_one] using h

theorem d021287 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) :
    DifferentiableOn ℂ (_root_.GD.N0106.N0428.N0765.N1535.d021136 q) _root_.GD.N0106.N0428.N0765.N1535.d021126 :=
  fun _ hz => (_root_.GD.N0106.N0428.N0765.N1565.d021286 hq hz).differentiableAt.differentiableWithinAt



theorem d021288 (z : ℂ) :
    Measurable (fun p : _root_.GD.N0106.N0428.N0765.N1535.d021124 × ℝ => _root_.GD.N0106.N0428.N0765.N1535.d021130 p.1 z p.2) := by
  have hb : Measurable (fun p : _root_.GD.N0106.N0428.N0765.N1535.d021124 × ℝ => _root_.GD.N0106.N0428.N0765.N1535.d021129 p.1 p.2 z) := by
    unfold _root_.GD.N0106.N0428.N0765.N1535.d021129 _root_.GD.N0106.N0428.N0765.N1535.d021127 _root_.GD.N0106.N0428.N0765.N1535.d021128
    fun_prop
  have hw : Measurable (fun p : _root_.GD.N0106.N0428.N0765.N1535.d021124 × ℝ =>
      (((p.2 * (1 - p.2)) ^ ((9 : ℝ) / 2) : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.measurable.comp
      (((Real.continuous_rpow_const (by norm_num)).comp (by fun_prop)).measurable)
  exact hw.mul ((_root_.GD.N0106.N0428.N0765.N1565.d021269 (-((21 : ℂ) / 2))).comp hb)

theorem d021289 (z : ℂ) :
    Measurable (fun p : _root_.GD.N0106.N0428.N0765.N1535.d021124 × ℝ => _root_.GD.N0106.N0428.N0765.N1565.d021262 p.1 z p.2) := by
  have hb : Measurable (fun p : _root_.GD.N0106.N0428.N0765.N1535.d021124 × ℝ => _root_.GD.N0106.N0428.N0765.N1535.d021129 p.1 p.2 z) := by
    unfold _root_.GD.N0106.N0428.N0765.N1535.d021129 _root_.GD.N0106.N0428.N0765.N1535.d021127 _root_.GD.N0106.N0428.N0765.N1535.d021128
    fun_prop
  have hw : Measurable (fun p : _root_.GD.N0106.N0428.N0765.N1535.d021124 × ℝ =>
      (((p.2 * (1 - p.2)) ^ ((9 : ℝ) / 2) : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.measurable.comp
      (((Real.continuous_rpow_const (by norm_num)).comp (by fun_prop)).measurable)
  have hc : Measurable (fun p : _root_.GD.N0106.N0428.N0765.N1535.d021124 × ℝ => Complex.exp z * (_root_.GD.N0106.N0428.N0765.N1535.d021128 p.1 p.2 : ℂ)) := by
    unfold _root_.GD.N0106.N0428.N0765.N1535.d021128
    fun_prop
  exact hw.mul ((measurable_const.mul
    ((_root_.GD.N0106.N0428.N0765.N1565.d021269 (-((21 : ℂ) / 2) - 1)).comp hb)).mul hc)

theorem d021290 (n : ℕ) (z : ℂ) : Measurable (fun q => _root_.GD.N0106.N0428.N0765.N1565.d021263 n q z) := by
  have hm : Measurable (fun p : _root_.GD.N0106.N0428.N0765.N1535.d021124 × ℝ => (p.2 : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1535.d021130 p.1 z p.2) :=
    ((Complex.continuous_ofReal.measurable.comp measurable_snd).pow_const n).mul
      (_root_.GD.N0106.N0428.N0765.N1565.d021288 z)
  simpa only [_root_.GD.N0106.N0428.N0765.N1565.d021263, intervalIntegral.integral_of_le zero_le_one] using
    (hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable

theorem d021291 (n : ℕ) (z : ℂ) :
    Measurable (fun q => _root_.GD.N0106.N0428.N0765.N1565.d021264 n q z) := by
  have hm : Measurable (fun p : _root_.GD.N0106.N0428.N0765.N1535.d021124 × ℝ =>
      (p.2 : ℂ) ^ n * _root_.GD.N0106.N0428.N0765.N1565.d021262 p.1 z p.2) :=
    ((Complex.continuous_ofReal.measurable.comp measurable_snd).pow_const n).mul
      (_root_.GD.N0106.N0428.N0765.N1565.d021289 z)
  simpa only [_root_.GD.N0106.N0428.N0765.N1565.d021264, intervalIntegral.integral_of_le zero_le_one] using
    (hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable

theorem d021292 (z : ℂ) : Measurable (fun q => _root_.GD.N0106.N0428.N0765.N1535.d021131 q z) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1565.d021263, _root_.GD.N0106.N0428.N0765.N1535.d021131, pow_zero, one_mul] using _root_.GD.N0106.N0428.N0765.N1565.d021290 0 z

theorem d021293 (z : ℂ) : Measurable (fun q => _root_.GD.N0106.N0428.N0765.N1535.d021132 q z) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1565.d021263, _root_.GD.N0106.N0428.N0765.N1535.d021132, pow_one] using _root_.GD.N0106.N0428.N0765.N1565.d021290 1 z

theorem d021294 (z : ℂ) : Measurable (fun q => _root_.GD.N0106.N0428.N0765.N1535.d021133 q z) :=
  (_root_.GD.N0106.N0428.N0765.N1565.d021293 z).div (_root_.GD.N0106.N0428.N0765.N1565.d021292 z)

theorem d021295 (z : ℂ) : Measurable (fun q => _root_.GD.N0106.N0428.N0765.N1535.d021134 q z) := by
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021134
  fun_prop

theorem d021296 (z : ℂ) : Measurable (fun q => _root_.GD.N0106.N0428.N0765.N1535.d021136 q z) :=
  (((_root_.GD.N0106.N0428.N0765.N1565.d021295 z).sub measurable_const).pow_const (2 : ℕ)).sub
    (((_root_.GD.N0106.N0428.N0765.N1565.d021294 z).sub measurable_const).pow_const (2 : ℕ))

theorem d021297 (z : ℂ) : Measurable (fun q => _root_.GD.N0106.N0428.N0765.N1565.d021265 q z) :=
  (((_root_.GD.N0106.N0428.N0765.N1565.d021291 1 z).mul (_root_.GD.N0106.N0428.N0765.N1565.d021292 z)).sub
    ((_root_.GD.N0106.N0428.N0765.N1565.d021293 z).mul (_root_.GD.N0106.N0428.N0765.N1565.d021291 0 z))).div
      ((_root_.GD.N0106.N0428.N0765.N1565.d021292 z).pow_const (2 : ℕ))

theorem d021298 (z : ℂ) : Measurable (fun q => _root_.GD.N0106.N0428.N0765.N1565.d021268 q z) := by
  have hgd : Measurable (fun q => _root_.GD.N0106.N0428.N0765.N1565.d021266 q z) := by
    unfold _root_.GD.N0106.N0428.N0765.N1565.d021266
    fun_prop
  exact ((measurable_const.mul ((_root_.GD.N0106.N0428.N0765.N1565.d021295 z).sub measurable_const)).mul
    (hgd.sub measurable_const)).sub
      ((measurable_const.mul ((_root_.GD.N0106.N0428.N0765.N1565.d021294 z).sub measurable_const)).mul
        ((_root_.GD.N0106.N0428.N0765.N1565.d021297 z).sub measurable_const))


theorem d021299 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : ‖_root_.GD.N0106.N0428.N0765.N1535.d021134 q z‖ ≤ 1 := by
  have hr : q 1 ≤ ((q 1 : ℂ) + Complex.exp z * (q 2 : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.exp_re]
    have hp := mul_nonneg (mul_nonneg (Real.exp_pos z.re).le (_root_.GD.N0106.N0428.N0765.N1535.d021140 hz).le) hq.2.2.le
    linarith
  have hn := hr.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  rw [_root_.GD.N0106.N0428.N0765.N1535.d021134, norm_div, Complex.norm_of_nonneg hq.2.1.le]
  exact (div_le_one (norm_pos_iff.mpr (_root_.GD.N0106.N0428.N0765.N1565.d021281 hq hz))).mpr hn

theorem d021300 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : ‖_root_.GD.N0106.N0428.N0765.N1535.d021135 z‖ ≤ 1 := by
  have hr : 1 ≤ (1 + Complex.exp z).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.exp_re]
    have hp := mul_nonneg (Real.exp_pos z.re).le (_root_.GD.N0106.N0428.N0765.N1535.d021140 hz).le
    linarith
  have hn := hr.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  rw [_root_.GD.N0106.N0428.N0765.N1535.d021135, norm_div, norm_one]
  exact (div_le_one (norm_pos_iff.mpr (_root_.GD.N0106.N0428.N0765.N1565.d021283 hz))).mpr hn

def d021301 (t : ℝ) : ℝ := 4 + (1 / Real.cos ((21 : ℝ) / 4 * t) + 1) ^ 2

theorem d021302 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    {t : ℝ} (ht : t < 2 * Real.pi / 21) (hz : |z.im| ≤ t) :
    ‖_root_.GD.N0106.N0428.N0765.N1535.d021136 q z‖ ≤ _root_.GD.N0106.N0428.N0765.N1565.d021301 t := by
  have hz' : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126 := lt_of_le_of_lt hz ht
  have ht0 : 0 ≤ t := (abs_nonneg z.im).trans hz
  have hct : 0 < Real.cos ((21 : ℝ) / 4 * t) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos]
  have hcos : Real.cos ((21 : ℝ) / 4 * t) ≤ Real.cos ((21 : ℝ) / 4 * |z.im|) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos]) (by nlinarith)
  have hh : ‖_root_.GD.N0106.N0428.N0765.N1535.d021133 q z‖ ≤ 1 / Real.cos ((21 : ℝ) / 4 * t) :=
    (_root_.GD.N0106.N0428.N0765.N1536.d021185 hq hz').trans (one_div_le_one_div_of_le hct hcos)
  have hg : ‖_root_.GD.N0106.N0428.N0765.N1535.d021134 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [_root_.GD.N0106.N0428.N0765.N1565.d021299 hq hz', _root_.GD.N0106.N0428.N0765.N1565.d021300 hz'])
  have hho : ‖_root_.GD.N0106.N0428.N0765.N1535.d021133 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z‖ ≤ 1 / Real.cos ((21 : ℝ) / 4 * t) + 1 :=
    (norm_sub_le _ _).trans (add_le_add hh (_root_.GD.N0106.N0428.N0765.N1565.d021300 hz'))
  calc
    ‖_root_.GD.N0106.N0428.N0765.N1535.d021136 q z‖ ≤ ‖(_root_.GD.N0106.N0428.N0765.N1535.d021134 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z) ^ 2‖ + ‖(_root_.GD.N0106.N0428.N0765.N1535.d021133 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z) ^ 2‖ := norm_sub_le _ _
    _ = ‖_root_.GD.N0106.N0428.N0765.N1535.d021134 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z‖ ^ 2 + ‖_root_.GD.N0106.N0428.N0765.N1535.d021133 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z‖ ^ 2 := by rw [norm_pow, norm_pow]
    _ ≤ _root_.GD.N0106.N0428.N0765.N1565.d021301 t := by
      unfold _root_.GD.N0106.N0428.N0765.N1565.d021301
      nlinarith [norm_nonneg (_root_.GD.N0106.N0428.N0765.N1535.d021134 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z), norm_nonneg (_root_.GD.N0106.N0428.N0765.N1535.d021133 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z)]

theorem d021303 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    Integrable (fun q => _root_.GD.N0106.N0428.N0765.N1535.d021136 q z) _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  letI : IsProbabilityMeasure _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    _root_.GD.N0235.d004251 (by norm_num) (by norm_num) (by norm_num)
  apply (integrable_const (_root_.GD.N0106.N0428.N0765.N1565.d021301 |z.im|)).mono' (_root_.GD.N0106.N0428.N0765.N1565.d021296 z).aestronglyMeasurable
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1627.d021090] with q hq
  exact _root_.GD.N0106.N0428.N0765.N1565.d021302 hq hz le_rfl

theorem d021304 {z w : ℂ} {r : ℝ} (hw : w ∈ closedBall z r) :
    |w.im| ≤ |z.im| + r := by
  have hd : ‖w - z‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hw
  calc
    |w.im| = |(w - z).im + z.im| := by simp
    _ ≤ |(w - z).im| + |z.im| := abs_add_le _ _
    _ ≤ ‖w - z‖ + |z.im| := by linarith [Complex.abs_im_le_norm (w - z)]
    _ ≤ |z.im| + r := by linarith


theorem d021305 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    ∃ r > 0, closedBall z r ⊆ _root_.GD.N0106.N0428.N0765.N1535.d021126 ∧ ∃ C : ℝ,
      ∀ q, _root_.GD.N0106.N0428.N0765.N1535.d021125 q → ∀ w ∈ closedBall z r, ‖_root_.GD.N0106.N0428.N0765.N1565.d021268 q w‖ ≤ C := by
  let r : ℝ := (2 * Real.pi / 21 - |z.im|) / 4
  let t : ℝ := |z.im| + 2 * r
  have hr : 0 < r := by change |z.im| < 2 * Real.pi / 21 at hz; dsimp [r]; linarith
  have ht : t < 2 * Real.pi / 21 := by
    change |z.im| < 2 * Real.pi / 21 at hz
    dsimp [t, r]
    linarith
  have hs : closedBall z r ⊆ _root_.GD.N0106.N0428.N0765.N1535.d021126 := by
    intro w hw
    have hw' := _root_.GD.N0106.N0428.N0765.N1565.d021304 hw
    change |w.im| < 2 * Real.pi / 21
    dsimp [t] at ht
    linarith
  refine ⟨r, hr, hs, _root_.GD.N0106.N0428.N0765.N1565.d021301 t / r, ?_⟩
  intro q hq w hw
  have hsub : closedBall w r ⊆ _root_.GD.N0106.N0428.N0765.N1535.d021126 := by
    intro v hv
    have hv' := _root_.GD.N0106.N0428.N0765.N1565.d021304 hv
    have hw' := _root_.GD.N0106.N0428.N0765.N1565.d021304 hw
    change |v.im| < 2 * Real.pi / 21
    dsimp [t] at ht
    linarith
  have hb : ∀ v ∈ sphere w r, ‖_root_.GD.N0106.N0428.N0765.N1535.d021136 q v‖ ≤ _root_.GD.N0106.N0428.N0765.N1565.d021301 t := by
    intro v hv
    apply _root_.GD.N0106.N0428.N0765.N1565.d021302 hq ht
    have hv' := _root_.GD.N0106.N0428.N0765.N1565.d021304 (sphere_subset_closedBall hv)
    have hw' := _root_.GD.N0106.N0428.N0765.N1565.d021304 hw
    dsimp [t]
    linarith
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    ((_root_.GD.N0106.N0428.N0765.N1565.d021287 hq).diffContOnCl_ball hsub) hb
  rw [(_root_.GD.N0106.N0428.N0765.N1565.d021286 hq (hs hw)).deriv] at hc
  exact hc


theorem d021306 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) :
    HasDerivAt _root_.GD.N0106.N0428.N0765.N1535.d021137 (∫ q, _root_.GD.N0106.N0428.N0765.N1565.d021268 q z ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) z := by
  letI : IsProbabilityMeasure _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    _root_.GD.N0235.d004251 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨r, hr, hs, C, hC⟩ := _root_.GD.N0106.N0428.N0765.N1565.d021305 hz
  have hm : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (fun q => _root_.GD.N0106.N0428.N0765.N1535.d021136 q w) _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    Eventually.of_forall fun w => (_root_.GD.N0106.N0428.N0765.N1565.d021296 w).aestronglyMeasurable
  have hb : ∀ᵐ q ∂_root_.GD.N0106.N0428.N0765.N1529.d020798, ∀ w ∈ closedBall z r, ‖_root_.GD.N0106.N0428.N0765.N1565.d021268 q w‖ ≤ C :=
    _root_.GD.N0106.N0428.N0765.N1627.d021090.mono fun q hq => hC q hq
  have hd : ∀ᵐ q ∂_root_.GD.N0106.N0428.N0765.N1529.d020798, ∀ w ∈ closedBall z r,
      HasDerivAt (_root_.GD.N0106.N0428.N0765.N1535.d021136 q) (_root_.GD.N0106.N0428.N0765.N1565.d021268 q w) w :=
    _root_.GD.N0106.N0428.N0765.N1627.d021090.mono fun _ hq _ hw => _root_.GD.N0106.N0428.N0765.N1565.d021286 hq (hs hw)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (closedBall_mem_nhds z hr) hm (_root_.GD.N0106.N0428.N0765.N1565.d021303 hz)
    (_root_.GD.N0106.N0428.N0765.N1565.d021298 z).aestronglyMeasurable hb (integrable_const C) hd).2

theorem d021307 : DifferentiableOn ℂ _root_.GD.N0106.N0428.N0765.N1535.d021137 _root_.GD.N0106.N0428.N0765.N1535.d021126 :=
  fun _ hz => (_root_.GD.N0106.N0428.N0765.N1565.d021306 hz).differentiableAt.differentiableWithinAt

end
end GD.N0106.N0428.N0765.N1565

#print axioms _root_.GD.N0106.N0428.N0765.N1565.d021269
#print axioms _root_.GD.N0106.N0428.N0765.N1565.d021274
#print axioms _root_.GD.N0106.N0428.N0765.N1565.d021276
#print axioms _root_.GD.N0106.N0428.N0765.N1565.d021277
#print axioms _root_.GD.N0106.N0428.N0765.N1565.d021279
#print axioms _root_.GD.N0106.N0428.N0765.N1565.d021298
#print axioms _root_.GD.N0106.N0428.N0765.N1565.d021302
#print axioms _root_.GD.N0106.N0428.N0765.N1565.d021303
#print axioms _root_.GD.N0106.N0428.N0765.N1565.d021305
#print axioms _root_.GD.N0106.N0428.N0765.N1565.d021307
