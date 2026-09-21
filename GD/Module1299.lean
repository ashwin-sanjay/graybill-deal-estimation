import GD.Module1298
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds


















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD.N0106.N0428.N0765.N1535
noncomputable section

open _root_.GD.N0106.N0428.N0765.N1611 _root_.GD.N0106.N0428.N0765.N1606 _root_.GD.N0106.N0428.N0765.N1607 _root_.GD.N0106.N0428.N0765.N1610 _root_.GD.N0106.N0428.N0765.N1529

abbrev d021124 := Fin 3 → ℝ

def d021125 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) : Prop := 0 ≤ q 0 ∧ 0 < q 1 ∧ 0 < q 2

def d021126 : Set ℂ := {z | |z.im| < 2 * Real.pi / 21}


def d021127 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (l : ℝ) : ℝ := (1 - l) * (q 1 + q 0 * l)
def d021128 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (l : ℝ) : ℝ := l * (q 2 + q 0 * (1 - l))

def d021129 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (l : ℝ) (z : ℂ) : ℂ :=
  (_root_.GD.N0106.N0428.N0765.N1535.d021127 q l : ℂ) + Complex.exp z * (_root_.GD.N0106.N0428.N0765.N1535.d021128 q l : ℂ)

def d021130 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) (l : ℝ) : ℂ :=
  ((l * (1 - l)) ^ ((9 : ℝ) / 2) : ℝ) *
    (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z) ^ (-((21 : ℂ) / 2))

def d021131 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) : ℂ := ∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1535.d021130 q z l
def d021132 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) : ℂ := ∫ l in (0 : ℝ)..1, (l : ℂ) * _root_.GD.N0106.N0428.N0765.N1535.d021130 q z l
def d021133 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) : ℂ := _root_.GD.N0106.N0428.N0765.N1535.d021132 q z / _root_.GD.N0106.N0428.N0765.N1535.d021131 q z
def d021134 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) : ℂ := (q 1 : ℂ) / ((q 1 : ℂ) + Complex.exp z * (q 2 : ℂ))
def d021135 (z : ℂ) : ℂ := 1 / (1 + Complex.exp z)
def d021136 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (z : ℂ) : ℂ := (_root_.GD.N0106.N0428.N0765.N1535.d021134 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z) ^ 2 - (_root_.GD.N0106.N0428.N0765.N1535.d021133 q z - _root_.GD.N0106.N0428.N0765.N1535.d021135 z) ^ 2
def d021137 (z : ℂ) : ℂ := ∫ q, _root_.GD.N0106.N0428.N0765.N1535.d021136 q z ∂_root_.GD.N0106.N0428.N0765.N1529.d020798

theorem d021138 (x : ℝ) : (x : ℂ) ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126 := by
  simp only [_root_.GD.N0106.N0428.N0765.N1535.d021126, Set.mem_setOf_eq, Complex.ofReal_im, abs_zero]
  positivity

theorem d021139 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : |z.im| < Real.pi / 2 := by
  have h := hz
  change |z.im| < 2 * Real.pi / 21 at h
  linarith [Real.pi_pos]

theorem d021140 {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : 0 < Real.cos z.im :=
  Real.cos_pos_of_mem_Ioo (abs_lt.mp (_root_.GD.N0106.N0428.N0765.N1535.d021139 hz))

theorem d021141 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1535.d021127 q l := by
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021127
  exact mul_nonneg (sub_nonneg.mpr hl.2) (add_nonneg hq.2.1.le (mul_nonneg hq.1 hl.1))

theorem d021142 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1535.d021128 q l := by
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021128
  exact mul_nonneg hl.1 (add_nonneg hq.2.2.le (mul_nonneg hq.1 (sub_nonneg.mpr hl.2)))

theorem d021143 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) : 0 < _root_.GD.N0106.N0428.N0765.N1535.d021127 q l + _root_.GD.N0106.N0428.N0765.N1535.d021128 q l := by
  rcases lt_or_eq_of_le hl.2 with hl1 | hl1
  · have ha : 0 < _root_.GD.N0106.N0428.N0765.N1535.d021127 q l := by
      unfold _root_.GD.N0106.N0428.N0765.N1535.d021127
      exact mul_pos (sub_pos.mpr hl1) (add_pos_of_pos_of_nonneg hq.2.1 (mul_nonneg hq.1 hl.1))
    exact add_pos_of_pos_of_nonneg ha (_root_.GD.N0106.N0428.N0765.N1535.d021142 hq hl)
  · subst l
    simpa [_root_.GD.N0106.N0428.N0765.N1535.d021127, _root_.GD.N0106.N0428.N0765.N1535.d021128] using hq.2.2

theorem d021144 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (l : ℝ) (z : ℂ) :
    (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).re = _root_.GD.N0106.N0428.N0765.N1535.d021127 q l + Real.exp z.re * Real.cos z.im * _root_.GD.N0106.N0428.N0765.N1535.d021128 q l := by
  simp [_root_.GD.N0106.N0428.N0765.N1535.d021129, Complex.mul_re, Complex.exp_re]


theorem d021145 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : 0 < (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l z).re := by
  rw [_root_.GD.N0106.N0428.N0765.N1535.d021144]
  have ha := _root_.GD.N0106.N0428.N0765.N1535.d021141 hq hl
  have hb := _root_.GD.N0106.N0428.N0765.N1535.d021142 hq hl
  have hab := _root_.GD.N0106.N0428.N0765.N1535.d021143 hq hl
  have hc : 0 < Real.exp z.re * Real.cos z.im := mul_pos (Real.exp_pos _) (_root_.GD.N0106.N0428.N0765.N1535.d021140 hz)
  by_cases hbpos : 0 < _root_.GD.N0106.N0428.N0765.N1535.d021128 q l
  · exact add_pos_of_nonneg_of_pos ha (mul_pos hc hbpos)
  · have hbzero : _root_.GD.N0106.N0428.N0765.N1535.d021128 q l = 0 := by linarith
    simpa [hbzero] using hab

theorem d021146 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : _root_.GD.N0106.N0428.N0765.N1535.d021129 q l z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (_root_.GD.N0106.N0428.N0765.N1535.d021145 hq hl hz))

theorem d021147 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : _root_.GD.N0106.N0428.N0765.N1535.d021129 q l z ≠ 0 :=
  Complex.slitPlane_ne_zero (_root_.GD.N0106.N0428.N0765.N1535.d021146 hq hl hz)

theorem d021148 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (l : ℝ) : Differentiable ℂ (_root_.GD.N0106.N0428.N0765.N1535.d021129 q l) := by
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021129
  fun_prop

theorem d021149 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) : DifferentiableOn ℂ (fun z => _root_.GD.N0106.N0428.N0765.N1535.d021130 q z l) _root_.GD.N0106.N0428.N0765.N1535.d021126 := by
  intro z hz
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021130
  exact (differentiableWithinAt_const _).mul
    (((_root_.GD.N0106.N0428.N0765.N1535.d021148 q l).differentiableAt.differentiableWithinAt).cpow_const
      (_root_.GD.N0106.N0428.N0765.N1535.d021146 hq hl hz))

theorem d021150 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1535.d021130 q z) (Icc (0 : ℝ) 1) := by
  have hr : Continuous (fun l : ℝ => (l * (1 - l)) ^ ((9 : ℝ) / 2)) :=
    (Real.continuous_rpow_const (by norm_num)).comp (by fun_prop)
  have hb : Continuous (fun l : ℝ => _root_.GD.N0106.N0428.N0765.N1535.d021129 q l z) := by
    unfold _root_.GD.N0106.N0428.N0765.N1535.d021129 _root_.GD.N0106.N0428.N0765.N1535.d021127 _root_.GD.N0106.N0428.N0765.N1535.d021128
    fun_prop
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021130
  exact (Complex.continuous_ofReal.comp hr).continuousOn.mul
    (hb.continuousOn.cpow_const fun l hl => _root_.GD.N0106.N0428.N0765.N1535.d021146 hq hl hz)

theorem d021151 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : IntervalIntegrable (_root_.GD.N0106.N0428.N0765.N1535.d021130 q z) volume 0 1 :=
  (_root_.GD.N0106.N0428.N0765.N1535.d021150 hq hz).intervalIntegrable_of_Icc zero_le_one

theorem d021152 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {z : ℂ}
    (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126) : IntervalIntegrable (fun l => (l : ℂ) * _root_.GD.N0106.N0428.N0765.N1535.d021130 q z l) volume 0 1 :=
  (Complex.continuous_ofReal.continuousOn.mul (_root_.GD.N0106.N0428.N0765.N1535.d021150 hq hz)).intervalIntegrable_of_Icc
    zero_le_one

theorem d021153 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (l x : ℝ) : _root_.GD.N0106.N0428.N0765.N1535.d021129 q l (x : ℂ) =
    (_root_.GD.N0106.N0428.N0765.N1534.d005328 (Real.exp x) (q 0) (q 1) (q 2) l : ℝ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1535.d021129, ← Complex.ofReal_exp]
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021127 _root_.GD.N0106.N0428.N0765.N1535.d021128 _root_.GD.N0106.N0428.N0765.N1534.d005328
  push_cast
  ring

theorem d021154 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    0 < _root_.GD.N0106.N0428.N0765.N1534.d005328 (Real.exp x) (q 0) (q 1) (q 2) l := by
  have h := _root_.GD.N0106.N0428.N0765.N1535.d021145 hq hl (_root_.GD.N0106.N0428.N0765.N1535.d021138 x)
  rw [_root_.GD.N0106.N0428.N0765.N1535.d021153, Complex.ofReal_re] at h
  exact h

theorem d021155 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) {l : ℝ}
    (hl : l ∈ Icc (0 : ℝ) 1) (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1535.d021130 q (x : ℂ) l =
      (_root_.GD.N0106.N0428.N0765.N1534.d005329 (Real.exp x) (q 0) (q 1) (q 2) l : ℝ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1535.d021130, _root_.GD.N0106.N0428.N0765.N1535.d021153]
  have hp := Complex.ofReal_cpow (_root_.GD.N0106.N0428.N0765.N1535.d021154 hq hl x).le (-((21 : ℝ) / 2))
  push_cast at hp
  rw [← hp]
  simp only [_root_.GD.N0106.N0428.N0765.N1534.d005329, Complex.ofReal_mul]

theorem d021156 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1535.d021131 q (x : ℂ) =
      ((∫ l in (0 : ℝ)..1,
        _root_.GD.N0106.N0428.N0765.N1534.d005329 (Real.exp x) (q 0) (q 1) (q 2) l) : ℝ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021131
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro l hl
  rw [Set.uIcc_of_le zero_le_one] at hl
  exact _root_.GD.N0106.N0428.N0765.N1535.d021155 hq hl x

theorem d021157 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1535.d021132 q (x : ℂ) =
      ((∫ l in (0 : ℝ)..1, l *
        _root_.GD.N0106.N0428.N0765.N1534.d005329 (Real.exp x) (q 0) (q 1) (q 2) l) : ℝ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021132
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro l hl
  rw [Set.uIcc_of_le zero_le_one] at hl
  dsimp only
  rw [_root_.GD.N0106.N0428.N0765.N1535.d021155 hq hl x, Complex.ofReal_mul]


theorem d021158 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1535.d021133 q (x : ℂ) = (_root_.GD.N0106.N0428.N0765.N1529.d020799 (Real.exp x) q : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1535.d021133, _root_.GD.N0106.N0428.N0765.N1535.d021157 hq, _root_.GD.N0106.N0428.N0765.N1535.d021156 hq]
  simp only [_root_.GD.N0106.N0428.N0765.N1529.d020799, _root_.GD.N0106.N0428.N0765.N1534.d005330, Complex.ofReal_div]

theorem d021159 (q : _root_.GD.N0106.N0428.N0765.N1535.d021124) (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1535.d021134 q (x : ℂ) = (_root_.GD.N0106.N0428.N0765.N1529.d020800 (Real.exp x) q : ℂ) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1535.d021134, _root_.GD.N0106.N0428.N0765.N1529.d020800, ← Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_add, Complex.ofReal_mul]

theorem d021160 (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1535.d021135 (x : ℂ) = (_root_.GD.N0106.N0428.N0765.N1607.d012678 (Real.exp x) : ℂ) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1535.d021135, _root_.GD.N0106.N0428.N0765.N1607.d012678, ← Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_add]

theorem d021161 {q : _root_.GD.N0106.N0428.N0765.N1535.d021124} (hq : _root_.GD.N0106.N0428.N0765.N1535.d021125 q) (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1535.d021136 q (x : ℂ) = (_root_.GD.N0106.N0428.N0765.N1529.d020802 (Real.exp x) q : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1535.d021136, _root_.GD.N0106.N0428.N0765.N1535.d021159, _root_.GD.N0106.N0428.N0765.N1535.d021160, _root_.GD.N0106.N0428.N0765.N1535.d021158 hq]
  simp only [_root_.GD.N0106.N0428.N0765.N1529.d020802, Complex.ofReal_sub, Complex.ofReal_pow]

theorem d021162 (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1535.d021137 (x : ℂ) =
    ((∫ q, _root_.GD.N0106.N0428.N0765.N1529.d020802 (Real.exp x) q ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) : ℝ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1535.d021137
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1627.d021090] with q hq
  exact _root_.GD.N0106.N0428.N0765.N1535.d021161 hq x


theorem d021163 (location x : ℝ) : _root_.GD.N0106.N0428.N0765.N1535.d021137 (x : ℂ) =
    ((11 * _root_.GD.N0106.N0428.N0765.N1627.d021120 location (Real.exp x) / (1 + Real.exp x)) : ℝ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1535.d021162]
  congr 1
  unfold _root_.GD.N0106.N0428.N0765.N1627.d021120
  rw [_root_.GD.N0106.N0428.N0765.N1529.d020832 location (Real.exp x) (Real.exp_pos x)]
  field_simp [show (1 + Real.exp x : ℝ) ≠ 0 by positivity]
  <;> ring


theorem d021164 (x : ℝ) {z : ℂ} (hz : ‖z - (x : ℂ)‖ ≤ (1 : ℝ) / 7) : z ∈ _root_.GD.N0106.N0428.N0765.N1535.d021126 := by
  have him : |z.im| ≤ (1 : ℝ) / 7 := by
    have h := (Complex.abs_im_le_norm (z - (x : ℂ))).trans hz
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using h
  change |z.im| < 2 * Real.pi / 21
  have hp := Real.pi_gt_three
  linarith


theorem d021165 {y : ℝ} (hy : |y| ≤ (1 : ℝ) / 7) :
    1 / Real.cos (|y| / 2) < (101 : ℝ) / 100 ∧
      1 / Real.cos (((21 : ℝ) / 2) * |y| / 2) < (3 : ℝ) / 2 := by
  have ha := abs_nonneg y
  have hs : |y| ^ 2 ≤ ((1 : ℝ) / 7) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy) (by positivity : 0 ≤ (1 : ℝ) / 7 + |y|)]
  have hc := Real.one_sub_sq_div_two_le_cos (x := |y| / 2)
  have hc' := Real.one_sub_sq_div_two_le_cos (x := ((21 : ℝ) / 2) * |y| / 2)
  constructor
  · have hp : 0 < Real.cos (|y| / 2) := by nlinarith
    apply (div_lt_iff₀ hp).2
    nlinarith
  · have hp : 0 < Real.cos (((21 : ℝ) / 2) * |y| / 2) := by nlinarith
    apply (div_lt_iff₀ hp).2
    nlinarith

theorem d021166 :
    4 * ((101 : ℝ) / 100) ^ 2 + ((3 : ℝ) / 2 + 101 / 100) ^ 2 < 11 := by
  norm_num

end
end GD.N0106.N0428.N0765.N1535

#print axioms _root_.GD.N0106.N0428.N0765.N1535.d021145
#print axioms _root_.GD.N0106.N0428.N0765.N1535.d021146
#print axioms _root_.GD.N0106.N0428.N0765.N1535.d021149
#print axioms _root_.GD.N0106.N0428.N0765.N1535.d021151
#print axioms _root_.GD.N0106.N0428.N0765.N1535.d021152
#print axioms _root_.GD.N0106.N0428.N0765.N1535.d021158
#print axioms _root_.GD.N0106.N0428.N0765.N1535.d021163
#print axioms _root_.GD.N0106.N0428.N0765.N1535.d021164
#print axioms _root_.GD.N0106.N0428.N0765.N1535.d021165
#print axioms _root_.GD.N0106.N0428.N0765.N1535.d021166
