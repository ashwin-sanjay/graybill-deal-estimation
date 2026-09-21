import GD.Module0986
import GD.Module1171
import GD.Module1030
import GD.Module1034
import GD.Module1172
import GD.Module0965
import GD.Module1163
import GD.Module0093
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic









































open Filter MeasureTheory Set Topology
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1454

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0691
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1288
open _root_.GD.N0232.N0720.N1369
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1449
open _root_.GD.N0232.N0720.N1047

variable (m n : ℕ)




def d018901 (a : ℝ) : _root_.GD.N0232.N0719.N0946.d009229 := ⟨0, Real.log a⟩

theorem d018902 (a : ℝ) : (_root_.GD.N0232.N0720.N1454.d018901 a).shift = 0 := rfl

theorem d018903 (a : ℝ) : (_root_.GD.N0232.N0720.N1454.d018901 a).logScale = Real.log a := rfl

theorem d018904 {a : ℝ} (ha : 0 < a) : (_root_.GD.N0232.N0720.N1454.d018901 a).d009239 = a := by
  show Real.exp (_root_.GD.N0232.N0720.N1454.d018901 a).logScale = a
  rw [_root_.GD.N0232.N0720.N1454.d018903, Real.exp_log ha]

theorem d018905 : _root_.GD.N0232.N0720.N1454.d018901 1 = 1 := by
  show (⟨0, Real.log 1⟩ : _root_.GD.N0232.N0719.N0946.d009229) = ⟨0, 0⟩
  rw [Real.log_one]

theorem d018906 {a : ℝ} (ha : 0 < a) :
    (_root_.GD.N0232.N0720.N1454.d018901 a)⁻¹.d009239 = a⁻¹ := by
  show Real.exp (_root_.GD.N0232.N0720.N1454.d018901 a)⁻¹.logScale = a⁻¹
  rw [_root_.GD.N0232.N0719.N0946.d009229.d009238, _root_.GD.N0232.N0720.N1454.d018903, Real.exp_neg, Real.exp_log ha]

theorem d018907 (a : ℝ) : (_root_.GD.N0232.N0720.N1454.d018901 a)⁻¹.shift = 0 := by
  rw [_root_.GD.N0232.N0719.N0946.d009229.d009237, _root_.GD.N0232.N0720.N1454.d018902, mul_zero, neg_zero]


def d018908 (a : ℝ) (ha : 0 < a) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := 0
  scale₁ := a⁻¹
  scale₂ := a⁻¹
  scale₁_pos := inv_pos.2 ha
  scale₂_pos := inv_pos.2 ha

theorem d018909 (a : ℝ) (ha : 0 < a) :
    (_root_.GD.N0232.N0720.N1454.d018908 a ha).location = 0 := rfl

theorem d018910 {a : ℝ} (ha : 0 < a) :
    _root_.GD.N0232.N0720.N1215.d014272 (_root_.GD.N0232.N0720.N1454.d018901 a)⁻¹ _root_.GD.N0232.N0720.N1080.d014169 = _root_.GD.N0232.N0720.N1454.d018908 a ha := by
  apply _root_.GD.N0232.N0720.N1215.d014277
  · rw [_root_.GD.N0232.N0720.N1215.d014273, _root_.GD.N0232.N0720.N1454.d018907]
    show 0 + (_root_.GD.N0232.N0720.N1454.d018901 a)⁻¹.d009239 * 0 = 0
    ring
  · rw [_root_.GD.N0232.N0720.N1215.d014274, _root_.GD.N0232.N0720.N1454.d018906 ha]
    show a⁻¹ * 1 = a⁻¹
    ring
  · rw [_root_.GD.N0232.N0720.N1215.d014275, _root_.GD.N0232.N0720.N1454.d018906 ha]
    show a⁻¹ * 1 = a⁻¹
    ring



theorem d018911 (a x : ℝ) :
    x ^ 2 / 2 - (x - 0) ^ 2 / (2 * (a⁻¹) ^ 2) = (1 - a ^ 2) / 2 * x ^ 2 := by
  rw [sub_zero, inv_pow, div_eq_mul_inv (x ^ 2) (2 * (a ^ 2)⁻¹), mul_inv, inv_inv]
  ring

theorem d018912 {a : ℝ} (ha : 0 < a) (x : ℝ) :
    _root_.GD.N0232.N0719.N0932.d009204 0 a⁻¹ x = a * Real.exp ((1 - a ^ 2) / 2 * x ^ 2) := by
  rw [_root_.GD.N0232.N0720.N1124.d016497 0 a⁻¹ x (inv_pos.2 ha), inv_inv, _root_.GD.N0232.N0720.N1454.d018911]

theorem d018913 {a : ℝ} (ha : 0 < a) (N : ℕ)
    (x : _root_.GD.N0137.d008894 N) :
    _root_.GD.N0232.N0719.N0932.d009213 N 0 a⁻¹ x =
      a ^ N * Real.exp ((1 - a ^ 2) / 2 * ∑ i, x i ^ 2) := by
  unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  calc ∏ i : Fin N, _root_.GD.N0232.N0719.N0932.d009204 0 a⁻¹ (x i)
      = ∏ i : Fin N, (a * Real.exp ((1 - a ^ 2) / 2 * x i ^ 2)) := by
        apply Finset.prod_congr rfl
        intro i _
        exact _root_.GD.N0232.N0720.N1454.d018912 ha (x i)
    _ = (∏ _i : Fin N, a) * ∏ i : Fin N, Real.exp ((1 - a ^ 2) / 2 * x i ^ 2) :=
        Finset.prod_mul_distrib
    _ = a ^ N * Real.exp (∑ i : Fin N, (1 - a ^ 2) / 2 * x i ^ 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_sum]
    _ = a ^ N * Real.exp ((1 - a ^ 2) / 2 * ∑ i : Fin N, x i ^ 2) := by
        rw [Finset.mul_sum]



theorem d018914 {a : ℝ} (ha : 0 < a)
    (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1454.d018908 a ha) ω =
      a ^ (m + n) * Real.exp ((1 - a ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) := by
  unfold _root_.GD.N0232.N0720.N1499.d015001
  show _root_.GD.N0232.N0719.N0932.d009213 m 0 a⁻¹ ω.1 *
      _root_.GD.N0232.N0719.N0932.d009213 n 0 a⁻¹ ω.2 = _
  rw [_root_.GD.N0232.N0720.N1454.d018913 ha, _root_.GD.N0232.N0720.N1454.d018913 ha]
  unfold _root_.GD.N0232.N0720.N1449.d018831 _root_.GD.N0140.d006651
  rw [pow_add, mul_add, Real.exp_add]
  ring

theorem d018915 (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) : 0 ≤ _root_.GD.N0232.N0720.N1449.d018831 ω := by
  unfold _root_.GD.N0232.N0720.N1449.d018831 _root_.GD.N0140.d006651
  positivity





theorem d018916 (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : _root_.GD.N0232.N0720.N1159.d014637 m n d) {κ : ℝ} (hκ : κ < 1 / 2) :
    Integrable (fun ω ↦ Real.exp (κ * _root_.GD.N0232.N0720.N1449.d018831 ω) * (d ω) ^ 2) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hpos : 0 < 1 - 2 * κ := by linarith
  obtain ⟨a, ha, hasq⟩ : ∃ a : ℝ, 0 < a ∧ a ^ 2 = 1 - 2 * κ :=
    ⟨Real.sqrt (1 - 2 * κ), Real.sqrt_pos.2 hpos, Real.sq_sqrt hpos.le⟩
  have hκa : (1 - a ^ 2) / 2 = κ := by rw [hasq]; ring
  have hint := _root_.GD.N0232.N0720.N1126.d016429
    (_root_.GD.N0232.N0720.N1454.d018908 a ha) d (hd _)
  refine (hint.const_mul (a ^ (m + n))⁻¹).congr ?_
  filter_upwards with ω
  rw [_root_.GD.N0232.N0720.N1454.d018914 m n ha ω, hκa, _root_.GD.N0232.N0720.N1454.d018909,
    sub_zero, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]

theorem d018917 {κ η t : ℝ} (hη : 0 < η) :
    t * Real.exp (κ * t) ≤ η⁻¹ * Real.exp ((κ + η) * t) := by
  have h1 : η * t + 1 ≤ Real.exp (η * t) := Real.add_one_le_exp _
  have h2 : t ≤ η⁻¹ * Real.exp (η * t) := by
    calc t = η⁻¹ * (η * t) := by rw [← mul_assoc, inv_mul_cancel₀ hη.ne', one_mul]
      _ ≤ η⁻¹ * Real.exp (η * t) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_pos.2 hη).le
  calc t * Real.exp (κ * t) ≤ η⁻¹ * Real.exp (η * t) * Real.exp (κ * t) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = η⁻¹ * Real.exp ((κ + η) * t) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring



theorem d018918 (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : _root_.GD.N0232.N0720.N1159.d014637 m n d) {κ : ℝ} (hκ : κ < 1 / 2) :
    Integrable (fun ω ↦ _root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp (κ * _root_.GD.N0232.N0720.N1449.d018831 ω) * (d ω) ^ 2))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hη : 0 < (1 / 2 - κ) / 2 := by linarith
  have hκη : κ + (1 / 2 - κ) / 2 < 1 / 2 := by linarith
  have hmaj := (_root_.GD.N0232.N0720.N1454.d018916 m n d hd hκη).const_mul ((1 / 2 - κ) / 2)⁻¹
  refine hmaj.mono' ?_ ?_
  · exact (_root_.GD.N0232.N0720.N1449.d018832.aestronglyMeasurable).mul
      (((_root_.GD.N0232.N0720.N1449.d018832.const_mul κ).exp.aestronglyMeasurable).mul
        ((Lp.aestronglyMeasurable d).pow 2))
  · filter_upwards with ω
    have hS := _root_.GD.N0232.N0720.N1454.d018915 m n ω
    have hp := sq_nonneg (d ω)
    have hE := (Real.exp_pos (κ * _root_.GD.N0232.N0720.N1449.d018831 ω)).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hS (mul_nonneg hE hp))]
    have hb := _root_.GD.N0232.N0720.N1454.d018917 (κ := κ) (t := _root_.GD.N0232.N0720.N1449.d018831 ω) hη
    calc _root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp (κ * _root_.GD.N0232.N0720.N1449.d018831 ω) * (d ω) ^ 2)
        = (_root_.GD.N0232.N0720.N1449.d018831 ω * Real.exp (κ * _root_.GD.N0232.N0720.N1449.d018831 ω)) * (d ω) ^ 2 := by ring
      _ ≤ (((1 / 2 - κ) / 2)⁻¹ * Real.exp ((κ + (1 / 2 - κ) / 2) * _root_.GD.N0232.N0720.N1449.d018831 ω)) *
            (d ω) ^ 2 := mul_le_mul_of_nonneg_right hb hp
      _ = ((1 / 2 - κ) / 2)⁻¹ *
            (Real.exp ((κ + (1 / 2 - κ) / 2) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (d ω) ^ 2) := by ring





def d018919 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (a : ℝ) : ℝ :=
  a ^ (m + n + 2) *
    ∫ ω, Real.exp ((1 - a ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n

theorem d018920 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1454.d018919 m n P 1 = ‖P‖ ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1454.d018919
  simp only [one_pow, one_mul, sub_self, zero_div, zero_mul, Real.exp_zero]
  exact (_root_.GD.N0230.N0691.d001213 _ _).symm


def d018921 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (a : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1454.d018919 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) a

theorem d018922 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1454.d018921 m n s 1 = ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 :=
  _root_.GD.N0232.N0720.N1454.d018920 m n _



theorem d018923 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    {a : ℝ} (ha : 0 < a) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s (_root_.GD.N0232.N0720.N1454.d018901 a) =
      _root_.GD.N0232.N0720.N1454.d018921 m n s a - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1288.d015630, _root_.GD.N0232.N0720.N1454.d018904 ha,
    _root_.GD.N0232.N0720.N1454.d018910 ha,
    _root_.GD.N0232.N0720.N1126.d016430 (_root_.GD.N0232.N0720.N1454.d018908 a ha) _
      (_root_.GD.N0232.N0720.N1369.d018804 s _)]
  have hint : ∫ ω, _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1454.d018908 a ha) ω *
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value ω - (_root_.GD.N0232.N0720.N1454.d018908 a ha).location) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n =
      a ^ (m + n) * ∫ ω, Real.exp ((1 - a ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) *
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    rw [← integral_const_mul]
    congr 1
    funext ω
    rw [_root_.GD.N0232.N0720.N1454.d018914 m n ha ω, _root_.GD.N0232.N0720.N1454.d018909,
      sub_zero]
    ring
  rw [hint]
  unfold _root_.GD.N0232.N0720.N1454.d018921 _root_.GD.N0232.N0720.N1454.d018919
  ring



theorem d018924 (S p a : ℝ) :
    HasDerivAt (fun b : ℝ ↦ Real.exp ((1 - b ^ 2) / 2 * S) * p ^ 2)
      ((-a * S) * (Real.exp ((1 - a ^ 2) / 2 * S) * p ^ 2)) a := by
  have h0 : HasDerivAt (fun b : ℝ ↦ b ^ 2) (2 * a) a := by
    refine (hasDerivAt_pow 2 a).congr_deriv ?_
    norm_num
  have h1 : HasDerivAt (fun b : ℝ ↦ (1 - b ^ 2) / 2 * S) (-a * S) a :=
    (((h0.const_sub 1).div_const 2).mul_const S).congr_deriv (by ring)
  exact ((h1.exp).mul_const (p ^ 2)).congr_deriv (by ring)



theorem d018925 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfin : _root_.GD.N0232.N0720.N1159.d014637 m n P) :
    HasDerivAt (_root_.GD.N0232.N0720.N1454.d018919 m n P)
      ((((m + n : ℕ) : ℝ) + 2) * ‖P‖ ^ 2 -
        ∫ ω, _root_.GD.N0232.N0720.N1449.d018831 ω * (P ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) 1 := by
  have hmeasF : ∀ b : ℝ, AEStronglyMeasurable
      (fun ω ↦ Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := fun b ↦
    ((_root_.GD.N0232.N0720.N1449.d018832.const_mul ((1 - b ^ 2) / 2)).exp.aestronglyMeasurable).mul
      ((Lp.aestronglyMeasurable P).pow 2)
  have hF_meas : ∀ᶠ b in 𝓝 (1 : ℝ), AEStronglyMeasurable
      (fun ω ↦ Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    Filter.Eventually.of_forall hmeasF
  have hF_int : Integrable
      (fun ω ↦ Real.exp ((1 - (1 : ℝ) ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1454.d018916 m n P hfin (κ := (1 - (1 : ℝ) ^ 2) / 2) (by norm_num)
  have hF'_meas : AEStronglyMeasurable
      (fun ω ↦ (-(1 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) *
        (Real.exp ((1 - (1 : ℝ) ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    ((_root_.GD.N0232.N0720.N1449.d018832.const_mul (-(1 : ℝ))).aestronglyMeasurable).mul (hmeasF 1)
  have hbound_int : Integrable
      (fun ω ↦ (5 / 4 : ℝ) *
        (_root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (_root_.GD.N0232.N0720.N1454.d018918 m n P hfin (κ := 7 / 32) (by norm_num)).const_mul
      (5 / 4)
  have h_bound : ∀ᵐ ω ∂_root_.GD.N0232.N0720.N1080.d014172 m n, ∀ b ∈ Metric.ball (1 : ℝ) (1 / 4),
      ‖(-b * _root_.GD.N0232.N0720.N1449.d018831 ω) *
        (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)‖ ≤
      (5 / 4 : ℝ) *
        (_root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω b hb
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hb
    have hb1 : 3 / 4 < b := by linarith [hb.1]
    have hb2 : b < 5 / 4 := by linarith [hb.2]
    have hS := _root_.GD.N0232.N0720.N1454.d018915 m n ω
    have hp := sq_nonneg (P ω)
    have hE := (Real.exp_pos ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω)).le
    have hexp : Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) ≤
        Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) := by
      apply Real.exp_le_exp.2
      apply mul_le_mul_of_nonneg_right _ hS
      nlinarith
    have h1 : _root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) ≤
        _root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hp) hS
    have h0 : 0 ≤ _root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) :=
      mul_nonneg hS (mul_nonneg (Real.exp_pos _).le hp)
    have hmain : b * (_root_.GD.N0232.N0720.N1449.d018831 ω *
        (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) ≤
        (5 / 4 : ℝ) *
          (_root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) :=
      calc b * (_root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2))
          ≤ b * (_root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ ≤ (5 / 4 : ℝ) *
            (_root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) :=
            mul_le_mul_of_nonneg_right hb2.le h0
    have hnn : 0 ≤ b * _root_.GD.N0232.N0720.N1449.d018831 ω *
        (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) :=
      mul_nonneg (mul_nonneg (by linarith) hS) (mul_nonneg hE hp)
    have hx0 : -b * _root_.GD.N0232.N0720.N1449.d018831 ω *
        (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) ≤ 0 := by
      linarith
    rw [Real.norm_eq_abs, abs_of_nonpos hx0]
    linarith
  have h_diff : ∀ᵐ ω ∂_root_.GD.N0232.N0720.N1080.d014172 m n, ∀ b ∈ Metric.ball (1 : ℝ) (1 / 4),
      HasDerivAt (fun b : ℝ ↦ Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)
        ((-b * _root_.GD.N0232.N0720.N1449.d018831 ω) *
          (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) b :=
    Filter.Eventually.of_forall fun ω b _ ↦ _root_.GD.N0232.N0720.N1454.d018924 (_root_.GD.N0232.N0720.N1449.d018831 ω) (P ω) b
  have hderiv : HasDerivAt
      (fun b : ℝ ↦ ∫ ω, Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n)
      (∫ ω, (-(1 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) *
        (Real.exp ((1 - (1 : ℝ) ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) ∂_root_.GD.N0232.N0720.N1080.d014172 m n)
      1 :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4))
      hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  have hF1 : ∫ ω, Real.exp ((1 - (1 : ℝ) ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2
      ∂_root_.GD.N0232.N0720.N1080.d014172 m n = ‖P‖ ^ 2 := by
    rw [_root_.GD.N0230.N0691.d001213 (_root_.GD.N0232.N0720.N1080.d014172 m n) P]
    congr 1
    funext ω
    simp only [one_pow, sub_self, zero_div, zero_mul, Real.exp_zero, one_mul]
  have hF'1 : ∫ ω, (-(1 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) *
      (Real.exp ((1 - (1 : ℝ) ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) ∂_root_.GD.N0232.N0720.N1080.d014172 m n =
      -∫ ω, _root_.GD.N0232.N0720.N1449.d018831 ω * (P ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    rw [← integral_neg]
    congr 1
    funext ω
    simp only [one_pow, sub_self, zero_div, zero_mul, Real.exp_zero, one_mul]
    ring
  refine ((hasDerivAt_pow (m + n + 2) (1 : ℝ)).mul hderiv).congr_deriv ?_
  show ((m + n + 2 : ℕ) : ℝ) * (1 : ℝ) ^ (m + n + 2 - 1) *
      (∫ ω, Real.exp ((1 - (1 : ℝ) ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
    (1 : ℝ) ^ (m + n + 2) *
      (∫ ω, (-(1 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) *
        (Real.exp ((1 - (1 : ℝ) ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = _
  rw [hF1, hF'1, one_pow, one_pow]
  push_cast
  ring


theorem d018926 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    HasDerivAt (_root_.GD.N0232.N0720.N1454.d018921 m n s)
      ((((m + n : ℕ) : ℝ) + 2) * ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        ∫ ω, _root_.GD.N0232.N0720.N1449.d018831 ω * (_root_.GD.N0232.N0720.N1159.d014633 m n s.value ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n)
      1 :=
  _root_.GD.N0232.N0720.N1454.d018925 m n _ (_root_.GD.N0232.N0720.N1369.d018804 s)






theorem d018927 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (∫ ω, _root_.GD.N0232.N0720.N1449.d018831 ω * (_root_.GD.N0232.N0720.N1159.d014633 m n s.value ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      (((m + n : ℕ) : ℝ) + 2) * ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  have hmin : IsLocalMin
      (fun a : ℝ ↦ _root_.GD.N0232.N0720.N1454.d018921 m n s a - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) 1 := by
    have h1 : _root_.GD.N0232.N0720.N1454.d018921 m n s 1 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 = 0 := by
      rw [_root_.GD.N0232.N0720.N1454.d018922, sub_self]
    refine Filter.eventually_of_mem (Ioi_mem_nhds (zero_lt_one' ℝ)) ?_
    intro a ha
    show _root_.GD.N0232.N0720.N1454.d018921 m n s 1 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1454.d018921 m n s a - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2
    rw [h1, ← _root_.GD.N0232.N0720.N1454.d018923 m n s ha]
    exact _root_.GD.N0232.N0720.N1159.d014650 m n s _
  have hd := (hasDerivAt_sub_const_iff (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)).2
    (_root_.GD.N0232.N0720.N1454.d018926 m n s)
  have hzero := hmin.hasDerivAt_eq_zero hd
  linarith


theorem d018928 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (∫ ω, _root_.GD.N0232.N0720.N1449.d018831 ω * (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      (((m + n : ℕ) : ℝ) + 2) * ‖_root_.GD.N0232.N0720.N1047.d018650 m n hm hn‖ ^ 2 :=
  _root_.GD.N0232.N0720.N1454.d018927 m n (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn)


theorem d018929 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (∫ ω, _root_.GD.N0232.N0720.N1449.d018831 ω * (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      (((m + n : ℕ) : ℝ) + 2) * ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1288.d015635]
  exact _root_.GD.N0232.N0720.N1454.d018927 m n (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn)

end

end N1454
end N0720
end N0232
end GD
