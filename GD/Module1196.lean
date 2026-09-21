import GD.Module1175
import GD.Module1195
import Mathlib.Analysis.Calculus.MeanValue

































open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1419

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0691
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1449
open _root_.GD.N0232.N0720.N1454
open _root_.GD.N0232.N0720.N1453
open _root_.GD.N0232.N0720.N1445

local notation "PA" => _root_.GD.N0232.N0720.N1482.d015118






theorem d019308 {f f' : ℝ → ℝ} {x₀ L : ℝ}
    (hmin : ∀ᶠ x in 𝓝 x₀, f x₀ ≤ f x)
    (hf : ∀ᶠ x in 𝓝 x₀, HasDerivAt f (f' x) x)
    (h0 : f' x₀ = 0) (hf' : HasDerivAt f' L x₀) : 0 ≤ L := by
  by_contra hL
  push Not at hL
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.eventually_nhds_iff.1 (hmin.and hf)
  have hev : ∀ᶠ x in 𝓝[≠] x₀, slope f' x₀ x < 0 :=
    (hasDerivAt_iff_tendsto_slope.1 hf').eventually (eventually_lt_nhds hL)
  obtain ⟨δ₂, hδ₂, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
  have hmpos : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  set δ := min δ₁ δ₂ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ < δ₁ := by
    have := min_le_left δ₁ δ₂
    linarith
  have hδ2 : δ < δ₂ := by
    have := min_le_right δ₁ δ₂
    linarith
  have hab : x₀ < x₀ + δ := by linarith
  have hcont : ContinuousOn f (Icc x₀ (x₀ + δ)) := by
    intro x hx
    have hdist : dist x x₀ < δ₁ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    exact (hball hdist).2.continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioo x₀ (x₀ + δ), HasDerivAt f (f' x) x := by
    intro x hx
    have hdist : dist x x₀ < δ₁ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    exact (hball hdist).2
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hab hcont hderiv
  have hcdist : dist c x₀ < δ₂ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hc.1, hc.2]
  have hcne : c ∈ ({x₀}ᶜ : Set ℝ) := ne_of_gt hc.1
  have hslope : slope f' x₀ c < 0 := hsub ⟨Metric.mem_ball.2 hcdist, hcne⟩
  rw [slope_def_field, h0, sub_zero] at hslope
  have hcpos : 0 < c - x₀ := by linarith [hc.1]
  have hfc : f' c < 0 := by
    by_contra h
    push Not at h
    have := div_nonneg h hcpos.le
    linarith
  have hfb : f (x₀ + δ) < f x₀ := by
    have h1 : f' c = (f (x₀ + δ) - f x₀) / (x₀ + δ - x₀) := hcs
    have h2 : x₀ + δ - x₀ = δ := by ring
    rw [h2] at h1
    have h3 : f (x₀ + δ) - f x₀ = f' c * δ := by
      rw [h1]
      field_simp
    nlinarith [hfc, hδpos]
  have hbdist : dist (x₀ + δ) x₀ < δ₁ := by
    rw [Real.dist_eq]
    have : x₀ + δ - x₀ = δ := by ring
    rw [this, abs_of_pos hδpos]
    exact hδ1
  exact absurd (hball hbdist).1 (not_le.2 hfb)

variable (m n : ℕ)




theorem d019309 (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : _root_.GD.N0232.N0720.N1159.d014637 m n d) {κ : ℝ} (hκ : κ < 1 / 2) :
    Integrable (fun ω ↦ _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2 * (Real.exp (κ * _root_.GD.N0232.N0720.N1449.d018831 ω) * (d ω) ^ 2))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hη : 0 < (1 / 2 - κ) / 2 := by linarith
  have hκη : κ + (1 / 2 - κ) / 2 < 1 / 2 := by linarith
  have hmaj := (_root_.GD.N0232.N0720.N1454.d018918 m n d hd hκη).const_mul
    ((1 / 2 - κ) / 2)⁻¹
  refine hmaj.mono' ?_ ?_
  · exact ((_root_.GD.N0232.N0720.N1449.d018832.pow_const 2).aestronglyMeasurable).mul
      (((_root_.GD.N0232.N0720.N1449.d018832.const_mul κ).exp.aestronglyMeasurable).mul
        ((Lp.aestronglyMeasurable d).pow 2))
  · filter_upwards with ω
    have hS := _root_.GD.N0232.N0720.N1454.d018915 m n ω
    have hp := sq_nonneg (d ω)
    have hE := (Real.exp_pos (κ * _root_.GD.N0232.N0720.N1449.d018831 ω)).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hE hp))]
    have hb := _root_.GD.N0232.N0720.N1454.d018917 (κ := κ) (t := _root_.GD.N0232.N0720.N1449.d018831 ω) hη
    calc _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2 * (Real.exp (κ * _root_.GD.N0232.N0720.N1449.d018831 ω) * (d ω) ^ 2)
        = _root_.GD.N0232.N0720.N1449.d018831 ω * ((_root_.GD.N0232.N0720.N1449.d018831 ω * Real.exp (κ * _root_.GD.N0232.N0720.N1449.d018831 ω)) * (d ω) ^ 2) := by
          ring
      _ ≤ _root_.GD.N0232.N0720.N1449.d018831 ω * ((((1 / 2 - κ) / 2)⁻¹ *
            Real.exp ((κ + (1 / 2 - κ) / 2) * _root_.GD.N0232.N0720.N1449.d018831 ω)) * (d ω) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hp) hS
      _ = ((1 / 2 - κ) / 2)⁻¹ *
            (_root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((κ + (1 / 2 - κ) / 2) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (d ω) ^ 2)) := by
          ring




def d019310 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (a : ℝ) : ℝ :=
  ∫ ω, Real.exp ((1 - a ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n


def d019311 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (a : ℝ) : ℝ :=
  ∫ ω, (-a * _root_.GD.N0232.N0720.N1449.d018831 ω) * (Real.exp ((1 - a ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)
    ∂_root_.GD.N0232.N0720.N1080.d014172 m n


def d019312 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (a : ℝ) : ℝ :=
  ((m + n + 2 : ℕ) : ℝ) * (a ^ (m + n + 2 - 1) * _root_.GD.N0232.N0720.N1419.d019310 m n P a) + a ^ (m + n + 2) * _root_.GD.N0232.N0720.N1419.d019311 m n P a

theorem d019313 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (a : ℝ) :
    _root_.GD.N0232.N0720.N1454.d018919 m n P a = a ^ (m + n + 2) * _root_.GD.N0232.N0720.N1419.d019310 m n P a := rfl

theorem d019314 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : _root_.GD.N0232.N0720.N1419.d019310 m n P 1 = ‖P‖ ^ 2 := by
  rw [_root_.GD.N0230.N0691.d001213 (_root_.GD.N0232.N0720.N1080.d014172 m n) P]
  unfold _root_.GD.N0232.N0720.N1419.d019310
  congr 1
  funext ω
  simp only [one_pow, sub_self, zero_div, zero_mul, Real.exp_zero, one_mul]

theorem d019315 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1419.d019311 m n P 1 = -∫ ω, _root_.GD.N0232.N0720.N1449.d018831 ω * (P ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  unfold _root_.GD.N0232.N0720.N1419.d019311
  rw [← integral_neg]
  congr 1
  funext ω
  simp only [one_pow, sub_self, zero_div, zero_mul, Real.exp_zero, one_mul]
  ring

theorem d019316 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (b : ℝ) :
    AEStronglyMeasurable
      (fun ω ↦ Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  ((_root_.GD.N0232.N0720.N1449.d018832.const_mul ((1 - b ^ 2) / 2)).exp.aestronglyMeasurable).mul
    ((Lp.aestronglyMeasurable P).pow 2)


theorem d019317 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) {b : ℝ}
    (hb : dist b 1 < 1 / 4) :
    ‖(-b * _root_.GD.N0232.N0720.N1449.d018831 ω) * (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)‖ ≤
      (5 / 4 : ℝ) * (_root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) := by
  rw [Real.dist_eq, abs_lt] at hb
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
      (5 / 4 : ℝ) * (_root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) :=
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


theorem d019318 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) {b : ℝ}
    (hb : dist b 1 < 1 / 4) :
    ‖(-_root_.GD.N0232.N0720.N1449.d018831 ω + b ^ 2 * _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2) *
        (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)‖ ≤
      _root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) +
        (25 / 16 : ℝ) *
          (_root_.GD.N0232.N0720.N1449.d018831 ω ^ 2 * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) := by
  rw [Real.dist_eq, abs_lt] at hb
  have hb1 : 3 / 4 < b := by linarith [hb.1]
  have hb2 : b < 5 / 4 := by linarith [hb.2]
  have hS := _root_.GD.N0232.N0720.N1454.d018915 m n ω
  have hp := sq_nonneg (P ω)
  have hE := (Real.exp_pos ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω)).le
  have hexp : Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2 ≤
      Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ hp
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_right _ hS
    nlinarith
  have habs : |-_root_.GD.N0232.N0720.N1449.d018831 ω + b ^ 2 * _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2| ≤
      _root_.GD.N0232.N0720.N1449.d018831 ω + (25 / 16 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2 := by
    have hb3 : b ^ 2 ≤ 25 / 16 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_right hb3 (sq_nonneg (_root_.GD.N0232.N0720.N1449.d018831 ω))
    have hnn := mul_nonneg (sq_nonneg b) (sq_nonneg (_root_.GD.N0232.N0720.N1449.d018831 ω))
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (_root_.GD.N0232.N0720.N1449.d018831 ω), hS, hprod, hnn]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hE hp)]
  calc |-_root_.GD.N0232.N0720.N1449.d018831 ω + b ^ 2 * _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2| *
        (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)
      ≤ (_root_.GD.N0232.N0720.N1449.d018831 ω + (25 / 16 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2) *
          (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) :=
        mul_le_mul habs hexp (mul_nonneg hE hp) (by positivity)
    _ = _root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) +
        (25 / 16 : ℝ) *
          (_root_.GD.N0232.N0720.N1449.d018831 ω ^ 2 * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) := by
        ring

theorem d019319 (S p a : ℝ) :
    HasDerivAt (fun b : ℝ ↦ (-b * S) * (Real.exp ((1 - b ^ 2) / 2 * S) * p ^ 2))
      ((-S + a ^ 2 * S ^ 2) * (Real.exp ((1 - a ^ 2) / 2 * S) * p ^ 2)) a := by
  have h1 : HasDerivAt (fun b : ℝ ↦ -b * S) (-S) a := by
    have := ((hasDerivAt_id a).neg).mul_const S
    simpa using this
  have h2 := _root_.GD.N0232.N0720.N1454.d018924 S p a
  exact (h1.mul h2).congr_deriv (by ring)


theorem d019320 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hfin : _root_.GD.N0232.N0720.N1159.d014637 m n P)
    {a₀ : ℝ} (ha₀ : dist a₀ 1 < 1 / 8) :
    HasDerivAt (_root_.GD.N0232.N0720.N1419.d019310 m n P) (_root_.GD.N0232.N0720.N1419.d019311 m n P a₀) a₀ := by
  unfold _root_.GD.N0232.N0720.N1419.d019310 _root_.GD.N0232.N0720.N1419.d019311
  have ha₀' : 7 / 8 < a₀ := by
    rw [Real.dist_eq, abs_lt] at ha₀
    linarith [ha₀.1]
  have hF_int : Integrable
      (fun ω ↦ Real.exp ((1 - a₀ ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1454.d018916 m n P hfin (κ := (1 - a₀ ^ 2) / 2) (by nlinarith)
  have hF'_meas : AEStronglyMeasurable
      (fun ω ↦ (-a₀ * _root_.GD.N0232.N0720.N1449.d018831 ω) *
        (Real.exp ((1 - a₀ ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    ((_root_.GD.N0232.N0720.N1449.d018832.const_mul (-a₀)).aestronglyMeasurable).mul (_root_.GD.N0232.N0720.N1419.d019316 m n P a₀)
  have hbound_int : Integrable
      (fun ω ↦ (5 / 4 : ℝ) *
        (_root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (_root_.GD.N0232.N0720.N1454.d018918 m n P hfin (κ := 7 / 32) (by norm_num)).const_mul
      (5 / 4)
  have h_bound : ∀ᵐ ω ∂_root_.GD.N0232.N0720.N1080.d014172 m n, ∀ b ∈ Metric.ball a₀ (1 / 8),
      ‖(-b * _root_.GD.N0232.N0720.N1449.d018831 ω) *
        (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)‖ ≤
      (5 / 4 : ℝ) *
        (_root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) := by
    refine Filter.Eventually.of_forall fun ω b hb => _root_.GD.N0232.N0720.N1419.d019317 m n P ω ?_
    rw [Metric.mem_ball] at hb
    calc dist b 1 ≤ dist b a₀ + dist a₀ 1 := dist_triangle _ _ _
      _ < 1 / 8 + 1 / 8 := add_lt_add hb ha₀
      _ = 1 / 4 := by norm_num
  have h_diff : ∀ᵐ ω ∂_root_.GD.N0232.N0720.N1080.d014172 m n, ∀ b ∈ Metric.ball a₀ (1 / 8),
      HasDerivAt (fun b : ℝ ↦ Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)
        ((-b * _root_.GD.N0232.N0720.N1449.d018831 ω) *
          (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) b :=
    Filter.Eventually.of_forall fun ω b _ ↦ _root_.GD.N0232.N0720.N1454.d018924 (_root_.GD.N0232.N0720.N1449.d018831 ω) (P ω) b
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds a₀ (by norm_num : (0 : ℝ) < 1 / 8))
    (Filter.Eventually.of_forall (_root_.GD.N0232.N0720.N1419.d019316 m n P)) hF_int hF'_meas h_bound hbound_int
    h_diff).2


theorem d019321 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hfin : _root_.GD.N0232.N0720.N1159.d014637 m n P) :
    HasDerivAt (_root_.GD.N0232.N0720.N1419.d019311 m n P)
      (∫ ω, (_root_.GD.N0232.N0720.N1449.d018831 ω ^ 2 - _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) 1 := by
  unfold _root_.GD.N0232.N0720.N1419.d019311
  have hmeasF : ∀ b : ℝ, AEStronglyMeasurable
      (fun ω ↦ (-b * _root_.GD.N0232.N0720.N1449.d018831 ω) *
        (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    fun b ↦ ((_root_.GD.N0232.N0720.N1449.d018832.const_mul (-b)).aestronglyMeasurable).mul
      (_root_.GD.N0232.N0720.N1419.d019316 m n P b)
  have hbound_int1 : Integrable
      (fun ω ↦ (5 / 4 : ℝ) *
        (_root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (_root_.GD.N0232.N0720.N1454.d018918 m n P hfin (κ := 7 / 32) (by norm_num)).const_mul
      (5 / 4)
  have hF_int : Integrable
      (fun ω ↦ (-(1 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) *
        (Real.exp ((1 - (1 : ℝ) ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    hbound_int1.mono' (hmeasF 1)
      (Filter.Eventually.of_forall fun ω ↦ _root_.GD.N0232.N0720.N1419.d019317 m n P ω (by simp))
  have hF'_meas : AEStronglyMeasurable
      (fun ω ↦ (-_root_.GD.N0232.N0720.N1449.d018831 ω + (1 : ℝ) ^ 2 * _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2) *
        (Real.exp ((1 - (1 : ℝ) ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    ((_root_.GD.N0232.N0720.N1449.d018832.neg.add
      ((_root_.GD.N0232.N0720.N1449.d018832.pow_const 2).const_mul ((1 : ℝ) ^ 2))).aestronglyMeasurable).mul
      (_root_.GD.N0232.N0720.N1419.d019316 m n P 1)
  have hbound_int : Integrable
      (fun ω ↦ _root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) +
        (25 / 16 : ℝ) *
          (_root_.GD.N0232.N0720.N1449.d018831 ω ^ 2 * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (_root_.GD.N0232.N0720.N1454.d018918 m n P hfin (κ := 7 / 32) (by norm_num)).add
      ((_root_.GD.N0232.N0720.N1419.d019309 m n P hfin (κ := 7 / 32)
        (by norm_num)).const_mul (25 / 16))
  have h_bound : ∀ᵐ ω ∂_root_.GD.N0232.N0720.N1080.d014172 m n, ∀ b ∈ Metric.ball (1 : ℝ) (1 / 4),
      ‖(-_root_.GD.N0232.N0720.N1449.d018831 ω + b ^ 2 * _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2) *
        (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)‖ ≤
      _root_.GD.N0232.N0720.N1449.d018831 ω * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2) +
        (25 / 16 : ℝ) *
          (_root_.GD.N0232.N0720.N1449.d018831 ω ^ 2 * (Real.exp ((7 / 32 : ℝ) * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) :=
    Filter.Eventually.of_forall fun ω b hb ↦
      _root_.GD.N0232.N0720.N1419.d019318 m n P ω (by rwa [Metric.mem_ball] at hb)
  have h_diff : ∀ᵐ ω ∂_root_.GD.N0232.N0720.N1080.d014172 m n, ∀ b ∈ Metric.ball (1 : ℝ) (1 / 4),
      HasDerivAt (fun b : ℝ ↦ (-b * _root_.GD.N0232.N0720.N1449.d018831 ω) *
          (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2))
        ((-_root_.GD.N0232.N0720.N1449.d018831 ω + b ^ 2 * _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2) *
          (Real.exp ((1 - b ^ 2) / 2 * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2)) b :=
    Filter.Eventually.of_forall fun ω b _ ↦ _root_.GD.N0232.N0720.N1419.d019319 (_root_.GD.N0232.N0720.N1449.d018831 ω) (P ω) b
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4))
    (Filter.Eventually.of_forall hmeasF) hF_int hF'_meas h_bound hbound_int h_diff).2
  refine hderiv.congr_deriv ?_
  congr 1
  funext ω
  simp only [one_pow, sub_self, zero_div, zero_mul, Real.exp_zero, one_mul]
  ring


theorem d019322 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfin : _root_.GD.N0232.N0720.N1159.d014637 m n P) {a₀ : ℝ} (ha₀ : dist a₀ 1 < 1 / 8) :
    HasDerivAt (_root_.GD.N0232.N0720.N1454.d018919 m n P) (_root_.GD.N0232.N0720.N1419.d019312 m n P a₀) a₀ := by
  have hJ := _root_.GD.N0232.N0720.N1419.d019320 m n P hfin ha₀
  have := (hasDerivAt_pow (m + n + 2) a₀).mul hJ
  refine this.congr_deriv ?_
  unfold _root_.GD.N0232.N0720.N1419.d019312
  ring


theorem d019323 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hfin : _root_.GD.N0232.N0720.N1159.d014637 m n P) :
    HasDerivAt (_root_.GD.N0232.N0720.N1419.d019312 m n P)
      (((m + n + 2 : ℕ) : ℝ) *
          (((m + n + 2 - 1 : ℕ) : ℝ) * (1 : ℝ) ^ (m + n + 2 - 1 - 1) * _root_.GD.N0232.N0720.N1419.d019310 m n P 1 +
            (1 : ℝ) ^ (m + n + 2 - 1) * _root_.GD.N0232.N0720.N1419.d019311 m n P 1) +
        (((m + n + 2 : ℕ) : ℝ) * (1 : ℝ) ^ (m + n + 2 - 1) * _root_.GD.N0232.N0720.N1419.d019311 m n P 1 +
          (1 : ℝ) ^ (m + n + 2) *
            ∫ ω, (_root_.GD.N0232.N0720.N1449.d018831 ω ^ 2 - _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n)) 1 := by
  have hJ := _root_.GD.N0232.N0720.N1419.d019320 m n P hfin (a₀ := 1) (by simp)
  have hJ1 := _root_.GD.N0232.N0720.N1419.d019321 m n P hfin
  have h1 := ((hasDerivAt_pow (m + n + 2 - 1) (1 : ℝ)).mul hJ).const_mul ((m + n + 2 : ℕ) : ℝ)
  have h2 := (hasDerivAt_pow (m + n + 2) (1 : ℝ)).mul hJ1
  exact h1.add h2



theorem d019324 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfin : _root_.GD.N0232.N0720.N1159.d014637 m n P) :
    Integrable (fun ω ↦ _root_.GD.N0232.N0720.N1449.d018831 ω * (P ω) ^ 2) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have := _root_.GD.N0232.N0720.N1454.d018918 m n P hfin (κ := 0) (by norm_num)
  simpa using this

theorem d019325 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfin : _root_.GD.N0232.N0720.N1159.d014637 m n P) :
    Integrable (fun ω ↦ _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2 * (P ω) ^ 2) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have := _root_.GD.N0232.N0720.N1419.d019309 m n P hfin (κ := 0) (by norm_num)
  simpa using this



theorem d019326 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (((m + n : ℕ) : ℝ) + 2) * (((m + n : ℕ) : ℝ) + 4) *
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      ∫ ω, _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2 * (_root_.GD.N0232.N0720.N1159.d014633 m n s.value ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  set P := _root_.GD.N0232.N0720.N1159.d014633 m n s.value with hPdef
  have hfin : _root_.GD.N0232.N0720.N1159.d014637 m n P :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s _ (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hmin : ∀ᶠ a in 𝓝 (1 : ℝ), _root_.GD.N0232.N0720.N1454.d018919 m n P 1 ≤ _root_.GD.N0232.N0720.N1454.d018919 m n P a := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with a ha
    have h := _root_.GD.N0232.N0720.N1159.d014650 m n s (_root_.GD.N0232.N0720.N1454.d018901 a)
    rw [_root_.GD.N0232.N0720.N1454.d018923 m n s ha] at h
    rw [_root_.GD.N0232.N0720.N1454.d018920]
    unfold _root_.GD.N0232.N0720.N1454.d018921 at h
    linarith
  have hf : ∀ᶠ a in 𝓝 (1 : ℝ), HasDerivAt (_root_.GD.N0232.N0720.N1454.d018919 m n P) (_root_.GD.N0232.N0720.N1419.d019312 m n P a) a := by
    filter_upwards [Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 8)] with a ha
    exact _root_.GD.N0232.N0720.N1419.d019322 m n P hfin (Metric.mem_ball.1 ha)
  have hvir := _root_.GD.N0232.N0720.N1454.d018927 m n s
  rw [← hPdef] at hvir
  have h0 : _root_.GD.N0232.N0720.N1419.d019312 m n P 1 = 0 := by
    unfold _root_.GD.N0232.N0720.N1419.d019312
    rw [_root_.GD.N0232.N0720.N1419.d019314, _root_.GD.N0232.N0720.N1419.d019315, hvir]
    simp only [one_pow, one_mul, mul_one]
    push_cast
    ring
  have hL := _root_.GD.N0232.N0720.N1419.d019308 hmin hf h0 (_root_.GD.N0232.N0720.N1419.d019323 m n P hfin)
  rw [_root_.GD.N0232.N0720.N1419.d019314, _root_.GD.N0232.N0720.N1419.d019315, hvir] at hL
  simp only [one_pow, one_mul, mul_one, sub_mul] at hL
  rw [integral_sub (_root_.GD.N0232.N0720.N1419.d019325 m n P hfin)
    (_root_.GD.N0232.N0720.N1419.d019324 m n P hfin), hvir] at hL
  have hN : ((m + n + 2 - 1 : ℕ) : ℝ) = ((m + n : ℕ) : ℝ) + 1 := by
    have : m + n + 2 - 1 = m + n + 1 := by omega
    rw [this]
    push_cast
    ring
  rw [hN] at hL
  push_cast at hL ⊢
  nlinarith [hL]


theorem d019327 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (((m + n : ℕ) : ℝ) + 2) * (((m + n : ℕ) : ℝ) + 4) *
        ‖_root_.GD.N0232.N0720.N1047.d018650 m n hm hn‖ ^ 2 ≤
      ∫ ω, _root_.GD.N0232.N0720.N1449.d018831 ω ^ 2 *
        (_root_.GD.N0232.N0720.N1047.d018650 m n hm hn ω) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n :=
  _root_.GD.N0232.N0720.N1419.d019326 m n
    (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn)




def d019328 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (t : ℝ) : ℝ :=
  ∫ ω, Real.exp (t * _root_.GD.N0232.N0720.N1449.d018831 ω) * (P ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n

theorem d019329 (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) {t : ℝ} (ht : t < 1 / 2) :
    _root_.GD.N0232.N0720.N1454.d018919 m n P (Real.sqrt (1 - 2 * t)) =
      Real.sqrt (1 - 2 * t) ^ (m + n + 2) * _root_.GD.N0232.N0720.N1419.d019328 m n P t := by
  unfold _root_.GD.N0232.N0720.N1454.d018919 _root_.GD.N0232.N0720.N1419.d019328
  have h : (1 - Real.sqrt (1 - 2 * t) ^ 2) / 2 = t := by
    rw [Real.sq_sqrt (by linarith)]
    ring
  rw [h]


theorem d019330 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (∀ a : ℝ, 0 < a → _root_.GD.N0232.N0720.N1159.d014647 m n s (_root_.GD.N0232.N0720.N1454.d018901 a) = 0) ↔
      ∀ t : ℝ, t < 1 / 2 →
        Real.sqrt (1 - 2 * t) ^ (m + n + 2) *
            _root_.GD.N0232.N0720.N1419.d019328 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) t =
          ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  constructor
  · intro h t ht
    have ha : 0 < Real.sqrt (1 - 2 * t) := Real.sqrt_pos.2 (by linarith)
    have h1 := h _ ha
    rw [_root_.GD.N0232.N0720.N1454.d018923 m n s ha, sub_eq_zero] at h1
    unfold _root_.GD.N0232.N0720.N1454.d018921 at h1
    rw [_root_.GD.N0232.N0720.N1419.d019329 m n _ ht] at h1
    exact h1
  · intro h a ha
    rw [_root_.GD.N0232.N0720.N1454.d018923 m n s ha, sub_eq_zero]
    unfold _root_.GD.N0232.N0720.N1454.d018921
    have ht : (1 - a ^ 2) / 2 < 1 / 2 := by nlinarith
    have hsq : Real.sqrt (1 - 2 * ((1 - a ^ 2) / 2)) = a := by
      rw [show (1 : ℝ) - 2 * ((1 - a ^ 2) / 2) = a ^ 2 by ring, Real.sqrt_sq ha.le]
    have h1 := h _ ht
    rw [hsq] at h1
    exact h1


theorem d019331 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 ↔
      (∀ t : ℝ, _root_.GD.N0232.N0720.N1482.d015128 t ∈
          _root_.GD.N0232.N0720.N1453.d018885 m n s) ∧
        (∀ a : ℝ, 0 < a → _root_.GD.N0232.N0720.N1454.d018901 a ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s) := by
  rw [_root_.GD.N0232.N0720.N1453.d018896]
  constructor
  · intro h
    rw [h]
    exact ⟨fun _ => Subgroup.mem_top _, fun _ _ => Subgroup.mem_top _⟩
  · rintro ⟨ht, hd⟩
    rw [eq_top_iff]
    intro g _
    obtain ⟨b, l⟩ := g
    rw [← _root_.GD.N0232.N0720.N1445.d019305]
    refine mul_mem (ht b) ?_
    have h1 := hd (Real.exp l) (Real.exp_pos l)
    have heq : _root_.GD.N0232.N0720.N1454.d018901 (Real.exp l) = _root_.GD.N0232.N0720.N1482.d015129 l := by
      show (⟨0, Real.log (Real.exp l)⟩ : PA) = ⟨0, l⟩
      rw [Real.log_exp]
    rwa [heq] at h1


theorem d019332 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (h : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0) :
    ∀ t : ℝ, t < 1 / 2 →
      Real.sqrt (1 - 2 * t) ^ (m + n + 2) *
          _root_.GD.N0232.N0720.N1419.d019328 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) t =
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  rw [← _root_.GD.N0232.N0720.N1419.d019330]
  intro a ha
  have hall := (_root_.GD.N0232.N0720.N1482.d015171
    (m := m) (n := n) s).1 h
  exact hall _


theorem d019333 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (h2 : _root_.GD.N0232.N0720.N1482.d015129 (Real.log 2) ∈
      _root_.GD.N0232.N0720.N1453.d018885 m n s)
    (h3 : _root_.GD.N0232.N0720.N1482.d015129 (Real.log 3) ∈
      _root_.GD.N0232.N0720.N1453.d018885 m n s) :
    ∀ a : ℝ, 0 < a → _root_.GD.N0232.N0720.N1454.d018901 a ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s := by
  have hle : AddSubgroup.closure {Real.log 2, Real.log 3} ≤ _root_.GD.N0232.N0720.N1445.d019302 m n s := by
    apply (AddSubgroup.closure_le _).2
    intro r hr
    rcases hr with (rfl | rfl)
    · exact h2
    · exact h3
  have hdense : Dense ((AddSubgroup.closure {Real.log 2, Real.log 3} : AddSubgroup ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.2
      _root_.GD.N0232.N0720.N1482.d015151
  have hdense' : Dense (_root_.GD.N0232.N0720.N1445.d019302 m n s : Set ℝ) :=
    hdense.mono (SetLike.coe_subset_coe.2 hle)
  have hcl := _root_.GD.N0232.N0720.N1445.d019304 m n s
  have huniv : (_root_.GD.N0232.N0720.N1445.d019302 m n s : Set ℝ) = Set.univ := by
    rw [← hcl.closure_eq]
    exact hdense'.closure_eq
  intro a _
  have hmem : Real.log a ∈ (_root_.GD.N0232.N0720.N1445.d019302 m n s : Set ℝ) := by
    rw [huniv]
    exact Set.mem_univ _
  exact hmem




theorem d019334 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 ↔
      _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 = 0 ∧
        ∀ t : ℝ, t < 1 / 2 →
          Real.sqrt (1 - 2 * t) ^ (m + n + 2) *
              _root_.GD.N0232.N0720.N1419.d019328 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) t =
            ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  constructor
  · intro h
    exact ⟨(_root_.GD.N0232.N0720.N1482.d015171
      (m := m) (n := n) s).1 h _, _root_.GD.N0232.N0720.N1419.d019332 m n s h⟩
  · rintro ⟨h3, hmgf⟩
    rw [_root_.GD.N0232.N0720.N1419.d019331]
    refine ⟨?_, ?_⟩
    · intro t
      rw [_root_.GD.N0232.N0720.N1453.d018887]
      exact _root_.GD.N0232.N0720.N1445.d019295 m n s h3 t
    · intro a ha
      rw [_root_.GD.N0232.N0720.N1453.d018887]
      exact (_root_.GD.N0232.N0720.N1419.d019330 m n s).2 hmgf a ha



theorem d019335 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 ↔
      (∀ t : ℝ, _root_.GD.N0232.N0720.N1482.d015128 t ∈
          _root_.GD.N0232.N0720.N1453.d018885 m n s) ∧
        ∀ t : ℝ, t < 1 / 2 →
          Real.sqrt (1 - 2 * t) ^ (m + n + 2) *
              _root_.GD.N0232.N0720.N1419.d019328 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) t =
            ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1419.d019331]
  constructor
  · rintro ⟨ht, hd⟩
    refine ⟨ht, (_root_.GD.N0232.N0720.N1419.d019330 m n s).1 fun a ha => ?_⟩
    rw [← _root_.GD.N0232.N0720.N1453.d018887]
    exact hd a ha
  · rintro ⟨ht, hmgf⟩
    refine ⟨ht, fun a ha => ?_⟩
    rw [_root_.GD.N0232.N0720.N1453.d018887]
    exact (_root_.GD.N0232.N0720.N1419.d019330 m n s).2 hmgf a ha

end

end N1419
end N0720
end N0232
end GD
