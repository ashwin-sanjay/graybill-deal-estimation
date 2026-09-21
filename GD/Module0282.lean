import GD.Module0271
import GD.Module0278
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic












open MeasureTheory Set Filter
open scoped Topology Interval

namespace GD.N0232.N0720.N1353

open _root_.GD.N0232.N0720.N1358 _root_.GD.N0232.N0720.N1413
open _root_.GD.N0232.N0720.N1415

noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

abbrev d004179 := Icc (-1 : ℝ) 1

def d004180 (x : _root_.GD.N0232.N0720.N1353.d004179) : ℝ := (3 / 4 : ℝ) * (1 - (x : ℝ) ^ 2)

theorem d004181 (x : _root_.GD.N0232.N0720.N1353.d004179) : 0 ≤ _root_.GD.N0232.N0720.N1353.d004180 x := by
  have hx : |(x : ℝ)| ≤ 1 := abs_le.mpr x.2
  have hsq : (x : ℝ) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one (x : ℝ)).2 hx
  unfold _root_.GD.N0232.N0720.N1353.d004180
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr hsq)

def d004182 : Measure _root_.GD.N0232.N0720.N1353.d004179 :=
  volume.withDensity fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1353.d004180 x)


theorem d004183 (f : ℝ → ℝ) :
    (∫ x : _root_.GD.N0232.N0720.N1353.d004179, f x ∂_root_.GD.N0232.N0720.N1353.d004182) =
      (3 / 4 : ℝ) * ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * f x := by
  rw [_root_.GD.N0232.N0720.N1353.d004182, integral_withDensity_eq_integral_toReal_smul
    (f := fun x : _root_.GD.N0232.N0720.N1353.d004179 ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1353.d004180 x))
    ((by unfold _root_.GD.N0232.N0720.N1353.d004180; fun_prop : Measurable _root_.GD.N0232.N0720.N1353.d004180).ennreal_ofReal) (by simp)]
  calc
    _ = ∫ x : _root_.GD.N0232.N0720.N1353.d004179, (3 / 4 : ℝ) * ((1 - (x : ℝ) ^ 2) * f x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1353.d004181 x)]
      simp only [smul_eq_mul, _root_.GD.N0232.N0720.N1353.d004180]
      ring
    _ = (3 / 4 : ℝ) * ∫ x : _root_.GD.N0232.N0720.N1353.d004179, (1 - (x : ℝ) ^ 2) * f x := by
      rw [integral_const_mul]
    _ = _ := by
      rw [Measure.Subtype.volume_def, integral_subtype_comap measurableSet_Icc (fun x : ℝ ↦ (1 - x ^ 2) * f x),
        integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

theorem d004184 :
    (∫ x in (-1 : ℝ)..1, (1 - x ^ 2 : ℝ)) = 4 / 3 := by
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ ↦ (1 : ℝ))
      (g := fun x : ℝ ↦ x ^ 2) intervalIntegrable_const
      ((continuous_id.pow 2).intervalIntegrable (-1) 1),
    intervalIntegral.integral_const, integral_pow]
  norm_num

instance d004185 : IsProbabilityMeasure _root_.GD.N0232.N0720.N1353.d004182 := by
  have hnorm : (∫ _ : _root_.GD.N0232.N0720.N1353.d004179, (1 : ℝ) ∂_root_.GD.N0232.N0720.N1353.d004182) = 1 := by
    rw [_root_.GD.N0232.N0720.N1353.d004183 (fun _ : ℝ ↦ (1 : ℝ))]
    simp only [mul_one]
    rw [_root_.GD.N0232.N0720.N1353.d004184]
    norm_num
  apply isProbabilityMeasure_iff_real.2
  simpa only [integral_const, smul_eq_mul, mul_one] using hnorm

theorem d004186 : (∫ x : _root_.GD.N0232.N0720.N1353.d004179, (x : ℝ) ∂_root_.GD.N0232.N0720.N1353.d004182) = 0 := by
  rw [_root_.GD.N0232.N0720.N1353.d004183 (fun x : ℝ ↦ x)]
  have hpoly : (fun x : ℝ ↦ (1 - x ^ 2) * x) = fun x ↦ x ^ 1 - x ^ 3 := by
    funext x
    ring
  rw [hpoly, intervalIntegral.integral_sub (f := fun x : ℝ ↦ x ^ 1)
      (g := fun x : ℝ ↦ x ^ 3)
      ((continuous_id.pow 1).intervalIntegrable (-1) 1) ((continuous_id.pow 3).intervalIntegrable (-1) 1),
    integral_pow, integral_pow]
  norm_num

theorem d004187 :
    (∫ x : _root_.GD.N0232.N0720.N1353.d004179, (x : ℝ) ^ 2 ∂_root_.GD.N0232.N0720.N1353.d004182) = 1 / 5 := by
  rw [_root_.GD.N0232.N0720.N1353.d004183 (fun x : ℝ ↦ x ^ 2)]
  have hpoly : (fun x : ℝ ↦ (1 - x ^ 2) * x ^ 2) = fun x ↦ x ^ 2 - x ^ 4 := by
    funext x
    ring
  rw [hpoly, intervalIntegral.integral_sub (f := fun x : ℝ ↦ x ^ 2)
      (g := fun x : ℝ ↦ x ^ 4)
      ((continuous_id.pow 2).intervalIntegrable (-1) 1) ((continuous_id.pow 4).intervalIntegrable (-1) 1),
    integral_pow, integral_pow]
  norm_num

private theorem d004188 {epsilon : ℝ} (he : |epsilon| < 1)
    (x : _root_.GD.N0232.N0720.N1353.d004179) : 0 < 1 - epsilon * (x : ℝ) := by
  have hx : |(x : ℝ)| ≤ 1 := abs_le.mpr x.2
  have hprod : |epsilon * (x : ℝ)| < 1 := by
    rw [abs_mul]
    calc
      |epsilon| * |(x : ℝ)| ≤ |epsilon| * 1 :=
        mul_le_mul_of_nonneg_left hx (abs_nonneg epsilon)
      _ = |epsilon| := mul_one _
      _ < 1 := he
  linarith [(abs_lt.mp hprod).2]

def d004189 (q : ℝ) (j : ℕ) (epsilon : ℝ) (x : _root_.GD.N0232.N0720.N1353.d004179) : ℝ :=
  (x : ℝ) ^ j * (1 - epsilon * (x : ℝ)) ^ (-q)

theorem d004190 (q : ℝ) (j : ℕ)
    {epsilon : ℝ} (he : |epsilon| < 1) :
    Integrable (_root_.GD.N0232.N0720.N1353.d004189 q j epsilon) _root_.GD.N0232.N0720.N1353.d004182 := by
  have hc : Continuous (_root_.GD.N0232.N0720.N1353.d004189 q j epsilon) := by
    unfold _root_.GD.N0232.N0720.N1353.d004189
    apply Continuous.mul
    · fun_prop
    apply Continuous.rpow_const
    · fun_prop
    · intro x
      exact Or.inl (ne_of_gt (_root_.GD.N0232.N0720.N1353.d004188 he x))
  exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

theorem d004191 {epsilon : ℝ} (he : |epsilon| < 1) :
    (∫ x : _root_.GD.N0232.N0720.N1353.d004179, ((x : ℝ) - _root_.GD.N0232.N0720.N1358.d004015 epsilon) *
      (1 - epsilon * (x : ℝ)) ^ (-(5 / 2 : ℝ)) ∂_root_.GD.N0232.N0720.N1353.d004182) = 0 ∧
    (∫ x : _root_.GD.N0232.N0720.N1353.d004179, ((x : ℝ) - _root_.GD.N0232.N0720.N1358.d004015 epsilon) ^ 3 *
      (1 - epsilon * (x : ℝ)) ^ (-(7 / 2 : ℝ)) ∂_root_.GD.N0232.N0720.N1353.d004182) = 0 := by
  obtain ⟨hfirst, hcubic⟩ := _root_.GD.N0232.N0720.N1358.d004018 he
  constructor
  · rw [_root_.GD.N0232.N0720.N1353.d004183 (fun x : ℝ ↦ (x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) * (1 - epsilon * x) ^ (-(5 / 2 : ℝ)))]
    have horder :
        (fun x : ℝ ↦ (1 - x ^ 2) *
          ((x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) * (1 - epsilon * x) ^ (-(5 / 2 : ℝ)))) =
        fun x ↦ (x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) * (1 - x ^ 2) *
          (1 - epsilon * x) ^ (-(5 / 2 : ℝ)) := by
      funext x
      ring
    rw [horder, hfirst, mul_zero]
  · rw [_root_.GD.N0232.N0720.N1353.d004183 (fun x : ℝ ↦ (x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) ^ 3 * (1 - epsilon * x) ^ (-(7 / 2 : ℝ)))]
    have horder :
        (fun x : ℝ ↦ (1 - x ^ 2) *
          ((x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) ^ 3 * (1 - epsilon * x) ^ (-(7 / 2 : ℝ)))) =
        fun x ↦ (x - _root_.GD.N0232.N0720.N1358.d004015 epsilon) ^ 3 * (1 - x ^ 2) *
          (1 - epsilon * x) ^ (-(7 / 2 : ℝ)) := by
      funext x
      ring
    rw [horder, hcubic, mul_zero]


theorem d004192 {epsilon : ℝ} (he : |epsilon| < 1) :
    _root_.GD.N0232.N0720.N1413.d004128 (-1) 1 0 (5 / 2) _root_.GD.N0232.N0720.N1353.d004182 epsilon = 0 := by
  let a := _root_.GD.N0232.N0720.N1358.d004015 epsilon
  let M := ∫ x, _root_.GD.N0232.N0720.N1353.d004189 (5 / 2) 0 epsilon x ∂_root_.GD.N0232.N0720.N1353.d004182
  let B := ∫ x, _root_.GD.N0232.N0720.N1353.d004189 (5 / 2) 1 epsilon x ∂_root_.GD.N0232.N0720.N1353.d004182
  let A := fun j ↦ ∫ x, _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) j epsilon x ∂_root_.GD.N0232.N0720.N1353.d004182
  have hi (q : ℝ) (j : ℕ) := _root_.GD.N0232.N0720.N1353.d004190 q j he
  obtain ⟨hfirst, hcubic⟩ := _root_.GD.N0232.N0720.N1353.d004191 he
  have hfirstEq :
      (∫ x : _root_.GD.N0232.N0720.N1353.d004179, ((x : ℝ) - a) *
        (1 - epsilon * (x : ℝ)) ^ (-(5 / 2 : ℝ)) ∂_root_.GD.N0232.N0720.N1353.d004182) = B - a * M := by
    calc
      _ = ∫ x, _root_.GD.N0232.N0720.N1353.d004189 (5 / 2) 1 epsilon x -
          a * _root_.GD.N0232.N0720.N1353.d004189 (5 / 2) 0 epsilon x ∂_root_.GD.N0232.N0720.N1353.d004182 := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [_root_.GD.N0232.N0720.N1353.d004189, pow_one, pow_zero, one_mul]
        ring
      _ = _ := by
        rw [integral_sub (hi (5 / 2) 1) ((hi (5 / 2) 0).const_mul a), integral_const_mul]
  have hB : B = a * M := by
    change (∫ x : _root_.GD.N0232.N0720.N1353.d004179, ((x : ℝ) - a) *
      (1 - epsilon * (x : ℝ)) ^ (-(5 / 2 : ℝ)) ∂_root_.GD.N0232.N0720.N1353.d004182) = 0 at hfirst
    rw [hfirstEq] at hfirst
    linarith
  have hcubicEq :
      (∫ x : _root_.GD.N0232.N0720.N1353.d004179, ((x : ℝ) - a) ^ 3 *
        (1 - epsilon * (x : ℝ)) ^ (-(7 / 2 : ℝ)) ∂_root_.GD.N0232.N0720.N1353.d004182) =
        A 3 - (3 * a) * A 2 + (3 * a ^ 2) * A 1 - a ^ 3 * A 0 := by
    calc
      _ = ∫ x, _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 3 epsilon x -
          (3 * a) * _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 2 epsilon x +
          (3 * a ^ 2) * _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 1 epsilon x -
          a ^ 3 * _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 0 epsilon x ∂_root_.GD.N0232.N0720.N1353.d004182 := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [_root_.GD.N0232.N0720.N1353.d004189, pow_one, pow_zero, one_mul]
        ring
      _ = _ := by
        have hi32 : Integrable (fun x ↦ _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 3 epsilon x -
            (3 * a) * _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 2 epsilon x) _root_.GD.N0232.N0720.N1353.d004182 :=
          (hi (7 / 2) 3).sub ((hi (7 / 2) 2).const_mul (3 * a))
        have hi321 : Integrable (fun x ↦ _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 3 epsilon x -
            (3 * a) * _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 2 epsilon x +
            (3 * a ^ 2) * _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 1 epsilon x) _root_.GD.N0232.N0720.N1353.d004182 :=
          hi32.add ((hi (7 / 2) 1).const_mul (3 * a ^ 2))
        rw [integral_sub (f := fun x ↦ _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 3 epsilon x -
              (3 * a) * _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 2 epsilon x +
              (3 * a ^ 2) * _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 1 epsilon x)
            (g := fun x ↦ a ^ 3 * _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 0 epsilon x)
            hi321 ((hi (7 / 2) 0).const_mul (a ^ 3)),
          integral_add (f := fun x ↦ _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 3 epsilon x -
              (3 * a) * _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 2 epsilon x)
            (g := fun x ↦ (3 * a ^ 2) * _root_.GD.N0232.N0720.N1353.d004189 (7 / 2) 1 epsilon x)
            hi32 ((hi (7 / 2) 1).const_mul (3 * a ^ 2)),
          integral_sub (hi (7 / 2) 3) ((hi (7 / 2) 2).const_mul (3 * a)),
          integral_const_mul, integral_const_mul, integral_const_mul]
  have hA : A 3 - (3 * a) * A 2 + (3 * a ^ 2) * A 1 - a ^ 3 * A 0 = 0 := by
    rw [← hcubicEq]
    exact hcubic
  have hq (j : ℕ) : _root_.GD.N0232.N0720.N1413.d004111 (-1) 1 0 (5 / 2) j _root_.GD.N0232.N0720.N1353.d004182 epsilon =
      ∫ x, _root_.GD.N0232.N0720.N1353.d004189 (5 / 2) j epsilon x ∂_root_.GD.N0232.N0720.N1353.d004182 := by
    simp [_root_.GD.N0232.N0720.N1413.d004111, _root_.GD.N0232.N0720.N1353.d004189]
  have hq1 (j : ℕ) : _root_.GD.N0232.N0720.N1413.d004111 (-1) 1 0 ((5 / 2 : ℝ) + 1) j _root_.GD.N0232.N0720.N1353.d004182 epsilon =
      A j := by
    norm_num [_root_.GD.N0232.N0720.N1413.d004111, _root_.GD.N0232.N0720.N1353.d004189, A]
  simp only [_root_.GD.N0232.N0720.N1413.d004128, _root_.GD.N0232.N0720.N1413.d004126, Pi.sub_apply, Pi.add_apply,
    Pi.mul_apply, Pi.pow_apply, hq, hq1]
  change M ^ 3 * A 3 - 3 * (B * M ^ 2 * A 2) +
    3 * (B ^ 2 * M * A 1) - B ^ 3 * A 0 = 0
  rw [hB]
  linear_combination M ^ 3 * hA



theorem d004193 :
    _root_.GD.N0232.N0720.N1415.d004078 (5 / 2 : ℝ) (_root_.GD.N0232.N0720.N1415.d004091 (-1) 1 0 _root_.GD.N0232.N0720.N1353.d004182) = 0 := by
  apply _root_.GD.N0232.N0720.N1413.d004130 (-1) 1 0 (5 / 2) _root_.GD.N0232.N0720.N1353.d004182
  have hzero : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  filter_upwards [isOpen_Ioo.eventually_mem hzero] with epsilon he
  exact _root_.GD.N0232.N0720.N1353.d004192 ((abs_lt).2 he)

end

end GD.N0232.N0720.N1353

#print axioms _root_.GD.N0232.N0720.N1353.d004185
#print axioms _root_.GD.N0232.N0720.N1353.d004187
#print axioms _root_.GD.N0232.N0720.N1353.d004193
