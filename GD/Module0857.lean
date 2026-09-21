import GD.Module0856
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

















open MeasureTheory Filter Set

namespace GD
namespace N0232
namespace N0720
namespace N1427

noncomputable section

open _root_.GD.N0232.N0720.N1421
open _root_.GD.N0232.N0720.N1428



noncomputable def d013155 (beta t X : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1428.d013135 beta X *
    _root_.GD.N0232.N0720.N1428.d013136 t X ^ 2


noncomputable def d013156 (beta t : ℝ) : ℝ :=
  ∫ X : ℝ in (0 : ℝ)..t, _root_.GD.N0232.N0720.N1427.d013155 beta t X


noncomputable def d013157 (beta t : ℝ) : ℝ :=
  ∫ X : ℝ in Ioi (1 : ℝ), _root_.GD.N0232.N0720.N1427.d013155 beta t X

theorem d013158 (beta t : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1427.d013155 beta t) := by
  unfold _root_.GD.N0232.N0720.N1427.d013155 _root_.GD.N0232.N0720.N1428.d013135
    _root_.GD.N0232.N0720.N1428.d013133 _root_.GD.N0232.N0720.N1428.d013136
  fun_prop

theorem d013159
    {beta X : ℝ} (hbeta : 0 < beta) (hX : 0 ≤ X) :
    0 ≤ _root_.GD.N0232.N0720.N1428.d013135 beta X := by
  have hden : 0 < beta + 2 * X := by positivity
  have hbase : 0 ≤ beta / (beta + 2 * X) :=
    div_nonneg hbeta.le hden.le
  unfold _root_.GD.N0232.N0720.N1428.d013135
  exact mul_nonneg
    (mul_nonneg (_root_.GD.N0232.N0720.N1428.d013134 hbeta).le hX)
    (Real.rpow_nonneg hbase _)

theorem d013160
    {beta t X : ℝ} (hbeta : 0 < beta) (hX : 0 ≤ X) :
    0 ≤ _root_.GD.N0232.N0720.N1427.d013155 beta t X := by
  unfold _root_.GD.N0232.N0720.N1427.d013155
  exact mul_nonneg (_root_.GD.N0232.N0720.N1427.d013159 hbeta hX) (sq_nonneg _)



theorem d013161
    {beta X : ℝ} (hbeta : 0 < beta) (hX : 0 ≤ X) :
    _root_.GD.N0232.N0720.N1428.d013135 beta X ≤
      _root_.GD.N0232.N0720.N1428.d013133 beta * X := by
  have hden : 0 < beta + 2 * X := by positivity
  have hbase0 : 0 ≤ beta / (beta + 2 * X) :=
    div_nonneg hbeta.le hden.le
  have hbase1 : beta / (beta + 2 * X) ≤ 1 :=
    (div_le_one hden).2 (by linarith)
  have hexp : 0 ≤ beta + 2 := by linarith
  have hpow : (beta / (beta + 2 * X)) ^ (beta + 2) ≤ 1 :=
    Real.rpow_le_one hbase0 hbase1 hexp
  unfold _root_.GD.N0232.N0720.N1428.d013135
  exact mul_le_of_le_one_right
    (mul_nonneg (_root_.GD.N0232.N0720.N1428.d013134 hbeta).le hX) hpow

theorem d013162
    {t X : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hX : X ∈ Icc (0 : ℝ) t) :
    _root_.GD.N0232.N0720.N1428.d013136 t X ∈ Icc (0 : ℝ) (1 / t) := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  have h1X : 0 ≤ 1 - X := by linarith [hX.2]
  have hden : 0 < (1 - t) * X + t :=
    add_pos_of_nonneg_of_pos (mul_nonneg h1t.le hX.1) ht0
  unfold _root_.GD.N0232.N0720.N1428.d013136
  constructor
  · exact div_nonneg (mul_nonneg h1t.le h1X) hden.le
  · rw [div_le_iff₀ hden]
    have hnum_le : (1 - t) * (1 - X) ≤ 1 := by
      nlinarith [mul_nonneg h1t.le hX.1]
    have hden_ge : t ≤ (1 - t) * X + t := by
      nlinarith [mul_nonneg h1t.le hX.1]
    have hone_le : 1 ≤ 1 / t * ((1 - t) * X + t) := by
      rw [show 1 / t * ((1 - t) * X + t) =
          ((1 - t) * X + t) / t by ring]
      apply (le_div_iff₀ ht0).2
      simpa using hden_ge
    exact hnum_le.trans hone_le

theorem d013163
    {beta t X : ℝ} (hbeta : 0 < beta)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hX : X ∈ Icc (0 : ℝ) t) :
    _root_.GD.N0232.N0720.N1427.d013155 beta t X ≤
      _root_.GD.N0232.N0720.N1428.d013133 beta * X / t ^ 2 := by
  have hdensity := _root_.GD.N0232.N0720.N1427.d013161 hbeta hX.1
  have herr := _root_.GD.N0232.N0720.N1427.d013162 ht0 ht1 hX
  have herrSq : _root_.GD.N0232.N0720.N1428.d013136 t X ^ 2 ≤ (1 / t) ^ 2 :=
    (sq_le_sq₀ herr.1 (one_div_nonneg.mpr ht0.le)).2 herr.2
  have hlinear : 0 ≤ _root_.GD.N0232.N0720.N1428.d013133 beta * X :=
    mul_nonneg (_root_.GD.N0232.N0720.N1428.d013134 hbeta).le hX.1
  unfold _root_.GD.N0232.N0720.N1427.d013155
  calc
    _ ≤ (_root_.GD.N0232.N0720.N1428.d013133 beta * X) * (1 / t) ^ 2 :=
      mul_le_mul hdensity herrSq (sq_nonneg _) hlinear
    _ = _root_.GD.N0232.N0720.N1428.d013133 beta * X / t ^ 2 := by
      field_simp [ht0.ne']




theorem d013164
    {beta t : ℝ} (hbeta : 0 < beta) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1427.d013156 beta t ≤ _root_.GD.N0232.N0720.N1428.d013133 beta / 2 := by
  have hmajor : IntervalIntegrable
      (fun X : ℝ => _root_.GD.N0232.N0720.N1428.d013133 beta * X / t ^ 2)
      volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hkernel : IntervalIntegrable
      (_root_.GD.N0232.N0720.N1427.d013155 beta t) volume 0 t := by
    apply hmajor.mono_fun'
    · exact (_root_.GD.N0232.N0720.N1427.d013158 beta t).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with X hX
      have hX' : X ∈ Icc (0 : ℝ) t :=
        by simpa [uIcc_of_le ht0.le] using uIoc_subset_uIcc hX
      have hnonneg :=
        _root_.GD.N0232.N0720.N1427.d013160 (t := t) hbeta hX'.1
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact _root_.GD.N0232.N0720.N1427.d013163 hbeta ht0 ht1 hX'
  unfold _root_.GD.N0232.N0720.N1427.d013156
  calc
    (∫ X : ℝ in (0 : ℝ)..t, _root_.GD.N0232.N0720.N1427.d013155 beta t X) ≤
        ∫ X : ℝ in (0 : ℝ)..t,
          _root_.GD.N0232.N0720.N1428.d013133 beta * X / t ^ 2 := by
      apply intervalIntegral.integral_mono_on ht0.le hkernel hmajor
      intro X hX
      exact _root_.GD.N0232.N0720.N1427.d013163 hbeta ht0 ht1 hX
    _ = _root_.GD.N0232.N0720.N1428.d013133 beta / 2 := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_const_mul,
        integral_id]
      field_simp [ht0.ne']
      ring



theorem d013165
    {t X : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hX : 1 ≤ X) :
    |_root_.GD.N0232.N0720.N1428.d013136 t X| ≤ 1 := by
  have h1t : 0 < 1 - t := sub_pos.mpr ht1
  have hden : 0 < (1 - t) * X + t := by positivity
  have hnum : 0 ≤ (1 - t) * (X - 1) :=
    mul_nonneg h1t.le (sub_nonneg.mpr hX)
  have hquot : (1 - t) * (X - 1) / ((1 - t) * X + t) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  unfold _root_.GD.N0232.N0720.N1428.d013136
  rw [abs_div, abs_of_pos hden, abs_mul, abs_of_pos h1t,
    abs_of_nonpos (by linarith : 1 - X ≤ 0)]
  simpa [show |1 - t| = 1 - t by rw [abs_of_pos h1t]] using hquot

theorem d013166
    {beta t X : ℝ} (hbeta : 0 < beta)
    (ht0 : 0 < t) (ht1 : t < 1)
    (hX : 1 ≤ X) :
    _root_.GD.N0232.N0720.N1427.d013155 beta t X ≤
      _root_.GD.N0232.N0720.N1428.d013135 beta X := by
  have herrAbs := _root_.GD.N0232.N0720.N1427.d013165 ht0 ht1 hX
  have herrSq : _root_.GD.N0232.N0720.N1428.d013136 t X ^ 2 ≤ 1 := by
    have hs := (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 herrAbs
    simpa [sq_abs] using hs
  unfold _root_.GD.N0232.N0720.N1427.d013155
  exact mul_le_of_le_one_right
    (_root_.GD.N0232.N0720.N1427.d013159 hbeta (zero_le_one.trans hX)) herrSq



noncomputable def d013167 (beta X : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1428.d013133 beta * beta ^ (beta + 2) *
    X ^ (-beta - 1)

theorem d013168
    {beta X : ℝ} (hbeta : 0 < beta) (hX : 1 ≤ X) :
    _root_.GD.N0232.N0720.N1428.d013135 beta X ≤
      _root_.GD.N0232.N0720.N1427.d013167 beta X := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hden : 0 < beta + 2 * X := by positivity
  have hbase0 : 0 ≤ beta / (beta + 2 * X) :=
    div_nonneg hbeta.le hden.le
  have hbase_le : beta / (beta + 2 * X) ≤ beta / X := by
    gcongr
    linarith
  have hexp : 0 ≤ beta + 2 := by linarith
  have hpow :
      (beta / (beta + 2 * X)) ^ (beta + 2) ≤
        (beta / X) ^ (beta + 2) :=
    Real.rpow_le_rpow hbase0 hbase_le hexp
  have hpow_eq :
      (beta / X) ^ (beta + 2) =
        beta ^ (beta + 2) * X ^ (-(beta + 2)) := by
    rw [Real.div_rpow hbeta.le hX0.le, div_eq_mul_inv,
      ← Real.rpow_neg hX0.le]
  have hcollect : X * X ^ (-(beta + 2)) = X ^ (-beta - 1) := by
    calc
      X * X ^ (-(beta + 2)) = X ^ (1 : ℝ) * X ^ (-(beta + 2)) := by
        rw [Real.rpow_one]
      _ = X ^ ((1 : ℝ) + -(beta + 2)) :=
        (Real.rpow_add hX0 1 (-(beta + 2))).symm
      _ = X ^ (-beta - 1) := by ring_nf
  unfold _root_.GD.N0232.N0720.N1428.d013135 _root_.GD.N0232.N0720.N1427.d013167
  calc
    _root_.GD.N0232.N0720.N1428.d013133 beta * X *
          (beta / (beta + 2 * X)) ^ (beta + 2) ≤
        _root_.GD.N0232.N0720.N1428.d013133 beta * X *
          (beta / X) ^ (beta + 2) := by
      exact mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (_root_.GD.N0232.N0720.N1428.d013134 hbeta).le hX0.le)
    _ = _root_.GD.N0232.N0720.N1428.d013133 beta * beta ^ (beta + 2) *
          X ^ (-beta - 1) := by rw [hpow_eq, ← hcollect]; ring

theorem d013169
    {beta : ℝ} (hbeta : 0 < beta) :
    IntegrableOn (_root_.GD.N0232.N0720.N1427.d013167 beta) (Ioi (1 : ℝ)) := by
  unfold _root_.GD.N0232.N0720.N1427.d013167
  exact (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _

theorem d013170
    {beta : ℝ} (hbeta : 0 < beta) :
    (∫ X : ℝ in Ioi (1 : ℝ), _root_.GD.N0232.N0720.N1427.d013167 beta X) =
      _root_.GD.N0232.N0720.N1428.d013133 beta * beta ^ (beta + 2) / beta := by
  unfold _root_.GD.N0232.N0720.N1427.d013167
  rw [integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith : -beta - 1 < -(1 : ℝ)) zero_lt_one]
  rw [Real.one_rpow]
  field_simp [hbeta.ne']
  ring

theorem d013171
    {beta t : ℝ} (hbeta : 0 < beta) (ht0 : 0 < t) (ht1 : t < 1) :
    IntegrableOn (_root_.GD.N0232.N0720.N1427.d013155 beta t) (Ioi (1 : ℝ)) := by
  apply (_root_.GD.N0232.N0720.N1427.d013169 hbeta).mono_nonneg
  · exact (_root_.GD.N0232.N0720.N1427.d013158 beta t).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    exact _root_.GD.N0232.N0720.N1427.d013160 hbeta (zero_le_one.trans hX.le)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
    exact (_root_.GD.N0232.N0720.N1427.d013166 hbeta ht0 ht1 hX.le).trans
      (_root_.GD.N0232.N0720.N1427.d013168 hbeta hX.le)



theorem d013172
    {beta t : ℝ} (hbeta : 0 < beta) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1427.d013157 beta t ≤
      _root_.GD.N0232.N0720.N1428.d013133 beta * beta ^ (beta + 2) / beta := by
  unfold _root_.GD.N0232.N0720.N1427.d013157
  calc
    (∫ X : ℝ in Ioi (1 : ℝ), _root_.GD.N0232.N0720.N1427.d013155 beta t X) ≤
        ∫ X : ℝ in Ioi (1 : ℝ), _root_.GD.N0232.N0720.N1427.d013167 beta X := by
      apply setIntegral_mono_on
      · exact _root_.GD.N0232.N0720.N1427.d013171 hbeta ht0 ht1
      · exact _root_.GD.N0232.N0720.N1427.d013169 hbeta
      · exact measurableSet_Ioi
      · intro X hX
        exact (_root_.GD.N0232.N0720.N1427.d013166 hbeta ht0 ht1 hX.le).trans
          (_root_.GD.N0232.N0720.N1427.d013168 hbeta hX.le)
    _ = _ := _root_.GD.N0232.N0720.N1427.d013170 hbeta

end

end N1427
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1427.d013163
#print axioms _root_.GD.N0232.N0720.N1427.d013166
#print axioms _root_.GD.N0232.N0720.N1427.d013164
#print axioms _root_.GD.N0232.N0720.N1427.d013172
