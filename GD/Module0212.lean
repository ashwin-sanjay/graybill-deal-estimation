import GD.Module0207
import GD.Module0211
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation







open Set Filter MeasureTheory
open scoped Topology

namespace GD.N0232.N0720.N1375

open _root_.GD.N0232.N0720.N1377 _root_.GD.N0232.N0720.N1374
open _root_.GD.N0232.N0720.N1380 _root_.GD.N0232.N0720.N1376

noncomputable section


theorem d002934 (n : ℕ)
    {A Amin B beta loss : ℝ} (hAmin : 0 < Amin) (hA : Amin ≤ A)
    (hloss : 1 < loss) (hrate : B ^ 2 / (2 * A) ≤ beta) (kappa : ℝ) :
    _root_.GD.N0232.N0720.N1377.d002852 n A (B * kappa) ≤
      Real.exp (loss * beta * kappa ^ 2) *
        _root_.GD.N0232.N0720.N1377.d002852 n (Amin * (loss - 1) / loss) 0 := by
  have hApos : 0 < A := hAmin.trans_le hA
  have hlosspos : 0 < loss := lt_trans zero_lt_one hloss
  have hlo : 0 < Amin * (loss - 1) / loss := by positivity
  have hhi : 0 < A * (loss - 1) / loss := by positivity
  have hred : Amin * (loss - 1) / loss ≤ A * (loss - 1) / loss := by
    gcongr
  have hmoment := _root_.GD.N0232.N0720.N1380.d002920 n hlo hhi hred (le_refl (0 : ℝ))
  have hexponent : loss * (B * kappa) ^ 2 / (2 * A) ≤ loss * beta * kappa ^ 2 := by
    calc
      loss * (B * kappa) ^ 2 / (2 * A) =
          (loss * (B ^ 2 / (2 * A))) * kappa ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrate hlosspos.le) (sq_nonneg kappa)
  exact (_root_.GD.N0232.N0720.N1374.d002868 n hApos hloss (B * kappa)).trans
    (mul_le_mul (Real.exp_le_exp.mpr hexponent) hmoment
      (_root_.GD.N0232.N0720.N1377.d002861 n hhi 0).le (Real.exp_pos _).le)

def d002935 (Amax Bmin : ℝ) : ℝ :=
  (Bmin / Amax) ^ 5 * Real.exp (-Amax / 2) / 8

theorem d002936 {Amax Bmin : ℝ}
    (hAmax : 0 < Amax) (hBmin : 0 < Bmin) :
    0 < _root_.GD.N0232.N0720.N1375.d002935 Amax Bmin := by
  unfold _root_.GD.N0232.N0720.N1375.d002935
  positivity


theorem d002937 {A Amax B Bmin beta kappa : ℝ}
    (hA : 0 < A) (hAupper : A ≤ Amax)
    (hBmin : 0 < Bmin) (hBlower : Bmin ≤ B)
    (hkappa : 1 ≤ kappa) (hrate : beta ≤ B ^ 2 / (2 * A)) :
    _root_.GD.N0232.N0720.N1375.d002935 Amax Bmin * Real.exp (beta * kappa ^ 2) ≤
      _root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) / 8 := by
  have hAmax : 0 < Amax := hA.trans_le hAupper
  have hB : 0 < B := hBmin.trans_le hBlower
  have hk : 0 ≤ kappa := le_trans zero_le_one hkappa
  have hBk : B ≤ B * kappa := by
    nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hkappa)]
  have hcenter : Bmin / Amax ≤ B * kappa / A := by
    apply (div_le_div_iff₀ hAmax hA).2
    calc
      Bmin * A ≤ Bmin * Amax := mul_le_mul_of_nonneg_left hAupper hBmin.le
      _ ≤ B * Amax := mul_le_mul_of_nonneg_right hBlower hAmax.le
      _ ≤ (B * kappa) * Amax := mul_le_mul_of_nonneg_right hBk hAmax.le
  have hbase : 0 ≤ Bmin / Amax := div_nonneg hBmin.le hAmax.le
  have hrate' : beta * kappa ^ 2 ≤ (B * kappa) ^ 2 / (2 * A) := by
    calc
      beta * kappa ^ 2 ≤ (B ^ 2 / (2 * A)) * kappa ^ 2 :=
        mul_le_mul_of_nonneg_right hrate (sq_nonneg kappa)
      _ = _ := by ring
  have hexponent : beta * kappa ^ 2 - Amax / 2 ≤
      (B * kappa) ^ 2 / (2 * A) - A / 2 := by linarith
  have hproduct := mul_le_mul
    (pow_le_pow_left₀ hbase hcenter 5) (Real.exp_le_exp.mpr hexponent)
    (Real.exp_pos _).le (pow_nonneg (div_nonneg (mul_nonneg hB.le hk) hA.le) 5)
  have hlower := hproduct.trans
    (_root_.GD.N0232.N0720.N1374.d002870 5 hA (mul_nonneg hB.le hk))
  have h := div_le_div_of_nonneg_right hlower (by norm_num : (0 : ℝ) ≤ 8)
  convert! h using 1
  simp only [_root_.GD.N0232.N0720.N1375.d002935, sub_eq_add_neg, Real.exp_add, neg_div]
  ring


theorem d002938
    {A Amax B Bmin beta kappa level delta : ℝ}
    (hA : 0 < A) (hAupper : A ≤ Amax)
    (hBmin : 0 < Bmin) (hBlower : Bmin ≤ B)
    (hkappa : 1 ≤ kappa) (hdelta : 0 ≤ delta)
    (hrate : beta ≤ B ^ 2 / (2 * A)) (hgeometry : level + delta ≤ A / B)
    (hcutoff : 8 * Amax ^ 2 ≤ delta * Bmin ^ 3 * kappa ^ 2) :
    delta / 2 * _root_.GD.N0232.N0720.N1375.d002935 Amax Bmin * Real.exp (beta * kappa ^ 2) ≤
      kappa * _root_.GD.N0232.N0720.N1377.d002852 4 A (B * kappa) / 8 -
        level * (_root_.GD.N0232.N0720.N1377.d002852 5 A (B * kappa) / 8) := by
  have h := mul_le_mul_of_nonneg_left
    (_root_.GD.N0232.N0720.N1375.d002937 hA hAupper hBmin hBlower hkappa hrate)
    (by positivity : 0 ≤ delta / 2)
  rw [← mul_assoc] at h
  exact h.trans (_root_.GD.N0232.N0720.N1380.d002931 hA hAupper hBmin hBlower
    (lt_of_lt_of_le zero_lt_one hkappa) hgeometry hcutoff)


theorem d002939 (n : ℕ) {inner outer : ℝ} (hgap : inner < outer) :
    Tendsto (fun kappa : ℝ ↦
      |kappa| ^ n * Real.exp (inner * kappa ^ 2) / Real.exp (outer * kappa ^ 2))
      (cocompact ℝ) (𝓝 0) := by
  have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (sub_pos.mpr hgap) (n : ℝ)
  convert! h using 1
  funext kappa
  rw [Real.rpow_natCast, div_eq_mul_inv, ← Real.exp_neg]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

end
end GD.N0232.N0720.N1375
