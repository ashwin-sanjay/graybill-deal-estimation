import GD.Module1018
import GD.Module0896
import Mathlib.Tactic











open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0232.N0720.N1234

noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1242
open _root_.GD.N0232.N0720.N1236
open _root_.GD.N0232.N0720.N1488

private abbrev d016222 : ℝ := (1 : ℝ) / 2



theorem d016223
    {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn (_root_.GD.N0232.N0720.N1236.d016211 t u) (Ioi (0 : ℝ)) := by
  let a := _root_.GD.N0232.N0720.N1242.d002130 t u
  let b := _root_.GD.N0232.N0720.N1236.d016210 t
  let C :=
    (3 / (2 * Real.pi) * u ^ (-_root_.GD.N0232.N0720.N1234.d016222) * (1 - u) ^ (-_root_.GD.N0232.N0720.N1234.d016222) * b ^ 2)
  have ha : 0 < a := _root_.GD.N0232.N0720.N1242.d002132 ht hu
  have hb : 0 < b := mul_pos ht.1 (sub_pos.mpr ht.2)
  have hscaled := (_root_.GD.N0232.N0720.N1236.d016216 ha hb).const_mul C
  apply IntegrableOn.congr_fun hscaled _ measurableSet_Ioi
  intro v hv
  unfold _root_.GD.N0232.N0720.N1236.d016211 _root_.GD.N0232.N0720.N1236.d016213 C a b
  ring

theorem d016224
    {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn
      (fun v : ℝ ↦ _root_.GD.N0232.N0720.N1436.d013273 2 2 t (u, v))
      (Ioi (0 : ℝ)) := by
  apply (_root_.GD.N0232.N0720.N1234.d016223 ht hu).congr_fun _
    measurableSet_Ioi
  intro v hv
  exact (_root_.GD.N0232.N0720.N1236.d016218
    ht hu hv).symm

theorem d016225
    {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫⁻ v : ℝ in Ioi 0,
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (u, v))) =
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1236.d016212 t u) := by
  have hint := _root_.GD.N0232.N0720.N1234.d016224 ht hu
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun v : ℝ ↦ _root_.GD.N0232.N0720.N1436.d013273 2 2 t (u, v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (_root_.GD.N0232.N0720.N1436.d013286 (m := 2) (n := 2)
      (by omega) (by omega) ht.1 ht.2 ⟨hu, hv⟩).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  congr 1
  calc
    (∫ v : ℝ in Ioi 0, _root_.GD.N0232.N0720.N1436.d013273 2 2 t (u, v)) =
        ∫ v : ℝ in Ioi 0, _root_.GD.N0232.N0720.N1236.d016211 t u v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      exact _root_.GD.N0232.N0720.N1236.d016218 ht hu hv
    _ = _root_.GD.N0232.N0720.N1236.d016212 t u :=
      _root_.GD.N0232.N0720.N1236.d016219 ht hu



theorem d016226
    {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    ENNReal.ofReal (_root_.GD.N0232.N0720.N1236.d016212 t u) =
      ENNReal.ofReal (betaPDFReal (1 / 2 : ℝ) (1 / 2) u) *
        ENNReal.ofReal
          (Real.sqrt (t * (1 - t)) / _root_.GD.N0232.N0720.N1242.d002130 t u) := by
  have hub : 0 < u * (1 - u) := mul_pos hu.1 (sub_pos.mpr hu.2)
  have hbase : 0 < Real.pi * Real.sqrt (u * (1 - u)) :=
    mul_pos Real.pi_pos (Real.sqrt_pos.2 hub)
  rw [_root_.GD.N0232.N0720.N1242.d002142 hu]
  rw [← ENNReal.ofReal_mul (one_div_pos.mpr hbase).le]
  congr 1
  rw [_root_.GD.N0232.N0720.N1236.d016220 ht hu]
  field_simp [hbase.ne', (_root_.GD.N0232.N0720.N1242.d002132 ht hu).ne']

theorem d016227
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u, F u ∂_root_.GD.N0232.N0720.N1242.d002143 t) =
      ∫⁻ u : ℝ in Ioo 0 1,
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1236.d016212 t u) * F u := by
  let likelihood : ℝ → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (Real.sqrt (t * (1 - t)) / _root_.GD.N0232.N0720.N1242.d002130 t u)
  have hlike : Measurable likelihood := by
    unfold likelihood _root_.GD.N0232.N0720.N1242.d002130
    fun_prop
  have hbeta : Measurable (fun u : ℝ =>
      ENNReal.ofReal (betaPDFReal (1 / 2 : ℝ) (1 / 2) u)) :=
    (measurable_betaPDFReal (1 / 2 : ℝ) (1 / 2)).ennreal_ofReal
  unfold _root_.GD.N0232.N0720.N1242.d002143 _root_.GD.N0232.N0720.N1242.d002139 ProbabilityTheory.betaMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ hlike hF]
  change (∫⁻ a : ℝ, likelihood a * F a ∂
      volume.withDensity (fun u =>
        ENNReal.ofReal (betaPDFReal (1 / 2 : ℝ) (1 / 2) u))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hbeta (hlike.mul hF)]
  simp only [Pi.mul_apply]
  have hrestrict :
      (∫⁻ u : ℝ,
          ENNReal.ofReal (betaPDFReal (1 / 2 : ℝ) (1 / 2) u) *
            (likelihood u * F u)) =
        ∫⁻ u : ℝ in Ioo 0 1,
          ENNReal.ofReal (betaPDFReal (1 / 2 : ℝ) (1 / 2) u) *
            (likelihood u * F u) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro u
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · simp [Set.indicator, hu]
    · have hout : ¬ (0 < u ∧ u < 1) := by
        simpa only [mem_Ioo] using hu
      simp [Set.indicator, hu, betaPDFReal, hout]
  rw [hrestrict]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro u hu
  change ENNReal.ofReal (betaPDFReal (1 / 2 : ℝ) (1 / 2) u) *
      (likelihood u * F u) =
    ENNReal.ofReal (_root_.GD.N0232.N0720.N1236.d016212 t u) * F u
  rw [_root_.GD.N0232.N0720.N1234.d016226 ht hu]
  simp only [likelihood]
  ac_rfl




theorem d016228
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p.1 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) =
      ∫⁻ u, F u ∂_root_.GD.N0232.N0720.N1242.d002143 t := by
  have hpdf : Measurable (fun p : _root_.GD.N0232.N0720.N1436.d013217 =>
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t p)) :=
    (_root_.GD.N0232.N0720.N1436.d013279 2 2 t).ennreal_ofReal
  have htest : Measurable (fun p : _root_.GD.N0232.N0720.N1436.d013217 => F p.1) :=
    hF.comp measurable_fst
  calc
    (∫⁻ p, F p.1 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) =
        ∫⁻ p,
          ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t p) * F p.1
          ∂_root_.GD.N0232.N0720.N1436.d013288 := by
      unfold _root_.GD.N0232.N0720.N1436.d013289
      rw [lintegral_withDensity_eq_lintegral_mul _ hpdf htest]
      rfl
    _ = ∫⁻ u : ℝ in Ioo 0 1,
          ∫⁻ v : ℝ in Ioi 0,
            ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (u, v)) *
              F u := by
      exact _root_.GD.N0232.N0720.N1488.d013935 _
        (hpdf.mul htest)
    _ = ∫⁻ u : ℝ in Ioo 0 1,
          ENNReal.ofReal (_root_.GD.N0232.N0720.N1236.d016212 t u) * F u := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro u hu
      have hsection : Measurable (fun v : ℝ =>
          ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (u, v))) :=
        hpdf.comp (measurable_const.prodMk measurable_id)
      change (∫⁻ v : ℝ in Ioi 0,
          ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (u, v)) * F u) =
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1236.d016212 t u) * F u
      rw [lintegral_mul_const'' _ hsection.aemeasurable]
      rw [_root_.GD.N0232.N0720.N1234.d016225 ht hu]
    _ = ∫⁻ u, F u ∂_root_.GD.N0232.N0720.N1242.d002143 t :=
      (_root_.GD.N0232.N0720.N1234.d016227 ht F hF).symm

end

end GD.N0232.N0720.N1234

#print axioms _root_.GD.N0232.N0720.N1234.d016225
