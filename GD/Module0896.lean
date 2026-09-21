import GD.Module0895
import Mathlib.MeasureTheory.Integral.Lebesgue.Map



































open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1488

noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1487





def d013925 :
    Measure _root_.GD.N0232.N0720.N1436.d013217 :=
  (volume.restrict (Ioo (0 : ℝ) 1)).prod
    (volume.restrict (Ioi (0 : ℝ)))


def d013926
    (t : ℝ) (p : _root_.GD.N0232.N0720.N1436.d013217) : _root_.GD.N0232.N0720.N1436.d013217 :=
  (p.1, p.1 * p.2 / t)



def d013927
    (t : ℝ) (p : _root_.GD.N0232.N0720.N1436.d013217) : ℝ≥0∞ :=
  ENNReal.ofReal p.1 *
    ENNReal.ofReal
      (_root_.GD.N0232.N0720.N1487.d013903 t p.1 (p.1 * p.2))

@[fun_prop]
theorem d013928 (t : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1488.d013926 t) := by
  unfold _root_.GD.N0232.N0720.N1488.d013926
  exact measurable_fst.prodMk
    ((measurable_fst.mul measurable_snd).div_const t)

@[fun_prop]
theorem d013929 (t : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1488.d013927 t) := by
  unfold _root_.GD.N0232.N0720.N1488.d013927
  have hpair : Measurable
      (fun p : _root_.GD.N0232.N0720.N1436.d013217 ↦ (p.1, p.1 * p.2)) :=
    measurable_fst.prodMk (measurable_fst.mul measurable_snd)
  exact measurable_fst.ennreal_ofReal.mul
    ((_root_.GD.N0232.N0720.N1487.d013907 t).comp hpair).ennreal_ofReal




theorem d013930 :
    _root_.GD.N0232.N0720.N1436.d013288 =
      _root_.GD.N0232.N0720.N1488.d013925 := by
  unfold _root_.GD.N0232.N0720.N1436.d013288 _root_.GD.N0232.N0720.N1436.d013218
    _root_.GD.N0232.N0720.N1488.d013925
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]





theorem d013931
    (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    {b : ℝ} (hb : 0 < b) :
    (∫⁻ x in Ioi (0 : ℝ), g (b * x)) =
      ENNReal.ofReal b⁻¹ * ∫⁻ y in Ioi (0 : ℝ), g y := by
  let m : ℝ → ℝ := fun x ↦ b * x
  have hm : Measurable m := measurable_const_mul b
  have hpre : m ⁻¹' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    simpa [m] using
      (preimage_const_mul_Ioi₀ (0 : ℝ) hb)
  have hmap : Measure.map m (volume.restrict (Ioi (0 : ℝ))) =
      ENNReal.ofReal b⁻¹ • volume.restrict (Ioi (0 : ℝ)) := by
    calc
      Measure.map m (volume.restrict (Ioi (0 : ℝ))) =
          Measure.map m (volume.restrict (m ⁻¹' Ioi (0 : ℝ))) := by
            rw [hpre]
      _ = (Measure.map m volume).restrict (Ioi (0 : ℝ)) := by
        exact (Measure.restrict_map (μ := volume) hm measurableSet_Ioi).symm
      _ = (ENNReal.ofReal |b⁻¹| • volume).restrict (Ioi (0 : ℝ)) := by
        rw [show m = (fun x : ℝ ↦ b * x) by rfl,
          Real.map_volume_mul_left hb.ne']
      _ = ENNReal.ofReal b⁻¹ • volume.restrict (Ioi (0 : ℝ)) := by
        rw [Measure.restrict_smul, abs_of_pos (inv_pos.mpr hb)]
  calc
    (∫⁻ x in Ioi (0 : ℝ), g (b * x)) =
        ∫⁻ x, g (m x) ∂volume.restrict (Ioi (0 : ℝ)) := by
      rfl
    _ = ∫⁻ y, g y ∂Measure.map m (volume.restrict (Ioi (0 : ℝ))) := by
      exact (lintegral_map hg hm).symm
    _ = ∫⁻ y, g y
        ∂(ENNReal.ofReal b⁻¹ • volume.restrict (Ioi (0 : ℝ))) := by
      rw [hmap]
    _ = ENNReal.ofReal b⁻¹ *
        ∫⁻ y in Ioi (0 : ℝ), g y := by
      simp only [lintegral_smul_measure, smul_eq_mul]



theorem d013932
    (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    {b : ℝ} (hb : 0 < b) :
    (∫⁻ y in Ioi (0 : ℝ), g y) =
      ENNReal.ofReal b * ∫⁻ x in Ioi (0 : ℝ), g (b * x) := by
  have hscale := _root_.GD.N0232.N0720.N1488.d013931 g hg hb
  have hb0 : ENNReal.ofReal b ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hb
  have hbtop : ENNReal.ofReal b ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    (∫⁻ y in Ioi (0 : ℝ), g y) =
        (ENNReal.ofReal b * (ENNReal.ofReal b)⁻¹) *
          ∫⁻ y in Ioi (0 : ℝ), g y := by
      rw [ENNReal.mul_inv_cancel hb0 hbtop, one_mul]
    _ = ENNReal.ofReal b *
        (ENNReal.ofReal b⁻¹ * ∫⁻ y in Ioi (0 : ℝ), g y) := by
      rw [ENNReal.ofReal_inv_of_pos hb, mul_assoc]
    _ = ENNReal.ofReal b *
        ∫⁻ x in Ioi (0 : ℝ), g (b * x) := by
      rw [← hscale]





theorem d013933
    {t r S : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hS : 0 < S) :
    (1 / t) * _root_.GD.N0232.N0720.N1436.d013273 2 2 t (r, S / t) =
      Real.sqrt t * _root_.GD.N0232.N0720.N1487.d013903 t r S := by
  have hdensity :=
    _root_.GD.N0232.N0720.N1487.d013919
      ht0 ht1 hr hS
  have hsqrt : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht0).ne'
  have htHalf : t ^ (1 / 2 : ℝ) = Real.sqrt t := by
    exact (Real.sqrt_eq_rpow t).symm
  have hinvHalf : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg ht0.le, htHalf]
  rw [hinvHalf] at hdensity
  calc
    (1 / t) * _root_.GD.N0232.N0720.N1436.d013273 2 2 t (r, S / t) =
        Real.sqrt t * ((Real.sqrt t)⁻¹ *
          ((1 / t) * _root_.GD.N0232.N0720.N1436.d013273 2 2 t (r, S / t))) := by
      field_simp [hsqrt]
    _ = Real.sqrt t * _root_.GD.N0232.N0720.N1487.d013903 t r S := by
      congr 1
      simpa [mul_assoc] using hdensity


theorem d013934
    {t r S : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hS : 0 < S) :
    ENNReal.ofReal (1 / t) *
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (r, S / t)) =
      ENNReal.ofReal (Real.sqrt t) *
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1487.d013903 t r S) := by
  rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr ht0.le),
    _root_.GD.N0232.N0720.N1488.d013933
      ht0 ht1 hr hS,
    ENNReal.ofReal_mul (Real.sqrt_nonneg t)]




theorem d013935
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p, g p ∂_root_.GD.N0232.N0720.N1436.d013288) =
      ∫⁻ r in Ioo (0 : ℝ) 1,
        ∫⁻ s in Ioi (0 : ℝ), g (r, s) := by
  rw [_root_.GD.N0232.N0720.N1488.d013930]
  unfold _root_.GD.N0232.N0720.N1488.d013925
  exact lintegral_prod g hg.aemeasurable





theorem d013936
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) =
      ENNReal.ofReal (Real.sqrt t) *
        ∫⁻ p,
          _root_.GD.N0232.N0720.N1488.d013927 t p *
            f (_root_.GD.N0232.N0720.N1488.d013926 t p)
          ∂_root_.GD.N0232.N0720.N1488.d013925 := by
  have hpdf : Measurable
      (fun p : _root_.GD.N0232.N0720.N1436.d013217 ↦
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t p)) :=
    (_root_.GD.N0232.N0720.N1436.d013279 2 2 t).ennreal_ofReal
  have hweighted : Measurable
      (fun p : _root_.GD.N0232.N0720.N1436.d013217 ↦
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t p) * f p) :=
    hpdf.mul hf
  have hratioIntegrand : Measurable
      (fun p : _root_.GD.N0232.N0720.N1436.d013217 ↦
        _root_.GD.N0232.N0720.N1488.d013927 t p *
          f (_root_.GD.N0232.N0720.N1488.d013926 t p)) :=
    (_root_.GD.N0232.N0720.N1488.d013929 t).mul
      (hf.comp (_root_.GD.N0232.N0720.N1488.d013928 t))
  have hsqrtTop : ENNReal.ofReal (Real.sqrt t) ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    (∫⁻ p, f p ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) =
        ∫⁻ p,
          ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t p) * f p
          ∂_root_.GD.N0232.N0720.N1436.d013288 := by
      unfold _root_.GD.N0232.N0720.N1436.d013289
      rw [lintegral_withDensity_eq_lintegral_mul _ hpdf hf]
      simp only [Pi.mul_apply]
    _ = ∫⁻ r in Ioo (0 : ℝ) 1,
          ∫⁻ F in Ioi (0 : ℝ),
            ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (r, F)) *
              f (r, F) := by
      exact _root_.GD.N0232.N0720.N1488.d013935 _ hweighted
    _ = ∫⁻ r in Ioo (0 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt t) *
            ∫⁻ S in Ioi (0 : ℝ),
              ENNReal.ofReal (_root_.GD.N0232.N0720.N1487.d013903 t r S) *
                f (r, S / t) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      let g : ℝ → ℝ≥0∞ := fun S ↦
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (r, S / t)) *
          f (r, S / t)
      have hchart : Measurable (fun S : ℝ ↦ (r, S / t)) :=
        measurable_const.prodMk (measurable_id.div_const t)
      have hg : Measurable g := by
        unfold g
        exact (hpdf.comp hchart).mul (hf.comp hchart)
      have hscale := _root_.GD.N0232.N0720.N1488.d013931 g hg ht0
      have hinv : t⁻¹ = 1 / t := by simp [div_eq_mul_inv]
      calc
        (∫⁻ F in Ioi (0 : ℝ),
            ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (r, F)) *
              f (r, F)) =
            ∫⁻ F in Ioi (0 : ℝ), g (t * F) := by
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro F _hF
          simp only [g]
          rw [mul_div_cancel_left₀ F ht0.ne']
        _ = ENNReal.ofReal t⁻¹ *
            ∫⁻ S in Ioi (0 : ℝ), g S := hscale
        _ = ENNReal.ofReal (1 / t) *
            ∫⁻ S in Ioi (0 : ℝ),
              ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (r, S / t)) *
                f (r, S / t) := by
          rw [hinv]
        _ = ∫⁻ S in Ioi (0 : ℝ),
            ENNReal.ofReal (1 / t) *
              (ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (r, S / t)) *
                f (r, S / t)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ∫⁻ S in Ioi (0 : ℝ),
            ENNReal.ofReal (Real.sqrt t) *
              (ENNReal.ofReal (_root_.GD.N0232.N0720.N1487.d013903 t r S) *
                f (r, S / t)) := by
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro S hS
          have hdensity :=
            _root_.GD.N0232.N0720.N1488.d013934
              ht0 ht1 hr hS
          calc
            ENNReal.ofReal (1 / t) *
                (ENNReal.ofReal
                    (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (r, S / t)) *
                  f (r, S / t)) =
                (ENNReal.ofReal (1 / t) *
                  ENNReal.ofReal
                    (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (r, S / t))) *
                  f (r, S / t) := by rw [mul_assoc]
            _ = (ENNReal.ofReal (Real.sqrt t) *
                  ENNReal.ofReal (_root_.GD.N0232.N0720.N1487.d013903 t r S)) *
                  f (r, S / t) := by rw [hdensity]
            _ = ENNReal.ofReal (Real.sqrt t) *
                (ENNReal.ofReal (_root_.GD.N0232.N0720.N1487.d013903 t r S) *
                  f (r, S / t)) := by rw [mul_assoc]
        _ = ENNReal.ofReal (Real.sqrt t) *
            ∫⁻ S in Ioi (0 : ℝ),
              ENNReal.ofReal (_root_.GD.N0232.N0720.N1487.d013903 t r S) *
                f (r, S / t) := by
          rw [lintegral_const_mul' _ _ hsqrtTop]
    _ = ENNReal.ofReal (Real.sqrt t) *
        ∫⁻ r in Ioo (0 : ℝ) 1,
          ∫⁻ S in Ioi (0 : ℝ),
            ENNReal.ofReal (_root_.GD.N0232.N0720.N1487.d013903 t r S) *
              f (r, S / t) := by
      rw [lintegral_const_mul' _ _ hsqrtTop]
    _ = ENNReal.ofReal (Real.sqrt t) *
        ∫⁻ r in Ioo (0 : ℝ) 1,
          ∫⁻ x in Ioi (0 : ℝ),
            _root_.GD.N0232.N0720.N1488.d013927 t (r, x) *
              f (_root_.GD.N0232.N0720.N1488.d013926 t (r, x)) := by
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      let g : ℝ → ℝ≥0∞ := fun S ↦
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1487.d013903 t r S) *
          f (r, S / t)
      have hchartDensity : Measurable (fun S : ℝ ↦ (r, S)) :=
        measurable_const.prodMk measurable_id
      have hchartObservation : Measurable (fun S : ℝ ↦ (r, S / t)) :=
        measurable_const.prodMk (measurable_id.div_const t)
      have hg : Measurable g := by
        unfold g
        exact (((_root_.GD.N0232.N0720.N1487.d013907 t).comp
          hchartDensity).ennreal_ofReal).mul (hf.comp hchartObservation)
      calc
        (∫⁻ S in Ioi (0 : ℝ),
            ENNReal.ofReal (_root_.GD.N0232.N0720.N1487.d013903 t r S) *
              f (r, S / t)) =
            ENNReal.ofReal r * ∫⁻ x in Ioi (0 : ℝ), g (r * x) := by
          exact _root_.GD.N0232.N0720.N1488.d013932
            g hg hr.1
        _ = ∫⁻ x in Ioi (0 : ℝ),
            ENNReal.ofReal r * g (r * x) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ = ∫⁻ x in Ioi (0 : ℝ),
            _root_.GD.N0232.N0720.N1488.d013927 t (r, x) *
              f (_root_.GD.N0232.N0720.N1488.d013926 t (r, x)) := by
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro x _hx
          simp only [g, _root_.GD.N0232.N0720.N1488.d013927,
            _root_.GD.N0232.N0720.N1488.d013926, mul_assoc]
    _ = ENNReal.ofReal (Real.sqrt t) *
        ∫⁻ p,
          _root_.GD.N0232.N0720.N1488.d013927 t p *
            f (_root_.GD.N0232.N0720.N1488.d013926 t p)
          ∂_root_.GD.N0232.N0720.N1488.d013925 := by
      congr 1
      unfold _root_.GD.N0232.N0720.N1488.d013925
      exact (lintegral_prod _ hratioIntegrand.aemeasurable).symm

end

end N1488
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1488.d013936
