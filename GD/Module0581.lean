import GD.Module0580
import GD.Module0494



















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1642
noncomputable section

open MeasureTheory Set Complex Metric Filter
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1530 _root_.GD.N0106.N0428.N0765.N1532
open _root_.GD.N0106.N0428.N0765.N1658
open scoped Topology

def d008471 (F : ℂ → ℝ → ℂ) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  F ((p.1 : ℂ) + z) p.2

theorem d008472 (F : ℂ → ℝ → ℂ) (z : ℂ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1642.d008471 F z p = _root_.GD.N0106.N0428.N0765.N1658.d008462 F z.im (p + (z.re, 0)) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1642.d008471, _root_.GD.N0106.N0428.N0765.N1658.d008462, Prod.fst_add, Prod.snd_add, add_zero, _root_.GD.N0106.N0428.N0765.N1530.d005194]
    using _root_.GD.N0106.N0428.N0765.N1530.d005198 (fun w : ℂ => F w p.2) z p.1

theorem d008473 {F : ℂ → ℝ → ℂ} {z : ℂ}
    (hF : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F z.im) (volume.prod volume)) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1642.d008471 F z) (volume.prod volume) := by
  change Integrable (fun p => _root_.GD.N0106.N0428.N0765.N1642.d008471 F z p) (volume.prod volume)
  simp_rw [_root_.GD.N0106.N0428.N0765.N1642.d008472]
  exact hF.comp_add_right (z.re, 0)

theorem d008474 (F : ℂ → ℝ → ℂ) (z : ℂ) :
    (∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1642.d008471 F z p‖ ∂(volume.prod volume)) = _root_.GD.N0106.N0428.N0765.N1658.d008463 F z.im := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1642.d008472]
  exact integral_add_right_eq_self (fun p : ℝ × ℝ => ‖_root_.GD.N0106.N0428.N0765.N1658.d008462 F z.im p‖) (z.re, 0)

def d008475 (F : ℂ → ℝ → ℂ) (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1532.d007583 (fun z : ℂ => F z p.2) R p.1

theorem d008476 (F : ℂ → ℝ → ℂ) (R : ℝ) (p : ℝ × ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1642.d008475 F R p := _root_.GD.N0106.N0428.N0765.N1532.d007584 _ _ _



theorem d008477 {F : ℂ → ℝ → ℂ} {d R B : ℝ}
    (hR : 0 ≤ R) (hRd : R ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ (univ : Set ℝ)))
    (hslice : ∀ y : ℝ, |y| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y) (volume.prod volume) ∧ _root_.GD.N0106.N0428.N0765.N1658.d008463 F y ≤ B) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1642.d008475 F R) (volume.prod volume) ∧
      (∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1642.d008475 F R p ∂(volume.prod volume)) ≤ B := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  let H : ℝ × (ℝ × ℝ) → ℝ := fun p => ‖_root_.GD.N0106.N0428.N0765.N1642.d008471 F (circleMap 0 R p.1) p.2‖
  have hheight (θ : ℝ) : |(circleMap 0 R θ).im| ≤ R :=
    (Complex.abs_im_le_norm _).trans_eq
      (by simp only [norm_circleMap_zero, abs_of_nonneg hR])
  have hH : Continuous H := by
    change Continuous (fun p : ℝ × (ℝ × ℝ) =>
      ‖F ((p.2.1 : ℂ) + circleMap 0 R p.1) p.2.2‖)
    apply Continuous.norm
    change Continuous ((Function.uncurry F) ∘
      (fun p : ℝ × (ℝ × ℝ) => ((p.2.1 : ℂ) + circleMap 0 R p.1, p.2.2)))
    apply hc.comp_continuous (by fun_prop) (fun p => ?_)
    constructor
    · change |((p.2.1 : ℂ) + circleMap 0 R p.1).im| ≤ d
      simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using
        (hheight p.1).trans hRd
    · exact mem_univ _
  have hHint (θ : ℝ) :
      Integrable (fun p : ℝ × ℝ => H (θ, p)) (volume.prod volume) :=
    (_root_.GD.N0106.N0428.N0765.N1642.d008473 (hslice _ (hheight θ)).1).norm
  have hmass (θ : ℝ) :
      (∫ p : ℝ × ℝ, ‖H (θ, p)‖ ∂(volume.prod volume)) ≤ B := by
    simp only [H, norm_norm]
    rw [_root_.GD.N0106.N0428.N0765.N1642.d008474]
    exact (hslice _ (hheight θ)).2
  have hparam : Integrable
      (fun θ : ℝ => ∫ p : ℝ × ℝ, ‖H (θ, p)‖ ∂(volume.prod volume)) μ := by
    apply (integrable_const B : Integrable (fun _ : ℝ => B) μ).mono'
      hH.norm.aestronglyMeasurable.integral_prod_right'
    exact ae_of_all _ (fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact hmass θ)
  have hprod : Integrable H (μ.prod (volume.prod volume)) :=
    (integrable_prod_iff hH.aestronglyMeasurable).2 ⟨ae_of_all _ hHint, hparam⟩
  have haverage := hprod.integral_prod_right.const_mul ((2 * Real.pi)⁻¹)
  have heq : _root_.GD.N0106.N0428.N0765.N1642.d008475 F R = fun p : ℝ × ℝ =>
      (2 * Real.pi)⁻¹ * ∫ θ : ℝ, H (θ, p) ∂μ := by
    funext p
    exact _root_.GD.N0106.N0428.N0765.N1532.d007585 (fun z : ℂ => F z p.2) R p.1
  have hi : Integrable (_root_.GD.N0106.N0428.N0765.N1642.d008475 F R) (volume.prod volume) := by
    rw [heq]
    exact haverage
  refine ⟨hi, ?_⟩
  calc
    (∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1642.d008475 F R p ∂(volume.prod volume)) =
        (2 * Real.pi)⁻¹ * ∫ θ : ℝ,
          ∫ p : ℝ × ℝ, H (θ, p) ∂(volume.prod volume) ∂μ := by
      rw [heq, integral_const_mul]
      congr 1
      exact integral_integral_swap (f := fun p θ => H (θ, p)) hprod.swap
    _ ≤ (2 * Real.pi)⁻¹ * ∫ _θ : ℝ, B ∂μ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.two_pi_pos.le)
      apply integral_mono_ae hprod.integral_prod_left (integrable_const B)
      exact ae_of_all _ (fun θ => by simpa only [H, norm_norm] using hmass θ)
    _ = B := by
      have hμ : μ.real univ = 2 * Real.pi := by
        dsimp only [μ]
        rw [measureReal_restrict_apply_univ,
          Real.volume_real_Ioc_of_le Real.two_pi_pos.le, sub_zero]
      rw [integral_const, smul_eq_mul, hμ, ← mul_assoc,
        inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul]

theorem d008478 {F : ℂ → ℝ → ℂ} {d R B : ℝ}
    (hR : 0 ≤ R) (hRd : R ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ (univ : Set ℝ)))
    (hslice : ∀ y : ℝ, |y| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y) (volume.prod volume) ∧ _root_.GD.N0106.N0428.N0765.N1658.d008463 F y ≤ B) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1642.d008475 F R) (volume.prod volume) :=
  (_root_.GD.N0106.N0428.N0765.N1642.d008477 hR hRd hc hslice).1





theorem d008479 {F : ℂ → ℝ → ℂ} {d R B : ℝ}
    (hR : 0 < R) (hRd : R < d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ (univ : Set ℝ)))
    (hf : ∀ b : ℝ, DifferentiableOn ℂ (fun z : ℂ => F z b) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hslice : ∀ y : ℝ, |y| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y) (volume.prod volume) ∧ _root_.GD.N0106.N0428.N0765.N1658.d008463 F y ≤ B)
    (x : ℝ) :
    ∃ A : ℝ → ℝ, Integrable A ∧ (∀ b : ℝ, 0 ≤ A b) ∧
      ∀ z ∈ ball (x : ℂ) (R / 8), ∀ b : ℝ, ‖F z b‖ ≤ A b := by
  have hprod := _root_.GD.N0106.N0428.N0765.N1642.d008478 hR.le hRd.le hc hslice
  have hgood : ∀ᵐ t : ℝ, Integrable (fun b : ℝ => _root_.GD.N0106.N0428.N0765.N1642.d008475 F R (t, b)) :=
    hprod.prod_right_ae
  have hvol : volume (Ioo (x - R / 8) (x + R / 8)) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  obtain ⟨t, ht, htint⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol
    (ae_restrict_of_ae hgood)
  refine ⟨fun b : ℝ => 2 * _root_.GD.N0106.N0428.N0765.N1642.d008475 F R (t, b), htint.const_mul 2,
    (fun b => mul_nonneg (by norm_num) (_root_.GD.N0106.N0428.N0765.N1642.d008476 F R (t, b))), ?_⟩
  intro z hz b
  have hct : ContinuousOn (fun w : ℂ => F w b) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) := by
    change ContinuousOn ((Function.uncurry F) ∘ (fun w : ℂ => (w, b))) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d)
    apply hc.comp (by fun_prop) (fun w hw => ?_)
    exact ⟨hw, mem_univ b⟩
  have hdisc : DiffContOnCl ℂ (fun w : ℂ => F w b) (ball (t : ℂ) |R|) := by
    constructor
    · apply (hf b).mono
      intro w hw
      have hwn : ‖w - (t : ℂ)‖ < R := by
        simpa only [mem_ball, dist_eq_norm, abs_of_pos hR] using hw
      change |w.im| < d
      have him : |w.im| ≤ ‖w - (t : ℂ)‖ := by
        simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
          Complex.abs_im_le_norm (w - (t : ℂ))
      exact (him.trans_lt hwn).trans hRd
    · rw [closure_ball _ (abs_ne_zero.mpr hR.ne'), abs_of_pos hR]
      exact hct.mono (_root_.GD.N0106.N0428.N0765.N1532.d007587 hRd.le)
  have hzx : ‖z - (x : ℂ)‖ < R / 8 := mem_ball_iff_norm.mp hz
  have hxt : |x - t| < R / 8 := abs_lt.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hzt : ‖z - (t : ℂ)‖ ≤ R / 2 := by
    calc
      _ = ‖(z - (x : ℂ)) + ((x : ℂ) - (t : ℂ))‖ := by congr 1; ring
      _ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ) - (t : ℂ)‖ := norm_add_le _ _
      _ ≤ R / 2 := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        linarith
  exact _root_.GD.N0106.N0428.N0765.N1532.d007574 hR hdisc hzt

theorem d008480 {F : ℂ → ℝ → ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ (univ : Set ℝ))) :
    Continuous (fun p : ℝ × ℝ => F (p.1 : ℂ) p.2) := by
  change Continuous ((Function.uncurry F) ∘ (fun p : ℝ × ℝ => ((p.1 : ℂ), p.2)))
  apply hc.comp_continuous (by fun_prop) (fun p => ?_)
  constructor
  · change |(p.1 : ℂ).im| ≤ d
    simpa only [Complex.ofReal_im, abs_zero] using hd
  · exact mem_univ _



theorem d008481 {F : ℂ → ℝ → ℂ} {d R B : ℝ}
    (hR : 0 < R) (hRd : R < d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ (univ : Set ℝ)))
    (hf : ∀ b : ℝ, DifferentiableOn ℂ (fun z : ℂ => F z b) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hslice : ∀ y : ℝ, |y| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y) (volume.prod volume) ∧ _root_.GD.N0106.N0428.N0765.N1658.d008463 F y ≤ B)
    (x : ℝ) : Integrable (fun b : ℝ => F (x : ℂ) b) := by
  obtain ⟨A, hA, _hA0, hbound⟩ := _root_.GD.N0106.N0428.N0765.N1642.d008479 hR hRd hc hf hslice x
  have hreal := _root_.GD.N0106.N0428.N0765.N1642.d008480 (hR.le.trans hRd.le) hc
  have hrow : Continuous (fun b : ℝ => F (x : ℂ) b) :=
    hreal.comp (continuous_const.prodMk continuous_id)
  exact Integrable.mono' hA hrow.aestronglyMeasurable
    (ae_of_all _ (hbound (x : ℂ) (mem_ball_self (by positivity))))




theorem d008482 {F : ℂ → ℝ → ℂ} {d R B : ℝ}
    (hR : 0 < R) (hRd : R < d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ (univ : Set ℝ)))
    (hf : ∀ b : ℝ, DifferentiableOn ℂ (fun z : ℂ => F z b) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hslice : ∀ y : ℝ, |y| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y) (volume.prod volume) ∧ _root_.GD.N0106.N0428.N0765.N1658.d008463 F y ≤ B)
    {u : ℝ → ℂ} (hu : Measurable u) (hunorm : ∀ b : ℝ, ‖u b‖ ≤ 1) :
    Continuous (fun x : ℝ => ∫ b : ℝ, u b * F (x : ℂ) b) := by
  have hreal := _root_.GD.N0106.N0428.N0765.N1642.d008480 (hR.le.trans hRd.le) hc
  have hrows (x : ℝ) : Continuous (fun b : ℝ => F (x : ℂ) b) :=
    hreal.comp (continuous_const.prodMk continuous_id)
  have hcols (b : ℝ) : Continuous (fun x : ℝ => F (x : ℂ) b) :=
    hreal.comp (continuous_id.prodMk continuous_const)
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨A, hA, _hA0, hbound⟩ := _root_.GD.N0106.N0428.N0765.N1642.d008479 hR hRd hc hf hslice x
  apply continuousAt_of_dominated
    (Filter.Eventually.of_forall (fun t : ℝ =>
      (hu.mul (hrows t).measurable).aestronglyMeasurable))
    ?_ hA (ae_of_all _ (fun b : ℝ => ((hcols b).const_mul (u b)).continuousAt))
  filter_upwards [Metric.ball_mem_nhds x (by positivity : 0 < R / 8)] with t ht
  apply ae_of_all
  intro b
  have htc : (t : ℂ) ∈ ball (x : ℂ) (R / 8) := by
    rw [mem_ball_iff_norm, ← Complex.ofReal_sub, Complex.norm_real]
    exact mem_ball_iff_norm.mp ht
  calc
    ‖u b * F (t : ℂ) b‖ = ‖u b‖ * ‖F (t : ℂ) b‖ := norm_mul _ _
    _ ≤ 1 * ‖F (t : ℂ) b‖ :=
      mul_le_mul_of_nonneg_right (hunorm b) (norm_nonneg _)
    _ = ‖F (t : ℂ) b‖ := one_mul _
    _ ≤ A b := hbound (t : ℂ) htc b

end
end GD.N0106.N0428.N0765.N1642

#print axioms _root_.GD.N0106.N0428.N0765.N1642.d008478
#print axioms _root_.GD.N0106.N0428.N0765.N1642.d008477
#print axioms _root_.GD.N0106.N0428.N0765.N1642.d008479
#print axioms _root_.GD.N0106.N0428.N0765.N1642.d008481
#print axioms _root_.GD.N0106.N0428.N0765.N1642.d008482
