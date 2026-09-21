import GD.Module0581
import GD.Module0577




















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1645
noncomputable section

open MeasureTheory Set Complex Filter
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1530 _root_.GD.N0106.N0428.N0765.N1532
open _root_.GD.N0106.N0428.N0765.N1642 _root_.GD.N0106.N0428.N0765.N1638
open scoped Topology BigOperators

def d008483 : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))

instance d008484 : IsFiniteMeasure _root_.GD.N0106.N0428.N0765.N1645.d008483 := by
  unfold _root_.GD.N0106.N0428.N0765.N1645.d008483
  infer_instance

theorem d008485 : _root_.GD.N0106.N0428.N0765.N1645.d008483.real univ = 2 * Real.pi := by
  unfold _root_.GD.N0106.N0428.N0765.N1645.d008483
  rw [measureReal_restrict_apply_univ,
    Real.volume_real_Ioc_of_le Real.two_pi_pos.le, sub_zero]

def d008486 (F : ℂ → ℂ → ℂ) (z : ℂ) (w : ℂ) (a : ℝ) : ℂ :=
  F ((a : ℂ) + z) w

theorem d008487 (F : ℂ → ℂ → ℂ) (z : ℂ) (β : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1658.d008462 (_root_.GD.N0106.N0428.N0765.N1645.d008486 F z) β p =
      _root_.GD.N0106.N0428.N0765.N1658.d008467 F z.im β (p.swap + (z.re, 0)) := by
  change F ((p.2 : ℂ) + z) ((p.1 : ℂ) + (β : ℂ) * Complex.I) =
    F (((p.2 + z.re : ℝ) : ℂ) + (z.im : ℂ) * Complex.I)
      (((p.1 + 0 : ℝ) : ℂ) + (β : ℂ) * Complex.I)
  simp only [add_zero]
  congr 1
  apply Complex.ext <;> simp

theorem d008488 {F : ℂ → ℂ → ℂ} {z : ℂ} {β : ℝ}
    (hi : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F z.im β) (volume.prod volume)) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 (_root_.GD.N0106.N0428.N0765.N1645.d008486 F z) β) (volume.prod volume) := by
  have heq : _root_.GD.N0106.N0428.N0765.N1658.d008462 (_root_.GD.N0106.N0428.N0765.N1645.d008486 F z) β =
      fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1658.d008467 F z.im β (p.swap + (z.re, 0)) :=
    funext (_root_.GD.N0106.N0428.N0765.N1645.d008487 F z β)
  rw [heq]
  exact (hi.comp_add_right (z.re, 0)).swap

theorem d008489 (F : ℂ → ℂ → ℂ) (z : ℂ) (β : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1658.d008463 (_root_.GD.N0106.N0428.N0765.N1645.d008486 F z) β = _root_.GD.N0106.N0428.N0765.N1658.d008468 F z.im β := by
  unfold _root_.GD.N0106.N0428.N0765.N1658.d008463
  simp_rw [_root_.GD.N0106.N0428.N0765.N1645.d008487]
  calc
    (∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1658.d008467 F z.im β (p.swap + (z.re, 0))‖
        ∂(volume.prod volume)) =
      ∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1658.d008467 F z.im β (p + (z.re, 0))‖
        ∂(volume.prod volume) := integral_prod_swap (fun p : ℝ × ℝ => ‖_root_.GD.N0106.N0428.N0765.N1658.d008467 F z.im β (p + (z.re, 0))‖)
    _ = _root_.GD.N0106.N0428.N0765.N1658.d008468 F z.im β :=
      integral_add_right_eq_self (fun p : ℝ × ℝ => ‖_root_.GD.N0106.N0428.N0765.N1658.d008467 F z.im β p‖)
        (z.re, 0)

def d008490 (F : ℂ → ℂ → ℂ) (R θ : ℝ) (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1642.d008475 (_root_.GD.N0106.N0428.N0765.N1645.d008486 F (circleMap 0 R θ)) R p.swap

def d008491 (F : ℂ → ℂ → ℂ) (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ : ℝ, _root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ p ∂_root_.GD.N0106.N0428.N0765.N1645.d008483

theorem d008492 (F : ℂ → ℂ → ℂ) (R θ : ℝ) (p : ℝ × ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ p := _root_.GD.N0106.N0428.N0765.N1642.d008476 _ _ _

theorem d008493 (F : ℂ → ℂ → ℂ) (R : ℝ) (p : ℝ × ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1645.d008491 F R p :=
  mul_nonneg (inv_nonneg.mpr Real.two_pi_pos.le)
    (integral_nonneg (fun θ => _root_.GD.N0106.N0428.N0765.N1645.d008492 F R θ p))

theorem d008494 (F : ℂ → ℂ → ℂ) (R θ : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ p = (2 * Real.pi)⁻¹ * ∫ φ : ℝ,
      ‖F ((p.1 : ℂ) + circleMap 0 R θ) ((p.2 : ℂ) + circleMap 0 R φ)‖
        ∂_root_.GD.N0106.N0428.N0765.N1645.d008483 :=
  _root_.GD.N0106.N0428.N0765.N1532.d007585 (fun w : ℂ => F ((p.1 : ℂ) + circleMap 0 R θ) w) R p.2

theorem d008495 {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) :
    |(circleMap 0 R θ).im| ≤ R :=
  (Complex.abs_im_le_norm _).trans_eq
    (by simp only [norm_circleMap_zero, abs_of_nonneg hR])

theorem d008496 {F : ℂ → ℂ → ℂ} {d R : ℝ}
    (hR : 0 ≤ R) (hRd : R ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d)) :
    StronglyMeasurable (fun p : ℝ × (ℝ × ℝ) => _root_.GD.N0106.N0428.N0765.N1645.d008490 F R p.1 p.2) := by
  let G : (ℝ × (ℝ × ℝ)) × ℝ → ℝ := fun p =>
    ‖F ((p.1.2.1 : ℂ) + circleMap 0 R p.1.1)
      ((p.1.2.2 : ℂ) + circleMap 0 R p.2)‖
  have hmap : Continuous (fun p : (ℝ × (ℝ × ℝ)) × ℝ =>
      (((p.1.2.1 : ℂ) + circleMap 0 R p.1.1),
        ((p.1.2.2 : ℂ) + circleMap 0 R p.2))) := by fun_prop
  have hG : Continuous G := by
    apply (hc.comp_continuous hmap (fun p => ?_)).norm
    constructor
    · change |((p.1.2.1 : ℂ) + circleMap 0 R p.1.1).im| ≤ d
      simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using
        (_root_.GD.N0106.N0428.N0765.N1645.d008495 hR p.1.1).trans hRd
    · change |((p.1.2.2 : ℂ) + circleMap 0 R p.2).im| ≤ d
      simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using
        (_root_.GD.N0106.N0428.N0765.N1645.d008495 hR p.2).trans hRd
  have hInt : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      ∫ φ : ℝ, G (p, φ) ∂_root_.GD.N0106.N0428.N0765.N1645.d008483) :=
    hG.stronglyMeasurable.integral_prod_right'.measurable
  have heq : (fun p : ℝ × (ℝ × ℝ) => _root_.GD.N0106.N0428.N0765.N1645.d008490 F R p.1 p.2) =
      fun p : ℝ × (ℝ × ℝ) => (2 * Real.pi)⁻¹ * ∫ φ : ℝ, G (p, φ) ∂_root_.GD.N0106.N0428.N0765.N1645.d008483 := by
    funext p
    exact _root_.GD.N0106.N0428.N0765.N1645.d008494 F R p.1 p.2
  rw [heq]
  exact (hInt.const_mul _).stronglyMeasurable

theorem d008497 {F : ℂ → ℂ → ℂ} {d R B : ℝ}
    (hR : 0 ≤ R) (hRd : R ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hslice : ∀ α β : ℝ, |α| ≤ R → |β| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤ B)
    (θ : ℝ) : Integrable (_root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ) (volume.prod volume) ∧
      (∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ p ∂(volume.prod volume)) ≤ B := by
  let z : ℂ := circleMap 0 R θ
  have hz : |z.im| ≤ R := _root_.GD.N0106.N0428.N0765.N1645.d008495 hR θ
  have hmap : Continuous (fun p : ℂ × ℝ => (((p.2 : ℂ) + z), p.1)) := by fun_prop
  have hcS : ContinuousOn (Function.uncurry (_root_.GD.N0106.N0428.N0765.N1645.d008486 F z))
      (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ (univ : Set ℝ)) := by
    apply hc.comp hmap.continuousOn (fun p hp => ?_)
    constructor
    · change |((p.2 : ℂ) + z).im| ≤ d
      simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using hz.trans hRd
    · exact hp.1
  have hsliceS (β : ℝ) (hβ : |β| ≤ R) :
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 (_root_.GD.N0106.N0428.N0765.N1645.d008486 F z) β) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008463 (_root_.GD.N0106.N0428.N0765.N1645.d008486 F z) β ≤ B := by
    obtain ⟨hi, hb⟩ := hslice z.im β hz hβ
    exact ⟨_root_.GD.N0106.N0428.N0765.N1645.d008488 hi, (_root_.GD.N0106.N0428.N0765.N1645.d008489 F z β).le.trans hb⟩
  obtain ⟨hi, hb⟩ := _root_.GD.N0106.N0428.N0765.N1642.d008477 hR hRd hcS hsliceS
  refine ⟨hi.swap, ?_⟩
  exact (integral_prod_swap (_root_.GD.N0106.N0428.N0765.N1642.d008475 (_root_.GD.N0106.N0428.N0765.N1645.d008486 F z) R)).le.trans hb

theorem d008498 {F : ℂ → ℂ → ℂ} {d R B : ℝ}
    (hR : 0 ≤ R) (hRd : R ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hslice : ∀ α β : ℝ, |α| ≤ R → |β| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤ B) :
    Integrable (fun p : ℝ × (ℝ × ℝ) => _root_.GD.N0106.N0428.N0765.N1645.d008490 F R p.1 p.2)
      (_root_.GD.N0106.N0428.N0765.N1645.d008483.prod (volume.prod volume)) := by
  have hm := _root_.GD.N0106.N0428.N0765.N1645.d008496 hR hRd hc
  have hi (θ : ℝ) := _root_.GD.N0106.N0428.N0765.N1645.d008497 hR hRd hc hslice θ
  have hparam : Integrable (fun θ : ℝ =>
      ∫ p : ℝ × ℝ, ‖_root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ p‖ ∂(volume.prod volume)) _root_.GD.N0106.N0428.N0765.N1645.d008483 := by
    apply (integrable_const B : Integrable (fun _ : ℝ => B) _root_.GD.N0106.N0428.N0765.N1645.d008483).mono'
      hm.norm.aestronglyMeasurable.integral_prod_right'
    apply ae_of_all
    intro θ
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    have hnorm : (fun p : ℝ × ℝ => ‖_root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ p‖) = _root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ := by
      funext p
      rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1645.d008492 F R θ p)]
    rw [hnorm]
    exact (hi θ).2
  exact (integrable_prod_iff hm.aestronglyMeasurable).2
    ⟨ae_of_all _ (fun θ => (hi θ).1), hparam⟩

theorem d008499 {F : ℂ → ℂ → ℂ} {d R B : ℝ}
    (hR : 0 ≤ R) (hRd : R ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hslice : ∀ α β : ℝ, |α| ≤ R → |β| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤ B) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1645.d008491 F R) (volume.prod volume) ∧
      (∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1645.d008491 F R p ∂(volume.prod volume)) ≤ B := by
  have hi := _root_.GD.N0106.N0428.N0765.N1645.d008498 hR hRd hc hslice
  refine ⟨hi.integral_prod_right.const_mul ((2 * Real.pi)⁻¹), ?_⟩
  calc
    (∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1645.d008491 F R p ∂(volume.prod volume)) =
      (2 * Real.pi)⁻¹ * ∫ θ : ℝ,
        ∫ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ p ∂(volume.prod volume) ∂_root_.GD.N0106.N0428.N0765.N1645.d008483 := by
      change (∫ p : ℝ × ℝ, (2 * Real.pi)⁻¹ * ∫ θ : ℝ, _root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ p ∂_root_.GD.N0106.N0428.N0765.N1645.d008483 ∂(volume.prod volume)) = _
      rw [integral_const_mul]
      congr 1
      exact integral_integral_swap (f := fun p θ => _root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ p) hi.swap
    _ ≤ (2 * Real.pi)⁻¹ * ∫ _θ : ℝ, B ∂_root_.GD.N0106.N0428.N0765.N1645.d008483 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.two_pi_pos.le)
      exact integral_mono_ae hi.integral_prod_left (integrable_const B)
        (ae_of_all _ (fun θ => (_root_.GD.N0106.N0428.N0765.N1645.d008497 hR hRd hc hslice θ).2))
    _ = B := by
      rw [integral_const, smul_eq_mul, _root_.GD.N0106.N0428.N0765.N1645.d008485, ← mul_assoc,
        inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul]



theorem d008500 {F : ℂ → ℂ → ℂ} {d R B : ℝ}
    (hR : 0 < R) (hRd : R < d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hslice : ∀ α β : ℝ, |α| ≤ R → |β| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤ B)
    (x : ℝ × ℝ) :
    ∀ᵐ t : ℝ × ℝ ∂(volume.prod volume), |x.1 - t.1| ≤ R / 2 →
      |x.2 - t.2| ≤ R / 2 → ‖F (x.1 : ℂ) (x.2 : ℂ)‖ ≤ 4 * _root_.GD.N0106.N0428.N0765.N1645.d008491 F R t := by
  have hcdA (w : ℂ) (hw : w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) :
      ContinuousOn (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) := by
    have hm : Continuous (fun z : ℂ => (z, w)) := by fun_prop
    exact hc.comp hm.continuousOn (fun z hz => ⟨hz, hw⟩)
  have hcdB (z : ℂ) (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) :
      ContinuousOn (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) := by
    have hm : Continuous (fun w : ℂ => (z, w)) := by fun_prop
    exact hc.comp hm.continuousOn (fun w hw => ⟨hz, hw⟩)
  have hx2 : (x.2 : ℂ) ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := by
    change |(x.2 : ℂ).im| ≤ d
    simpa only [Complex.ofReal_im, abs_zero] using hR.le.trans hRd.le
  have hi := _root_.GD.N0106.N0428.N0765.N1645.d008498 hR.le hRd.le hc hslice
  filter_upwards [hi.prod_left_ae] with t ht
  intro hxt hyt
  have hz (θ : ℝ) : ((t.1 : ℂ) + circleMap 0 R θ) ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := by
    change |((t.1 : ℂ) + circleMap 0 R θ).im| ≤ d
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using
      (_root_.GD.N0106.N0428.N0765.N1645.d008495 hR.le θ).trans hRd.le
  have hleft : Continuous (fun θ : ℝ => ‖F ((t.1 : ℂ) + circleMap 0 R θ) (x.2 : ℂ)‖) := by
    have hm : Continuous (fun θ : ℝ => (t.1 : ℂ) + circleMap 0 R θ) := by fun_prop
    exact ((hcdA (x.2 : ℂ) hx2).comp_continuous hm hz).norm
  have hleftInt : Integrable
      (fun θ : ℝ => ‖F ((t.1 : ℂ) + circleMap 0 R θ) (x.2 : ℂ)‖) _root_.GD.N0106.N0428.N0765.N1645.d008483 :=
    hleft.integrableOn_Ioc
  have hsecond (θ : ℝ) : ‖F ((t.1 : ℂ) + circleMap 0 R θ) (x.2 : ℂ)‖ ≤
      2 * _root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ t :=
    _root_.GD.N0106.N0428.N0765.N1532.d007588 hR hRd (hcdB _ (hz θ)) (hfB _ (hz θ)) hyt
  calc
    ‖F (x.1 : ℂ) (x.2 : ℂ)‖ ≤
      2 * _root_.GD.N0106.N0428.N0765.N1532.d007583 (fun z : ℂ => F z (x.2 : ℂ)) R t.1 :=
      _root_.GD.N0106.N0428.N0765.N1532.d007588 hR hRd (hcdA _ hx2) (hfA _ hx2) hxt
    _ = 2 * ((2 * Real.pi)⁻¹ * ∫ θ : ℝ,
        ‖F ((t.1 : ℂ) + circleMap 0 R θ) (x.2 : ℂ)‖ ∂_root_.GD.N0106.N0428.N0765.N1645.d008483) :=
      congrArg (fun q : ℝ => 2 * q)
        (_root_.GD.N0106.N0428.N0765.N1532.d007585 (fun z : ℂ => F z (x.2 : ℂ)) R t.1)
    _ ≤ 2 * ((2 * Real.pi)⁻¹ * ∫ θ : ℝ, 2 * _root_.GD.N0106.N0428.N0765.N1645.d008490 F R θ t ∂_root_.GD.N0106.N0428.N0765.N1645.d008483) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.two_pi_pos.le)
      exact integral_mono_ae hleftInt (ht.const_mul 2) (ae_of_all _ hsecond)
    _ = 4 * _root_.GD.N0106.N0428.N0765.N1645.d008491 F R t := by
      rw [integral_const_mul]
      unfold _root_.GD.N0106.N0428.N0765.N1645.d008491
      ring



theorem d008501 {F : ℂ → ℂ → ℂ} {d R B : ℝ}
    (hR : 0 < R) (hRd : R < d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hslice : ∀ α β : ℝ, |α| ≤ R → |β| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤ B)
    (a b : ℝ) : Summable (fun n : ℤ × ℤ =>
      F ((a + (n.1 : ℝ) : ℝ) : ℂ) ((b + (n.2 : ℝ) : ℝ) : ℂ)) := by
  let δ : ℝ := min (R / 8) (1 / 8)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδR : δ ≤ R / 8 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 8 := min_le_right _ _
  apply _root_.GD.N0106.N0428.N0765.N1638.d008457
    (g := fun x : ℝ × ℝ => F (x.1 : ℂ) (x.2 : ℂ))
    (A := _root_.GD.N0106.N0428.N0765.N1645.d008491 F R) hδ (by linarith)
    (_root_.GD.N0106.N0428.N0765.N1645.d008499 hR.le hRd.le hc hslice).1
    (_root_.GD.N0106.N0428.N0765.N1645.d008493 F R)
  intro x
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1645.d008500 hR hRd hc hfA hfB hslice x] with t ht
  intro hxt hyt
  exact ht (hxt.trans (by linarith)) (hyt.trans (by linarith))

end
end GD.N0106.N0428.N0765.N1645

#print axioms _root_.GD.N0106.N0428.N0765.N1645.d008499
#print axioms _root_.GD.N0106.N0428.N0765.N1645.d008500
#print axioms _root_.GD.N0106.N0428.N0765.N1645.d008501
