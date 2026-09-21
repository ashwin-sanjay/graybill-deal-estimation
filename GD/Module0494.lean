import GD.Module0493
import GD.Module0442
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Fourier.PoissonSummation















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1532
noncomputable section

open MeasureTheory Set Metric Complex TopologicalSpace
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1530 _root_.GD.N0106.N0428.N0765.N1531
open scoped Topology


theorem d007572 {c w z : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : z ∈ sphere c R) (hw : ‖w - c‖ ≤ R / 2) :
    ‖(z - c) / (z - w)‖ ≤ 2 := by
  have hzc : ‖z - c‖ = R := mem_sphere_iff_norm.mp hz
  have ht : R ≤ ‖z - w‖ + R / 2 := calc
    R = ‖z - c‖ := hzc.symm
    _ = ‖(z - w) + (w - c)‖ := by congr 1 <;> ring
    _ ≤ ‖z - w‖ + ‖w - c‖ := norm_add_le _ _
    _ ≤ ‖z - w‖ + R / 2 := add_le_add le_rfl hw
  have hden : 0 < ‖z - w‖ := by linarith
  rw [norm_div, hzc]
  exact (div_le_iff₀ hden).2 (by linarith)

theorem d007573 (F : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    ‖Real.circleAverage F c R‖ ≤ Real.circleAverage (fun z => ‖F z‖) c R := by
  simp only [Real.circleAverage_def, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr Real.two_pi_pos), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le)
    (inv_nonneg.mpr Real.two_pi_pos.le)



theorem d007574 {f : ℂ → ℂ} {c w : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c |R|))
    (hw : ‖w - c‖ ≤ R / 2) :
    ‖f w‖ ≤ 2 * Real.circleAverage (fun z => ‖f z‖) c R := by
  have hwball : w ∈ ball c |R| := by
    rw [mem_ball, dist_eq_norm, abs_of_pos hR]
    linarith
  have hfc : ContinuousOn f (sphere c |R|) := by
    apply hf.2.mono
    rw [closure_ball c (abs_ne_zero.mpr hR.ne')]
    exact sphere_subset_closedBall
  have hden : ∀ z ∈ sphere c |R|, z - w ≠ 0 := by
    intro z hz heq
    have hzw : z = w := sub_eq_zero.mp heq
    subst z
    have hz' : ‖w - c‖ = R := by
      simpa only [abs_of_pos hR] using mem_sphere_iff_norm.mp hz
    linarith
  have hk : ContinuousOn (fun z : ℂ => (z - c) / (z - w)) (sphere c |R|) :=
    (continuous_id.sub continuous_const).continuousOn.div
      (continuous_id.sub continuous_const).continuousOn hden
  have hmono :
      Real.circleAverage (fun z => ‖((z - c) / (z - w)) * f z‖) c R ≤
        Real.circleAverage (fun z => 2 * ‖f z‖) c R := by
    apply Real.circleAverage_mono (hk.mul hfc).norm.circleIntegrable'
      (continuousOn_const.mul hfc.norm).circleIntegrable'
    intro z hz
    change ‖((z - c) / (z - w)) * f z‖ ≤ 2 * ‖f z‖
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact _root_.GD.N0106.N0428.N0765.N1532.d007572 hR (by simpa only [abs_of_pos hR] using hz) hw
  have hmean := hf.circleAverage_smul_div (R := R) hwball
  simp only [smul_eq_mul] at hmean
  calc
    ‖f w‖ = ‖Real.circleAverage (fun z => ((z - c) / (z - w)) * f z) c R‖ :=
      congrArg norm hmean.symm
    _ ≤ Real.circleAverage (fun z => ‖((z - c) / (z - w)) * f z‖) c R :=
      _root_.GD.N0106.N0428.N0765.N1532.d007573 _ _ _
    _ ≤ Real.circleAverage (fun z => 2 * ‖f z‖) c R := hmono
    _ = 2 * Real.circleAverage (fun z => ‖f z‖) c R := by
      simpa only [smul_eq_mul] using
        (Real.circleAverage_fun_smul (a := (2 : ℝ)) (f := fun z => ‖f z‖)
          (c := c) (R := R))

def d007575 (a δ : ℝ) (n : ℤ) : Set ℝ :=
  Icc (a + (n : ℝ) - δ) (a + (n : ℝ) + δ)

def d007576 (a δ : ℝ) : Compacts ℝ :=
  ⟨Icc (a - δ) (a + δ), isCompact_Icc⟩

def d007577 (g : C(ℝ, ℂ)) (a δ : ℝ) (n : ℤ) : ℝ :=
  ‖(g.comp (ContinuousMap.addRight (n : ℝ))).restrict (_root_.GD.N0106.N0428.N0765.N1532.d007576 a δ)‖

theorem d007578 {δ : ℝ} (hδ : 2 * δ < 1) (a : ℝ) :
    Pairwise (fun i j : ℤ => Disjoint (_root_.GD.N0106.N0428.N0765.N1532.d007575 a δ i) (_root_.GD.N0106.N0428.N0765.N1532.d007575 a δ j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  change a + (i : ℝ) - δ ≤ x ∧ x ≤ a + (i : ℝ) + δ at hxi
  change a + (j : ℝ) - δ ≤ x ∧ x ≤ a + (j : ℝ) + δ at hxj
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hgap : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hij')
    linarith [hxi.2, hxj.1]
  · have hgap : (j : ℝ) + 1 ≤ (i : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hji')
    linarith [hxj.2, hxi.1]



theorem d007579 {g : C(ℝ, ℂ)} {A : ℝ → ℝ} {δ a x : ℝ} {n : ℤ}
    (hδ : 0 < δ) (hA : Integrable A)
    (hlocal : ∀ x t : ℝ, |x - t| ≤ 2 * δ → ‖g x‖ ≤ 2 * A t)
    (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n) :
    ‖g x‖ ≤ (∫ t in _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n, A t) / δ := by
  have hab : a + (n : ℝ) - δ ≤ a + (n : ℝ) + δ := by linarith
  have hcompare :
      (∫ _t in _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n, ‖g x‖) ≤
        ∫ t in _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n, 2 * A t := by
    apply setIntegral_mono_on (integrableOn_const isCompact_Icc.measure_ne_top)
      (hA.integrableOn.const_mul 2) measurableSet_Icc
    intro t ht
    apply hlocal
    apply abs_le.mpr
    change _ ≤ x ∧ x ≤ _ at hx
    change _ ≤ t ∧ t ≤ _ at ht
    constructor <;> linarith [hx.1, hx.2, ht.1, ht.2]
  rw [setIntegral_const, integral_const_mul] at hcompare
  simp only [_root_.GD.N0106.N0428.N0765.N1532.d007575, Real.volume_real_Icc_of_le hab, smul_eq_mul] at hcompare
  apply (le_div_iff₀ hδ).2
  change ‖g x‖ * δ ≤ ∫ t in Icc (a + (n : ℝ) - δ) (a + (n : ℝ) + δ), A t
  nlinarith

theorem d007580 {g : C(ℝ, ℂ)} {A : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hA : Integrable A) (hA0 : ∀ t, 0 ≤ A t)
    (hlocal : ∀ x t : ℝ, |x - t| ≤ 2 * δ → ‖g x‖ ≤ 2 * A t)
    (a : ℝ) (n : ℤ) :
    _root_.GD.N0106.N0428.N0765.N1532.d007577 g a δ n ≤ (∫ t in _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n, A t) / δ := by
  apply (ContinuousMap.norm_le _ (div_nonneg (integral_nonneg hA0) hδ.le)).2
  intro x
  change ‖g ((x : ℝ) + (n : ℝ))‖ ≤ _
  apply _root_.GD.N0106.N0428.N0765.N1532.d007579 hδ hA hlocal
  have hx := x.property
  change a - δ ≤ (x : ℝ) ∧ (x : ℝ) ≤ a + δ at hx
  change a + (n : ℝ) - δ ≤ (x : ℝ) + (n : ℝ) ∧
    (x : ℝ) + (n : ℝ) ≤ a + (n : ℝ) + δ
  constructor <;> linarith [hx.1, hx.2]

theorem d007581 {g : C(ℝ, ℂ)} {A : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hsep : 2 * δ < 1) (hA : Integrable A) (hA0 : ∀ t, 0 ≤ A t)
    (hlocal : ∀ x t : ℝ, |x - t| ≤ 2 * δ → ‖g x‖ ≤ 2 * A t)
    (a : ℝ) (s : Finset ℤ) :
    ∑ n ∈ s, _root_.GD.N0106.N0428.N0765.N1532.d007577 g a δ n ≤ (∫ t : ℝ, A t) / δ := by
  have hsum : (∑ n ∈ s, ∫ t in _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n, A t) ≤ ∫ t : ℝ, A t := by
    rw [← integral_biUnion_finset (s := _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ) s (fun _ _ => measurableSet_Icc)
      (fun i _ j _ hij => _root_.GD.N0106.N0428.N0765.N1532.d007578 hsep a hij)
      (fun _ _ => hA.integrableOn)]
    exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ hA0) hA
  calc
    _ ≤ ∑ n ∈ s, (∫ t in _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n, A t) / δ :=
      Finset.sum_le_sum (fun n _ => _root_.GD.N0106.N0428.N0765.N1532.d007580 hδ hA hA0 hlocal a n)
    _ = (∑ n ∈ s, ∫ t in _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n, A t) / δ :=
      (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right hsum hδ.le



theorem d007582 {g : C(ℝ, ℂ)} {A : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hsep : 2 * δ < 1) (hA : Integrable A) (hA0 : ∀ t, 0 ≤ A t)
    (hlocal : ∀ x t : ℝ, |x - t| ≤ 2 * δ → ‖g x‖ ≤ 2 * A t)
    (K : Compacts ℝ) :
    Summable (fun n : ℤ => ‖(g.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖) := by
  classical
  obtain ⟨s, hs⟩ := K.isCompact.elim_finite_subcover (fun a : ℝ => ball a δ)
    (fun _ => isOpen_ball) (by
      intro x _hx
      exact mem_iUnion.mpr ⟨x, mem_ball_self hδ⟩)
  have hmajor (n : ℤ) :
      ‖(g.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ ≤
        ∑ a ∈ s, _root_.GD.N0106.N0428.N0765.N1532.d007577 g a δ n := by
    apply (ContinuousMap.norm_le _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).2
    intro x
    obtain ⟨a, has, hax⟩ := mem_iUnion₂.mp (hs x.property)
    have hxc : (x : ℝ) ∈ _root_.GD.N0106.N0428.N0765.N1532.d007576 a δ := by
      have hxabs : |(x : ℝ) - a| < δ := by simpa only [mem_ball, Real.dist_eq] using hax
      change a - δ ≤ (x : ℝ) ∧ (x : ℝ) ≤ a + δ
      constructor <;> linarith [(abs_lt.mp hxabs).1, (abs_lt.mp hxabs).2]
    have hxnorm := ((g.comp (ContinuousMap.addRight (n : ℝ))).restrict
      (_root_.GD.N0106.N0428.N0765.N1532.d007576 a δ)).norm_coe_le_norm ⟨(x : ℝ), hxc⟩
    change ‖g ((x : ℝ) + (n : ℝ))‖ ≤ _
    exact hxnorm.trans (Finset.single_le_sum (f := fun a => _root_.GD.N0106.N0428.N0765.N1532.d007577 g a δ n)
      (fun _ _ => norm_nonneg _) has)
  apply summable_of_sum_le (fun _ => norm_nonneg _)
  intro u
  calc
    _ ≤ ∑ n ∈ u, ∑ a ∈ s, _root_.GD.N0106.N0428.N0765.N1532.d007577 g a δ n := Finset.sum_le_sum (fun n _ => hmajor n)
    _ = ∑ a ∈ s, ∑ n ∈ u, _root_.GD.N0106.N0428.N0765.N1532.d007577 g a δ n := Finset.sum_comm
    _ ≤ ∑ _a ∈ s, (∫ t : ℝ, A t) / δ :=
      Finset.sum_le_sum (fun a _ => _root_.GD.N0106.N0428.N0765.N1532.d007581 hδ hsep hA hA0 hlocal a u)


def d007583 (f : ℂ → ℂ) (R t : ℝ) : ℝ :=
  Real.circleAverage (fun z => ‖f z‖) (t : ℂ) R

theorem d007584 (f : ℂ → ℂ) (R t : ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1532.d007583 f R t :=
  Real.circleAverage_nonneg_of_nonneg (fun _ _ => norm_nonneg _)

theorem d007585 (f : ℂ → ℂ) (R t : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1532.d007583 f R t = (2 * Real.pi)⁻¹ *
      ∫ θ in Ioc 0 (2 * Real.pi), ‖f ((t : ℂ) + circleMap 0 R θ)‖ := by
  unfold _root_.GD.N0106.N0428.N0765.N1532.d007583
  rw [← Real.circleAverage_map_add_const]
  simp only [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    smul_eq_mul, add_comm]




theorem d007586 {f : ℂ → ℂ} {d R B : ℝ}
    (hR : 0 ≤ R) (hRd : R ≤ d) (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hslice : ∀ y : ℝ, |y| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f y) ∧ _root_.GD.N0106.N0428.N0765.N1530.d005195 f y ≤ B) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1532.d007583 f R) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  let H : ℝ × ℝ → ℝ := fun p => ‖f ((p.2 : ℂ) + circleMap 0 R p.1)‖
  have hheight (θ : ℝ) : |(circleMap 0 R θ).im| ≤ R := by
    exact (Complex.abs_im_le_norm _).trans_eq (by simp only [norm_circleMap_zero, abs_of_nonneg hR])
  have hH : Continuous H := by
    apply (hc.comp_continuous (by fun_prop) (fun p => ?_)).norm
    change |((p.2 : ℂ) + circleMap 0 R p.1).im| ≤ d
    simpa only [Complex.add_im, Complex.ofReal_im, zero_add] using (hheight p.1).trans hRd
  have hHint (θ : ℝ) : Integrable (fun t : ℝ => H (θ, t)) :=
    (_root_.GD.N0106.N0428.N0765.N1530.d005199 (hslice _ (hheight θ)).1).norm
  have hmass (θ : ℝ) : (∫ t : ℝ, ‖H (θ, t)‖) ≤ B := by
    simp only [H, norm_norm]
    rw [_root_.GD.N0106.N0428.N0765.N1530.d005200]
    exact (hslice _ (hheight θ)).2
  have hparam : Integrable (fun θ : ℝ => ∫ t : ℝ, ‖H (θ, t)‖) μ := by
    apply (integrable_const B : Integrable (fun _ : ℝ => B) μ).mono'
      hH.norm.aestronglyMeasurable.integral_prod_right'
    exact ae_of_all _ (fun θ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact hmass θ)
  have hprod : Integrable H (μ.prod volume) :=
    (integrable_prod_iff hH.aestronglyMeasurable).2 ⟨ae_of_all _ hHint, hparam⟩
  have haverage := hprod.integral_prod_right.const_mul ((2 * Real.pi)⁻¹)
  have heq : _root_.GD.N0106.N0428.N0765.N1532.d007583 f R = fun t : ℝ =>
      (2 * Real.pi)⁻¹ * ∫ θ : ℝ, H (θ, t) ∂μ := by
    funext t
    exact _root_.GD.N0106.N0428.N0765.N1532.d007585 f R t
  rw [heq]
  exact haverage

theorem d007587 {d R t : ℝ} (hRd : R ≤ d) :
    closedBall (t : ℂ) R ⊆ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := by
  intro z hz
  change |z.im| ≤ d
  have hz' : ‖z - (t : ℂ)‖ ≤ R := mem_closedBall_iff_norm.mp hz
  have him : |z.im| ≤ ‖z - (t : ℂ)‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      Complex.abs_im_le_norm (z - (t : ℂ))
  exact him.trans (hz'.trans hRd)

theorem d007588 {f : ℂ → ℂ} {d R : ℝ}
    (hR : 0 < R) (hRd : R < d)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    {x t : ℝ} (hxt : |x - t| ≤ R / 2) :
    ‖f (x : ℂ)‖ ≤ 2 * _root_.GD.N0106.N0428.N0765.N1532.d007583 f R t := by
  have hdisc : DiffContOnCl ℂ f (ball (t : ℂ) |R|) := by
    constructor
    · apply hf.mono
      intro z hz
      have hz' : ‖z - (t : ℂ)‖ < R := by
        simpa only [mem_ball, dist_eq_norm, abs_of_pos hR] using hz
      change |z.im| < d
      have him : |z.im| ≤ ‖z - (t : ℂ)‖ := by
        simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
          Complex.abs_im_le_norm (z - (t : ℂ))
      exact (him.trans_lt hz').trans hRd
    · rw [closure_ball _ (abs_ne_zero.mpr hR.ne'), abs_of_pos hR]
      exact hc.mono (_root_.GD.N0106.N0428.N0765.N1532.d007587 hRd.le)
  apply _root_.GD.N0106.N0428.N0765.N1532.d007574 hR hdisc
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hxt



theorem d007589 {f : ℂ → ℂ} {d B : ℝ}
    (hd : 0 < d) (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hslice : ∀ y : ℝ, |y| ≤ d →
      Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f y) ∧ _root_.GD.N0106.N0428.N0765.N1530.d005195 f y ≤ B)
    (K : Compacts ℝ) :
    Summable (fun n : ℤ =>
      ‖((⟨_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0, _root_.GD.N0106.N0428.N0765.N1531.d007567 hc (by simpa using hd.le)⟩ : C(ℝ, ℂ)).comp
        (ContinuousMap.addRight (n : ℝ))).restrict K‖) := by
  let δ : ℝ := min (d / 8) (1 / 8)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδd : δ ≤ d / 8 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 8 := min_le_right _ _
  have hR : 0 < 4 * δ := by positivity
  have hRd : 4 * δ < d := by linarith
  apply _root_.GD.N0106.N0428.N0765.N1532.d007582 (A := _root_.GD.N0106.N0428.N0765.N1532.d007583 f (4 * δ)) hδ
    (by linarith)
    (_root_.GD.N0106.N0428.N0765.N1532.d007586 hR.le hRd.le hc
      (fun y hy => hslice y (hy.trans hRd.le)))
    (_root_.GD.N0106.N0428.N0765.N1532.d007584 f (4 * δ))
  intro x t hxt
  change ‖_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0 x‖ ≤ 2 * _root_.GD.N0106.N0428.N0765.N1532.d007583 f (4 * δ) t
  simpa only [_root_.GD.N0106.N0428.N0765.N1530.d005194, Complex.ofReal_zero, zero_mul, add_zero] using
    (_root_.GD.N0106.N0428.N0765.N1532.d007588 hR hRd hc hf (x := x) (t := t) (by linarith))




theorem d007590 {f : ℂ → ℂ} {d M : ℝ}
    (hd : 0 < d) (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d))) (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d))
    (K : Compacts ℝ) :
    Summable (fun n : ℤ =>
      ‖((⟨_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0, _root_.GD.N0106.N0428.N0765.N1531.d007567 hc (by simpa using hd.le)⟩ : C(ℝ, ℂ)).comp
        (ContinuousMap.addRight (n : ℝ))).restrict K‖) := by
  apply _root_.GD.N0106.N0428.N0765.N1532.d007589 hd hc hf (B := max (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d))
    (_root_.GD.N0106.N0428.N0765.N1530.d005195 f d))
  intro y hy
  exact ⟨(_root_.GD.N0106.N0428.N0765.N1531.d007569 hd hy hc hf hM hminus hplus).1,
    _root_.GD.N0106.N0428.N0765.N1531.d007570 hd hy hc hf hM hminus hplus⟩



theorem d007591 {f : ℂ → ℂ} {d : ℝ}
    (hd : 0 < d) (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d))) (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x s : ℝ,
      R ≤ |x| → |s| ≤ d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε)
    (K : Compacts ℝ) :
    Summable (fun n : ℤ =>
      ‖((⟨_root_.GD.N0106.N0428.N0765.N1530.d005194 f 0, _root_.GD.N0106.N0428.N0765.N1531.d007567 hc (by simpa using hd.le)⟩ : C(ℝ, ℂ)).comp
        (ContinuousMap.addRight (n : ℝ))).restrict K‖) := by
  obtain ⟨M, _hMpos, hM⟩ := _root_.GD.N0106.N0428.N0765.N1551.d006791 hc hdecay
  exact _root_.GD.N0106.N0428.N0765.N1532.d007590 hd hc hf hM hminus hplus K

end
end GD.N0106.N0428.N0765.N1532

#print axioms _root_.GD.N0106.N0428.N0765.N1532.d007574
#print axioms _root_.GD.N0106.N0428.N0765.N1532.d007582
#print axioms _root_.GD.N0106.N0428.N0765.N1532.d007586
#print axioms _root_.GD.N0106.N0428.N0765.N1532.d007591
