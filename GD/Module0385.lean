import GD.Module0359
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology intervalIntegral

namespace GD.N0106.N0428.N0765.N1673
open _root_.GD.N0106.N0428.N0765.N1534
noncomputable section




def d005830 (v S t : ℝ) : ℝ := t ^ ((9 : ℝ) / 2) * (v + S * t) ^ (-((21 : ℝ) / 2))


def d005831 (v S : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), _root_.GD.N0106.N0428.N0765.N1673.d005830 v S t


def d005832 (v S : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), t * _root_.GD.N0106.N0428.N0765.N1673.d005830 v S t

section Envelope
variable {v S : ℝ} (hv : 0 < v) (hS : 0 < S)
include hv hS

theorem d005833 {t : ℝ} (ht : 0 ≤ t) : 0 < v + S * t := by positivity


theorem d005834 {p : ℝ} (hp : p < -1) :
    IntegrableOn (fun t : ℝ => (v + S * t) ^ p) (Ioi 0) := by
  have hp1 : p + 1 ≠ 0 := by linarith
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => (v + S * t) ^ (p + 1) / (S * (p + 1)))
      ((v + S * t) ^ p) t := by
    intro t ht
    have h0 : v + S * t ≠ 0 := (_root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS (le_of_lt ht)).ne'
    have h : HasDerivAt (fun t : ℝ => v + S * t) S t := by
      simpa using ((hasDerivAt_id' t).const_mul S).const_add v
    refine ((h.rpow_const (p := p + 1) (Or.inl h0)).div_const (S * (p + 1))).congr_deriv ?_
    rw [show p + 1 - 1 = p by ring]
    field_simp
  refine integrableOn_Ioi_deriv_of_nonneg ?_ hderiv ?_ (l := 0) ?_
  · apply ContinuousAt.continuousWithinAt
    have h0 : v + S * 0 ≠ 0 := by simp [hv.ne']
    exact ((by fun_prop : Continuous fun t : ℝ => v + S * t).continuousAt.rpow_const
      (Or.inl h0)).div_const _
  · intro t ht
    exact (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS (le_of_lt ht)) _).le
  · have h1 : Tendsto (fun t : ℝ => v + S * t) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hS)
    have h2 : Tendsto (fun t : ℝ => (v + S * t) ^ (p + 1)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (by linarith : 0 < -(p + 1))).comp h1
      simpa [Function.comp_def] using this
    simpa using h2.div_const (S * (p + 1))


theorem d005835 {a b t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    t ^ a * (v + S * t) ^ (-(a + b)) ≤ S ^ (-a) * (v + S * t) ^ (-b) := by
  have hpos := _root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS ht.le
  have h1 : (v + S * t) ^ (-(a + b)) = (v + S * t) ^ (-a) * (v + S * t) ^ (-b) := by
    rw [← Real.rpow_add hpos]; ring_nf
  rw [h1, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hpos _).le
  rw [Real.rpow_neg hpos.le, Real.rpow_neg hS.le, ← Real.inv_rpow hpos.le, ← Real.inv_rpow hS.le,
    ← Real.mul_rpow ht.le (inv_nonneg.mpr hpos.le)]
  apply Real.rpow_le_rpow (by positivity) _ ha
  rw [← div_eq_mul_inv, div_le_iff₀ hpos, inv_mul_eq_div, le_div_iff₀ hS]
  nlinarith

theorem d005836 {t : ℝ} (ht : 0 ≤ t) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1673.d005830 v S t := by
  unfold _root_.GD.N0106.N0428.N0765.N1673.d005830
  exact mul_nonneg (Real.rpow_nonneg ht _) (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS ht).le _)

theorem d005837 {t : ℝ} (ht : 0 < t) : 0 < _root_.GD.N0106.N0428.N0765.N1673.d005830 v S t := by
  unfold _root_.GD.N0106.N0428.N0765.N1673.d005830
  exact mul_pos (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS ht.le) _)

theorem d005838 {t : ℝ} (ht : 0 < t) :
    _root_.GD.N0106.N0428.N0765.N1673.d005830 v S t ≤ S ^ (-((9 : ℝ) / 2)) * (v + S * t) ^ (-(6 : ℝ)) := by
  unfold _root_.GD.N0106.N0428.N0765.N1673.d005830
  have := _root_.GD.N0106.N0428.N0765.N1673.d005835 hv hS (a := (9 : ℝ) / 2) (b := 6) (t := t) (by norm_num) ht
  rwa [show ((9 : ℝ) / 2 + 6) = 21 / 2 by norm_num] at this

theorem d005839 {t : ℝ} (ht : 0 < t) :
    t * _root_.GD.N0106.N0428.N0765.N1673.d005830 v S t ≤ S ^ (-((11 : ℝ) / 2)) * (v + S * t) ^ (-(5 : ℝ)) := by
  unfold _root_.GD.N0106.N0428.N0765.N1673.d005830
  have h := _root_.GD.N0106.N0428.N0765.N1673.d005835 hv hS (a := (11 : ℝ) / 2) (b := 5) (t := t) (by norm_num) ht
  rw [show ((11 : ℝ) / 2 + 5) = 21 / 2 by norm_num] at h
  have h2 : t * t ^ ((9 : ℝ) / 2) = t ^ ((11 : ℝ) / 2) := by
    rw [show ((11 : ℝ) / 2) = 1 + 9 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one]
  rw [← mul_assoc, h2]
  exact h

theorem d005840 : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1673.d005830 v S) (Ioi 0) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  unfold _root_.GD.N0106.N0428.N0765.N1673.d005830
  refine ContinuousAt.mul ?_ ?_
  · exact Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt ht))
  · exact (by fun_prop : Continuous fun t : ℝ => v + S * t).continuousAt.rpow_const
      (Or.inl (_root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS (le_of_lt ht)).ne')

theorem d005841 : IntegrableOn (_root_.GD.N0106.N0428.N0765.N1673.d005830 v S) (Ioi 0) := by
  refine Integrable.mono' ((_root_.GD.N0106.N0428.N0765.N1673.d005834 hv hS (p := -6) (by norm_num)).const_mul
    (S ^ (-((9 : ℝ) / 2)))) ((_root_.GD.N0106.N0428.N0765.N1673.d005840 hv hS).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1673.d005836 hv hS (le_of_lt ht))]
  exact _root_.GD.N0106.N0428.N0765.N1673.d005838 hv hS ht

theorem d005842 : IntegrableOn (fun t => t * _root_.GD.N0106.N0428.N0765.N1673.d005830 v S t) (Ioi 0) := by
  refine Integrable.mono' ((_root_.GD.N0106.N0428.N0765.N1673.d005834 hv hS (p := -5) (by norm_num)).const_mul
    (S ^ (-((11 : ℝ) / 2)))) ?_ ?_
  · exact (continuousOn_id.mul (_root_.GD.N0106.N0428.N0765.N1673.d005840 hv hS)).aestronglyMeasurable measurableSet_Ioi
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt ht) (_root_.GD.N0106.N0428.N0765.N1673.d005836 hv hS (le_of_lt ht)))]
  exact _root_.GD.N0106.N0428.N0765.N1673.d005839 hv hS ht

theorem d005843 : 0 < _root_.GD.N0106.N0428.N0765.N1673.d005831 v S := by
  unfold _root_.GD.N0106.N0428.N0765.N1673.d005831
  rw [setIntegral_pos_iff_support_of_nonneg_ae ?_ (_root_.GD.N0106.N0428.N0765.N1673.d005841 hv hS)]
  · have hsub : Ioi (0 : ℝ) ⊆ Function.support (_root_.GD.N0106.N0428.N0765.N1673.d005830 v S) ∩ Ioi 0 := fun t ht =>
      ⟨Function.mem_support.mpr (_root_.GD.N0106.N0428.N0765.N1673.d005837 hv hS ht).ne', ht⟩
    exact lt_of_lt_of_le (by simp) (measure_mono hsub)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact _root_.GD.N0106.N0428.N0765.N1673.d005836 hv hS (le_of_lt ht)




theorem d005844 {t : ℝ} (ht : 0 < t) :
    t ^ ((9 : ℝ) / 2) * (v + S * t) ^ (-((19 : ℝ) / 2)) = v * _root_.GD.N0106.N0428.N0765.N1673.d005830 v S t + S * (t * _root_.GD.N0106.N0428.N0765.N1673.d005830 v S t) := by
  unfold _root_.GD.N0106.N0428.N0765.N1673.d005830
  have hpos := _root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS ht.le
  have h : (v + S * t) ^ (-((19 : ℝ) / 2)) = (v + S * t) * (v + S * t) ^ (-((21 : ℝ) / 2)) := by
    rw [show (-((19 : ℝ) / 2)) = 1 + -(21 / 2) by norm_num, Real.rpow_add hpos, Real.rpow_one]
  rw [h]
  ring

theorem d005845 :
    IntegrableOn (fun t : ℝ => t ^ ((9 : ℝ) / 2) * (v + S * t) ^ (-((19 : ℝ) / 2))) (Ioi 0) := by
  refine IntegrableOn.congr_fun (((_root_.GD.N0106.N0428.N0765.N1673.d005841 hv hS).const_mul v).add
    ((_root_.GD.N0106.N0428.N0765.N1673.d005842 hv hS).const_mul S)) ?_ measurableSet_Ioi
  intro t ht
  simp only [Pi.add_apply]
  exact (_root_.GD.N0106.N0428.N0765.N1673.d005844 hv hS ht).symm

theorem d005846 : _root_.GD.N0106.N0428.N0765.N1673.d005832 v S = 11 * v / (8 * S) * _root_.GD.N0106.N0428.N0765.N1673.d005831 v S := by

  set F : ℝ → ℝ := fun t => t ^ ((11 : ℝ) / 2) * (v + S * t) ^ (-((19 : ℝ) / 2)) with hF
  set F' : ℝ → ℝ := fun t => (11 / 2) * (t ^ ((9 : ℝ) / 2) * (v + S * t) ^ (-((19 : ℝ) / 2))) -
    (19 / 2) * S * (t * _root_.GD.N0106.N0428.N0765.N1673.d005830 v S t) with hF'
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt F (F' t) t := by
    intro t ht
    have hpos := _root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS (le_of_lt ht)
    have h1 : HasDerivAt (fun t : ℝ => t ^ ((11 : ℝ) / 2)) ((11 / 2) * t ^ ((11 : ℝ) / 2 - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt ht))
    have h2 : HasDerivAt (fun t : ℝ => (v + S * t) ^ (-((19 : ℝ) / 2)))
        ((-((19 : ℝ) / 2)) * (v + S * t) ^ (-((19 : ℝ) / 2) - 1) * S) t := by
      have h : HasDerivAt (fun t : ℝ => v + S * t) S t := by
        simpa using ((hasDerivAt_id' t).const_mul S).const_add v
      exact (h.rpow_const (p := -((19 : ℝ) / 2)) (Or.inl hpos.ne')).congr_deriv (by ring)
    show HasDerivAt (fun t : ℝ => t ^ ((11 : ℝ) / 2) * (v + S * t) ^ (-((19 : ℝ) / 2)))
      ((11 / 2) * (t ^ ((9 : ℝ) / 2) * (v + S * t) ^ (-((19 : ℝ) / 2))) -
        (19 / 2) * S * (t * _root_.GD.N0106.N0428.N0765.N1673.d005830 v S t)) t
    refine (h1.mul h2).congr_deriv ?_
    unfold _root_.GD.N0106.N0428.N0765.N1673.d005830
    rw [show ((11 : ℝ) / 2 - 1) = 9 / 2 by norm_num,
      show (-((19 : ℝ) / 2) - 1) = -(21 / 2) by norm_num]
    have h4 : t * t ^ ((9 : ℝ) / 2) = t ^ ((11 : ℝ) / 2) := by
      rw [show ((11 : ℝ) / 2) = 1 + 9 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one]
    rw [← h4]
    ring
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    show ContinuousAt (fun t : ℝ => t ^ ((11 : ℝ) / 2) * (v + S * t) ^ (-((19 : ℝ) / 2))) 0
    refine ContinuousAt.mul ?_ ?_
    · exact Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))
    · have h0 : v + S * 0 ≠ 0 := by simp [hv.ne']
      exact (by fun_prop : Continuous fun t : ℝ => v + S * t).continuousAt.rpow_const (Or.inl h0)
  have hint : IntegrableOn F' (Ioi 0) := by
    rw [hF']
    exact ((_root_.GD.N0106.N0428.N0765.N1673.d005845 hv hS).const_mul _).sub ((_root_.GD.N0106.N0428.N0765.N1673.d005842 hv hS).const_mul _)
  have hlim : Tendsto F atTop (𝓝 0) := by

    have hbound : ∀ᶠ t in atTop, F t ≤ S ^ (-((11 : ℝ) / 2)) * (v + S * t) ^ (-(4 : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      have := _root_.GD.N0106.N0428.N0765.N1673.d005835 hv hS (a := (11 : ℝ) / 2) (b := 4) (t := t) (by norm_num) ht
      rwa [show ((11 : ℝ) / 2 + 4) = 19 / 2 by norm_num] at this
    have hnn : ∀ᶠ t in atTop, 0 ≤ F t := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS ht.le).le _)
    have h1 : Tendsto (fun t : ℝ => v + S * t) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop hS)
    have h2 : Tendsto (fun t : ℝ => S ^ (-((11 : ℝ) / 2)) * (v + S * t) ^ (-(4 : ℝ))) atTop (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4)).comp h1).const_mul
        (S ^ (-((11 : ℝ) / 2)))
      simpa [Function.comp_def] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 hnn hbound
  have hIBP := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hF0 : F 0 = 0 := by
    show (0 : ℝ) ^ ((11 : ℝ) / 2) * (v + S * 0) ^ (-((19 : ℝ) / 2)) = 0
    simp
  have e1 : (∫ t in Ioi (0 : ℝ), F' t) =
      (11 / 2) * (v * _root_.GD.N0106.N0428.N0765.N1673.d005831 v S + S * _root_.GD.N0106.N0428.N0765.N1673.d005832 v S) - (19 / 2) * S * _root_.GD.N0106.N0428.N0765.N1673.d005832 v S := by
    show (∫ t in Ioi (0 : ℝ), (11 / 2) * (t ^ ((9 : ℝ) / 2) * (v + S * t) ^ (-((19 : ℝ) / 2))) -
      (19 / 2) * S * (t * _root_.GD.N0106.N0428.N0765.N1673.d005830 v S t)) = _
    rw [MeasureTheory.integral_sub ((_root_.GD.N0106.N0428.N0765.N1673.d005845 hv hS).const_mul _)
        ((_root_.GD.N0106.N0428.N0765.N1673.d005842 hv hS).const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => _root_.GD.N0106.N0428.N0765.N1673.d005844 hv hS ht),
      MeasureTheory.integral_add ((_root_.GD.N0106.N0428.N0765.N1673.d005841 hv hS).const_mul v)
        ((_root_.GD.N0106.N0428.N0765.N1673.d005842 hv hS).const_mul S),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rfl
  have key : (11 / 2) * (v * _root_.GD.N0106.N0428.N0765.N1673.d005831 v S + S * _root_.GD.N0106.N0428.N0765.N1673.d005832 v S) - (19 / 2) * S * _root_.GD.N0106.N0428.N0765.N1673.d005832 v S = 0 := by
    rw [← e1, hIBP, hF0, sub_zero]
  have hS8 : (8 * S : ℝ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hS8]
  linear_combination (-2 : ℝ) * key

end Envelope




def d005847 (η u v w t : ℝ) : ℝ :=
  (t * (1 - t / η)) ^ ((9 : ℝ) / 2) *
    (v * (1 - t / η) + w * t + (1 + η⁻¹) * u * t * (1 - t / η)) ^ (-((21 : ℝ) / 2))

section Rescale
variable {η u v w : ℝ}

theorem d005848 (hη : 0 < η) {t : ℝ} (ht0 : 0 ≤ t) (htη : t ≤ η) :
    _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w (t / η) = η ^ (-((9 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w t := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005329 _root_.GD.N0106.N0428.N0765.N1534.d005328 _root_.GD.N0106.N0428.N0765.N1673.d005847
  have hr : 0 ≤ 1 - t / η := by
    rw [sub_nonneg, div_le_one hη]; exact htη
  have h1 : t / η * (1 - t / η) = η⁻¹ * (t * (1 - t / η)) := by ring
  have h2 : v * (1 - t / η) + η * w * (t / η) + (1 + η) * u * (t / η) * (1 - t / η) =
      v * (1 - t / η) + w * t + (1 + η⁻¹) * u * t * (1 - t / η) := by
    field_simp
    ring
  rw [h1, h2, Real.mul_rpow (inv_nonneg.mpr hη.le) (mul_nonneg ht0 hr), Real.inv_rpow hη.le,
    ← Real.rpow_neg hη.le]
  ring


theorem d005849 (hη : 0 < η) :
    η * _root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w =
      (∫ t in (0 : ℝ)..η, t * _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w t) / ∫ t in (0 : ℝ)..η, _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w t := by
  unfold _root_.GD.N0106.N0428.N0765.N1534.d005330
  set c : ℝ := η⁻¹ * η ^ (-((9 : ℝ) / 2)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact mul_ne_zero (inv_ne_zero hη.ne') (Real.rpow_pos_of_pos hη _).ne'
  have hden : (∫ l in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w l) =
      c * ∫ t in (0 : ℝ)..η, _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w t := by
    have h := intervalIntegral.integral_comp_div (a := 0) (b := η) (c := η)
      (fun l => _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w l) hη.ne'
    rw [zero_div, div_self hη.ne', smul_eq_mul] at h
    have h2 : (∫ x in (0 : ℝ)..η, _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w (x / η)) =
        ∫ x in (0 : ℝ)..η, η ^ (-((9 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w x :=
      intervalIntegral.integral_congr fun x hx => by
        rw [uIcc_of_le hη.le] at hx
        exact _root_.GD.N0106.N0428.N0765.N1673.d005848 hη hx.1 hx.2
    rw [h2, intervalIntegral.integral_const_mul] at h
    rw [hc, mul_assoc, h, ← mul_assoc, inv_mul_cancel₀ hη.ne', one_mul]
  have hnum : (∫ l in (0 : ℝ)..1, l * _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w l) =
      c * (η⁻¹ * ∫ t in (0 : ℝ)..η, t * _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w t) := by
    have h := intervalIntegral.integral_comp_div (a := 0) (b := η) (c := η)
      (fun l => l * _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w l) hη.ne'
    rw [zero_div, div_self hη.ne', smul_eq_mul] at h
    have h2 : (∫ x in (0 : ℝ)..η, x / η * _root_.GD.N0106.N0428.N0765.N1534.d005329 η u v w (x / η)) =
        ∫ x in (0 : ℝ)..η, (η⁻¹ * η ^ (-((9 : ℝ) / 2))) * (x * _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w x) :=
      intervalIntegral.integral_congr fun x hx => by
        rw [uIcc_of_le hη.le] at hx
        rw [_root_.GD.N0106.N0428.N0765.N1673.d005848 hη hx.1 hx.2]
        ring
    rw [h2, intervalIntegral.integral_const_mul] at h
    rw [hc, mul_left_comm, h, ← mul_assoc, inv_mul_cancel₀ hη.ne', one_mul]
  rw [hnum, hden, mul_div_mul_left _ _ hc0, ← mul_div_assoc, ← mul_assoc,
    mul_inv_cancel₀ hη.ne', one_mul]

end Rescale




def d005850 (u v w : ℝ) : ℝ := min (1 / 2) (min (w / (2 * (u + w))) (w / (4 * v)))


theorem d005851 (f : ℝ → ℝ) {η : ℝ} (hη : 0 < η) :
    (∫ t in (0 : ℝ)..η, f t) = ∫ t in Ioi (0 : ℝ), (Ioc 0 η).indicator f t := by
  rw [intervalIntegral.integral_of_le hη.le, MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]

section Limit
variable {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
include hu hv hw

theorem d005852 : 0 < _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w := by
  unfold _root_.GD.N0106.N0428.N0765.N1673.d005850
  have hS : 0 < u + w := by linarith
  exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))

theorem d005853 : _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w ≤ 1 / 2 := min_le_left _ _

theorem d005854 : _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w * (u + w) ≤ w / 2 := by
  have hS : 0 < u + w := by linarith
  have h : _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w ≤ w / (2 * (u + w)) := (min_le_right _ _).trans (min_le_left _ _)
  calc _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w * (u + w) ≤ w / (2 * (u + w)) * (u + w) :=
        mul_le_mul_of_nonneg_right h hS.le
    _ = w / 2 := by field_simp

theorem d005855 : _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w * v ≤ w / 4 := by
  have h : _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w ≤ w / (4 * v) := (min_le_right _ _).trans (min_le_right _ _)
  calc _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w * v ≤ w / (4 * v) * v := mul_le_mul_of_nonneg_right h hv.le
    _ = w / 4 := by field_simp


theorem d005856 {η t : ℝ} (hη : 1 ≤ η) (ht : 0 < t) (htη : t ≤ η) :
    _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w * (v + (u + w) * t) ≤
      v * (1 - t / η) + w * t + (1 + η⁻¹) * u * t * (1 - t / η) := by
  have hη0 : 0 < η := by linarith
  have hr0 : 0 ≤ t / η := div_nonneg ht.le hη0.le
  have hr1 : t / η ≤ 1 := by rw [div_le_one hη0]; exact htη
  have hc1 := _root_.GD.N0106.N0428.N0765.N1673.d005853 hu hv hw
  have hc2 := _root_.GD.N0106.N0428.N0765.N1673.d005854 hu hv hw
  have hc3 := _root_.GD.N0106.N0428.N0765.N1673.d005855 hu hv hw
  have hc0 := _root_.GD.N0106.N0428.N0765.N1673.d005852 hu hv hw
  have huterm : 0 ≤ (1 + η⁻¹) * u * t * (1 - t / η) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hu) ht.le) (by linarith)
  have huterm' : u * t * (1 - t / η) ≤ (1 + η⁻¹) * u * t * (1 - t / η) := by
    have : 0 ≤ η⁻¹ * (u * t * (1 - t / η)) :=
      mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hu ht.le) (by linarith))
    linarith
  rcases le_or_gt (t / η) (1 / 2) with hcase | hcase
  · have h1 : v / 2 ≤ v * (1 - t / η) := by nlinarith
    have h2 : u * t / 2 ≤ u * t * (1 - t / η) := by
      have := mul_nonneg (mul_nonneg hu ht.le) (by linarith : (0 : ℝ) ≤ 1 / 2 - t / η)
      nlinarith
    have h3 : _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w * (v + (u + w) * t) ≤ (1 / 2) * (v + (u + w) * t) :=
      mul_le_mul_of_nonneg_right hc1 (by positivity)
    nlinarith
  · have ht2 : 1 / 2 < t := by
      have := (lt_div_iff₀ hη0).mp hcase
      linarith
    have h1 : 0 ≤ v * (1 - t / η) := mul_nonneg hv.le (by linarith)
    have h2 : _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w * (v + (u + w) * t) ≤ w / 4 + w / 2 * t := by nlinarith
    have h3 : w / 4 ≤ w / 2 * t := by nlinarith
    nlinarith

theorem d005857 {η t : ℝ} (hη : 1 ≤ η) (ht : 0 < t) (htη : t ≤ η) :
    0 < v * (1 - t / η) + w * t + (1 + η⁻¹) * u * t * (1 - t / η) := by
  have hS : 0 < u + w := by linarith
  have hpos : 0 < v + (u + w) * t := by positivity
  exact lt_of_lt_of_le (mul_pos (_root_.GD.N0106.N0428.N0765.N1673.d005852 hu hv hw) hpos) (_root_.GD.N0106.N0428.N0765.N1673.d005856 hu hv hw hη ht htη)

theorem d005858 {η t : ℝ} (hη : 1 ≤ η) (ht : 0 < t) (htη : t ≤ η) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w t := by
  unfold _root_.GD.N0106.N0428.N0765.N1673.d005847
  exact mul_nonneg (Real.rpow_nonneg (mul_nonneg ht.le (by
    rw [sub_nonneg, div_le_one (by linarith)]; exact htη)) _)
    (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1673.d005857 hu hv hw hη ht htη).le _)


theorem d005859 {η t : ℝ} (hη : 1 ≤ η) (ht : 0 < t) (htη : t ≤ η) :
    _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w t ≤ _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w ^ (-((21 : ℝ) / 2)) *
      ((u + w) ^ (-((9 : ℝ) / 2)) * (v + (u + w) * t) ^ (-(6 : ℝ))) := by
  have hS : 0 < u + w := by linarith
  have hc0 := _root_.GD.N0106.N0428.N0765.N1673.d005852 hu hv hw
  have hr : 0 ≤ 1 - t / η := by rw [sub_nonneg, div_le_one (by linarith)]; exact htη
  have hpos := _root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS ht.le
  unfold _root_.GD.N0106.N0428.N0765.N1673.d005847
  have h1 : (t * (1 - t / η)) ^ ((9 : ℝ) / 2) ≤ t ^ ((9 : ℝ) / 2) :=
    Real.rpow_le_rpow (mul_nonneg ht.le hr) (by nlinarith [mul_nonneg ht.le hr, div_nonneg ht.le (by linarith : (0:ℝ) ≤ η)]) (by norm_num)
  have h2 : (v * (1 - t / η) + w * t + (1 + η⁻¹) * u * t * (1 - t / η)) ^ (-((21 : ℝ) / 2)) ≤
      (_root_.GD.N0106.N0428.N0765.N1673.d005850 u v w * (v + (u + w) * t)) ^ (-((21 : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (_root_.GD.N0106.N0428.N0765.N1673.d005856 hu hv hw hη ht htη) (by norm_num)
  calc (t * (1 - t / η)) ^ ((9 : ℝ) / 2) *
        (v * (1 - t / η) + w * t + (1 + η⁻¹) * u * t * (1 - t / η)) ^ (-((21 : ℝ) / 2))
      ≤ t ^ ((9 : ℝ) / 2) * (_root_.GD.N0106.N0428.N0765.N1673.d005850 u v w * (v + (u + w) * t)) ^ (-((21 : ℝ) / 2)) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1673.d005857 hu hv hw hη ht htη).le _)
          (Real.rpow_nonneg ht.le _)
    _ = _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w ^ (-((21 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1673.d005830 v (u + w) t := by
        unfold _root_.GD.N0106.N0428.N0765.N1673.d005830
        rw [Real.mul_rpow hc0.le hpos.le]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1673.d005838 hv hS ht) (Real.rpow_nonneg hc0.le _)

theorem d005860 {η t : ℝ} (hη : 1 ≤ η) (ht : 0 < t) (htη : t ≤ η) :
    t * _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w t ≤ _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w ^ (-((21 : ℝ) / 2)) *
      ((u + w) ^ (-((11 : ℝ) / 2)) * (v + (u + w) * t) ^ (-(5 : ℝ))) := by
  have hS : 0 < u + w := by linarith
  have hc0 := _root_.GD.N0106.N0428.N0765.N1673.d005852 hu hv hw
  have hr : 0 ≤ 1 - t / η := by rw [sub_nonneg, div_le_one (by linarith)]; exact htη
  have hpos := _root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS ht.le
  unfold _root_.GD.N0106.N0428.N0765.N1673.d005847
  have h1 : (t * (1 - t / η)) ^ ((9 : ℝ) / 2) ≤ t ^ ((9 : ℝ) / 2) :=
    Real.rpow_le_rpow (mul_nonneg ht.le hr) (by nlinarith [mul_nonneg ht.le hr, div_nonneg ht.le (by linarith : (0:ℝ) ≤ η)]) (by norm_num)
  have h2 : (v * (1 - t / η) + w * t + (1 + η⁻¹) * u * t * (1 - t / η)) ^ (-((21 : ℝ) / 2)) ≤
      (_root_.GD.N0106.N0428.N0765.N1673.d005850 u v w * (v + (u + w) * t)) ^ (-((21 : ℝ) / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (_root_.GD.N0106.N0428.N0765.N1673.d005856 hu hv hw hη ht htη) (by norm_num)
  calc t * ((t * (1 - t / η)) ^ ((9 : ℝ) / 2) *
        (v * (1 - t / η) + w * t + (1 + η⁻¹) * u * t * (1 - t / η)) ^ (-((21 : ℝ) / 2)))
      ≤ t * (t ^ ((9 : ℝ) / 2) * (_root_.GD.N0106.N0428.N0765.N1673.d005850 u v w * (v + (u + w) * t)) ^ (-((21 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2
          (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1673.d005857 hu hv hw hη ht htη).le _) (Real.rpow_nonneg ht.le _)) ht.le
    _ = _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w ^ (-((21 : ℝ) / 2)) * (t * _root_.GD.N0106.N0428.N0765.N1673.d005830 v (u + w) t) := by
        unfold _root_.GD.N0106.N0428.N0765.N1673.d005830
        rw [Real.mul_rpow hc0.le hpos.le]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1673.d005839 hv hS ht) (Real.rpow_nonneg hc0.le _)

theorem d005861 {η : ℝ} (hη : 1 ≤ η) : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w) (Ioc 0 η) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  unfold _root_.GD.N0106.N0428.N0765.N1673.d005847
  refine ContinuousAt.mul ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => t * (1 - t / η)).continuousAt.rpow_const
      (Or.inr (by norm_num))
  · exact (by fun_prop : Continuous fun t : ℝ =>
      v * (1 - t / η) + w * t + (1 + η⁻¹) * u * t * (1 - t / η)).continuousAt.rpow_const
      (Or.inl (_root_.GD.N0106.N0428.N0765.N1673.d005857 hu hv hw hη ht.1 ht.2).ne')


theorem d005862 {t : ℝ} (ht : 0 < t) :
    Tendsto (fun η : ℝ => _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w t) atTop (𝓝 (_root_.GD.N0106.N0428.N0765.N1673.d005830 v (u + w) t)) := by
  have h0 : Tendsto (fun η : ℝ => t / η) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hinv : Tendsto (fun η : ℝ => η⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h1 : Tendsto (fun η : ℝ => (t * (1 - t / η)) ^ ((9 : ℝ) / 2)) atTop
      (𝓝 ((t * (1 - 0)) ^ ((9 : ℝ) / 2))) :=
    (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).tendsto.comp
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub h0))
  have hL : v * (1 - 0) + w * t + (1 + 0) * u * t * (1 - 0) ≠ 0 := by
    have : v * (1 - 0) + w * t + (1 + 0) * u * t * (1 - 0) = v + (u + w) * t := by ring
    rw [this]; positivity
  have h2 : Tendsto (fun η : ℝ =>
      (v * (1 - t / η) + w * t + (1 + η⁻¹) * u * t * (1 - t / η)) ^ (-((21 : ℝ) / 2))) atTop
      (𝓝 ((v * (1 - 0) + w * t + (1 + 0) * u * t * (1 - 0)) ^ (-((21 : ℝ) / 2)))) :=
    (Real.continuousAt_rpow_const _ _ (Or.inl hL)).tendsto.comp
      (((tendsto_const_nhds.mul (tendsto_const_nhds.sub h0)).add
        (tendsto_const_nhds.mul tendsto_const_nhds)).add
        ((((tendsto_const_nhds.add hinv).mul tendsto_const_nhds).mul tendsto_const_nhds).mul
          (tendsto_const_nhds.sub h0)))
  have h3 := h1.mul h2
  have hval : (t * (1 - 0)) ^ ((9 : ℝ) / 2) *
      (v * (1 - 0) + w * t + (1 + 0) * u * t * (1 - 0)) ^ (-((21 : ℝ) / 2)) =
      _root_.GD.N0106.N0428.N0765.N1673.d005830 v (u + w) t := by
    unfold _root_.GD.N0106.N0428.N0765.N1673.d005830
    rw [show v * (1 - 0) + w * t + (1 + 0) * u * t * (1 - 0) = v + (u + w) * t by ring,
      show t * (1 - 0) = t by ring]
  rw [hval] at h3
  exact h3

theorem d005863 {η : ℝ} (hη : 1 ≤ η) :
    AEStronglyMeasurable ((Ioc 0 η).indicator (_root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w)) (volume.restrict (Ioi 0)) := by
  rw [aestronglyMeasurable_indicator_iff measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr Ioc_subset_Ioi_self]
  exact (_root_.GD.N0106.N0428.N0765.N1673.d005861 hu hv hw hη).aestronglyMeasurable measurableSet_Ioc

theorem d005864 :
    Tendsto (fun η : ℝ => ∫ t in (0 : ℝ)..η, _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w t) atTop (𝓝 (_root_.GD.N0106.N0428.N0765.N1673.d005831 v (u + w))) := by
  have hS : 0 < u + w := by linarith
  have hc0 := _root_.GD.N0106.N0428.N0765.N1673.d005852 hu hv hw
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (l := atTop)
    (F := fun η t => (Ioc 0 η).indicator (_root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w) t) (f := _root_.GD.N0106.N0428.N0765.N1673.d005830 v (u + w))
    (fun t => _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w ^ (-((21 : ℝ) / 2)) *
      ((u + w) ^ (-((9 : ℝ) / 2)) * (v + (u + w) * t) ^ (-(6 : ℝ))))
    (by
      filter_upwards [eventually_ge_atTop 1] with η hη
      exact _root_.GD.N0106.N0428.N0765.N1673.d005863 hu hv hw hη)
    (by
      filter_upwards [eventually_ge_atTop 1] with η hη
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      by_cases hmem : t ∈ Ioc 0 η
      · rw [indicator_of_mem hmem, Real.norm_eq_abs,
          abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1673.d005858 hu hv hw hη hmem.1 hmem.2)]
        exact _root_.GD.N0106.N0428.N0765.N1673.d005859 hu hv hw hη hmem.1 hmem.2
      · rw [indicator_of_notMem hmem, norm_zero]
        have := _root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS (le_of_lt ht)
        positivity)
    (((_root_.GD.N0106.N0428.N0765.N1673.d005834 hv hS (p := -6) (by norm_num)).const_mul _).const_mul _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      refine (_root_.GD.N0106.N0428.N0765.N1673.d005862 hu hv hw ht).congr' ?_
      filter_upwards [eventually_ge_atTop t] with η hη
      rw [indicator_of_mem (show t ∈ Ioc 0 η from ⟨ht, hη⟩)])
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with η hη
  exact (_root_.GD.N0106.N0428.N0765.N1673.d005851 _ hη).symm

theorem d005865 :
    Tendsto (fun η : ℝ => ∫ t in (0 : ℝ)..η, t * _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w t) atTop (𝓝 (_root_.GD.N0106.N0428.N0765.N1673.d005832 v (u + w))) := by
  have hS : 0 < u + w := by linarith
  have hc0 := _root_.GD.N0106.N0428.N0765.N1673.d005852 hu hv hw
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (l := atTop)
    (F := fun η t => (Ioc 0 η).indicator (fun t => t * _root_.GD.N0106.N0428.N0765.N1673.d005847 η u v w t) t)
    (f := fun t => t * _root_.GD.N0106.N0428.N0765.N1673.d005830 v (u + w) t)
    (fun t => _root_.GD.N0106.N0428.N0765.N1673.d005850 u v w ^ (-((21 : ℝ) / 2)) *
      ((u + w) ^ (-((11 : ℝ) / 2)) * (v + (u + w) * t) ^ (-(5 : ℝ))))
    (by
      filter_upwards [eventually_ge_atTop 1] with η hη
      rw [aestronglyMeasurable_indicator_iff measurableSet_Ioc,
        Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.mpr Ioc_subset_Ioi_self]
      exact (continuousOn_id.mul (_root_.GD.N0106.N0428.N0765.N1673.d005861 hu hv hw hη)).aestronglyMeasurable
        measurableSet_Ioc)
    (by
      filter_upwards [eventually_ge_atTop 1] with η hη
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      by_cases hmem : t ∈ Ioc 0 η
      · rw [indicator_of_mem hmem, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hmem.1.le (_root_.GD.N0106.N0428.N0765.N1673.d005858 hu hv hw hη hmem.1 hmem.2))]
        exact _root_.GD.N0106.N0428.N0765.N1673.d005860 hu hv hw hη hmem.1 hmem.2
      · rw [indicator_of_notMem hmem, norm_zero]
        have := _root_.GD.N0106.N0428.N0765.N1673.d005833 hv hS (le_of_lt ht)
        positivity)
    (((_root_.GD.N0106.N0428.N0765.N1673.d005834 hv hS (p := -5) (by norm_num)).const_mul _).const_mul _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      refine (tendsto_const_nhds.mul (_root_.GD.N0106.N0428.N0765.N1673.d005862 hu hv hw ht)).congr' ?_
      filter_upwards [eventually_ge_atTop t] with η hη
      rw [indicator_of_mem (show t ∈ Ioc 0 η from ⟨ht, hη⟩)])
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with η hη
  exact (_root_.GD.N0106.N0428.N0765.N1673.d005851 _ hη).symm


theorem d005866 :
    Tendsto (fun η : ℝ => η * _root_.GD.N0106.N0428.N0765.N1534.d005330 η u v w) atTop (𝓝 (11 / 8 * v / (u + w))) := by
  have hS : 0 < u + w := by linarith
  have h := (_root_.GD.N0106.N0428.N0765.N1673.d005865 hu hv hw).div (_root_.GD.N0106.N0428.N0765.N1673.d005864 hu hv hw) (_root_.GD.N0106.N0428.N0765.N1673.d005843 hv hS).ne'
  have hval : _root_.GD.N0106.N0428.N0765.N1673.d005832 v (u + w) / _root_.GD.N0106.N0428.N0765.N1673.d005831 v (u + w) = 11 / 8 * v / (u + w) := by
    rw [_root_.GD.N0106.N0428.N0765.N1673.d005846 hv hS, mul_div_assoc, div_self (_root_.GD.N0106.N0428.N0765.N1673.d005843 hv hS).ne', mul_one]
    field_simp <;> ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with η hη
  exact (_root_.GD.N0106.N0428.N0765.N1673.d005849 hη).symm

end Limit

end

end GD.N0106.N0428.N0765.N1673
