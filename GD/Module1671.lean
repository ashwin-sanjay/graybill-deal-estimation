import GD.Module1670
import Mathlib.Probability.Distributions.Pareto

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators

namespace GD.N0089
noncomputable section

theorem d028316 (a : ℝ) : ∀ᵐ x ∂paretoMeasure 1 a, 1 ≤ x := by
  rw [paretoMeasure]
  change ∀ᵐ x ∂volume.withDensity (fun x => ENNReal.ofReal (paretoPDFReal 1 a x)), 1 ≤ x
  rw [ae_withDensity_iff ((measurable_paretoPDFReal 1 a).ennreal_ofReal)]
  filter_upwards with x hx
  by_contra h
  exact hx (paretoPDF_of_lt (lt_of_not_ge h))

theorem d028317 (a t : ℝ) (ha : 0 < a) :
    paretoMeasure 1 a (Ici t) = ENNReal.ofReal ((max 1 t) ^ (-a)) := by
  letI := isProbabilityMeasure_paretoMeasure (by norm_num : (0 : ℝ) < 1) ha
  by_cases ht : t ≤ 1
  · have hfull : Ici t =ᵐ[paretoMeasure 1 a] univ := by
      filter_upwards [_root_.GD.N0089.d028316 a] with x hx
      apply propext
      exact iff_of_true (ht.trans hx) trivial
    rw [measure_congr hfull, measure_univ, max_eq_left ht, Real.one_rpow, ENNReal.ofReal_one]
  · have ht1 : 1 ≤ t := (lt_of_not_ge ht).le
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
    rw [paretoMeasure, withDensity_apply _ measurableSet_Ici, max_eq_right ht1]
    have heq : (∫⁻ x in Ici t, paretoPDF 1 a x) =
        ∫⁻ x in Ici t, ENNReal.ofReal (a * x ^ (-(a + 1))) := by
      apply setLIntegral_congr_fun measurableSet_Ici
      intro x hx
      rw [paretoPDF_of_le (ht1.trans hx), Real.one_rpow, mul_one]
    rw [heq, ← restrict_Ioi_eq_restrict_Ici,
      ← ofReal_integral_eq_lintegral_ofReal
        ((integrableOn_Ioi_rpow_of_lt (by linarith : -(a + 1) < -1) ht0).const_mul a)]
    · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ht0]
      congr 1
      rw [show -(a + 1) + 1 = -a by ring]
      field_simp [ha.ne']
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg ha.le (Real.rpow_nonneg (ht0.trans hx).le _)

def d028318 {k : ℕ} (x : Fin (k + 1) → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty x

theorem d028319 {k : ℕ} (x : Fin (k + 1) → ℝ) (t : ℝ) :
    t ≤ _root_.GD.N0089.d028318 x ↔ ∀ i, t ≤ x i := by
  simp [_root_.GD.N0089.d028318]

@[fun_prop] theorem d028320 {k : ℕ} :
    Measurable (_root_.GD.N0089.d028318 (k := k)) := by
  exact (Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun i _ => continuous_apply i)).measurable

def d028321 {k : ℕ} (a : ℝ) : Measure (Fin (k + 1) → ℝ) :=
  Measure.pi fun _ => paretoMeasure 1 a



theorem d028322 {k : ℕ} (a : ℝ) (ha : 0 < a) :
    MeasurePreserving _root_.GD.N0089.d028318 (_root_.GD.N0089.d028321 (k := k) a)
      (paretoMeasure 1 ((k + 1 : ℝ) * a)) := by
  letI := isProbabilityMeasure_paretoMeasure (by norm_num : (0 : ℝ) < 1) ha
  letI : IsProbabilityMeasure (_root_.GD.N0089.d028321 (k := k) a) := by
    unfold _root_.GD.N0089.d028321
    infer_instance
  have hk0 : 0 < (k + 1 : ℝ) := by positivity
  refine ⟨_root_.GD.N0089.d028320, ?_⟩
  apply Measure.ext_of_Ici
  intro t
  rw [Measure.map_apply _root_.GD.N0089.d028320 measurableSet_Ici]
  have heq : _root_.GD.N0089.d028318 ⁻¹' Ici t = (univ : Set (Fin (k + 1))).pi (fun _ => Ici t) := by
    ext x
    simp only [mem_preimage, mem_Ici, _root_.GD.N0089.d028319, Set.mem_pi, mem_univ, forall_const]
  rw [heq, _root_.GD.N0089.d028321, Measure.pi_pi]
  simp_rw [_root_.GD.N0089.d028317 a t ha]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (by positivity), _root_.GD.N0089.d028317 _ t (mul_pos hk0 ha)]
  congr 1
  have ht : 0 ≤ max (1 : ℝ) t := le_trans (by norm_num) (le_max_left _ _)
  rw [← Real.rpow_mul_natCast ht]
  congr 1
  push_cast
  ring

end
end GD.N0089

#print axioms _root_.GD.N0089.d028317
#print axioms _root_.GD.N0089.d028322
