import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.LIntegral

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0217
noncomputable section

def d008089 : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))

def d008090 : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume

def d008091 (z : ℝ × ℝ) : ℝ × ℝ :=
  (Real.exp (z.1 + z.2), Real.exp (z.1 - z.2))

@[fun_prop] theorem d008092 : Measurable _root_.GD.N0217.d008091 := by
  unfold _root_.GD.N0217.d008091
  fun_prop


theorem d008093 (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in Ioi (0 : ℝ), f x) =
      ∫⁻ p : ℝ, ENNReal.ofReal (Real.exp p) * f (Real.exp p) := by
  have h := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun p _ => (Real.hasDerivAt_exp p).hasDerivWithinAt)
    (fun _ _ _ _ h => Real.exp_le_exp.mpr h) f
  simpa only [image_univ, Real.range_exp, Measure.restrict_univ] using h

theorem d008094 (f : ℝ → ℝ≥0∞) (x : ℝ) :
    (∫⁻ y : ℝ, f y) = ∫⁻ s : ℝ, 2 * f (2*s-x) := by
  have hd : ∀ s ∈ (univ : Set ℝ),
      HasDerivWithinAt (fun s : ℝ => 2*s-x) 2 univ s := by
    intro s _
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id s).const_mul 2).sub_const x).hasDerivWithinAt (s := univ)
  have hm : MonotoneOn (fun s : ℝ => 2*s-x) univ := by
    intro s _ t _ hst
    linarith
  have himage : (fun s : ℝ => 2*s-x) '' univ = univ := by
    apply eq_univ_of_forall
    intro y
    exact ⟨(y+x)/2, mem_univ _, by ring⟩
  have h := lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
    MeasurableSet.univ hd hm f
  simpa only [himage, Measure.restrict_univ, ENNReal.ofReal_ofNat] using h



theorem d008095 (f : (ℝ × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : ℝ, ∫⁻ y : ℝ, f (x,y)) =
      ∫⁻ s : ℝ, ∫⁻ v : ℝ, 2 * f (s+v,s-v) := by
  have hm : Measurable (fun z : ℝ × ℝ => (2 : ℝ≥0∞) * f (z.1, 2*z.2-z.1)) := by
    fun_prop
  calc
    _ = ∫⁻ x : ℝ, ∫⁻ s : ℝ, 2 * f (x,2*s-x) :=
      lintegral_congr (fun x => _root_.GD.N0217.d008094 (fun y => f (x,y)) x)
    _ = ∫⁻ s : ℝ, ∫⁻ x : ℝ, 2 * f (x,2*s-x) :=
      lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro s
      calc
        _ = ∫⁻ v : ℝ, 2 * f (s+v,2*s-(s+v)) :=
          (lintegral_add_left_eq_self (fun x : ℝ => 2 * f (x,2*s-x)) s).symm
        _ = _ := by
          apply lintegral_congr
          intro v
          rw [show 2*s-(s+v) = s-v by ring]

theorem d008096
    (f : (ℝ × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in Ioi (0 : ℝ), ∫⁻ y in Ioi (0 : ℝ), f (x,y)) =
      ∫⁻ s : ℝ, ∫⁻ v : ℝ, ENNReal.ofReal (2 * Real.exp (2*s)) *
        f (Real.exp (s+v), Real.exp (s-v)) := by
  have hi (x : ℝ) : (∫⁻ y in Ioi (0 : ℝ), f (x,y)) =
      ∫⁻ q : ℝ, ENNReal.ofReal (Real.exp q) * f (x,Real.exp q) :=
    _root_.GD.N0217.d008093 (fun y => f (x,y))
  have hm : Measurable (fun z : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (z.1+z.2)) * f (Real.exp z.1, Real.exp z.2)) := by fun_prop
  calc
    _ = ∫⁻ p : ℝ, ENNReal.ofReal (Real.exp p) *
        (∫⁻ q : ℝ, ENNReal.ofReal (Real.exp q) * f (Real.exp p,Real.exp q)) := by
      simp_rw [hi]
      exact _root_.GD.N0217.d008093 _
    _ = ∫⁻ p : ℝ, ∫⁻ q : ℝ,
        ENNReal.ofReal (Real.exp (p+q)) * f (Real.exp p,Real.exp q) := by
      apply lintegral_congr
      intro p
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro q
      rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos p).le, mul_assoc]
    _ = ∫⁻ s : ℝ, ∫⁻ v : ℝ, 2 *
        (ENNReal.ofReal (Real.exp ((s+v)+(s-v))) *
          f (Real.exp (s+v),Real.exp (s-v))) :=
      _root_.GD.N0217.d008095 _ hm
    _ = _ := by
      apply lintegral_congr
      intro s
      apply lintegral_congr
      intro v
      rw [show (s+v)+(s-v) = 2*s by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc]


theorem d008097
    (f : (ℝ × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂_root_.GD.N0217.d008089) =
      ∫⁻ z, ENNReal.ofReal (2 * Real.exp (2*z.1)) * f (_root_.GD.N0217.d008091 z) ∂_root_.GD.N0217.d008090 := by
  rw [_root_.GD.N0217.d008089, lintegral_prod _ hf.aemeasurable]
  rw [_root_.GD.N0217.d008096 f hf]
  symm
  apply lintegral_prod
  exact (show Measurable (fun z : ℝ × ℝ =>
    ENNReal.ofReal (2 * Real.exp (2*z.1)) * f (_root_.GD.N0217.d008091 z)) by fun_prop).aemeasurable

theorem d008098
    (w : (ℝ × ℝ) → ℝ) (hw : Measurable w)
    (f : (ℝ × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, ENNReal.ofReal (w z) * f z ∂_root_.GD.N0217.d008089) =
      ∫⁻ z, ENNReal.ofReal ((2 * Real.exp (2*z.1)) * w (_root_.GD.N0217.d008091 z)) *
        f (_root_.GD.N0217.d008091 z) ∂_root_.GD.N0217.d008090 := by
  rw [_root_.GD.N0217.d008097 _ (hw.ennreal_ofReal.mul hf)]
  apply lintegral_congr
  intro z
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * Real.exp (2*z.1)), mul_assoc]



theorem d008099 (w : (ℝ × ℝ) → ℝ) (hw : Measurable w) :
    (_root_.GD.N0217.d008090.withDensity (fun z =>
      ENNReal.ofReal ((2 * Real.exp (2*z.1)) * w (_root_.GD.N0217.d008091 z)))).map _root_.GD.N0217.d008091 =
      _root_.GD.N0217.d008089.withDensity (fun z => ENNReal.ofReal (w z)) := by
  ext S hS
  rw [Measure.map_apply _root_.GD.N0217.d008092 hS,
    withDensity_apply _ (_root_.GD.N0217.d008092 hS), withDensity_apply _ hS,
    ← lintegral_indicator (_root_.GD.N0217.d008092 hS), ← lintegral_indicator hS]
  have h := _root_.GD.N0217.d008098 w hw
    (S.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hS)
  calc
    _ = ∫⁻ z, ENNReal.ofReal ((2 * Real.exp (2*z.1)) * w (_root_.GD.N0217.d008091 z)) *
        S.indicator (fun _ => (1 : ℝ≥0∞)) (_root_.GD.N0217.d008091 z) ∂_root_.GD.N0217.d008090 := by
      apply lintegral_congr
      intro z
      by_cases hz : _root_.GD.N0217.d008091 z ∈ S <;> simp [hz]
    _ = ∫⁻ z, ENNReal.ofReal (w z) * S.indicator (fun _ => (1 : ℝ≥0∞)) z
        ∂_root_.GD.N0217.d008089 := h.symm
    _ = _ := by
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ S <;> simp [hz]

end
end GD.N0217

#print axioms _root_.GD.N0217.d008093
#print axioms _root_.GD.N0217.d008094
#print axioms _root_.GD.N0217.d008095
#print axioms _root_.GD.N0217.d008096
#print axioms _root_.GD.N0217.d008097
#print axioms _root_.GD.N0217.d008098
#print axioms _root_.GD.N0217.d008099
