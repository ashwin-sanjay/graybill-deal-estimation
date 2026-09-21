import GD.Module0838
import GD.Module1325

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory Set

namespace GD.N0150
noncomputable section
open _root_.GD.N0228.N0547.N0779
open _root_.GD.N0228.N0547.N0778
open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0719.N0876
open _root_.GD.N0232.N0720.N1091

def d021618 (q : ℝ × ℝ) : ℝ := (q.1 + q.2)⁻¹

def d021619 (r₀ r₁ : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (q.1 / r₀, q.2 / r₁)

@[fun_prop] theorem d021620 : Measurable _root_.GD.N0150.d021618 := by
  unfold _root_.GD.N0150.d021618
  fun_prop

@[fun_prop] theorem d021621 (r₀ r₁ : ℝ) : Measurable (_root_.GD.N0150.d021619 r₀ r₁) := by
  unfold _root_.GD.N0150.d021619
  fun_prop

theorem d021622 {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map (fun q : ℝ × ℝ => q.1 + q.2) =
      gammaMeasure (a + b) r := by
  letI := isProbabilityMeasureBeta ha hb
  letI := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  letI := isProbabilityMeasure_gammaMeasure ha hr
  letI := isProbabilityMeasure_gammaMeasure hb hr
  have h := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map (fun q : ℝ × ℝ => q.1 + q.2))
    (_root_.GD.N0228.N0547.N0779.d012812 ha hb hr)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  have heq : (fun q : ℝ × ℝ => q.1 + q.2) ∘ _root_.GD.N0228.N0547.N0778.d009366 = Prod.snd := by
    funext q
    unfold _root_.GD.N0228.N0547.N0778.d009366
    simp only [Function.comp_apply]
    ring
  rw [heq, Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h.symm

theorem d021623 {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : 1 < a + b) (hr : 0 < r) :
    Integrable _root_.GD.N0150.d021618 ((gammaMeasure a r).prod (gammaMeasure b r)) := by
  have hmap : MeasurePreserving (fun q : ℝ × ℝ => q.1 + q.2)
      ((gammaMeasure a r).prod (gammaMeasure b r)) (gammaMeasure (a + b) r) :=
    ⟨by fun_prop, _root_.GD.N0150.d021622 ha hb hr⟩
  exact hmap.integrable_comp_of_integrable (_root_.GD.N0232.N0719.N0876.d020682 hab hr)

theorem d021624 {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : 1 < a + b) (hr : 0 < r) :
    (∫ q, _root_.GD.N0150.d021618 q ∂(gammaMeasure a r).prod (gammaMeasure b r)) = r / (a + b - 1) := by
  have h := integral_map
    (μ := (gammaMeasure a r).prod (gammaMeasure b r))
    (f := fun x : ℝ => x⁻¹)
    (show Measurable (fun q : ℝ × ℝ => q.1 + q.2) by fun_prop).aemeasurable
    (show Measurable (fun x : ℝ => x⁻¹) by fun_prop).aestronglyMeasurable
  rw [_root_.GD.N0150.d021622 ha hb hr] at h
  unfold _root_.GD.N0150.d021618
  rw [← h, _root_.GD.N0023.N0257.d021615 hab hr]

theorem d021625 {a b r₀ r₁ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    ((gammaMeasure a 1).prod (gammaMeasure b 1)).map (_root_.GD.N0150.d021619 r₀ r₁) =
      (gammaMeasure a r₀).prod (gammaMeasure b r₁) := by
  letI := isProbabilityMeasure_gammaMeasure ha zero_lt_one
  letI := isProbabilityMeasure_gammaMeasure hb zero_lt_one
  have h₀ : (gammaMeasure a 1).map (fun x : ℝ => x / r₀) = gammaMeasure a r₀ := by
    simpa only [one_div, inv_inv, div_eq_mul_inv, mul_comm, one_mul, mul_one] using
      _root_.GD.N0232.N0719.N0954.d009354 ha zero_lt_one (inv_pos.mpr hr₀)
  have h₁ : (gammaMeasure b 1).map (fun x : ℝ => x / r₁) = gammaMeasure b r₁ := by
    simpa only [one_div, inv_inv, div_eq_mul_inv, mul_comm, one_mul, mul_one] using
      _root_.GD.N0232.N0719.N0954.d009354 hb zero_lt_one (inv_pos.mpr hr₁)
  rw [← h₀, ← h₁, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rfl

theorem d021626 {x y r₀ r₁ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    (x / r₀ + y / r₁)⁻¹ ≤ max r₀ r₁ * (x + y)⁻¹ := by
  have hM : 0 < max r₀ r₁ := hr₀.trans_le (le_max_left _ _)
  have h₀ : x / max r₀ r₁ ≤ x / r₀ :=
    div_le_div_of_nonneg_left hx.le hr₀ (le_max_left _ _)
  have h₁ : y / max r₀ r₁ ≤ y / r₁ :=
    div_le_div_of_nonneg_left hy.le hr₁ (le_max_right _ _)
  have hsum : (x + y) / max r₀ r₁ ≤ x / r₀ + y / r₁ := by
    rw [add_div]
    exact add_le_add h₀ h₁
  have h := one_div_le_one_div_of_le (div_pos (add_pos hx hy) hM) hsum
  simp only [one_div, inv_div] at h
  simpa only [div_eq_mul_inv] using h

theorem d021627 {a b r₀ r₁ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    ∀ᵐ q ∂(gammaMeasure a r₀).prod (gammaMeasure b r₁), 0 < q.1 ∧ 0 < q.2 := by
  letI := isProbabilityMeasure_gammaMeasure ha hr₀
  letI := isProbabilityMeasure_gammaMeasure hb hr₁
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd))).mpr
  filter_upwards [_root_.GD.N0232.N0720.N1091.d012773 ha hr₀] with x hx
  filter_upwards [_root_.GD.N0232.N0720.N1091.d012773 hb hr₁] with y hy
  exact ⟨hx, hy⟩

theorem d021628 {a b r₀ r₁ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : 1 < a + b) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    Integrable (_root_.GD.N0150.d021618 ∘ _root_.GD.N0150.d021619 r₀ r₁) ((gammaMeasure a 1).prod (gammaMeasure b 1)) := by
  have h := (_root_.GD.N0150.d021623 ha hb hab zero_lt_one).const_mul (max r₀ r₁)
  apply h.mono' (_root_.GD.N0150.d021620.comp (_root_.GD.N0150.d021621 r₀ r₁)).aestronglyMeasurable
  filter_upwards [_root_.GD.N0150.d021627 ha hb zero_lt_one zero_lt_one] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    dsimp only [Function.comp_apply, _root_.GD.N0150.d021618, _root_.GD.N0150.d021619]
    exact inv_nonneg.mpr (add_nonneg (div_nonneg hq.1.le hr₀.le)
      (div_nonneg hq.2.le hr₁.le)))]
  exact _root_.GD.N0150.d021626 hq.1 hq.2 hr₀ hr₁

theorem d021629 {a b r₀ r₁ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : 1 < a + b) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    Integrable (fun q : ℝ × ℝ => (q.1 + q.2)⁻¹)
      ((gammaMeasure a r₀).prod (gammaMeasure b r₁)) := by
  rw [← _root_.GD.N0150.d021625 ha hb hr₀ hr₁]
  exact (integrable_map_measure _root_.GD.N0150.d021620.aestronglyMeasurable
    (_root_.GD.N0150.d021621 r₀ r₁).aemeasurable).mpr
      (_root_.GD.N0150.d021628 ha hb hab hr₀ hr₁)

theorem d021630 {a b r₀ r₁ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : 1 < a + b) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    (∫ q : ℝ × ℝ, (q.1 + q.2)⁻¹ ∂(gammaMeasure a r₀).prod (gammaMeasure b r₁)) ≤
      max r₀ r₁ / (a + b - 1) := by
  change (∫ q, _root_.GD.N0150.d021618 q ∂(gammaMeasure a r₀).prod (gammaMeasure b r₁)) ≤ _
  rw [← _root_.GD.N0150.d021625 ha hb hr₀ hr₁]
  rw [integral_map (_root_.GD.N0150.d021621 r₀ r₁).aemeasurable
    _root_.GD.N0150.d021620.aestronglyMeasurable]
  have h := integral_mono_ae (_root_.GD.N0150.d021628 ha hb hab hr₀ hr₁)
    ((_root_.GD.N0150.d021623 ha hb hab zero_lt_one).const_mul (max r₀ r₁)) (by
      filter_upwards [_root_.GD.N0150.d021627 ha hb zero_lt_one zero_lt_one] with q hq
      exact _root_.GD.N0150.d021626 hq.1 hq.2 hr₀ hr₁)
  apply h.trans_eq
  rw [integral_const_mul, _root_.GD.N0150.d021624 ha hb hab zero_lt_one]
  ring

theorem d021631 {a b r₀ r₁ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : 1 < a + b) (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    (∫ q : ℝ × ℝ, (q.1 + q.2)⁻¹ ∂(gammaMeasure a r₀).prod (gammaMeasure b r₁)) ≤
      (r₀ + r₁) / (a + b - 1) :=
  (_root_.GD.N0150.d021630 ha hb hab hr₀ hr₁).trans
    (div_le_div_of_nonneg_right (max_le (by linarith) (by linarith)) (by linarith))

theorem d021632 {r₀ r₁ : ℝ} (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) :
    Integrable (fun q : ℝ × ℝ => (q.1 + q.2)⁻¹)
      ((gammaMeasure 1 r₀).prod (gammaMeasure 1 r₁)) ∧
    (∫ q : ℝ × ℝ, (q.1 + q.2)⁻¹ ∂(gammaMeasure 1 r₀).prod (gammaMeasure 1 r₁)) ≤
      r₀ + r₁ := by
  exact ⟨_root_.GD.N0150.d021629 zero_lt_one zero_lt_one (by norm_num) hr₀ hr₁,
    by simpa using _root_.GD.N0150.d021631 zero_lt_one zero_lt_one (by norm_num) hr₀ hr₁⟩

#print axioms _root_.GD.N0150.d021622
#print axioms _root_.GD.N0150.d021623
#print axioms _root_.GD.N0150.d021624
#print axioms _root_.GD.N0150.d021625
#print axioms _root_.GD.N0150.d021626
#print axioms _root_.GD.N0150.d021629
#print axioms _root_.GD.N0150.d021630
#print axioms _root_.GD.N0150.d021631
#print axioms _root_.GD.N0150.d021632

end
end GD.N0150
