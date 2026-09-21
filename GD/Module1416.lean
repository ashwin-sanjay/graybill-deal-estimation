import GD.Module1354

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace GD.N0065
noncomputable section
open _root_.GD.N0024 _root_.GD.N0024.N0264
open _root_.GD.N0023 _root_.GD.N0023.N0258
open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1423
open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0719.N0876
open _root_.GD.N0232.N0719.N0877


theorem d022698 (t U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) : _root_.GD.N0024.N0264.d005086 t U V ≤ V / U + 1 := by
  have ht1 : t ≤ 1 := by linarith
  have h1t : 0 ≤ 1 - t := by linarith
  by_cases hUV : U ≤ V
  · have hr := _root_.GD.N0024.N0264.d005092 t U V hU hV ht0 ht1
    have hu : U / V ≤ 1 := (div_le_one hV).mpr hUV
    have hvu : 0 ≤ V / U := div_nonneg hV.le hU.le
    unfold _root_.GD.N0024.N0264.d005087 at hr
    linarith
  · have hVU : V ≤ U := (lt_of_not_ge hUV).le
    have hs : (V - U) ^ 2 ≤ U ^ 2 := by nlinarith
    have hnum := mul_le_mul_of_nonneg_left hs (mul_nonneg ht0 h1t)
    have hhalf := mul_nonneg (mul_nonneg h1t (sq_nonneg U))
      (show 0 ≤ 1 - t - t by linarith)
    have hd : 0 < (1 - t) * U + t * V := _root_.GD.N0024.N0264.d005090 t U V hU hV ht0 ht1
    have hden : ((1 - t) * U) ^ 2 ≤ ((1 - t) * U + t * V) ^ 2 := by
      apply (sq_le_sq₀ (mul_nonneg h1t hU.le) hd.le).mpr
      exact le_add_of_nonneg_right (mul_nonneg ht0 hV.le)
    have hr : _root_.GD.N0024.N0264.d005086 t U V ≤ 1 := by
      unfold _root_.GD.N0024.N0264.d005086
      apply (div_le_one (sq_pos_of_pos hd)).mpr
      nlinarith
    exact hr.trans (le_add_of_nonneg_left (div_nonneg hV.le hU.le))

theorem d022699
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
    (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V)
    (hpos : ∀ᵐ z ∂ν, 0 < U z ∧ 0 < V z)
    (hratio : Integrable (fun z => V z / U z) ν)
    (t : ℕ → ℝ) (ht0 : ∀ n, 0 ≤ t n) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, _root_.GD.N0024.N0264.d005086 (t n) (U z) (V z) ∂ν) atTop (𝓝 0) := by
  let u := fun n => min (t n) (1 / 2)
  have hu0 : ∀ n, 0 ≤ u n := fun n => le_min (ht0 n) (by norm_num)
  have huh : ∀ n, u n ≤ 1 / 2 := fun n => min_le_right _ _
  have hu1 : ∀ n, u n ≤ 1 := fun n => (huh n).trans (by norm_num)
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa only [min_eq_left (show (0 : ℝ) ≤ 1 / 2 by norm_num)] using
      ht.min (tendsto_const_nhds (x := (1 / 2 : ℝ)))
  have hlim := tendsto_integral_of_dominated_convergence
    (fun z => V z / U z + 1)
    (fun n => (_root_.GD.N0024.N0264.d005100 U V hU hV (u n)).aestronglyMeasurable)
    (hratio.add (integrable_const 1)) (fun n => ?_) (f := fun _ => (0 : ℝ)) ?_
  · have heq : ∀ᶠ n in atTop,
        (∫ z, _root_.GD.N0024.N0264.d005086 (t n) (U z) (V z) ∂ν) = ∫ z, _root_.GD.N0024.N0264.d005086 (u n) (U z) (V z) ∂ν := by
      filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn
      simp only [u, min_eq_left hn.le]
    have hh : Tendsto (fun n => ∫ z, _root_.GD.N0024.N0264.d005086 (u n) (U z) (V z) ∂ν) atTop (𝓝 0) := by
      simpa only [integral_zero] using hlim
    exact hh.congr' (heq.mono fun _ hn => hn.symm)
  · filter_upwards [hpos] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0024.N0264.d005091 _ _ _ (hu0 n) (hu1 n))]
    exact _root_.GD.N0065.d022698 (u n) (U z) (V z) hz.1 hz.2 (hu0 n) (huh n)
  · filter_upwards [hpos] with z hz
    exact _root_.GD.N0024.N0264.d005098 u (U z) (V z) hz.1.ne' hu

theorem d022700 (m n : ℕ) (hm : 4 ≤ m) (hn : 2 ≤ n)
    (t : ℕ → _root_.GD.N0023.N0258.d021865) (ht : Tendsto (fun j => (t j).1) atTop (𝓝 0)) :
    Tendsto (fun j => _root_.GD.N0023.N0258.d021868 m n (t j)) atTop (𝓝 0) := by
  let a := _root_.GD.N0232.N0720.N1436.d013207 m
  let b := _root_.GD.N0232.N0720.N1436.d013208 n
  have ha : 1 < a := _root_.GD.N0023.N0258.d021870 m hm
  have ha0 : 0 < a := by linarith
  have hb : 0 < b := _root_.GD.N0232.N0720.N1436.d013212 hn
  letI := isProbabilityMeasure_gammaMeasure ha0 ha0
  letI := isProbabilityMeasure_gammaMeasure hb hb
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1091.d012754 a b) := by unfold _root_.GD.N0232.N0720.N1091.d012754; infer_instance
  have hi : Integrable (fun q : ℝ × ℝ => q.2 / q.1) (_root_.GD.N0232.N0720.N1091.d012754 a b) := by
    simpa only [_root_.GD.N0232.N0720.N1091.d012754, div_eq_mul_inv, mul_comm] using
      (_root_.GD.N0232.N0719.N0876.d020682 ha ha0).mul_prod (_root_.GD.N0232.N0719.N0877.d020694 hb hb)
  have h := _root_.GD.N0065.d022699 (_root_.GD.N0232.N0720.N1091.d012754 a b)
    Prod.fst Prod.snd measurable_fst measurable_snd (_root_.GD.N0232.N0720.N1091.d012774 ha0 hb)
    hi (fun j => (t j).1) (fun j => (t j).2.1.le) ht
  exact h.congr' (Eventually.of_forall fun j =>
    (_root_.GD.N0023.N0258.d021872 m n (by omega) hn (t j)).symm)

theorem d022701 (m n : ℕ) (hm : 2 ≤ m) (hn : 4 ≤ n)
    (t : ℕ → _root_.GD.N0023.N0258.d021865) (ht : Tendsto (fun j => (t j).1) atTop (𝓝 1)) :
    Tendsto (fun j => _root_.GD.N0023.N0258.d021868 m n (t j)) atTop (𝓝 0) := by
  let a := _root_.GD.N0232.N0720.N1436.d013207 m
  let b := _root_.GD.N0232.N0720.N1436.d013208 n
  have ha : 0 < a := _root_.GD.N0232.N0720.N1436.d013211 hm
  have hb : 1 < b := _root_.GD.N0023.N0258.d021871 n hn
  have hb0 : 0 < b := by linarith
  letI := isProbabilityMeasure_gammaMeasure ha ha
  letI := isProbabilityMeasure_gammaMeasure hb0 hb0
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1091.d012754 a b) := by unfold _root_.GD.N0232.N0720.N1091.d012754; infer_instance
  have hi : Integrable (fun q : ℝ × ℝ => q.1 / q.2) (_root_.GD.N0232.N0720.N1091.d012754 a b) := by
    simpa only [_root_.GD.N0232.N0720.N1091.d012754, div_eq_mul_inv] using
      (_root_.GD.N0232.N0719.N0877.d020694 ha ha).mul_prod (_root_.GD.N0232.N0719.N0876.d020682 hb hb0)
  have hpos : ∀ᵐ q ∂_root_.GD.N0232.N0720.N1091.d012754 a b, 0 < q.2 ∧ 0 < q.1 := by
    filter_upwards [_root_.GD.N0232.N0720.N1091.d012774 ha hb0] with q hq
    exact hq.symm
  have ht' : Tendsto (fun j => 1 - (t j).1) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub ht
  have h := _root_.GD.N0065.d022699 (_root_.GD.N0232.N0720.N1091.d012754 a b)
    Prod.snd Prod.fst measurable_snd measurable_fst hpos hi
    (fun j => 1 - (t j).1) (fun j => sub_nonneg.mpr (t j).2.2.le) ht'
  apply h.congr' (Eventually.of_forall fun j => ?_)
  rw [_root_.GD.N0023.N0258.d021872 m n hm (by omega) (t j)]
  exact integral_congr_ae (ae_of_all _ fun q => _root_.GD.N0024.N0264.d005093 (t j).1 q.1 q.2)

end
end GD.N0065

#print axioms _root_.GD.N0065.d022698
#print axioms _root_.GD.N0065.d022699
#print axioms _root_.GD.N0065.d022700
#print axioms _root_.GD.N0065.d022701
