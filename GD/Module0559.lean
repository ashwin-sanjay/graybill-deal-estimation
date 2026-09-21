import GD.Module0557

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0149.N0433
noncomputable section

open _root_.GD.N0232.N0720.N1089
open _root_.GD.N0082.N0334
open _root_.GD.N0149.N0432

theorem d008322 (H : ℝ → ℝ) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    ((H u-t)/_root_.GD.N0082.N0334.d008256 t u)^2 ≤ _root_.GD.N0149.N0432.d008291 H u := by
  let l := (1-t)*u/_root_.GD.N0082.N0334.d008256 t u
  let r := t*(1-u)/_root_.GD.N0082.N0334.d008256 t u
  let a := H u/u
  let b := (H u-1)/(1-u)
  have hd := _root_.GD.N0082.N0334.d008263 ht hu
  have hl : 0 ≤ l := div_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hu.1.le) hd.le
  have hr : 0 ≤ r := div_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr hu.2.le)) hd.le
  have hsum : l+r=1 := by
    dsimp [l,r]
    rw [← add_div]
    apply (div_eq_one_iff_eq hd.ne').mpr
    unfold _root_.GD.N0082.N0334.d008256
    ring
  have hquot : (H u-t)/_root_.GD.N0082.N0334.d008256 t u = l*a+r*b := by
    dsimp [l,r,a,b]
    field_simp [hu.1.ne', (sub_pos.mpr hu.2).ne']
    ring
  have hvar : l*a^2+r*b^2-(l*a+r*b)^2=l*r*(a-b)^2 := by
    calc
      _ = (l+r)*(l*a^2+r*b^2)-(l*a+r*b)^2 := by rw [hsum]; ring
      _ = _ := by ring
  have hJ : (l*a+r*b)^2 ≤ l*a^2+r*b^2 := by
    nlinarith [mul_nonneg (mul_nonneg hl hr) (sq_nonneg (a-b))]
  have hl1 : l ≤ 1 := by linarith
  have hr1 : r ≤ 1 := by linarith
  rw [hquot]
  exact hJ.trans (by
    change _ ≤ a^2+b^2
    simpa using add_le_add (mul_le_mul_of_nonneg_right hl1 (sq_nonneg a))
      (mul_le_mul_of_nonneg_right hr1 (sq_nonneg b)))

def d008323 (H : ℝ → ℝ) : Prop :=
  Measurable H ∧ Integrable (_root_.GD.N0149.N0432.d008291 H) (volume.restrict (Ioo (0 : ℝ) 1))

theorem d008324 (H : ℝ → ℝ) (hH : _root_.GD.N0149.N0433.d008323 H) :
    ContinuousOn (_root_.GD.N0082.N0334.d008258 H) (Icc (0 : ℝ) 1) := by
  intro t ht
  change Tendsto (fun t => ∫ u in Ioo (0 : ℝ) 1, ((H u-t)/_root_.GD.N0082.N0334.d008256 t u)^2)
    (𝓝[Icc (0 : ℝ) 1] t) (𝓝 (_root_.GD.N0082.N0334.d008258 H t))
  apply tendsto_integral_filter_of_dominated_convergence (_root_.GD.N0149.N0432.d008291 H)
  · exact Eventually.of_forall fun _ => by
      apply Measurable.aestronglyMeasurable
      unfold _root_.GD.N0082.N0334.d008256
      have hHm := hH.1
      fun_prop
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact _root_.GD.N0149.N0433.d008322 H hs hu
  · exact hH.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hc : ContinuousAt (fun s => ((H u-s)/_root_.GD.N0082.N0334.d008256 s u)^2) t := by
      apply ContinuousAt.pow
      apply ContinuousAt.div
      · fun_prop
      · unfold _root_.GD.N0082.N0334.d008256; fun_prop
      · exact (_root_.GD.N0082.N0334.d008263 ht hu).ne'
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem d008325 (H : ℝ → ℝ) (hH : _root_.GD.N0149.N0433.d008323 H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun u => ((H u-t)/_root_.GD.N0082.N0334.d008256 t u)^2)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply hH.2.mono'
  · apply Measurable.aestronglyMeasurable
    unfold _root_.GD.N0082.N0334.d008256
    have hHm := hH.1
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact _root_.GD.N0149.N0433.d008322 H ht hu

theorem d008326 : _root_.GD.N0149.N0433.d008323 _root_.GD.N0232.N0720.N1089.d003092 :=
  ⟨_root_.GD.N0149.N0432.d008282,
    _root_.GD.N0149.N0432.d008295 _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0432.d008282 _root_.GD.N0149.N0432.d008284⟩

theorem d008327 (H : ℝ → ℝ) (hH : _root_.GD.N0149.N0433.d008323 H) :
    (∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008291 H u) = _root_.GD.N0082.N0334.d008258 H 0+_root_.GD.N0082.N0334.d008258 H 1 := by
  have h0 := _root_.GD.N0149.N0433.d008325 H hH (t := 0) (by norm_num)
  have h1 := _root_.GD.N0149.N0433.d008325 H hH (t := 1) (by norm_num)
  unfold _root_.GD.N0082.N0334.d008258
  rw [← integral_add h0 h1]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u _
  unfold _root_.GD.N0149.N0432.d008291 _root_.GD.N0082.N0334.d008256
  congr 2 <;> ring

theorem d008328 (H : ℝ → ℝ) (hH : _root_.GD.N0149.N0433.d008323 H) :
    Integrable (_root_.GD.N0149.N0432.d008292 H) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply (hH.2.sub _root_.GD.N0149.N0433.d008326.2).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have := _root_.GD.N0149.N0432.d008293 H hu
  change _root_.GD.N0149.N0432.d008291 H u-_root_.GD.N0149.N0432.d008291 _root_.GD.N0232.N0720.N1089.d003092 u=_root_.GD.N0149.N0432.d008292 H u
  linarith

theorem d008329 (H : ℝ → ℝ) (hH : _root_.GD.N0149.N0433.d008323 H) :
    _root_.GD.N0082.N0334.d008258 H 0+_root_.GD.N0082.N0334.d008258 H 1=Real.pi/2+
      ∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008292 H u := by
  have hid : (∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008291 H u)=
      (∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008291 _root_.GD.N0232.N0720.N1089.d003092 u)+
        ∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008292 H u := by
    rw [← integral_add _root_.GD.N0149.N0433.d008326.2 (_root_.GD.N0149.N0433.d008328 H hH)]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    exact _root_.GD.N0149.N0432.d008293 H hu
  rw [_root_.GD.N0149.N0433.d008327 H hH, _root_.GD.N0149.N0433.d008327 _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0433.d008326,
    _root_.GD.N0149.N0432.d008285] at hid
  have h1 : _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 1=Real.pi/4 := by
    simpa using (_root_.GD.N0082.N0334.d008276 _root_.GD.N0149.N0432.d008283 0).trans _root_.GD.N0149.N0432.d008285
  rw [h1] at hid
  linarith

theorem d008330 :
    IsLeast (_root_.GD.N0149.N0432.d008302 '' {H | _root_.GD.N0149.N0433.d008323 H}) (1/2+Real.pi/8) := by
  constructor
  · exact ⟨_root_.GD.N0232.N0720.N1089.d003092, _root_.GD.N0149.N0433.d008326, _root_.GD.N0149.N0432.d008303⟩
  · rintro x ⟨H,hH,rfl⟩
    have h := _root_.GD.N0149.N0433.d008329 H hH
    have hn : 0 ≤ ∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008292 H u :=
      integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    have h0 := le_max_left ((1+_root_.GD.N0082.N0334.d008258 H 0)/2) ((1+_root_.GD.N0082.N0334.d008258 H 1)/2)
    have h1 := le_max_right ((1+_root_.GD.N0082.N0334.d008258 H 0)/2) ((1+_root_.GD.N0082.N0334.d008258 H 1)/2)
    change _ ≤ _root_.GD.N0149.N0432.d008302 H at h0 h1
    linarith

end
end GD.N0149.N0433

#print axioms _root_.GD.N0149.N0433.d008322
#print axioms _root_.GD.N0149.N0433.d008324
#print axioms _root_.GD.N0149.N0433.d008329
#print axioms _root_.GD.N0149.N0433.d008330
