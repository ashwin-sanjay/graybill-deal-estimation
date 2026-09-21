import GD.Module0343

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0053
noncomputable section

def d007664 (t u : ℝ) : ℝ := 2*u+t-3*t*u
def d007665 (u : ℝ) : ℝ := _root_.GD.N0053.d005107 (max 0 (min 1 u))

theorem d007666 {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : _root_.GD.N0053.d007665 u=_root_.GD.N0053.d005107 u := by
  simp [_root_.GD.N0053.d007665, min_eq_right hu.2, max_eq_right hu.1]

theorem d007667 (u : ℝ) : _root_.GD.N0053.d007665 u ∈ Icc (0:ℝ) 1 := by
  apply _root_.GD.N0053.d005112
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem d007668 : Measurable _root_.GD.N0053.d007665 := by
  unfold _root_.GD.N0053.d007665 _root_.GD.N0053.d005107
  fun_prop

def d007669 (H : ℝ → ℝ) : Prop :=
  ∀ u ∈ Ioo (0:ℝ) 1, |H u-u| ≤ u*(1-u)

theorem d007670 : _root_.GD.N0053.d007669 _root_.GD.N0053.d007665 := by
  intro u hu
  rw [_root_.GD.N0053.d007666 ⟨hu.1.le,hu.2.le⟩]
  exact _root_.GD.N0053.d005113 hu

theorem d007671 : _root_.GD.N0053.d007669 id := by
  intro u hu
  simp only [id_eq, sub_self, abs_zero]
  exact mul_nonneg hu.1.le (sub_nonneg.mpr hu.2.le)

theorem d007672 {t u : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hu : u ∈ Ioo (0:ℝ) 1) :
    0 < _root_.GD.N0053.d007664 t u ∧ _root_.GD.N0053.d007664 t u ≤ 2 ∧
    u*(1-u) ≤ _root_.GD.N0053.d007664 t u ∧ |u-t| ≤ _root_.GD.N0053.d007664 t u := by
  have h1 := mul_nonneg (sub_nonneg.mpr ht.2) hu.1.le
  have h2 := mul_nonneg ht.1 (sub_nonneg.mpr hu.2.le)
  have h3 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hu.2.le)
  have h4 := mul_nonneg ht.1 hu.1.le
  have h5 := mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg u)
  have h6 := mul_nonneg ht.1 (sq_nonneg (1-u))
  have hp := mul_pos hu.1 (sub_pos.mpr hu.2)
  unfold _root_.GD.N0053.d007664
  rw [abs_le]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith

def d007673 (H : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * ∫ u, ((H u-t)/_root_.GD.N0053.d007664 t u)^2 * Real.sqrt (_root_.GD.N0053.d007664 t u)
    ∂betaMeasure 1 (1/2)

theorem d007674 {H : ℝ → ℝ} (hH : _root_.GD.N0053.d007669 H)
    {t u : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hu : u ∈ Ioo (0:ℝ) 1) :
    ‖((H u-t)/_root_.GD.N0053.d007664 t u)^2 * Real.sqrt (_root_.GD.N0053.d007664 t u)‖ ≤ 8 := by
  have hd := _root_.GD.N0053.d007672 ht hu
  have hH' := abs_le.mp (hH u hu)
  have hbase := abs_le.mp hd.2.2.2
  have hlo : -2 ≤ (H u-t)/_root_.GD.N0053.d007664 t u := by
    apply (le_div_iff₀ hd.1).mpr
    nlinarith [hd.2.2.1]
  have hhi : (H u-t)/_root_.GD.N0053.d007664 t u ≤ 2 := by
    apply (div_le_iff₀ hd.1).mpr
    nlinarith [hd.2.2.1]
  have hsq : ((H u-t)/_root_.GD.N0053.d007664 t u)^2 ≤ 4 := by nlinarith
  have hsqrt : Real.sqrt (_root_.GD.N0053.d007664 t u) ≤ 2 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num, by linarith [hd.2.1]⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))]
  calc
    _ ≤ 4*2 := mul_le_mul hsq hsqrt (Real.sqrt_nonneg _) (by norm_num)
    _ = 8 := by norm_num

theorem d007675 {H : ℝ → ℝ} (hHm : Measurable H)
    (hH : _root_.GD.N0053.d007669 H) : ContinuousOn (_root_.GD.N0053.d007673 H) (Icc (0:ℝ) 1) := by
  letI := isProbabilityMeasureBeta (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1/2)
  intro t ht
  apply ContinuousWithinAt.const_mul
  change Tendsto (fun t => ∫ u, ((H u-t)/_root_.GD.N0053.d007664 t u)^2 * Real.sqrt (_root_.GD.N0053.d007664 t u)
      ∂betaMeasure 1 (1/2)) (𝓝[Icc (0:ℝ) 1] t) _
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (8:ℝ))
  · exact Eventually.of_forall fun t => by
      apply Measurable.aestronglyMeasurable
      unfold _root_.GD.N0053.d007664
      fun_prop
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [_root_.GD.N0053.d005105 1 (1/2)] with u hu
    exact _root_.GD.N0053.d007674 hH hs hu
  · exact integrable_const 8
  · filter_upwards [_root_.GD.N0053.d005105 1 (1/2)] with u hu
    have hc : ContinuousAt (fun s => ((H u-s)/_root_.GD.N0053.d007664 s u)^2 *
        Real.sqrt (_root_.GD.N0053.d007664 s u)) t := by
      apply ContinuousAt.mul
      · apply ContinuousAt.pow
        apply ContinuousAt.div
        · fun_prop
        · unfold _root_.GD.N0053.d007664; fun_prop
        · exact (_root_.GD.N0053.d007672 ht hu).1.ne'
      · unfold _root_.GD.N0053.d007664; fun_prop
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem d007676 (H : ℝ → ℝ) (t : ℝ) : 0 ≤ _root_.GD.N0053.d007673 H t :=
  mul_nonneg (by norm_num) (integral_nonneg fun u =>
    mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))

theorem d007677 (f : ℝ → ℝ) :
    (∫ u, Real.sqrt u*f u ∂betaMeasure 1 (1/2)) =
      (ProbabilityTheory.beta (3/2) (1/2) / ProbabilityTheory.beta 1 (1/2)) *
        ∫ u, f u ∂betaMeasure (3/2) (1/2) := by
  rw [_root_.GD.N0235.d004041
      (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1/2),
    _root_.GD.N0235.d004041
      (by norm_num : (0:ℝ)<3/2) (by norm_num : (0:ℝ)<1/2),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : 0<u ∧ u<1
  · simp only [betaPDFReal, if_pos hu]
    norm_num only [sub_self, Real.rpow_zero, mul_one, show (3/2:ℝ)-1=1/2 by norm_num]
    rw [← Real.sqrt_eq_rpow]
    field_simp
    exact (mul_div_mul_right _ _
      (beta_pos (by norm_num : (0:ℝ)<3/2) (by norm_num : (0:ℝ)<1/2)).ne').symm
  · simp [betaPDFReal, hu]

theorem d007678 : ProbabilityTheory.beta 1 (1/2) = 2 := by
  unfold ProbabilityTheory.beta
  rw [Real.Gamma_one, show (1:ℝ)+1/2=1/2+1 by ring,
    Real.Gamma_add_one (by norm_num : (1/2:ℝ)≠0)]
  field_simp [(Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<1/2)).ne']

theorem d007679 (f : ℝ → ℝ) :
    (∫ u, Real.sqrt (1-u)*f u ∂betaMeasure 1 (1/2)) =
      (1/2) * ∫ u in Ioo (0:ℝ) 1, f u := by
  rw [_root_.GD.N0235.d004041
      (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1/2),
    ← integral_const_mul, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Ioo (0:ℝ) 1
  · rw [indicator_of_mem hu, betaPDFReal, if_pos (show 0<u ∧ u<1 from hu), _root_.GD.N0053.d007678]
    have hs : Real.sqrt (1-u) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hu.2)).ne'
    have hp : (1-u)^((1/2:ℝ)-1)=(Real.sqrt (1-u))⁻¹ := by
      rw [show (1/2:ℝ)-1=-(1/2) by norm_num,
        Real.rpow_neg (sub_nonneg.mpr hu.2.le), ← Real.sqrt_eq_rpow]
    rw [hp]
    norm_num only [sub_self, Real.rpow_zero, mul_one]
    field_simp [hs]
  · have hu' : ¬(0<u ∧ u<1) := hu
    rw [indicator_of_notMem hu]
    simp only [betaPDFReal, if_neg hu', zero_mul]

def d007680 : ℝ := (Real.sqrt 2/2) *
  (ProbabilityTheory.beta (3/2) (1/2) / ProbabilityTheory.beta 1 (1/2))

theorem d007681 : 0 < _root_.GD.N0053.d007680 := by
  unfold _root_.GD.N0053.d007680
  exact mul_pos (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num))
    (div_pos (beta_pos (by norm_num) (by norm_num)) (beta_pos (by norm_num) (by norm_num)))

theorem d007682 (H L : ℝ → ℝ)
    (hf : ∀ u ∈ Ioo (0:ℝ) 1, H u=u*L u) :
    _root_.GD.N0053.d007673 H 0 = _root_.GD.N0053.d007680 * ∫ u, (L u)^2 ∂betaMeasure (3/2) (1/2) := by
  have heq : (∫ u, ((H u-0)/_root_.GD.N0053.d007664 0 u)^2 * Real.sqrt (_root_.GD.N0053.d007664 0 u)
      ∂betaMeasure 1 (1/2)) =
      (Real.sqrt 2/4) * ∫ u, Real.sqrt u*(L u)^2 ∂betaMeasure 1 (1/2) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [_root_.GD.N0053.d005105 1 (1/2)] with u hu
    rw [hf u hu]
    simp only [sub_zero, _root_.GD.N0053.d007664, mul_zero, zero_mul, add_zero]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    field_simp [hu.1.ne']
    ring
  unfold _root_.GD.N0053.d007673
  rw [heq, _root_.GD.N0053.d007677]
  unfold _root_.GD.N0053.d007680
  ring

theorem d007683 (H R : ℝ → ℝ)
    (hf : ∀ u ∈ Ioo (0:ℝ) 1, 1-H u=(1-u)*R u) :
    _root_.GD.N0053.d007673 H 1 = ∫ u in Ioo (0:ℝ) 1, (R u)^2 := by
  have heq : (∫ u, ((H u-1)/_root_.GD.N0053.d007664 1 u)^2 * Real.sqrt (_root_.GD.N0053.d007664 1 u)
      ∂betaMeasure 1 (1/2)) =
      ∫ u, Real.sqrt (1-u)*(R u)^2 ∂betaMeasure 1 (1/2) := by
    apply integral_congr_ae
    filter_upwards [_root_.GD.N0053.d005105 1 (1/2)] with u hu
    have hd : _root_.GD.N0053.d007664 1 u=1-u := by unfold _root_.GD.N0053.d007664; ring
    rw [hd]
    have hh : H u-1=-((1-u)*R u) := by linarith [hf u hu]
    rw [hh]
    field_simp [(sub_pos.mpr hu.2).ne']
  unfold _root_.GD.N0053.d007673
  rw [heq, _root_.GD.N0053.d007679]
  ring

theorem d007684 : _root_.GD.N0053.d007673 _root_.GD.N0053.d007665 0=_root_.GD.N0053.d007680*(3079/3200) := by
  rw [_root_.GD.N0053.d007682 _root_.GD.N0053.d007665 _root_.GD.N0053.d005108, _root_.GD.N0053.d005115]
  intro u hu
  rw [_root_.GD.N0053.d007666 ⟨hu.1.le,hu.2.le⟩, _root_.GD.N0053.d005110]

theorem d007685 : _root_.GD.N0053.d007673 id 0=_root_.GD.N0053.d007680 := by
  letI := isProbabilityMeasureBeta (by norm_num : (0:ℝ)<3/2) (by norm_num : (0:ℝ)<1/2)
  rw [_root_.GD.N0053.d007682 id (fun _ => 1) (by intro u _; simp)]
  simp only [one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one]

theorem d007686 : _root_.GD.N0053.d007673 _root_.GD.N0053.d007665 1=143/150 := by
  rw [_root_.GD.N0053.d007683 _root_.GD.N0053.d007665 _root_.GD.N0053.d005109, _root_.GD.N0053.d005116]
  intro u hu
  rw [_root_.GD.N0053.d007666 ⟨hu.1.le,hu.2.le⟩, _root_.GD.N0053.d005111]

theorem d007687 : _root_.GD.N0053.d007673 id 1=1 := by
  rw [_root_.GD.N0053.d007683 id (fun _ => 1) (by intro u _; simp)]
  simp

def d007688 (t : ℝ) : ℝ := (Real.sqrt t+_root_.GD.N0053.d007673 _root_.GD.N0053.d007665 t)/(Real.sqrt t+_root_.GD.N0053.d007673 id t)

theorem d007689 {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    0 < Real.sqrt t+_root_.GD.N0053.d007673 id t := by
  by_cases hz : t=0
  · simpa [hz, _root_.GD.N0053.d007685] using _root_.GD.N0053.d007681
  · exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (lt_of_le_of_ne ht.1 (Ne.symm hz)))
      (_root_.GD.N0053.d007676 id t)

theorem d007690 (t : ℝ) : 0 ≤ _root_.GD.N0053.d007688 t :=
  div_nonneg (add_nonneg (Real.sqrt_nonneg t) (_root_.GD.N0053.d007676 _root_.GD.N0053.d007665 t))
    (add_nonneg (Real.sqrt_nonneg t) (_root_.GD.N0053.d007676 id t))

theorem d007691 : ContinuousOn _root_.GD.N0053.d007688 (Icc (0:ℝ) 1) := by
  apply ContinuousOn.div
  · exact Real.continuous_sqrt.continuousOn.add
      (_root_.GD.N0053.d007675 _root_.GD.N0053.d007668 _root_.GD.N0053.d007670)
  · exact Real.continuous_sqrt.continuousOn.add
      (_root_.GD.N0053.d007675 measurable_id _root_.GD.N0053.d007671)
  · intro t ht
    exact (_root_.GD.N0053.d007689 ht).ne'

theorem d007692 : _root_.GD.N0053.d007688 0=3079/3200 := by
  unfold _root_.GD.N0053.d007688
  rw [Real.sqrt_zero, zero_add, zero_add, _root_.GD.N0053.d007684, _root_.GD.N0053.d007685]
  field_simp [_root_.GD.N0053.d007681.ne']

theorem d007693 : _root_.GD.N0053.d007688 1=293/300 := by
  norm_num [_root_.GD.N0053.d007688, _root_.GD.N0053.d007686, _root_.GD.N0053.d007687]

theorem d007694 :
    ContinuousOn _root_.GD.N0053.d007688 (Icc (0:ℝ) 1) ∧ _root_.GD.N0053.d007688 0=3079/3200 ∧ _root_.GD.N0053.d007688 1=293/300 ∧
      _root_.GD.N0053.d007688 0<1 ∧ _root_.GD.N0053.d007688 1<1 := by
  refine ⟨_root_.GD.N0053.d007691, _root_.GD.N0053.d007692, _root_.GD.N0053.d007693, ?_, ?_⟩ <;>
    norm_num [_root_.GD.N0053.d007692, _root_.GD.N0053.d007693]

end
end GD.N0053

#print axioms _root_.GD.N0053.d007667
#print axioms _root_.GD.N0053.d007675
#print axioms _root_.GD.N0053.d007694
