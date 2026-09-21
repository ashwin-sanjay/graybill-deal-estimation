import GD.Module0176
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

set_option warningAsError true
set_option autoImplicit false















open MeasureTheory Set Filter Topology

namespace GD.N0232.N0720.N1239

noncomputable section

open _root_.GD.N0232.N0720.N1240 _root_.GD.N0232.N0720.N1238

def d002116 : ℝ := Real.rpow (3 / 8) (-5 / 2)

theorem d002117 (z : _root_.GD.N0232.N0720.N1238.d002103) (x : _root_.GD.N0232.N0720.N1240.d002070) :
    _root_.GD.N0232.N0720.N1238.d002109 z x ≤ _root_.GD.N0232.N0720.N1239.d002116 := by
  exact Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 3 / 8)
    (_root_.GD.N0232.N0720.N1240.d002071 x.property
      ⟨z.property.1.1.le, z.property.1.2.le⟩
      ⟨by linarith [z.property.2.1], z.property.2.2.le⟩) (by norm_num)

theorem d002118 (x : _root_.GD.N0232.N0720.N1240.d002070) :
    Continuous (fun z : _root_.GD.N0232.N0720.N1238.d002103 ↦ _root_.GD.N0232.N0720.N1238.d002109 z x) := by
  apply (show Continuous (fun z : _root_.GD.N0232.N0720.N1238.d002103 ↦ _root_.GD.N0232.N0720.N1240.d002053 x z.val.1 z.val.2)
    from by unfold _root_.GD.N0232.N0720.N1240.d002053; fun_prop).rpow_const
  intro z
  left
  have h := _root_.GD.N0232.N0720.N1240.d002071 x.property
    ⟨z.property.1.1.le, z.property.1.2.le⟩
    ⟨by linarith [z.property.2.1], z.property.2.2.le⟩
  linarith

theorem d002119 (z : _root_.GD.N0232.N0720.N1238.d002103) (x : _root_.GD.N0232.N0720.N1240.d002070) :
    ‖_root_.GD.N0232.N0720.N1238.d002109 z x‖ ≤ _root_.GD.N0232.N0720.N1239.d002116 := by
  rw [Real.norm_eq_abs, abs_of_pos (_root_.GD.N0232.N0720.N1238.d002110 z x)]
  exact _root_.GD.N0232.N0720.N1239.d002117 z x

theorem d002120 (z : _root_.GD.N0232.N0720.N1238.d002103) (x : _root_.GD.N0232.N0720.N1240.d002070) :
    ‖((x : ℝ) + 1 / 2) * _root_.GD.N0232.N0720.N1238.d002109 z x‖ ≤ _root_.GD.N0232.N0720.N1239.d002116 := by
  have hx : 0 ≤ (x : ℝ) + 1 / 2 := by linarith [x.property.1]
  have hx' : (x : ℝ) + 1 / 2 ≤ 1 := by linarith [x.property.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (_root_.GD.N0232.N0720.N1238.d002110 z x).le)]
  exact (mul_le_of_le_one_left (_root_.GD.N0232.N0720.N1238.d002110 z x).le hx').trans
    (_root_.GD.N0232.N0720.N1239.d002117 z x)

theorem d002121
    (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
    Continuous (fun z : _root_.GD.N0232.N0720.N1238.d002103 ↦ _root_.GD.N0232.N0720.N1238.d002112 ρ z) := by
  have hd : Continuous (fun z : _root_.GD.N0232.N0720.N1238.d002103 ↦
      ∫ x, _root_.GD.N0232.N0720.N1238.d002109 z x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)) := by
    apply continuous_of_dominated (bound := fun _ ↦ _root_.GD.N0232.N0720.N1239.d002116)
    · intro z
      exact (_root_.GD.N0232.N0720.N1238.d002109 z).continuous.aestronglyMeasurable
    · intro z
      exact ae_of_all _ fun x ↦ _root_.GD.N0232.N0720.N1239.d002119 z x
    · exact integrable_const _root_.GD.N0232.N0720.N1239.d002116
    · exact ae_of_all _ _root_.GD.N0232.N0720.N1239.d002118
  have hn : Continuous (fun z : _root_.GD.N0232.N0720.N1238.d002103 ↦
      ∫ x, ((x : ℝ) + 1 / 2) * _root_.GD.N0232.N0720.N1238.d002109 z x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)) := by
    apply continuous_of_dominated (bound := fun _ ↦ _root_.GD.N0232.N0720.N1239.d002116)
    · intro z
      exact ((continuous_subtype_val.add continuous_const).mul
        (_root_.GD.N0232.N0720.N1238.d002109 z).continuous).aestronglyMeasurable
    · intro z
      exact ae_of_all _ fun x ↦ _root_.GD.N0232.N0720.N1239.d002120 z x
    · exact integrable_const _root_.GD.N0232.N0720.N1239.d002116
    · exact ae_of_all _ fun x ↦ continuous_const.mul
        (_root_.GD.N0232.N0720.N1239.d002118 x)
  have he : ∀ z : _root_.GD.N0232.N0720.N1238.d002103,
      (∫ x, _root_.GD.N0232.N0720.N1238.d002109 z x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)) ≠ 0 :=
    fun z ↦ ne_of_gt (_root_.GD.N0232.N0720.N1238.d002111 ρ z)
  simpa [_root_.GD.N0232.N0720.N1238.d002112, _root_.GD.N0232.N0720.N1240.d002095, _root_.GD.N0232.N0720.N1238.d002109] using
    (hn.div hd he).sub (show Continuous (fun z : _root_.GD.N0232.N0720.N1238.d002103 ↦ z.val.1 + 1 / 2)
      from by fun_prop)

theorem d002122
    (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) (z : _root_.GD.N0232.N0720.N1238.d002103) :
    _root_.GD.N0232.N0720.N1240.d002095 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) (z.val.1 + 1 / 2) z.val.2 ∈
      Icc (0 : ℝ) 1 := by
  let w := _root_.GD.N0232.N0720.N1238.d002109 z
  have hi : Integrable (fun x ↦ w x) (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) := by
    simpa using w.continuous.continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact (univ : Set _root_.GD.N0232.N0720.N1240.d002070))
      (μ := (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070))
  have hni : Integrable (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦ ((x : ℝ) + 1 / 2) * w x)
      (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) := by
    have hn : Continuous (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦ ((x : ℝ) + 1 / 2) * w x) :=
      (continuous_subtype_val.add continuous_const).mul w.continuous
    simpa using hn.continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact (univ : Set _root_.GD.N0232.N0720.N1240.d002070))
      (μ := (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070))
  have hnonneg : 0 ≤ ∫ x, ((x : ℝ) + 1 / 2) * w x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (by linarith [x.property.1]) (_root_.GD.N0232.N0720.N1238.d002110 z x).le
  have hle : (∫ x, ((x : ℝ) + 1 / 2) * w x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)) ≤
      (∫ x, w x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)) := by
    apply integral_mono hni hi
    intro x
    exact mul_le_of_le_one_left (_root_.GD.N0232.N0720.N1238.d002110 z x).le (by linarith [x.property.2])
  have hd := _root_.GD.N0232.N0720.N1238.d002111 ρ z
  change 0 ≤ _ ∧ _ ≤ 1
  simp only [_root_.GD.N0232.N0720.N1240.d002095, add_sub_cancel_right]
  exact ⟨div_nonneg hnonneg hd.le, (div_le_one hd).mpr hle⟩

theorem d002123
    (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) (z : _root_.GD.N0232.N0720.N1238.d002103) :
    |_root_.GD.N0232.N0720.N1238.d002112 ρ z| ≤ 1 := by
  have h := _root_.GD.N0232.N0720.N1239.d002122 ρ z
  unfold _root_.GD.N0232.N0720.N1238.d002112
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2, z.property.1.1, z.property.1.2]

theorem d002124
    (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) (z : _root_.GD.N0232.N0720.N1238.d002103) :
    ‖_root_.GD.N0232.N0720.N1238.d002112 ρ z ^ 2‖ ≤ 1 := by
  have h := _root_.GD.N0232.N0720.N1239.d002123 ρ z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (_root_.GD.N0232.N0720.N1238.d002112 ρ z),
    mul_nonneg (sub_nonneg.mpr h) (add_nonneg (abs_nonneg (_root_.GD.N0232.N0720.N1238.d002112 ρ z))
      (by norm_num : (0 : ℝ) ≤ 1))]

def d002125 (μ : Measure _root_.GD.N0232.N0720.N1238.d002103)
    (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) : ℝ :=
  ∫ z, _root_.GD.N0232.N0720.N1238.d002112 ρ z ^ 2 ∂μ

theorem d002126
    (μ : Measure _root_.GD.N0232.N0720.N1238.d002103) [IsFiniteMeasure μ]
    (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
    Integrable (fun z ↦ _root_.GD.N0232.N0720.N1238.d002112 ρ z ^ 2) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((_root_.GD.N0232.N0720.N1239.d002121 ρ).pow 2).aestronglyMeasurable
  exact ae_of_all μ fun z ↦ _root_.GD.N0232.N0720.N1239.d002124 ρ z

theorem d002127
    (μ : Measure _root_.GD.N0232.N0720.N1238.d002103) [IsFiniteMeasure μ] :
    Continuous (_root_.GD.N0232.N0720.N1239.d002125 μ) := by
  apply continuous_of_dominated (bound := fun _ ↦ (1 : ℝ))
  · intro ρ
    exact ((_root_.GD.N0232.N0720.N1239.d002121 ρ).pow 2).aestronglyMeasurable
  · intro ρ
    exact ae_of_all μ fun z ↦ _root_.GD.N0232.N0720.N1239.d002124 ρ z
  · exact integrable_const 1
  · exact ae_of_all μ fun z ↦ (_root_.GD.N0232.N0720.N1238.d002113 z).pow 2

theorem d002128
    (μ : Measure _root_.GD.N0232.N0720.N1238.d002103) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ]
    (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
    0 < _root_.GD.N0232.N0720.N1239.d002125 μ ρ := by
  obtain ⟨z, hz⟩ := _root_.GD.N0232.N0720.N1238.d002114 ρ
  exact integral_pos_of_integrable_nonneg_nonzero
    ((_root_.GD.N0232.N0720.N1239.d002121 ρ).pow 2)
    (_root_.GD.N0232.N0720.N1239.d002126 μ ρ) (fun _ ↦ sq_nonneg _)
    (pow_ne_zero 2 hz)



theorem d002129
    (μ : Measure _root_.GD.N0232.N0720.N1238.d002103) [IsFiniteMeasure μ] [Measure.IsOpenPosMeasure μ] :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070,
      c ≤ _root_.GD.N0232.N0720.N1239.d002125 μ ρ := by
  letI : Inhabited _root_.GD.N0232.N0720.N1240.d002070 := ⟨⟨0, by norm_num⟩⟩
  obtain ⟨ρ, _, hρ⟩ := (isCompact_univ : IsCompact
    (univ : Set (ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070))).exists_isMinOn
      univ_nonempty (_root_.GD.N0232.N0720.N1239.d002127 μ).continuousOn
  exact ⟨_root_.GD.N0232.N0720.N1239.d002125 μ ρ, _root_.GD.N0232.N0720.N1239.d002128 μ ρ,
    fun σ ↦ hρ (mem_univ σ)⟩

end

end GD.N0232.N0720.N1239

#print axioms _root_.GD.N0232.N0720.N1239.d002121
#print axioms _root_.GD.N0232.N0720.N1239.d002122
#print axioms _root_.GD.N0232.N0720.N1239.d002127
#print axioms _root_.GD.N0232.N0720.N1239.d002128
#print axioms _root_.GD.N0232.N0720.N1239.d002129
