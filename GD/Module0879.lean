import GD.Module0878

set_option warningAsError true
set_option autoImplicit false














open MeasureTheory Set Filter Topology

namespace GD.N0232.N0720.N1229

noncomputable section

open _root_.GD.N0232.N0720.N1240
open _root_.GD.N0232.N0720.N1241
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434

def d013586 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070)
    (z : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0232.N0720.N1240.d002100 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) z.1 z.2

theorem d013587 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
    Measurable (_root_.GD.N0232.N0720.N1229.d013586 ρ) := by
  have hr : Measurable (fun x : ℝ ↦ Real.rpow x (-5 / 2)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact continuousOn_id.rpow_const fun x hx ↦ Or.inl hx
  have hw : Measurable (fun z : _root_.GD.N0232.N0720.N1436.d013217 × _root_.GD.N0232.N0720.N1240.d002070 ↦
      Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 ((z.2 : ℝ) + 1 / 2) z.1.1 z.1.2) (-5 / 2)) := by
    apply hr.comp
    unfold _root_.GD.N0232.N0720.N1240.d002099
    fun_prop
  have hn : Measurable (fun z : _root_.GD.N0232.N0720.N1436.d013217 × _root_.GD.N0232.N0720.N1240.d002070 ↦
      ((z.2 : ℝ) + 1 / 2) *
        Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 ((z.2 : ℝ) + 1 / 2) z.1.1 z.1.2) (-5 / 2)) :=
    (show Measurable (fun z : _root_.GD.N0232.N0720.N1436.d013217 × _root_.GD.N0232.N0720.N1240.d002070 ↦
      (z.2 : ℝ) + 1 / 2) from by fun_prop).mul hw
  exact (hn.stronglyMeasurable.integral_prod_right'
      (ν := (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070))).measurable.div
    (hw.stronglyMeasurable.integral_prod_right'
      (ν := (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070))).measurable

theorem d013588 :
    ∀ᵐ z ∂_root_.GD.N0232.N0720.N1241.d013568, z ∈ _root_.GD.N0232.N0720.N1436.d013218 := by
  apply (_root_.GD.N0232.N0720.N1436.d013290 2 2 (1 / 2)).ae_le
  exact ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219

theorem d013589 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
    ∀ᵐ z ∂_root_.GD.N0232.N0720.N1241.d013568, _root_.GD.N0232.N0720.N1229.d013586 ρ z ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [_root_.GD.N0232.N0720.N1229.d013588] with z hz
  exact _root_.GD.N0232.N0720.N1241.d013581 ρ hz

theorem d013590 {z : _root_.GD.N0232.N0720.N1436.d013217}
    (hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    Continuous (fun ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1229.d013586 ρ z) := by
  let w : ContinuousMap _root_.GD.N0232.N0720.N1240.d002070 ℝ :=
    ⟨fun x ↦ Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 (x + 1 / 2) z.1 z.2) (-5 / 2), by
      apply (show Continuous (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦
        _root_.GD.N0232.N0720.N1240.d002099 (x + 1 / 2) z.1 z.2) from by
          unfold _root_.GD.N0232.N0720.N1240.d002099; fun_prop).rpow_const
      exact fun x ↦ Or.inl (ne_of_gt (_root_.GD.N0232.N0720.N1241.d013580 x hz))⟩
  let n : ContinuousMap _root_.GD.N0232.N0720.N1240.d002070 ℝ :=
    ⟨fun x ↦ ((x : ℝ) + 1 / 2) * w x,
      (continuous_subtype_val.add continuous_const).mul w.continuous⟩
  have hwpos (x : _root_.GD.N0232.N0720.N1240.d002070) : 0 < w x :=
    Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1241.d013580 x hz) _
  have hi (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
      Integrable (fun x ↦ w x) (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) := by
    simpa using w.continuous.continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact (univ : Set _root_.GD.N0232.N0720.N1240.d002070))
      (μ := (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070))
  have hd (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
      (∫ x, w x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)) ≠ 0 := by
    apply ne_of_gt
    apply (integral_pos_iff_support_of_nonneg (fun x ↦ (hwpos x).le) (hi ρ)).2
    have hs : Function.support (fun x ↦ w x) = univ := by
      ext x
      simp [Function.mem_support, ne_of_gt (hwpos x)]
    rw [hs]
    simp
  exact (ProbabilityMeasure.continuous_integral_continuousMap n).div
    (ProbabilityMeasure.continuous_integral_continuousMap w) hd

def d013591 (h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ)
    (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) : ℝ :=
  ∫ z, (h z - _root_.GD.N0232.N0720.N1229.d013586 ρ z) ^ 2 ∂_root_.GD.N0232.N0720.N1241.d013568

theorem d013592 (a b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    ‖(a - b) ^ 2‖ ≤ 2 * a ^ 2 + 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (a + b), mul_nonneg hb.1 (sub_nonneg.mpr hb.2)]

theorem d013593
    (h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hh : Measurable h)
    (hh2 : Integrable (fun z ↦ h z ^ 2) _root_.GD.N0232.N0720.N1241.d013568)
    (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
    Integrable (fun z ↦ (h z - _root_.GD.N0232.N0720.N1229.d013586 ρ z) ^ 2) _root_.GD.N0232.N0720.N1241.d013568 := by
  apply ((hh2.const_mul 2).add (integrable_const 2)).mono'
    ((hh.sub (_root_.GD.N0232.N0720.N1229.d013587 ρ)).pow_const 2).aestronglyMeasurable
  filter_upwards [_root_.GD.N0232.N0720.N1229.d013589 ρ] with z hz
  exact _root_.GD.N0232.N0720.N1229.d013592 (h z) (_root_.GD.N0232.N0720.N1229.d013586 ρ z) hz

theorem d013594
    (h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hh : Measurable h)
    (hh2 : Integrable (fun z ↦ h z ^ 2) _root_.GD.N0232.N0720.N1241.d013568) :
    Continuous (_root_.GD.N0232.N0720.N1229.d013591 h) := by
  apply continuous_of_dominated (bound := fun z ↦ 2 * h z ^ 2 + 2)
  · intro ρ
    exact ((hh.sub (_root_.GD.N0232.N0720.N1229.d013587 ρ)).pow_const 2).aestronglyMeasurable
  · intro ρ
    filter_upwards [_root_.GD.N0232.N0720.N1229.d013589 ρ] with z hz
    exact _root_.GD.N0232.N0720.N1229.d013592 (h z) (_root_.GD.N0232.N0720.N1229.d013586 ρ z) hz
  · exact (hh2.const_mul 2).add (integrable_const 2)
  · filter_upwards [_root_.GD.N0232.N0720.N1229.d013588] with z hz
    exact (continuous_const.sub (_root_.GD.N0232.N0720.N1229.d013590 hz)).pow 2




theorem d013595
    (h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hh : Measurable h)
    (hh2 : Integrable (fun z ↦ h z ^ 2) _root_.GD.N0232.N0720.N1241.d013568)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070, _root_.GD.N0232.N0720.N1229.d013591 h ρ < ε) :
    ∃ ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070,
      h =ᵐ[_root_.GD.N0232.N0720.N1241.d013568] _root_.GD.N0232.N0720.N1229.d013586 ρ := by
  letI : Inhabited _root_.GD.N0232.N0720.N1240.d002070 := ⟨⟨0, by norm_num⟩⟩
  obtain ⟨ρ, _, hmin⟩ := (isCompact_univ : IsCompact
    (univ : Set (ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070))).exists_isMinOn
      univ_nonempty (_root_.GD.N0232.N0720.N1229.d013594 h hh hh2).continuousOn
  have hzero : _root_.GD.N0232.N0720.N1229.d013591 h ρ = 0 := by
    apply le_antisymm
    · by_contra hnot
      have hpos : 0 < _root_.GD.N0232.N0720.N1229.d013591 h ρ := lt_of_not_ge hnot
      obtain ⟨σ, hσ⟩ := happrox (_root_.GD.N0232.N0720.N1229.d013591 h ρ) hpos
      exact (not_lt_of_ge (hmin (mem_univ σ))) hσ
    · exact integral_nonneg fun _ ↦ sq_nonneg _
  refine ⟨ρ, ?_⟩
  have hae : (fun z ↦ (h z - _root_.GD.N0232.N0720.N1229.d013586 ρ z) ^ 2) =ᵐ[_root_.GD.N0232.N0720.N1241.d013568] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun z ↦ sq_nonneg (h z - _root_.GD.N0232.N0720.N1229.d013586 ρ z))
      (_root_.GD.N0232.N0720.N1229.d013593 h hh hh2 ρ)).mp hzero
  filter_upwards [hae] with z hz
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

end
end GD.N0232.N0720.N1229

#print axioms _root_.GD.N0232.N0720.N1229.d013594
#print axioms _root_.GD.N0232.N0720.N1229.d013595
