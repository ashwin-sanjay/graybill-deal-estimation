import GD.Module0175
import Mathlib.MeasureTheory.Measure.Prokhorov

set_option warningAsError true
set_option autoImplicit false













open MeasureTheory Set Filter Topology

namespace GD.N0232.N0720.N1238

noncomputable section

open _root_.GD.N0232.N0720.N1240

abbrev d002103 :=
  {z : ℝ × ℝ // z.1 ∈ Ioo (-1 / 4 : ℝ) (1 / 4) ∧ z.2 ∈ Ioo (0 : ℝ) (1 / 4)}

def d002104 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) (z : _root_.GD.N0232.N0720.N1238.d002103) : ℝ :=
  ∫ x, _root_.GD.N0232.N0720.N1240.d002054 x z.val.1 z.val.2 ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)

theorem d002105 (z : _root_.GD.N0232.N0720.N1238.d002103) :
    Continuous (fun ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1238.d002104 ρ z) := by
  have hw : Continuous (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦
      Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x z.val.1 z.val.2) (-5 / 2)) := by
    apply (show Continuous (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦
      _root_.GD.N0232.N0720.N1240.d002053 x z.val.1 z.val.2) from by unfold _root_.GD.N0232.N0720.N1240.d002053; fun_prop).rpow_const
    intro x
    left
    have h := _root_.GD.N0232.N0720.N1240.d002071 x.property
      ⟨z.property.1.1.le, z.property.1.2.le⟩
      ⟨by linarith [z.property.2.1], z.property.2.2.le⟩
    linarith
  let f : ContinuousMap _root_.GD.N0232.N0720.N1240.d002070 ℝ :=
    ⟨fun x ↦ _root_.GD.N0232.N0720.N1240.d002054 x z.val.1 z.val.2,
      (continuous_subtype_val.sub continuous_const).mul hw⟩
  exact ProbabilityMeasure.continuous_integral_continuousMap f

theorem d002106 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
    ∃ z : _root_.GD.N0232.N0720.N1238.d002103, _root_.GD.N0232.N0720.N1238.d002104 ρ z ≠ 0 := by
  have h := _root_.GD.N0232.N0720.N1240.d002094 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)
  push Not at h
  obtain ⟨y, hy, v, hv, hne⟩ := h
  exact ⟨⟨(y, v), hy, hv⟩, hne⟩



theorem d002107
    {X I : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (f : X → I → ℝ) (hcontinuous : ∀ i, Continuous (fun x ↦ f x i))
    (hnonzero : ∀ x, ∃ i, f x i ≠ 0) :
    ∃ S : Finset I, ∃ c : ℝ, 0 < c ∧ ∀ x, ∃ i ∈ S, c < |f x i| := by
  classical
  letI : Inhabited X := Classical.inhabited_of_nonempty (inferInstance : Nonempty X)
  let chosen (ρ : X) : I := Classical.choose (hnonzero ρ)
  have hchosen (ρ : X) : f ρ (chosen ρ) ≠ 0 := Classical.choose_spec (hnonzero ρ)
  let radius (ρ : X) : ℝ := |f ρ (chosen ρ)| / 2
  have hrad (ρ : X) : 0 < radius ρ :=
    div_pos (abs_pos.mpr (hchosen ρ)) (by norm_num)
  let U (ρ : X) : Set X := {σ | radius ρ < |f σ (chosen ρ)|}
  have hU (ρ : X) : IsOpen (U ρ) :=
    isOpen_lt continuous_const (hcontinuous (chosen ρ)).abs
  have hcover : (univ : Set X) ⊆ ⋃ ρ, U ρ := by
    intro ρ _
    apply mem_iUnion.mpr
    refine ⟨ρ, ?_⟩
    change radius ρ < |f ρ (chosen ρ)|
    dsimp [radius]
    linarith [abs_pos.mpr (hchosen ρ)]
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (univ : Set X)).elim_finite_subcover U hU hcover
  have hsne : s.Nonempty := by
    have h := hs (mem_univ (default : X))
    obtain ⟨ρ, hρ⟩ := mem_iUnion.mp h
    obtain ⟨hρs, _⟩ := mem_iUnion.mp hρ
    exact ⟨ρ, hρs⟩
  refine ⟨s.image chosen, s.inf' hsne radius, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff hsne).2 fun ρ _ ↦ hrad ρ
  · intro σ
    obtain ⟨ρ, hρ⟩ := mem_iUnion.mp (hs (mem_univ σ))
    obtain ⟨hρs, hσ⟩ := mem_iUnion.mp hρ
    refine ⟨chosen ρ, Finset.mem_image.mpr ⟨ρ, hρs, rfl⟩, ?_⟩
    exact (Finset.inf'_le radius hρs).trans_lt hσ



theorem d002108 :
    ∃ S : Finset _root_.GD.N0232.N0720.N1238.d002103, ∃ c : ℝ, 0 < c ∧
      ∀ ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070,
        ∃ z ∈ S, c < |_root_.GD.N0232.N0720.N1238.d002104 ρ z| := by
  letI : Inhabited _root_.GD.N0232.N0720.N1240.d002070 := ⟨⟨0, by norm_num⟩⟩
  exact _root_.GD.N0232.N0720.N1238.d002107 _root_.GD.N0232.N0720.N1238.d002104
    _root_.GD.N0232.N0720.N1238.d002105 _root_.GD.N0232.N0720.N1238.d002106

def d002109 (z : _root_.GD.N0232.N0720.N1238.d002103) : ContinuousMap _root_.GD.N0232.N0720.N1240.d002070 ℝ := by
  refine ⟨fun x ↦ Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x z.val.1 z.val.2) (-5 / 2), ?_⟩
  apply (show Continuous (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1240.d002053 x z.val.1 z.val.2)
    from by unfold _root_.GD.N0232.N0720.N1240.d002053; fun_prop).rpow_const
  intro x
  left
  have h := _root_.GD.N0232.N0720.N1240.d002071 x.property
    ⟨z.property.1.1.le, z.property.1.2.le⟩
    ⟨by linarith [z.property.2.1], z.property.2.2.le⟩
  linarith

theorem d002110 (z : _root_.GD.N0232.N0720.N1238.d002103) (x : _root_.GD.N0232.N0720.N1240.d002070) :
    0 < _root_.GD.N0232.N0720.N1238.d002109 z x := by
  apply Real.rpow_pos_of_pos
  have h := _root_.GD.N0232.N0720.N1240.d002071 x.property
    ⟨z.property.1.1.le, z.property.1.2.le⟩
    ⟨by linarith [z.property.2.1], z.property.2.2.le⟩
  linarith

theorem d002111 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) (z : _root_.GD.N0232.N0720.N1238.d002103) :
    0 < ∫ x, _root_.GD.N0232.N0720.N1238.d002109 z x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) := by
  have hi : Integrable (fun x ↦ _root_.GD.N0232.N0720.N1238.d002109 z x) (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) := by
    simpa using (_root_.GD.N0232.N0720.N1238.d002109 z).continuous.continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact (univ : Set _root_.GD.N0232.N0720.N1240.d002070))
      (μ := (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070))
  apply (integral_pos_iff_support_of_nonneg (fun x ↦ (_root_.GD.N0232.N0720.N1238.d002110 z x).le) hi).2
  have hs : Function.support (fun x ↦ _root_.GD.N0232.N0720.N1238.d002109 z x) = univ := by
    ext x
    simp [Function.mem_support, ne_of_gt (_root_.GD.N0232.N0720.N1238.d002110 z x)]
  rw [hs]
  simp

def d002112 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) (z : _root_.GD.N0232.N0720.N1238.d002103) : ℝ :=
  _root_.GD.N0232.N0720.N1240.d002095 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) (z.val.1 + 1 / 2) z.val.2 -
    (z.val.1 + 1 / 2)

theorem d002113 (z : _root_.GD.N0232.N0720.N1238.d002103) :
    Continuous (fun ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1238.d002112 ρ z) := by
  let w := _root_.GD.N0232.N0720.N1238.d002109 z
  let n : ContinuousMap _root_.GD.N0232.N0720.N1240.d002070 ℝ :=
    ⟨fun x ↦ ((x : ℝ) + 1 / 2) * w x,
      (continuous_subtype_val.add continuous_const).mul w.continuous⟩
  have hn := ProbabilityMeasure.continuous_integral_continuousMap n
  have hd := ProbabilityMeasure.continuous_integral_continuousMap w
  have he : ∀ ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070,
      (∫ x, w x ∂(ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)) ≠ 0 :=
    fun ρ ↦ ne_of_gt (_root_.GD.N0232.N0720.N1238.d002111 ρ z)
  simpa [_root_.GD.N0232.N0720.N1238.d002112, _root_.GD.N0232.N0720.N1240.d002095, n, w, _root_.GD.N0232.N0720.N1238.d002109] using
    (hn.div hd he).sub (continuous_const : Continuous
      (fun _ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070 ↦ z.val.1 + 1 / 2))

theorem d002114 (ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070) :
    ∃ z : _root_.GD.N0232.N0720.N1238.d002103, _root_.GD.N0232.N0720.N1238.d002112 ρ z ≠ 0 := by
  by_contra h
  push Not at h
  apply _root_.GD.N0232.N0720.N1240.d002098 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070)
  intro u hu v hv
  let z : _root_.GD.N0232.N0720.N1238.d002103 :=
    ⟨(u - 1 / 2, v), ⟨by constructor <;> linarith [hu.1, hu.2], hv⟩⟩
  have hz := h z
  simpa [_root_.GD.N0232.N0720.N1238.d002112, z] using sub_eq_zero.mp hz



theorem d002115 :
    ∃ S : Finset _root_.GD.N0232.N0720.N1238.d002103, ∃ c : ℝ, 0 < c ∧
      ∀ ρ : ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070,
        ∃ z ∈ S, c < |_root_.GD.N0232.N0720.N1238.d002112 ρ z| := by
  letI : Inhabited _root_.GD.N0232.N0720.N1240.d002070 := ⟨⟨0, by norm_num⟩⟩
  exact _root_.GD.N0232.N0720.N1238.d002107 _root_.GD.N0232.N0720.N1238.d002112
    _root_.GD.N0232.N0720.N1238.d002113 _root_.GD.N0232.N0720.N1238.d002114

end

end GD.N0232.N0720.N1238

#print axioms _root_.GD.N0232.N0720.N1238.d002105
#print axioms _root_.GD.N0232.N0720.N1238.d002106
#print axioms _root_.GD.N0232.N0720.N1238.d002108
#print axioms _root_.GD.N0232.N0720.N1238.d002111
#print axioms _root_.GD.N0232.N0720.N1238.d002113
#print axioms _root_.GD.N0232.N0720.N1238.d002115
