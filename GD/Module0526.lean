import GD.Module0525
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0024.N0266

noncomputable section

open _root_.GD.N0024.N0277

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]

theorem d007897
    (μ : Measure Ω) (Q : _root_.GD.N0024.N0277.d007878 → Measure Ω)
    (K E : Set Ω) (hK : IsCompact K) (hKne : K.Nonempty)
    (hE : MeasurableSet E) (hEK : E ⊆ K) (hfinite : μ E ≠ ⊤)
    (hpositive : 0 < μ.real E)
    (density : ℝ × Ω → ℝ)
    (hcontinuous : ContinuousOn density (Icc (0 : ℝ) 1 ×ˢ K))
    (hdensity : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ z ∈ K, 0 < density (t, z))
    (hintegrable : ∀ t : _root_.GD.N0024.N0277.d007878, IntegrableOn (fun z => density (t.1, z)) E μ)
    (hmass : ∀ t : _root_.GD.N0024.N0277.d007878, (Q t).real E / _root_.GD.N0024.N0277.d007879 t = ∫ z in E, density (t.1, z) ∂μ)
    (d : ℝ) (hd : 0 < d) (hdhalf : d < 1 / 2) :
    ∃ M k : ℝ, 0 ≤ M ∧ 0 < k ∧
      (∀ t : _root_.GD.N0024.N0277.d007878, (Q t).real E / _root_.GD.N0024.N0277.d007879 t ≤ M) ∧
      (∀ t : _root_.GD.N0024.N0277.d007878, d ≤ t.1 → t.1 ≤ 1 - d → k ≤ (Q t).real E / _root_.GD.N0024.N0277.d007879 t) := by
  have hfullNe : (Icc (0 : ℝ) 1 ×ˢ K).Nonempty :=
    (nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)).prod hKne
  obtain ⟨pmax, hpmax, hmax⟩ :=
    (isCompact_Icc.prod hK).exists_isMaxOn hfullNe hcontinuous
  have hsmallSubset : (Icc d (1 - d) ×ˢ K) ⊆ Icc (0 : ℝ) 1 ×ˢ K := by
    intro p hp
    exact ⟨⟨hd.le.trans hp.1.1, hp.1.2.trans (by linarith)⟩, hp.2⟩
  have hsmallNe : (Icc d (1 - d) ×ˢ K).Nonempty :=
    (nonempty_Icc.mpr (by linarith : d ≤ 1 - d)).prod hKne
  obtain ⟨pmin, hpmin, hmin⟩ :=
    (isCompact_Icc.prod hK).exists_isMinOn hsmallNe (hcontinuous.mono hsmallSubset)
  have hpminPos : 0 < density pmin := by
    exact hdensity pmin.1 ⟨hd.trans_le hpmin.1.1, hpmin.1.2.trans_lt (by linarith)⟩
      pmin.2 hpmin.2
  refine ⟨μ.real E * max (density pmax) 0, μ.real E * density pmin,
    mul_nonneg hpositive.le (le_max_right _ _), mul_pos hpositive hpminPos, ?_, ?_⟩
  · intro t
    rw [hmass]
    have hi := setIntegral_mono_on (hintegrable t)
      (integrableOn_const hfinite : IntegrableOn (fun _ : Ω => max (density pmax) 0) E μ)
      hE (fun z hz => (hmax ⟨⟨t.2.1.le, t.2.2.le⟩, hEK hz⟩).trans (le_max_left _ _))
    simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ,
      smul_eq_mul] using hi
  · intro t htlo hthi
    rw [hmass]
    have hi := setIntegral_mono_on
      (integrableOn_const hfinite : IntegrableOn (fun _ : Ω => density pmin) E μ)
      (hintegrable t) hE (fun z hz => hmin ⟨⟨htlo, hthi⟩, hEK hz⟩)
    simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ,
      smul_eq_mul] using hi

#print axioms _root_.GD.N0024.N0266.d007897

end
end GD.N0024.N0266
