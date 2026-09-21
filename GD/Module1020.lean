import GD.Module0879
import GD.Module1018
import GD.Module0884

set_option warningAsError true
set_option autoImplicit false
set_option linter.unusedSectionVars false










open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace GD.N0232.N0720.N1235

noncomputable section

open _root_.GD.N0232.N0720.N1240 _root_.GD.N0232.N0720.N1229
open _root_.GD.N0232.N0720.N1236 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1436

variable {ι : Type*} [Fintype ι]

def d016229 (t : _root_.GD.N0232.N0720.N1441.d013676) : _root_.GD.N0232.N0720.N1240.d002070 :=
  ⟨(t : ℝ) - 1 / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

def d016230 (a : ι → ℝ) (t : ι → _root_.GD.N0232.N0720.N1441.d013676) (i : ι) : ℝ :=
  a i * ((t i : ℝ) * (1 - (t i : ℝ))) ^ 2

theorem d016231 (a : ι → ℝ) (t : ι → _root_.GD.N0232.N0720.N1441.d013676)
    (ha : ∀ i, 0 ≤ a i) (i : ι) : 0 ≤ _root_.GD.N0232.N0720.N1235.d016230 a t i :=
  mul_nonneg (ha i) (sq_nonneg _)

theorem d016232 (a : ι → ℝ) (t : ι → _root_.GD.N0232.N0720.N1441.d013676)
    {i : ι} (ha : 0 < a i) : 0 < _root_.GD.N0232.N0720.N1235.d016230 a t i := by
  exact mul_pos ha (sq_pos_of_pos
    (mul_pos (t i).property.1 (sub_pos.mpr (t i).property.2)))

def d016233 (a : ι → ℝ) (t : ι → _root_.GD.N0232.N0720.N1441.d013676) : Measure _root_.GD.N0232.N0720.N1240.d002070 :=
  ∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1235.d016230 a t i) • Measure.dirac (_root_.GD.N0232.N0720.N1235.d016229 (t i))

instance d016234 (a : ι → ℝ) (t : ι → _root_.GD.N0232.N0720.N1441.d013676) :
    IsFiniteMeasure (_root_.GD.N0232.N0720.N1235.d016233 a t) := by
  constructor
  simp [_root_.GD.N0232.N0720.N1235.d016233, Measure.finsetSum_apply]

theorem d016235 (a : ι → ℝ) (t : ι → _root_.GD.N0232.N0720.N1441.d013676)
    (_ha : ∀ i, 0 ≤ a i) (hpos : ∃ i, 0 < a i) : _root_.GD.N0232.N0720.N1235.d016233 a t ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := hpos
  intro hzero
  have hle : ENNReal.ofReal (_root_.GD.N0232.N0720.N1235.d016230 a t i) ≤ (_root_.GD.N0232.N0720.N1235.d016233 a t) univ := by
    simp only [_root_.GD.N0232.N0720.N1235.d016233, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    exact Finset.single_le_sum (f := fun j ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1235.d016230 a t j))
      (fun _ _ ↦ by positivity) (Finset.mem_univ i)
  rw [hzero] at hle
  simp only [Measure.coe_zero, Pi.zero_apply] at hle
  have hp := ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0720.N1235.d016232 a t hi)
  exact not_lt_of_ge hle hp

theorem d016236 (a : ι → ℝ) (t : ι → _root_.GD.N0232.N0720.N1441.d013676)
    (ha : ∀ i, 0 ≤ a i) (f : _root_.GD.N0232.N0720.N1240.d002070 → ℝ) :
    (∫ x, f x ∂_root_.GD.N0232.N0720.N1235.d016233 a t) =
      ∑ i, _root_.GD.N0232.N0720.N1235.d016230 a t i * f (_root_.GD.N0232.N0720.N1235.d016229 (t i)) := by
  rw [_root_.GD.N0232.N0720.N1235.d016233, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1235.d016231 a t ha i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

theorem d016237
    (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) (c : NNReal) (hc : c ≠ 0) (u v : ℝ) :
    _root_.GD.N0232.N0720.N1240.d002100 (c • ρ) u v =
      _root_.GD.N0232.N0720.N1240.d002100 ρ u v := by
  unfold _root_.GD.N0232.N0720.N1240.d002100
  rw [integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, smul_eq_mul]
  exact mul_div_mul_left _ _ (NNReal.coe_ne_zero.mpr hc)

def d016238 (a : ι → ℝ) (t : ι → _root_.GD.N0232.N0720.N1441.d013676) : FiniteMeasure _root_.GD.N0232.N0720.N1240.d002070 :=
  ⟨_root_.GD.N0232.N0720.N1235.d016233 a t, inferInstance⟩

def d016239 (a : ι → ℝ) (t : ι → _root_.GD.N0232.N0720.N1441.d013676) :
    ProbabilityMeasure _root_.GD.N0232.N0720.N1240.d002070 := by
  letI : Nonempty _root_.GD.N0232.N0720.N1240.d002070 := ⟨⟨0, by norm_num⟩⟩
  exact (_root_.GD.N0232.N0720.N1235.d016238 a t).normalize

theorem d016240 (a : ι → ℝ) (t : ι → _root_.GD.N0232.N0720.N1441.d013676)
    (ha : ∀ i, 0 ≤ a i) (hpos : ∃ i, 0 < a i)
    (z : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1229.d013586 (_root_.GD.N0232.N0720.N1235.d016239 a t) z =
      (∑ i, _root_.GD.N0232.N0720.N1235.d016230 a t i * (t i : ℝ) *
        Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 (t i) z.1 z.2) (-5 / 2)) /
      (∑ i, _root_.GD.N0232.N0720.N1235.d016230 a t i *
        Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 (t i) z.1 z.2) (-5 / 2)) := by
  letI : Nonempty _root_.GD.N0232.N0720.N1240.d002070 := ⟨⟨0, by norm_num⟩⟩
  have hne : _root_.GD.N0232.N0720.N1235.d016238 a t ≠ 0 := by
    intro hz
    have hmeasure := congrArg (fun ν : FiniteMeasure _root_.GD.N0232.N0720.N1240.d002070 ↦
      (ν : Measure _root_.GD.N0232.N0720.N1240.d002070)) hz
    exact _root_.GD.N0232.N0720.N1235.d016235 a t ha hpos hmeasure
  have hc : (_root_.GD.N0232.N0720.N1235.d016238 a t).mass⁻¹ ≠ 0 :=
    inv_ne_zero ((_root_.GD.N0232.N0720.N1235.d016238 a t).mass_nonzero_iff.mpr hne)
  change _root_.GD.N0232.N0720.N1240.d002100
    ((_root_.GD.N0232.N0720.N1235.d016238 a t).normalize : Measure _root_.GD.N0232.N0720.N1240.d002070) z.1 z.2 = _
  rw [(_root_.GD.N0232.N0720.N1235.d016238 a t).toMeasure_normalize_eq_of_nonzero hne,
    _root_.GD.N0232.N0720.N1235.d016237 _ _ hc]
  change _root_.GD.N0232.N0720.N1240.d002100 (_root_.GD.N0232.N0720.N1235.d016233 a t) z.1 z.2 = _
  unfold _root_.GD.N0232.N0720.N1240.d002100
  rw [_root_.GD.N0232.N0720.N1235.d016236 a t ha, _root_.GD.N0232.N0720.N1235.d016236 a t ha]
  simp only [_root_.GD.N0232.N0720.N1235.d016229, sub_add_cancel]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end GD.N0232.N0720.N1235

#print axioms _root_.GD.N0232.N0720.N1235.d016240
