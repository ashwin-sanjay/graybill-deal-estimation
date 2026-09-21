import GD.Module0887
import GD.Module0871










open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace GD.N0232.N0720.N1269

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1266 _root_.GD.N0232.N0720.N1271
open _root_.GD.N0232.N0720.N1268 _root_.GD.N0232.N0720.N1290

local instance : Nonempty _root_.GD.N0232.N0720.N1290.d004131 := ⟨⟨0, by constructor <;> norm_num⟩⟩

variable {I : Type*} [Fintype I]

def d013780 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) (i : I) : ℝ :=
  w i * _root_.GD.N0232.N0720.N1271.d013403 (q i).1 ^ 2

omit [Fintype I] in
theorem d013781 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : I) : 0 ≤ _root_.GD.N0232.N0720.N1269.d013780 q w i :=
  mul_nonneg (hw i) (sq_nonneg _)

omit [Fintype I] in
theorem d013782 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    {i : I} (hi : 0 < w i) : 0 < _root_.GD.N0232.N0720.N1269.d013780 q w i :=
  mul_pos hi (sq_pos_of_pos (_root_.GD.N0232.N0720.N1271.d013408 (q i).2.1 (q i).2.2))

def d013783 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) : FiniteMeasure _root_.GD.N0232.N0720.N1290.d004131 :=
  ⟨∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1269.d013780 q w i) • Measure.dirac (_root_.GD.N0232.N0720.N1266.d013713 (q i)),
    by
      letI : ∀ i : I, IsFiniteMeasure
          (ENNReal.ofReal (_root_.GD.N0232.N0720.N1269.d013780 q w i) • Measure.dirac (_root_.GD.N0232.N0720.N1266.d013713 (q i))) :=
        fun i ↦ (Measure.dirac (_root_.GD.N0232.N0720.N1266.d013713 (q i))).smul_finite ENNReal.ofReal_ne_top
      infer_instance⟩

theorem d013784 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hpositive : ∃ i, 0 < w i) : _root_.GD.N0232.N0720.N1269.d013783 q w ≠ 0 := by
  obtain ⟨j, hj⟩ := hpositive
  have hmass : 0 < (_root_.GD.N0232.N0720.N1269.d013783 q w : Measure _root_.GD.N0232.N0720.N1290.d004131) univ := by
    change 0 < (∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1269.d013780 q w i) •
      Measure.dirac (_root_.GD.N0232.N0720.N1266.d013713 (q i))) univ
    simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _),
      smul_eq_mul, mul_one]
    have hbound : ENNReal.ofReal (_root_.GD.N0232.N0720.N1269.d013780 q w j) ≤
        ∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1269.d013780 q w i) := by
      simpa only using! (Finset.single_le_sum
        (f := fun i : I ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1269.d013780 q w i))
        (fun i _ ↦ show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (_root_.GD.N0232.N0720.N1269.d013780 q w i) from bot_le)
        (Finset.mem_univ j))
    exact (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0720.N1269.d013782 q w hj)).trans_le hbound
  intro hz
  simp [hz] at hmass

def d013785 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131 :=
  (_root_.GD.N0232.N0720.N1269.d013783 q w).normalize

theorem d013786 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (f : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) :
    (∫ t, f t ∂(_root_.GD.N0232.N0720.N1269.d013783 q w : Measure _root_.GD.N0232.N0720.N1290.d004131)) =
      ∑ i, _root_.GD.N0232.N0720.N1269.d013780 q w i * f (_root_.GD.N0232.N0720.N1266.d013713 (q i)) := by
  change (∫ t, f t ∂(∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1269.d013780 q w i) •
      Measure.dirac (_root_.GD.N0232.N0720.N1266.d013713 (q i)))) = _
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1269.d013781 q w hw i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d013787 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hpositive : ∃ i, 0 < w i) (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) :
    _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) P (_root_.GD.N0232.N0720.N1269.d013785 q w : Measure _root_.GD.N0232.N0720.N1290.d004131) =
      _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) P (_root_.GD.N0232.N0720.N1269.d013783 q w : Measure _root_.GD.N0232.N0720.N1290.d004131) := by
  have hn := _root_.GD.N0232.N0720.N1269.d013784 q w hpositive
  have hm : ((_root_.GD.N0232.N0720.N1269.d013783 q w).mass)⁻¹ ≠ 0 :=
    inv_ne_zero ((_root_.GD.N0232.N0720.N1269.d013783 q w).mass_nonzero_iff.mpr hn)
  have hmreal : (↑((_root_.GD.N0232.N0720.N1269.d013783 q w).mass)⁻¹ : ℝ) ≠ 0 := by exact_mod_cast hm
  unfold _root_.GD.N0232.N0720.N1269.d013785 _root_.GD.N0232.N0720.N1290.d004140 _root_.GD.N0232.N0720.N1290.d004139
  rw [(_root_.GD.N0232.N0720.N1269.d013783 q w).toMeasure_normalize_eq_of_nonzero hn,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, smul_eq_mul]
  exact mul_div_mul_left _ _ hmreal

theorem d013788 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0232.N0720.N1290.d004139 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) (_root_.GD.N0232.N0720.N1269.d013783 q w : Measure _root_.GD.N0232.N0720.N1290.d004131) := by
  rw [_root_.GD.N0232.N0720.N1290.d004139, _root_.GD.N0232.N0720.N1269.d013786 q w hw]
  obtain ⟨j, hj⟩ := hpositive
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (_root_.GD.N0232.N0720.N1269.d013781 q w hw i)
      (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1271.d013407 hx _) _).le
  · exact ⟨j, Finset.mem_univ j, mul_pos (_root_.GD.N0232.N0720.N1269.d013782 q w hj)
      (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1271.d013407 hx _) _)⟩


theorem d013789 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1266.d013718 t (_root_.GD.N0232.N0720.N1266.d013726 x) =
      (16 / _root_.GD.N0232.N0720.N1271.d013404 x (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677) ^ (-(5 / 2 : ℝ))) *
        _root_.GD.N0232.N0720.N1271.d013403 t.1 ^ 2 * _root_.GD.N0232.N0720.N1271.d013404 x (_root_.GD.N0232.N0720.N1266.d013713 t) ^ (-(5 / 2 : ℝ)) := by
  rw [_root_.GD.N0232.N0720.N1266.d013730 hx t]
  ring

theorem d013790 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1268.d013764 q w (_root_.GD.N0232.N0720.N1266.d013726 x) =
      (16 / _root_.GD.N0232.N0720.N1271.d013404 x (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677) ^ (-(5 / 2 : ℝ))) *
        _root_.GD.N0232.N0720.N1290.d004139 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) (_root_.GD.N0232.N0720.N1269.d013783 q w : Measure _root_.GD.N0232.N0720.N1290.d004131) := by
  rw [_root_.GD.N0232.N0720.N1268.d013766, _root_.GD.N0232.N0720.N1290.d004139, _root_.GD.N0232.N0720.N1269.d013786 q w hw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0232.N0720.N1269.d013789 hx]
  unfold _root_.GD.N0232.N0720.N1269.d013780
  ring

theorem d013791 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1268.d013765 q w (_root_.GD.N0232.N0720.N1266.d013726 x) =
      (16 / _root_.GD.N0232.N0720.N1271.d013404 x (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677) ^ (-(5 / 2 : ℝ))) *
        ((∫ t, (t : ℝ) * _root_.GD.N0232.N0720.N1271.d013404 x t ^ (-(5 / 2 : ℝ))
            ∂(_root_.GD.N0232.N0720.N1269.d013783 q w : Measure _root_.GD.N0232.N0720.N1290.d004131)) -
          (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1290.d004139 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) (_root_.GD.N0232.N0720.N1269.d013783 q w : Measure _root_.GD.N0232.N0720.N1290.d004131)) := by
  rw [_root_.GD.N0232.N0720.N1268.d013767, _root_.GD.N0232.N0720.N1290.d004139, _root_.GD.N0232.N0720.N1269.d013786 q w hw,
    _root_.GD.N0232.N0720.N1269.d013786 q w hw, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0232.N0720.N1269.d013789 hx]
  simp only [_root_.GD.N0232.N0720.N1269.d013780, _root_.GD.N0232.N0720.N1441.d013680, _root_.GD.N0232.N0720.N1266.d013713]
  ring



theorem d013792 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1268.d013765 q w (_root_.GD.N0232.N0720.N1266.d013726 x) / _root_.GD.N0232.N0720.N1268.d013764 q w (_root_.GD.N0232.N0720.N1266.d013726 x) + 1 / 2 =
      _root_.GD.N0232.N0720.N1290.d004140 (5 / 2) (_root_.GD.N0232.N0720.N1271.d013404 x) (_root_.GD.N0232.N0720.N1269.d013785 q w : Measure _root_.GD.N0232.N0720.N1290.d004131) := by
  rw [_root_.GD.N0232.N0720.N1269.d013787 q w hpositive,
    _root_.GD.N0232.N0720.N1269.d013791 q w hw hx, _root_.GD.N0232.N0720.N1269.d013790 q w hw hx,
    _root_.GD.N0232.N0720.N1290.d004140]
  have hD := (_root_.GD.N0232.N0720.N1269.d013788 q w hw hpositive hx).ne'
  have hC : 16 / _root_.GD.N0232.N0720.N1271.d013404 x (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677) ^ (-(5 / 2 : ℝ)) ≠ 0 :=
    div_ne_zero (by norm_num) (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1271.d013407 hx _) _).ne'
  rw [mul_div_mul_left _ _ hC]
  field_simp [hD]
  ring

end
end GD.N0232.N0720.N1269

#print axioms _root_.GD.N0232.N0720.N1269.d013784
#print axioms _root_.GD.N0232.N0720.N1269.d013792
