import GD.Module0891
import GD.Module0281










open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace GD.N0232.N0720.N1306

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1312 _root_.GD.N0232.N0720.N1336
open _root_.GD.N0232.N0720.N1307 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1266 (d013713 d013726)

local instance : Nonempty _root_.GD.N0232.N0720.N1290.d004131 := ⟨⟨0, by constructor <;> norm_num⟩⟩

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
variable {I : Type*} [Fintype I]

def d013853 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) (i : I) : ℝ :=
  w i * _root_.GD.N0232.N0720.N1336.d013426 m n (q i).1

omit [Fintype I] in
theorem d013854 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : I) : 0 ≤ _root_.GD.N0232.N0720.N1306.d013853 m n q w i :=
  mul_nonneg (hw i) (_root_.GD.N0232.N0720.N1336.d013427 m n (q i).2.1 (q i).2.2).le

omit [Fintype I] in
theorem d013855 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    {i : I} (hi : 0 < w i) : 0 < _root_.GD.N0232.N0720.N1306.d013853 m n q w i :=
  mul_pos hi (_root_.GD.N0232.N0720.N1336.d013427 m n (q i).2.1 (q i).2.2)

def d013856 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) : FiniteMeasure _root_.GD.N0232.N0720.N1290.d004131 :=
  ⟨∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1306.d013853 m n q w i) • Measure.dirac (_root_.GD.N0232.N0720.N1266.d013713 (q i)),
    by
      letI : ∀ i : I, IsFiniteMeasure
          (ENNReal.ofReal (_root_.GD.N0232.N0720.N1306.d013853 m n q w i) • Measure.dirac (_root_.GD.N0232.N0720.N1266.d013713 (q i))) :=
        fun i ↦ (Measure.dirac (_root_.GD.N0232.N0720.N1266.d013713 (q i))).smul_finite ENNReal.ofReal_ne_top
      infer_instance⟩

theorem d013857 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hpositive : ∃ i, 0 < w i) : _root_.GD.N0232.N0720.N1306.d013856 m n q w ≠ 0 := by
  obtain ⟨j, hj⟩ := hpositive
  have hmass : 0 < (_root_.GD.N0232.N0720.N1306.d013856 m n q w : Measure _root_.GD.N0232.N0720.N1290.d004131) univ := by
    change 0 < (∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1306.d013853 m n q w i) •
      Measure.dirac (_root_.GD.N0232.N0720.N1266.d013713 (q i))) univ
    simp only [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _),
      smul_eq_mul, mul_one]
    have hbound : ENNReal.ofReal (_root_.GD.N0232.N0720.N1306.d013853 m n q w j) ≤
        ∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1306.d013853 m n q w i) := by
      simpa only using! (Finset.single_le_sum
        (f := fun i : I ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1306.d013853 m n q w i))
        (fun i _ ↦ show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (_root_.GD.N0232.N0720.N1306.d013853 m n q w i) from bot_le)
        (Finset.mem_univ j))
    exact (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0720.N1306.d013855 m n q w hj)).trans_le hbound
  intro hz
  simp [hz] at hmass

def d013858 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ) : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131 :=
  (_root_.GD.N0232.N0720.N1306.d013856 m n q w).normalize

theorem d013859 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (f : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) :
    (∫ t, f t ∂(_root_.GD.N0232.N0720.N1306.d013856 m n q w : Measure _root_.GD.N0232.N0720.N1290.d004131)) =
      ∑ i, _root_.GD.N0232.N0720.N1306.d013853 m n q w i * f (_root_.GD.N0232.N0720.N1266.d013713 (q i)) := by
  change (∫ t, f t ∂(∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1306.d013853 m n q w i) •
      Measure.dirac (_root_.GD.N0232.N0720.N1266.d013713 (q i)))) = _
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1306.d013854 m n q w hw i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d013860 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hpositive : ∃ i, 0 < w i) (P : _root_.GD.N0232.N0720.N1290.d004131 → ℝ) :
    _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) P (_root_.GD.N0232.N0720.N1306.d013858 m n q w : Measure _root_.GD.N0232.N0720.N1290.d004131) =
      _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) P (_root_.GD.N0232.N0720.N1306.d013856 m n q w : Measure _root_.GD.N0232.N0720.N1290.d004131) := by
  have hn := _root_.GD.N0232.N0720.N1306.d013857 m n q w hpositive
  have hm : ((_root_.GD.N0232.N0720.N1306.d013856 m n q w).mass)⁻¹ ≠ 0 :=
    inv_ne_zero ((_root_.GD.N0232.N0720.N1306.d013856 m n q w).mass_nonzero_iff.mpr hn)
  have hmreal : (↑((_root_.GD.N0232.N0720.N1306.d013856 m n q w).mass)⁻¹ : ℝ) ≠ 0 := by exact_mod_cast hm
  unfold _root_.GD.N0232.N0720.N1306.d013858 _root_.GD.N0232.N0720.N1290.d004140 _root_.GD.N0232.N0720.N1290.d004139
  rw [(_root_.GD.N0232.N0720.N1306.d013856 m n q w).toMeasure_normalize_eq_of_nonzero hn,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, smul_eq_mul]
  exact mul_div_mul_left _ _ hmreal

include hm hn in
theorem d013861 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0232.N0720.N1290.d004139 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x) (_root_.GD.N0232.N0720.N1306.d013856 m n q w : Measure _root_.GD.N0232.N0720.N1290.d004131) := by
  rw [_root_.GD.N0232.N0720.N1290.d004139, _root_.GD.N0232.N0720.N1306.d013859 m n q w hw]
  obtain ⟨j, hj⟩ := hpositive
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (_root_.GD.N0232.N0720.N1306.d013854 m n q w hw i)
      (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx _) _).le
  · exact ⟨j, Finset.mem_univ j, mul_pos (_root_.GD.N0232.N0720.N1306.d013855 m n q w hj)
      (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx _) _)⟩

include hm hn in

theorem d013862 {x : _root_.GD.N0232.N0720.N1436.d013217}
    (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1312.d013797 m n t (_root_.GD.N0232.N0720.N1266.d013726 x) =
      (1 / (_root_.GD.N0232.N0720.N1336.d013426 m n _root_.GD.N0232.N0720.N1441.d013677.1 *
        _root_.GD.N0232.N0720.N1336.d013420 m n x (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n))) *
        _root_.GD.N0232.N0720.N1336.d013426 m n t.1 * _root_.GD.N0232.N0720.N1336.d013420 m n x (_root_.GD.N0232.N0720.N1266.d013713 t) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n) := by
  rw [_root_.GD.N0232.N0720.N1312.d013803 m n hm hn hx t]
  simp only [div_eq_mul_inv]
  ring

theorem d013863 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1307.d013837 m n hm hn q w (_root_.GD.N0232.N0720.N1266.d013726 x) =
      (1 / (_root_.GD.N0232.N0720.N1336.d013426 m n _root_.GD.N0232.N0720.N1441.d013677.1 *
        _root_.GD.N0232.N0720.N1336.d013420 m n x (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n))) *
        _root_.GD.N0232.N0720.N1290.d004139 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x) (_root_.GD.N0232.N0720.N1306.d013856 m n q w : Measure _root_.GD.N0232.N0720.N1290.d004131) := by
  rw [_root_.GD.N0232.N0720.N1307.d013839 m n hm hn, _root_.GD.N0232.N0720.N1290.d004139, _root_.GD.N0232.N0720.N1306.d013859 m n q w hw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0232.N0720.N1306.d013862 m n hm hn hx]
  unfold _root_.GD.N0232.N0720.N1306.d013853
  ring

theorem d013864 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1307.d013838 m n hm hn q w (_root_.GD.N0232.N0720.N1266.d013726 x) =
      (1 / (_root_.GD.N0232.N0720.N1336.d013426 m n _root_.GD.N0232.N0720.N1441.d013677.1 *
        _root_.GD.N0232.N0720.N1336.d013420 m n x (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n))) *
        ((∫ t, (t : ℝ) * _root_.GD.N0232.N0720.N1336.d013420 m n x t ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n)
            ∂(_root_.GD.N0232.N0720.N1306.d013856 m n q w : Measure _root_.GD.N0232.N0720.N1290.d004131)) -
          (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1290.d004139 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x) (_root_.GD.N0232.N0720.N1306.d013856 m n q w : Measure _root_.GD.N0232.N0720.N1290.d004131)) := by
  rw [_root_.GD.N0232.N0720.N1307.d013840 m n hm hn, _root_.GD.N0232.N0720.N1290.d004139, _root_.GD.N0232.N0720.N1306.d013859 m n q w hw,
    _root_.GD.N0232.N0720.N1306.d013859 m n q w hw, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0232.N0720.N1306.d013862 m n hm hn hx]
  simp only [_root_.GD.N0232.N0720.N1306.d013853, _root_.GD.N0232.N0720.N1441.d013680, _root_.GD.N0232.N0720.N1266.d013713]
  ring



theorem d013865 (q : I → _root_.GD.N0232.N0720.N1441.d013676) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1307.d013838 m n hm hn q w (_root_.GD.N0232.N0720.N1266.d013726 x) / _root_.GD.N0232.N0720.N1307.d013837 m n hm hn q w (_root_.GD.N0232.N0720.N1266.d013726 x) + 1 / 2 =
      _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x) (_root_.GD.N0232.N0720.N1306.d013858 m n q w : Measure _root_.GD.N0232.N0720.N1290.d004131) := by
  rw [_root_.GD.N0232.N0720.N1306.d013860 m n q w hpositive,
    _root_.GD.N0232.N0720.N1306.d013864 m n hm hn q w hw hx, _root_.GD.N0232.N0720.N1306.d013863 m n hm hn q w hw hx,
    _root_.GD.N0232.N0720.N1290.d004140]
  have hD := (_root_.GD.N0232.N0720.N1306.d013861 m n hm hn q w hw hpositive hx).ne'
  have hC : 1 / (_root_.GD.N0232.N0720.N1336.d013426 m n _root_.GD.N0232.N0720.N1441.d013677.1 *
      _root_.GD.N0232.N0720.N1336.d013420 m n x (_root_.GD.N0232.N0720.N1266.d013713 _root_.GD.N0232.N0720.N1441.d013677) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n)) ≠ 0 :=
    div_ne_zero one_ne_zero (mul_ne_zero
      (_root_.GD.N0232.N0720.N1336.d013427 m n _root_.GD.N0232.N0720.N1441.d013677.2.1 _root_.GD.N0232.N0720.N1441.d013677.2.2).ne'
      (Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx _) _).ne')
  rw [mul_div_mul_left _ _ hC]
  field_simp [hD]
  ring

end
end GD.N0232.N0720.N1306

#print axioms _root_.GD.N0232.N0720.N1306.d013857
#print axioms _root_.GD.N0232.N0720.N1306.d013865
