import GD.Module0717
import GD.Module0658
import GD.Module0555

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal ProbabilityTheory
namespace GD.N0232.N0719.N0899
noncomputable section
open _root_.GD.N0137 _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N1009 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0232.N0719.N0875 _root_.GD.N0232.N0719.N1003
open _root_.GD.N0232.N0719.N0960

def d021931 (size : ℕ) (beta : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0875.d010339 size beta - _root_.GD.N0232.N0719.N0875.d010338 size beta

def d021932 {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) : ℝ :=
  _root_.GD.N0232.N0719.N1003.d010648 sizes beta s - _root_.GD.N0232.N0719.N1003.d010647 sizes beta s

theorem d021933 {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (beta : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    0 ≤ _root_.GD.N0232.N0719.N0899.d021932 sizes beta s :=
  sub_nonneg.mpr (_root_.GD.N0232.N0719.N1003.d010654 sizes beta s)

@[fun_prop] theorem d021934 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (beta : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0899.d021932 sizes beta) :=
  (_root_.GD.N0232.N0719.N1003.d010660 sizes beta).sub (_root_.GD.N0232.N0719.N1003.d010659 sizes beta)

theorem d021935 {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) {beta : ℝ}
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) (i : Fin (n + 1)) :
    _root_.GD.N0232.N0719.N0899.d021932 sizes beta s ≤ _root_.GD.N0232.N0719.N0899.d021931 (sizes i) beta *
      Real.sqrt (s.meanVariance i) := by
  have hgap : 0 ≤ _root_.GD.N0232.N0719.N0899.d021931 (sizes i) beta :=
    sub_nonneg.mpr (_root_.GD.N0232.N0719.N0875.d010344 (hsizes i) hb0 hb1)
  unfold _root_.GD.N0232.N0719.N0899.d021932 _root_.GD.N0232.N0719.N1003.d010648 _root_.GD.N0232.N0719.N1003.d010647
  split_ifs with h
  · have hl := _root_.GD.N0232.N0719.N1003.d010649 sizes beta s i
    have hu := _root_.GD.N0232.N0719.N1003.d010650 sizes beta s i
    unfold _root_.GD.N0232.N0719.N1003.d010642 _root_.GD.N0232.N0719.N0875.d010340 at hl
    unfold _root_.GD.N0232.N0719.N1003.d010643 _root_.GD.N0232.N0719.N0875.d010341 at hu
    unfold _root_.GD.N0232.N0719.N0899.d021931
    nlinarith
  · simp only [sub_self]
    exact mul_nonneg hgap (Real.sqrt_nonneg _)

theorem d021936 {q : ℝ} (hq : 0 ≤ q) :
    Real.sqrt q ≤ (q + 1) / 2 := by
  nlinarith [sq_nonneg (Real.sqrt q - 1), Real.sq_sqrt hq]

theorem d021937 {a : ℝ} (ha : 0 < a) :
    Integrable Real.sqrt (gammaMeasure a a) := by
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  have hbound : Integrable (fun q : ℝ => (q + 1) / 2) (gammaMeasure a a) :=
    ((_root_.GD.N0232.N0719.N0960.d009683 ha ha).add (integrable_const 1)).div_const 2
  apply hbound.mono' (by fun_prop)
  filter_upwards [_root_.GD.N0232.N0719.N0960.d009681 ha ha] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact _root_.GD.N0232.N0719.N0899.d021936 hq

theorem d021938 {a : ℝ} (ha : 0 < a) :
    (∫ q, Real.sqrt q ∂gammaMeasure a a) ≤ 1 := by
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  have hid := _root_.GD.N0232.N0719.N0960.d009683 ha ha
  have hbound : Integrable (fun q : ℝ => (q + 1) / 2) (gammaMeasure a a) :=
    (hid.add (integrable_const 1)).div_const 2
  calc
    (∫ q, Real.sqrt q ∂gammaMeasure a a) ≤
        ∫ q, (q + 1) / 2 ∂gammaMeasure a a := by
      apply integral_mono_ae (_root_.GD.N0232.N0719.N0899.d021937 ha) hbound
      filter_upwards [_root_.GD.N0232.N0719.N0960.d009681 ha ha] with q hq
      exact _root_.GD.N0232.N0719.N0899.d021936 hq
    _ = 1 := by
      rw [integral_div, integral_add hid (integrable_const 1),
        _root_.GD.N0232.N0719.N0960.d009682 ha ha]
      simp [ha.ne']

theorem d021939 {size : ℕ} (hsize : 2 ≤ size)
    (scale : ℝ) : Integrable Real.sqrt (_root_.GD.N0232.N0719.N0933.d009289 size scale) := by
  have ha : 0 < ((size - 1 : ℕ) : ℝ) / 2 := by
    have : 0 < size - 1 := by omega
    positivity
  unfold _root_.GD.N0232.N0719.N0933.d009289
  rw [integrable_map_measure (by fun_prop)
    (_root_.GD.N0232.N0719.N0933.d009294 size scale).aemeasurable]
  have h := (_root_.GD.N0232.N0719.N0899.d021937 ha).const_mul
    (Real.sqrt (scale ^ 2 / (size : ℝ)))
  apply h.congr
  filter_upwards with q
  simp only [Function.comp_apply, _root_.GD.N0232.N0719.N0933.d009287,
    Real.sqrt_mul (div_nonneg (sq_nonneg scale) (Nat.cast_nonneg size))]

theorem d021940 {size : ℕ} (hsize : 2 ≤ size)
    (scale : ℝ) :
    (∫ q, Real.sqrt q ∂_root_.GD.N0232.N0719.N0933.d009289 size scale) ≤
      Real.sqrt (scale ^ 2 / (size : ℝ)) := by
  have ha : 0 < ((size - 1 : ℕ) : ℝ) / 2 := by
    have : 0 < size - 1 := by omega
    positivity
  unfold _root_.GD.N0232.N0719.N0933.d009289
  rw [integral_map (_root_.GD.N0232.N0719.N0933.d009294 size scale).aemeasurable
    (by fun_prop)]
  simp only [_root_.GD.N0232.N0719.N0933.d009287,
    Real.sqrt_mul (div_nonneg (sq_nonneg scale) (Nat.cast_nonneg size))]
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (_root_.GD.N0232.N0719.N0899.d021938 ha)
    (Real.sqrt_nonneg _)).trans_eq (mul_one _)

theorem d021941 {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (i : Fin k) (location : ℝ)
    (scales : Fin k → ℝ) :
    MeasurePreserving (fun omega => (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega).meanVariance i)
      (_root_.GD.N0232.N0719.d009176 k sizes location scales)
      (_root_.GD.N0232.N0719.N0933.d009289 (sizes i) (scales i)) := by
  have hpair : MeasurePreserving (_root_.GD.N0232.N0719.N0875.d010333 i ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes)
      (_root_.GD.N0232.N0719.d009176 k sizes location scales)
      ((_root_.GD.N0232.N0719.N0933.d009288 (sizes i) location (scales i)).prod
        (_root_.GD.N0232.N0719.N0933.d009289 (sizes i) (scales i))) := by
    refine ⟨(_root_.GD.N0232.N0719.N0875.d010334 i).comp (_root_.GD.N0232.N0719.N0900.d009115 k sizes), ?_⟩
    rw [_root_.GD.N0232.N0719.N0875.d010336 sizes hsizes i location scales,
      _root_.GD.N0232.N0719.N0933.d009298]
  exact (measurePreserving_snd.comp hpair)

theorem d021942 {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (i : Fin k) (location : ℝ)
    (scales : Fin k → ℝ) :
    Integrable (fun omega => Real.sqrt ((_root_.GD.N0232.N0719.N0900.d009104 k sizes omega).meanVariance i))
      (_root_.GD.N0232.N0719.d009176 k sizes location scales) := by
  have hmp := _root_.GD.N0232.N0719.N0899.d021941 sizes hsizes i location scales
  exact (hmp.integrable_comp (by fun_prop)).mpr
    (_root_.GD.N0232.N0719.N0899.d021939 (hsizes i) (scales i))

theorem d021943 {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (i : Fin k) (location : ℝ)
    (scales : Fin k → ℝ) :
    (∫ omega, Real.sqrt ((_root_.GD.N0232.N0719.N0900.d009104 k sizes omega).meanVariance i)
      ∂_root_.GD.N0232.N0719.d009176 k sizes location scales) ≤
      Real.sqrt (scales i ^ 2 / (sizes i : ℝ)) := by
  have hmp := _root_.GD.N0232.N0719.N0899.d021941 sizes hsizes i location scales
  rw [← integral_map hmp.measurable.aemeasurable (by fun_prop), hmp.map_eq]
  exact _root_.GD.N0232.N0719.N0899.d021940 (hsizes i) (scales i)

theorem d021944 {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) {beta : ℝ}
    (hb0 : 0 < beta) (hb1 : beta < 1) (location : ℝ)
    (scales : Fin (n + 1) → ℝ) :
    Integrable (fun omega => _root_.GD.N0232.N0719.N0899.d021932 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega))
      (_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales) := by
  have hbound := (_root_.GD.N0232.N0719.N0899.d021942 sizes hsizes 0 location scales).const_mul
    (_root_.GD.N0232.N0719.N0899.d021931 (sizes 0) beta)
  apply hbound.mono' (((_root_.GD.N0232.N0719.N0899.d021934 sizes beta).comp
    (_root_.GD.N0232.N0719.N0900.d009115 (n + 1) sizes)).aestronglyMeasurable)
  filter_upwards with omega
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0719.N0899.d021933 _ _ _)]
  exact _root_.GD.N0232.N0719.N0899.d021935 sizes hsizes hb0 hb1 _ 0

theorem d021945 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hsizes : ∀ i, 2 ≤ sizes i) {beta : ℝ}
    (hb0 : 0 < beta) (hb1 : beta < 1) (i : Fin (n + 1))
    (location : ℝ) (scales : Fin (n + 1) → ℝ) :
    (∫ omega, _root_.GD.N0232.N0719.N0899.d021932 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)
      ∂_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales) ≤
      _root_.GD.N0232.N0719.N0899.d021931 (sizes i) beta * Real.sqrt (scales i ^ 2 / (sizes i : ℝ)) := by
  calc
    _ ≤ ∫ omega, _root_.GD.N0232.N0719.N0899.d021931 (sizes i) beta *
        Real.sqrt ((_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega).meanVariance i)
        ∂_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales := by
      apply integral_mono
        (_root_.GD.N0232.N0719.N0899.d021944 sizes hsizes hb0 hb1 location scales)
        ((_root_.GD.N0232.N0719.N0899.d021942 sizes hsizes i location scales).const_mul _)
      intro omega
      exact _root_.GD.N0232.N0719.N0899.d021935 sizes hsizes hb0 hb1 _ i
    _ ≤ _ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (_root_.GD.N0232.N0719.N0899.d021943 sizes hsizes i location scales)
        (sub_nonneg.mpr (_root_.GD.N0232.N0719.N0875.d010344 (hsizes i) hb0 hb1))

theorem d021946 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hsizes : ∀ i, 2 ≤ sizes i) {beta : ℝ}
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    (∫ omega, _root_.GD.N0232.N0719.N0899.d021932 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)
      ∂_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales) *
      Real.sqrt (∑ i, (sizes i : ℝ) / scales i ^ 2) ≤
      Real.sqrt (∑ i, _root_.GD.N0232.N0719.N0899.d021931 (sizes i) beta ^ 2) := by
  have hv : ∀ i, 0 < scales i ^ 2 / (sizes i : ℝ) := by
    intro i
    have hsize := hsizes i
    have hi : 0 < (sizes i : ℝ) := by exact_mod_cast (by omega : 0 < sizes i)
    exact div_pos (sq_pos_of_pos (hscales i)) hi
  have hp := _root_.GD.N0049.N0306.d008253
    (fun i => _root_.GD.N0232.N0719.N0899.d021931 (sizes i) beta)
    (fun i => Real.sqrt (scales i ^ 2 / (sizes i : ℝ)))
    (∫ omega, _root_.GD.N0232.N0719.N0899.d021932 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)
      ∂_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales)
    (fun i => sub_nonneg.mpr (_root_.GD.N0232.N0719.N0875.d010344 (hsizes i) hb0 hb1))
    (fun i => Real.sqrt_pos.mpr (hv i))
    (integral_nonneg fun omega => _root_.GD.N0232.N0719.N0899.d021933 _ _ _)
    (fun i => _root_.GD.N0232.N0719.N0899.d021945 sizes hsizes hb0 hb1 i location scales)
  have hsum : (∑ i, ((Real.sqrt (scales i ^ 2 / (sizes i : ℝ))) ^ 2)⁻¹) =
      ∑ i, (sizes i : ℝ) / scales i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.sq_sqrt (hv i).le, inv_div]
  rwa [hsum] at hp

theorem d021947 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hsizes : ∀ i, 2 ≤ sizes i) {alpha : ℝ}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ (L U : _root_.GD.N0232.N0719.N0900.d009096 (n + 1) → ℝ) (C : ℝ),
      Measurable L ∧ Measurable U ∧ (∀ s, L s ≤ U s) ∧ 0 ≤ C ∧
      ∀ (location : ℝ) (scales : Fin (n + 1) → ℝ),
        (∀ i, 0 < scales i) →
        (_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
          {omega | L (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ≤ location ∧
            location ≤ U (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)} = ENNReal.ofReal (1 - alpha)) ∧
        Integrable (fun omega => U (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) -
          L (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega))
          (_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales) ∧
        ((∫ omega, U (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) -
          L (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)
          ∂_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales) /
          Real.sqrt ((∑ i, (sizes i : ℝ) / scales i ^ 2)⁻¹) ≤ C) := by
  let beta := _root_.GD.N0232.N0719.N1003.d010685 n alpha
  have hb := _root_.GD.N0232.N0719.N1003.d010687 n ha0 ha1
  refine ⟨_root_.GD.N0232.N0719.N1003.d010647 sizes beta, _root_.GD.N0232.N0719.N1003.d010648 sizes beta,
    Real.sqrt (∑ i, _root_.GD.N0232.N0719.N0899.d021931 (sizes i) beta ^ 2),
    _root_.GD.N0232.N0719.N1003.d010659 _ _, _root_.GD.N0232.N0719.N1003.d010660 _ _,
    _root_.GD.N0232.N0719.N1003.d010654 _ _, Real.sqrt_nonneg _, ?_⟩
  intro location scales hscales
  refine ⟨_root_.GD.N0232.N0719.N1003.d010690 sizes hsizes ha0 ha1 location scales hscales,
    _root_.GD.N0232.N0719.N0899.d021944 sizes hsizes hb.1 hb.2 location scales, ?_⟩
  simpa only [Real.sqrt_inv, div_inv_eq_mul, _root_.GD.N0232.N0719.N0899.d021932] using
    _root_.GD.N0232.N0719.N0899.d021946 sizes hsizes hb.1 hb.2 location scales hscales

#print axioms _root_.GD.N0232.N0719.N0899.d021933
#print axioms _root_.GD.N0232.N0719.N0899.d021934
#print axioms _root_.GD.N0232.N0719.N0899.d021935
#print axioms _root_.GD.N0232.N0719.N0899.d021936
#print axioms _root_.GD.N0232.N0719.N0899.d021937
#print axioms _root_.GD.N0232.N0719.N0899.d021938
#print axioms _root_.GD.N0232.N0719.N0899.d021939
#print axioms _root_.GD.N0232.N0719.N0899.d021940
#print axioms _root_.GD.N0232.N0719.N0899.d021947

#print axioms _root_.GD.N0232.N0719.N0899.d021941
#print axioms _root_.GD.N0232.N0719.N0899.d021942
#print axioms _root_.GD.N0232.N0719.N0899.d021943
#print axioms _root_.GD.N0232.N0719.N0899.d021944
#print axioms _root_.GD.N0232.N0719.N0899.d021945
#print axioms _root_.GD.N0232.N0719.N0899.d021946

end
end GD.N0232.N0719.N0899
