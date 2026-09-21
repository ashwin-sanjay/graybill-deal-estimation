import GD.Module1492




set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0102.N0426
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0910 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0021 _root_.GD.N0072
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0102.N0421

variable {k : ℕ}

def d023359 (q : Fin k → ℝ) (i j : Fin k) : ℝ :=
  q i / q j + q j / q i - 2

theorem d023360 (q : Fin k → ℝ) (hq : ∀ i, 0 < q i) (i j : Fin k) :
    0 ≤ _root_.GD.N0102.N0426.d023359 q i j := by
  have heq : _root_.GD.N0102.N0426.d023359 q i j = (q i - q j) ^ 2 / (q i * q j) := by
    unfold _root_.GD.N0102.N0426.d023359
    field_simp [(hq i).ne', (hq j).ne']
    ring
  rw [heq]
  exact div_nonneg (sq_nonneg _) (mul_pos (hq i) (hq j)).le

theorem d023361 (q : Fin k → ℝ) :
    (∑ i, ∑ j, _root_.GD.N0102.N0426.d023359 q i j) = 2 * _root_.GD.N0021.d023316 q - 2 * (k : ℝ) ^ 2 := by
  have hflip : (∑ i, ∑ j, q j / q i) = _root_.GD.N0021.d023316 q := by
    rw [Finset.sum_comm]
    rfl
  have hc : (∑ _i : Fin k, ∑ _j : Fin k, (2 : ℝ)) = 2 * (k : ℝ) ^ 2 := by
    simp
    ring
  simp_rw [_root_.GD.N0102.N0426.d023359, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hflip, hc]
  change _root_.GD.N0021.d023316 q + _root_.GD.N0021.d023316 q - _ = _
  ring

theorem d023362 (w : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (i j : Fin k) (hij : i ≠ j) :
    w i * w j ≤ 1 / 4 := by
  classical
  have hp : w i + w j ≤ 1 := by
    calc
      w i + w j = ∑ l ∈ ({i, j} : Finset (Fin k)), w l :=
        (Finset.sum_pair hij).symm
      _ ≤ ∑ l, w l := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun l _ _ => hw l)
      _ = 1 := hsum
  have hp0 : 0 ≤ w i + w j := add_nonneg (hw i) (hw j)
  have hp2 : (w i + w j) ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (w i - w j)]

theorem d023363 (w q : Fin k → ℝ) (hsum : ∑ i, w i = 1) :
    (∑ i, ∑ j, w i * w j * _root_.GD.N0102.N0426.d023359 q i j) =
      2 * ((∑ i, w i * q i) * (∑ j, w j / q j)) - 2 := by
  have hf : (∑ i, ∑ j, w i * w j * (q i / q j)) =
      (∑ i, w i * q i) * (∑ j, w j / q j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hb : (∑ i, ∑ j, w i * w j * (q j / q i)) =
      (∑ i, w i * q i) * (∑ j, w j / q j) := by
    rw [← hf, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hm : (∑ i, ∑ j, w i * w j) = 1 := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, hsum, mul_one]
  have hc : (∑ i, ∑ j, w i * w j * 2) = 2 := by
    simp_rw [← Finset.sum_mul]
    rw [hm]
    norm_num
  simp_rw [_root_.GD.N0102.N0426.d023359, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  rw [hf, hb, hc]
  ring

def d023364 (q : Fin k → ℝ) : ℝ :=
  1 + (_root_.GD.N0021.d023316 q - (k : ℝ) ^ 2) / 4

theorem d023365 (q : Fin k → ℝ) (hq : ∀ i, 0 < q i) :
    1 ≤ _root_.GD.N0102.N0426.d023364 q := by
  have h : 0 ≤ ∑ i, ∑ j, _root_.GD.N0102.N0426.d023359 q i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => _root_.GD.N0102.N0426.d023360 q hq i j
  rw [_root_.GD.N0102.N0426.d023361] at h
  unfold _root_.GD.N0102.N0426.d023364
  linarith



theorem d023366 (w q : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hq : ∀ i, 0 < q i) :
    (∑ i, w i * q i) * (∑ j, w j / q j) ≤ _root_.GD.N0102.N0426.d023364 q := by
  have h : (∑ i, ∑ j, w i * w j * _root_.GD.N0102.N0426.d023359 q i j) ≤
      ∑ i, ∑ j, _root_.GD.N0102.N0426.d023359 q i j / 4 := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · subst j
      norm_num [_root_.GD.N0102.N0426.d023359, (hq i).ne']
    · have hmul := mul_le_mul_of_nonneg_right
        (_root_.GD.N0102.N0426.d023362 w hw hsum i j hij) (_root_.GD.N0102.N0426.d023360 q hq i j)
      linarith
  rw [_root_.GD.N0102.N0426.d023363 w q hsum] at h
  simp_rw [← Finset.sum_div] at h
  rw [_root_.GD.N0102.N0426.d023361] at h
  unfold _root_.GD.N0102.N0426.d023364
  linarith

theorem d023367 (hk : 0 < k) (v q : Fin k → ℝ)
    (hv : ∀ i, 0 < v i) (hq : ∀ i, 0 < q i) :
    _root_.GD.N0072.d007621 v (_root_.GD.N0021.d023313 (fun i => v i * q i)) ≤
      _root_.GD.N0102.N0426.d023364 q * (∑ i, (v i)⁻¹)⁻¹ := by
  have hP : 0 < ∑ i, (v i)⁻¹ := Finset.sum_pos (fun i _ => inv_pos.mpr (hv i))
    (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hk))
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hP).mpr
  rw [_root_.GD.N0021.d023318 hk v q hv hq]
  exact _root_.GD.N0102.N0426.d023366 _ q
    (fun i => _root_.GD.N0232.N0719.N0900.d009132 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), fun i => v i * q i)) i)
    (_root_.GD.N0232.N0719.N0900.d009131 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), fun i => v i * q i))) hq

theorem d023368 (sizes : Fin k → ℕ)
    (hn : ∀ i, 4 ≤ sizes i) : IsProbabilityMeasure (_root_.GD.N0021.d023347 sizes) := by
  have hs (i : Fin k) : 0 < _root_.GD.N0021.d023346 sizes i :=
    lt_trans zero_lt_one (_root_.GD.N0021.d023348 sizes hn i)
  letI (i : Fin k) : IsProbabilityMeasure
      (gammaMeasure (_root_.GD.N0021.d023346 sizes i) (_root_.GD.N0021.d023346 sizes i)) :=
    isProbabilityMeasure_gammaMeasure (hs i) (hs i)
  unfold _root_.GD.N0021.d023347
  infer_instance

theorem d023369 (sizes : Fin k → ℕ) (hn : ∀ i, 4 ≤ sizes i) :
    Integrable (_root_.GD.N0102.N0426.d023364 (k := k)) (_root_.GD.N0021.d023347 sizes) := by
  letI := _root_.GD.N0102.N0426.d023368 sizes hn
  exact (integrable_const 1).add
    (((_root_.GD.N0021.d023349 sizes hn).sub (integrable_const ((k : ℝ) ^ 2))).div_const 4)

def d023370 (sizes : Fin k → ℕ) : ℝ :=
  1 + ((k : ℝ) - 1) / 2 * ∑ i, 1 / ((sizes i : ℝ) - 3)

theorem d023371 (sizes : Fin k → ℕ) (hn : ∀ i, 4 ≤ sizes i) :
    (∫ q, _root_.GD.N0102.N0426.d023364 q ∂_root_.GD.N0021.d023347 sizes) = _root_.GD.N0102.N0426.d023370 sizes := by
  letI := _root_.GD.N0102.N0426.d023368 sizes hn
  change (∫ q, (1 : ℝ) + (_root_.GD.N0021.d023316 q - (k : ℝ) ^ 2) / 4
    ∂_root_.GD.N0021.d023347 sizes) = _
  have hsplit := integral_add (integrable_const (μ := _root_.GD.N0021.d023347 sizes) (1 : ℝ))
    (((_root_.GD.N0021.d023349 sizes hn).sub (integrable_const ((k : ℝ) ^ 2))).div_const 4)
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit,
    integral_div, integral_sub (_root_.GD.N0021.d023349 sizes hn) (integrable_const _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  change 1 + (_root_.GD.N0021.d023350 sizes - (k : ℝ) ^ 2) / 4 = _
  rw [_root_.GD.N0102.N0421.d023357 sizes hn]
  have hr : (∑ i, ((sizes i : ℝ) - 1) / ((sizes i : ℝ) - 3)) =
      (k : ℝ) + 2 * ∑ i, 1 / ((sizes i : ℝ) - 3) := by
    calc
      _ = ∑ i, (1 + 2 * (1 / ((sizes i : ℝ) - 3))) := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : (4 : ℝ) ≤ (sizes i : ℝ) := by exact_mod_cast hn i
        have hd : (sizes i : ℝ) - 3 ≠ 0 := by linarith
        rw [show (sizes i : ℝ) - 1 = ((sizes i : ℝ) - 3) + 2 by ring,
          add_div, div_self hd]
        ring
      _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hr]
  unfold _root_.GD.N0102.N0426.d023370
  ring

theorem d023372 (sizes : Fin k → ℕ) (hk : 0 < k) (hn : ∀ i, 4 ≤ sizes i) :
    0 ≤ _root_.GD.N0102.N0426.d023370 sizes := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hs : 0 ≤ ∑ i, 1 / ((sizes i : ℝ) - 3) := by
    apply Finset.sum_nonneg
    intro i _
    have hi : (4 : ℝ) ≤ (sizes i : ℝ) := by exact_mod_cast hn i
    exact div_nonneg zero_le_one (by linarith)
  unfold _root_.GD.N0102.N0426.d023370
  exact add_nonneg zero_le_one (mul_nonneg (by positivity) hs)



theorem d023373 (sizes : Fin k → ℕ) (hk : 0 < k)
    (hn : ∀ i, 4 ≤ sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≤
      ENNReal.ofReal (_root_.GD.N0102.N0426.d023370 sizes * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) := by
  have hn2 (i : Fin k) : 2 ≤ sizes i := le_trans (by norm_num) (hn i)
  have hv (i : Fin k) : 0 < θ.scale i ^ 2 / (sizes i : ℝ) :=
    div_pos (sq_pos_of_pos (θ.scale_pos i)) (Nat.cast_pos.mpr (by have := hn i; omega))
  have hs (i : Fin k) : 0 < _root_.GD.N0021.d023346 sizes i :=
    lt_trans zero_lt_one (_root_.GD.N0021.d023348 sizes hn i)
  have hpos := _root_.GD.N0232.N0719.N0910.d010287 hs hs
  have hmp := _root_.GD.N0021.d023352 sizes hn θ
  rw [_root_.GD.N0021.d023315, _root_.GD.N0072.d023297 sizes hn2 _
    _root_.GD.N0021.d023314 (fun t => _root_.GD.N0232.N0719.N0900.d009131 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)))]
  rw [← hmp.map_eq, lintegral_map]
  · have ho : (∑ i, (θ.scale i ^ 2 / (sizes i : ℝ))⁻¹)⁻¹ = _root_.GD.N0232.N0719.N0963.d012141 k sizes θ := by
      simp only [_root_.GD.N0232.N0719.N0963.d012141, _root_.GD.N0232.N0719.N0838.d012097,
        _root_.GD.N0232.N0719.N0838.d012096, inv_div]
    calc
      (∫⁻ q, ENNReal.ofReal (_root_.GD.N0072.d007621 (fun i => θ.scale i ^ 2 / (sizes i : ℝ))
          (_root_.GD.N0021.d023313 (fun i => (θ.scale i ^ 2 / (sizes i : ℝ)) * q i))) ∂_root_.GD.N0021.d023347 sizes) ≤
          ∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0426.d023364 q * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ)
            ∂_root_.GD.N0021.d023347 sizes := by
        apply lintegral_mono_ae
        filter_upwards [hpos] with q hq
        apply ENNReal.ofReal_le_ofReal
        simpa only [ho] using _root_.GD.N0102.N0426.d023367 hk _ q hv hq
      _ = ENNReal.ofReal (_root_.GD.N0102.N0426.d023370 sizes * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((_root_.GD.N0102.N0426.d023369 sizes hn).mul_const _)]
        · rw [integral_mul_const, _root_.GD.N0102.N0426.d023371 sizes hn]
        · filter_upwards [hpos] with q hq
          exact mul_nonneg (zero_le_one.trans (_root_.GD.N0102.N0426.d023365 q hq))
            (_root_.GD.N0232.N0719.N0963.d012142 k sizes θ)
  · exact ENNReal.measurable_ofReal.comp (by unfold _root_.GD.N0072.d007621; fun_prop)
  · exact hmp.measurable



theorem d023374 (sizes : Fin k → ℕ) (hk : 0 < k)
    (hn : ∀ i, 4 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≤
      ENNReal.ofReal (1 + ((k : ℝ) - 1) / 2 * ∑ i, 1 / ((sizes i : ℝ) - 3)) := by
  apply iSup_le
  intro θ
  apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes hk (fun i => by have := hn i; omega)
    _ (_root_.GD.N0102.N0426.d023372 sizes hk hn) θ _).mpr
  exact _root_.GD.N0102.N0426.d023373 sizes hk hn θ

end
end GD.N0102.N0426

#print axioms _root_.GD.N0102.N0426.d023366
#print axioms _root_.GD.N0102.N0426.d023371
#print axioms _root_.GD.N0102.N0426.d023373
#print axioms _root_.GD.N0102.N0426.d023374
