import GD.Module0362
import GD.Module1306













set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0106.N0428.N0765.N1661
noncomputable section
open _root_.GD.N0235 _root_.GD.N0106.N0428.N0765.N1543 _root_.GD.N0106.N0428.N0765.N1542
open _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1521 _root_.GD.N0106.N0428.N0765.N1632


theorem d021354 {p : ℝ × ℝ}
    (hp : p ∈ (Ioo (0 : ℝ) 1) ×ˢ Ioo 0 1) :
    _root_.GD.N0106.N0428.N0765.N1521.d020856 p =
      (2 * _root_.GD.N0106.N0428.N0765.N1632.d021345 * p.1 * (1 - p.1 ^ 2)) *
        _root_.GD.N0106.N0428.N0765.N1543.d005383 (p.1 ^ 2) ((1 - p.1 ^ 2) * p.2)
          ((1 - p.1 ^ 2) * (1 - p.2)) := by
  unfold _root_.GD.N0106.N0428.N0765.N1521.d020856 _root_.GD.N0106.N0428.N0765.N1632.d021345 _root_.GD.N0106.N0428.N0765.N1543.d005383
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hp.1.1]
  ring


theorem d021355 (f : (Fin 3 → ℝ) → ℝ)
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420,
      |_root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) * f ![p.1, p.2, 1 - p.1 - p.2]| ≤ C) :
    Integrable f _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  apply (_root_.GD.N0106.N0428.N0765.N1521.d020860 f hf).2
  have hvol : volume ((Ioo (0 : ℝ) 1) ×ˢ (Ioo (0 : ℝ) 1)) ≠ ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
    norm_num
  have hm : Measurable (fun p => _root_.GD.N0106.N0428.N0765.N1521.d020856 p * f (_root_.GD.N0106.N0428.N0765.N1521.d020853 p)) := by
    apply Measurable.mul ?_ (hf.comp _root_.GD.N0106.N0428.N0765.N1521.d020854)
    unfold _root_.GD.N0106.N0428.N0765.N1521.d020856
    fun_prop
  have hconst : IntegrableOn (fun _ : ℝ × ℝ => (2 * _root_.GD.N0106.N0428.N0765.N1632.d021345 * C : ℝ))
      ((Ioo (0 : ℝ) 1) ×ˢ (Ioo (0 : ℝ) 1)) := by
    exact integrableOn_const (C := 2 * _root_.GD.N0106.N0428.N0765.N1632.d021345 * C)
      (hC := by finiteness) (hs := hvol)
  refine Integrable.mono' hconst hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  have hu0 : 0 < p.1 ^ 2 := sq_pos_of_pos hp.1.1
  have hu1 : p.1 ^ 2 < 1 := by
    nlinarith [mul_pos hp.1.1 (sub_pos.mpr hp.1.2)]
  have hL0 : 0 < 1 - p.1 ^ 2 := sub_pos.mpr hu1
  have hv0 : 0 < (1 - p.1 ^ 2) * p.2 := mul_pos hL0 hp.2.1
  have hv1 : (1 - p.1 ^ 2) * p.2 ≤ 1 - p.1 ^ 2 := by
    nlinarith [mul_nonneg hL0.le (sub_nonneg.mpr hp.2.2.le)]
  have hT : (p.1 ^ 2, (1 - p.1 ^ 2) * p.2) ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420 :=
    ⟨hu0, hu1.le, hv0, hv1⟩
  have hb := hC _ hT
  have hw : 1 - p.1 ^ 2 - (1 - p.1 ^ 2) * p.2 =
      (1 - p.1 ^ 2) * (1 - p.2) := by ring
  simp only [Prod.fst, Prod.snd, hw] at hb
  have hc0 : 0 ≤ 2 * _root_.GD.N0106.N0428.N0765.N1632.d021345 * p.1 * (1 - p.1 ^ 2) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) _root_.GD.N0106.N0428.N0765.N1632.d021346.le)
        hp.1.1.le)
      hL0.le
  have hc1 : 2 * _root_.GD.N0106.N0428.N0765.N1632.d021345 * p.1 * (1 - p.1 ^ 2) ≤
      2 * _root_.GD.N0106.N0428.N0765.N1632.d021345 := by
    have hprod : p.1 * (1 - p.1 ^ 2) ≤ 1 := by
      have hL1 : 1 - p.1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg p.1]
      calc
        p.1 * (1 - p.1 ^ 2) ≤ 1 * 1 :=
          mul_le_mul hp.1.2.le hL1 hL0.le zero_le_one
        _ = 1 := by ring
    have h := mul_le_mul_of_nonneg_left hprod
      (show 0 ≤ 2 * _root_.GD.N0106.N0428.N0765.N1632.d021345 by linarith [_root_.GD.N0106.N0428.N0765.N1632.d021346])
    nlinarith
  rw [Real.norm_eq_abs, _root_.GD.N0106.N0428.N0765.N1661.d021354 hp, mul_assoc, abs_mul,
    abs_of_nonneg hc0]
  change (2 * _root_.GD.N0106.N0428.N0765.N1632.d021345 * p.1 * (1 - p.1 ^ 2)) *
    |_root_.GD.N0106.N0428.N0765.N1543.d005383 (p.1 ^ 2) ((1 - p.1 ^ 2) * p.2) ((1 - p.1 ^ 2) * (1 - p.2)) *
      f ![p.1 ^ 2, (1 - p.1 ^ 2) * p.2, (1 - p.1 ^ 2) * (1 - p.2)]| ≤
    2 * _root_.GD.N0106.N0428.N0765.N1632.d021345 * C
  exact (mul_le_mul_of_nonneg_left hb hc0).trans
    (mul_le_mul_of_nonneg_right hc1 hC0)


theorem d021356 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420) :
    |_root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) * (p.2 / (1 - p.1 - p.2) - 1) ^ 2| ≤ 4 := by
  obtain ⟨hu0, hu1, hv0, hv1⟩ := hp
  have hvle : p.2 ≤ 1 := by linarith
  have hw0 : 0 ≤ 1 - p.1 - p.2 := by linarith
  have hw1 : 1 - p.1 - p.2 ≤ 1 := by linarith
  have hpoly : _root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) *
      (p.2 / (1 - p.1 - p.2) - 1) ^ 2 =
      Real.sqrt p.1 * p.2 ^ 4 * (1 - p.1 - p.2) ^ 2 *
        (p.2 - (1 - p.1 - p.2)) ^ 2 := by
    unfold _root_.GD.N0106.N0428.N0765.N1543.d005383
    by_cases hw : 1 - p.1 - p.2 = 0
    · rw [hw]
      simp
    · field_simp [hw]
  rw [hpoly, abs_of_nonneg (by positivity)]
  have hs : Real.sqrt p.1 ≤ 1 := Real.sqrt_le_one.mpr hu1
  have hv4 : p.2 ^ 4 ≤ 1 := pow_le_one₀ hv0.le hvle
  have hw2 : (1 - p.1 - p.2) ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
  have hv2 : p.2 ^ 2 ≤ 1 := pow_le_one₀ hv0.le hvle
  have hdiff : (p.2 - (1 - p.1 - p.2)) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg hv0.le hw0]
  calc
    Real.sqrt p.1 * p.2 ^ 4 * (1 - p.1 - p.2) ^ 2 *
        (p.2 - (1 - p.1 - p.2)) ^ 2 ≤ 1 * 1 * 1 * 4 := by
      gcongr
    _ = 4 := by norm_num

theorem d021357 :
    Integrable (fun p : Fin 3 → ℝ => (p 1 / p 2 - 1) ^ 2) _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  apply _root_.GD.N0106.N0428.N0765.N1661.d021355 _ (by fun_prop) (C := 4) (by norm_num)
  intro p hp
  simpa [Matrix.vecHead, Matrix.vecTail]
    using _root_.GD.N0106.N0428.N0765.N1661.d021356 hp

theorem d021358 :
    Integrable (fun p : Fin 3 → ℝ => (11 / 8 * p 1 / (1 - p 1) - 1) ^ 2)
      _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  apply _root_.GD.N0106.N0428.N0765.N1661.d021355 _ (by fun_prop) (C := 6) (by norm_num)
  intro p hp
  simpa only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_zero]
    using _root_.GD.N0106.N0428.N0765.N1542.d005443 hp

theorem d021359 :
    (∫ p : Fin 3 → ℝ, (p 1 / p 2 - 1) ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) = 1 := by
  rw [← _root_.GD.N0106.N0428.N0765.N1632.d021349 _ (by fun_prop) _root_.GD.N0106.N0428.N0765.N1661.d021357]
  simpa [Matrix.vecHead, Matrix.vecTail]
    using _root_.GD.N0106.N0428.N0765.N1542.d005442

theorem d021360 :
    (∫ p : Fin 3 → ℝ, (11 / 8 * p 1 / (1 - p 1) - 1) ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) =
      19 / 24 := by
  rw [← _root_.GD.N0106.N0428.N0765.N1632.d021349 _ (by fun_prop) _root_.GD.N0106.N0428.N0765.N1661.d021358]
  have h : _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun _ v _ => (11 / 8 * v / (1 - v) - 1) ^ 2) =
      _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w => (11 / 8 * v / (u + w) - 1) ^ 2) := by
    unfold _root_.GD.N0106.N0428.N0765.N1543.d005385
    simp_rw [show ∀ u v : ℝ, u + (1 - u - v) = 1 - v by intros; ring]
  simpa only [Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_zero]
    using h.trans _root_.GD.N0106.N0428.N0765.N1542.d005446


theorem d021361 :
    Integrable (fun p : Fin 3 → ℝ => (p 1 / p 2) ^ 2) _root_.GD.N0106.N0428.N0765.N1529.d020798 := by
  letI : IsProbabilityMeasure _root_.GD.N0106.N0428.N0765.N1529.d020798 :=
    _root_.GD.N0235.d004251 (by norm_num) (by norm_num) (by norm_num)
  refine Integrable.mono'
    ((_root_.GD.N0106.N0428.N0765.N1661.d021357.const_mul 2).add (integrable_const 2))
    (((measurable_pi_apply 1).div (measurable_pi_apply 2)).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (p 1 / p 2) ^ 2 ≤ 2 * (p 1 / p 2 - 1) ^ 2 + 2
  nlinarith [sq_nonneg (p 1 / p 2 - 2)]


theorem d021362 :
    _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun _ v w => (v / w) ^ 2) = 5 / 2 := by
  have hinner (u : ℝ) :
      (∫ v in (0 : ℝ)..(1 - u), _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * (v / (1 - u - v)) ^ 2) =
      5 / 2 * ∫ v in (0 : ℝ)..(1 - u), _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * 1 := by
    have hraw (v : ℝ) : _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * (v / (1 - u - v)) ^ 2 =
        Real.sqrt u * (v ^ 6 * (1 - u - v) ^ 2) := by
      unfold _root_.GD.N0106.N0428.N0765.N1543.d005383
      by_cases hw : 1 - u - v = 0
      · rw [hw]
        simp
      · field_simp [hw]
    have hmass (v : ℝ) : _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * 1 =
        Real.sqrt u * (v ^ 4 * (1 - u - v) ^ 4) := by
      unfold _root_.GD.N0106.N0428.N0765.N1543.d005383
      ring
    simp_rw [hraw, hmass]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    change Real.sqrt u * _root_.GD.N0106.N0428.N0765.N1542.d005413 6 2 (1 - u) = 5 / 2 * (Real.sqrt u * _root_.GD.N0106.N0428.N0765.N1542.d005413 4 4 (1 - u))
    rw [_root_.GD.N0106.N0428.N0765.N1542.d005418, _root_.GD.N0106.N0428.N0765.N1542.d005416]
    ring
  have h : _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun _ v w => (v / w) ^ 2) =
      5 / 2 * _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun _ _ _ => 1) := by
    unfold _root_.GD.N0106.N0428.N0765.N1543.d005385
    simp_rw [hinner]
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [h, _root_.GD.N0106.N0428.N0765.N1542.d005441]
  norm_num

theorem d021363 :
    (∫ p : Fin 3 → ℝ, (p 1 / p 2) ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) = 5 / 2 := by
  rw [← _root_.GD.N0106.N0428.N0765.N1632.d021349 _ (by fun_prop) _root_.GD.N0106.N0428.N0765.N1661.d021361]
  simpa [Matrix.vecHead, Matrix.vecTail]
    using _root_.GD.N0106.N0428.N0765.N1661.d021362


theorem d021364 :
    (1 / 11 : ℝ) *
      (∫ p : Fin 3 → ℝ, (p 1 / p 2 - 1) ^ 2 -
        (11 / 8 * p 1 / (1 - p 1) - 1) ^ 2 ∂_root_.GD.N0106.N0428.N0765.N1529.d020798) = 5 / 264 := by
  rw [integral_sub _root_.GD.N0106.N0428.N0765.N1661.d021357 _root_.GD.N0106.N0428.N0765.N1661.d021358,
    _root_.GD.N0106.N0428.N0765.N1661.d021359, _root_.GD.N0106.N0428.N0765.N1661.d021360]
  norm_num

end
end GD.N0106.N0428.N0765.N1661

#print axioms _root_.GD.N0106.N0428.N0765.N1661.d021355
#print axioms _root_.GD.N0106.N0428.N0765.N1661.d021357
#print axioms _root_.GD.N0106.N0428.N0765.N1661.d021358
#print axioms _root_.GD.N0106.N0428.N0765.N1661.d021359
#print axioms _root_.GD.N0106.N0428.N0765.N1661.d021360
#print axioms _root_.GD.N0106.N0428.N0765.N1661.d021361
#print axioms _root_.GD.N0106.N0428.N0765.N1661.d021363
#print axioms _root_.GD.N0106.N0428.N0765.N1661.d021364
