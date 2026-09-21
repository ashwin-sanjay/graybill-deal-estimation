import GD.Module0361
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic



























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter intervalIntegral

namespace GD.N0106.N0428.N0765.N1542
open _root_.GD.N0106.N0428.N0765.N1543
noncomputable section




def d005413 (a b : ℕ) (L : ℝ) : ℝ := ∫ v in (0 : ℝ)..L, v ^ a * (L - v) ^ b

theorem d005414 (a : ℕ) (L : ℝ) : _root_.GD.N0106.N0428.N0765.N1542.d005413 a 0 L = L ^ (a + 1) / (a + 1) := by
  unfold _root_.GD.N0106.N0428.N0765.N1542.d005413
  simp only [pow_zero, mul_one]
  rw [integral_pow, zero_pow (Nat.succ_ne_zero a), sub_zero]

theorem d005415 (a b : ℕ) (L : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1542.d005413 a (b + 1) L = ((b + 1 : ℝ) / (a + 1)) * _root_.GD.N0106.N0428.N0765.N1542.d005413 (a + 1) b L := by
  unfold _root_.GD.N0106.N0428.N0765.N1542.d005413
  have ha : ((a : ℝ) + 1) ≠ 0 := by positivity
  have hu : ∀ x ∈ uIcc (0 : ℝ) L,
      HasDerivAt (fun v : ℝ => (L - v) ^ (b + 1)) (-((b + 1 : ℝ) * (L - x) ^ b)) x := by
    intro x _
    have h := ((hasDerivAt_id' x).const_sub L).pow (b + 1)
    refine h.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hv : ∀ x ∈ uIcc (0 : ℝ) L,
      HasDerivAt (fun v : ℝ => v ^ (a + 1) / ((a : ℝ) + 1)) (x ^ a) x := by
    intro x _
    have h := (hasDerivAt_pow (a + 1) x).div_const ((a : ℝ) + 1)
    refine h.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  have i1 : IntervalIntegrable (fun x : ℝ => -((b + 1 : ℝ) * (L - x) ^ b)) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  have i2 : IntervalIntegrable (fun x : ℝ => x ^ a) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv i1 i2
  simp only [sub_self, sub_zero, zero_pow (Nat.succ_ne_zero _), zero_mul, mul_zero, zero_div,
    zero_sub] at key
  rw [show (∫ v in (0 : ℝ)..L, v ^ a * (L - v) ^ (b + 1)) =
      ∫ x in (0 : ℝ)..L, (L - x) ^ (b + 1) * x ^ a from
    intervalIntegral.integral_congr fun x _ => mul_comm _ _, key,
    ← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  field_simp

theorem d005416 (L : ℝ) : _root_.GD.N0106.N0428.N0765.N1542.d005413 4 4 L = L ^ 9 / 630 := by
  have h0 := _root_.GD.N0106.N0428.N0765.N1542.d005414 8 L
  have h1 := _root_.GD.N0106.N0428.N0765.N1542.d005415 7 0 L
  have h2 := _root_.GD.N0106.N0428.N0765.N1542.d005415 6 1 L
  have h3 := _root_.GD.N0106.N0428.N0765.N1542.d005415 5 2 L
  have h4 := _root_.GD.N0106.N0428.N0765.N1542.d005415 4 3 L
  norm_num at h0 h1 h2 h3 h4
  rw [h4, h3, h2, h1, h0]
  ring

theorem d005417 (L : ℝ) : _root_.GD.N0106.N0428.N0765.N1542.d005413 5 3 L = L ^ 9 / 504 := by
  have h0 := _root_.GD.N0106.N0428.N0765.N1542.d005414 8 L
  have h1 := _root_.GD.N0106.N0428.N0765.N1542.d005415 7 0 L
  have h2 := _root_.GD.N0106.N0428.N0765.N1542.d005415 6 1 L
  have h3 := _root_.GD.N0106.N0428.N0765.N1542.d005415 5 2 L
  norm_num at h0 h1 h2 h3
  rw [h3, h2, h1, h0]
  ring

theorem d005418 (L : ℝ) : _root_.GD.N0106.N0428.N0765.N1542.d005413 6 2 L = L ^ 9 / 252 := by
  have h0 := _root_.GD.N0106.N0428.N0765.N1542.d005414 8 L
  have h1 := _root_.GD.N0106.N0428.N0765.N1542.d005415 7 0 L
  have h2 := _root_.GD.N0106.N0428.N0765.N1542.d005415 6 1 L
  norm_num at h0 h1 h2
  rw [h2, h1, h0]
  ring



theorem d005419 (u : ℝ) :
    (∫ v in (0 : ℝ)..(1 - u), _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * ((v / (1 - u - v) - 1) ^ 2)) =
      ∫ v in (0 : ℝ)..(1 - u), _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * 1 := by
  have h1 : ∀ v : ℝ, _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * ((v / (1 - u - v) - 1) ^ 2) =
      Real.sqrt u * (v ^ 6 * (1 - u - v) ^ 2 - 2 * (v ^ 5 * (1 - u - v) ^ 3) +
        v ^ 4 * (1 - u - v) ^ 4) := by
    intro v
    unfold _root_.GD.N0106.N0428.N0765.N1543.d005383
    by_cases hw : 1 - u - v = 0
    · rw [hw]; simp
    · field_simp
      ring
  have h2 : ∀ v : ℝ, _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * 1 = Real.sqrt u * (v ^ 4 * (1 - u - v) ^ 4) := by
    intro v; unfold _root_.GD.N0106.N0428.N0765.N1543.d005383; ring
  simp_rw [h1, h2]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  congr 1
  have iA : IntervalIntegrable (fun v : ℝ => v ^ 6 * (1 - u - v) ^ 2) volume 0 (1 - u) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have iB : IntervalIntegrable (fun v : ℝ => 2 * (v ^ 5 * (1 - u - v) ^ 3)) volume 0 (1 - u) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have iC : IntervalIntegrable (fun v : ℝ => v ^ 4 * (1 - u - v) ^ 4) volume 0 (1 - u) :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_add (iA.sub iB) iC, intervalIntegral.integral_sub iA iB,
    intervalIntegral.integral_const_mul]
  change _root_.GD.N0106.N0428.N0765.N1542.d005413 6 2 (1 - u) - 2 * _root_.GD.N0106.N0428.N0765.N1542.d005413 5 3 (1 - u) + _root_.GD.N0106.N0428.N0765.N1542.d005413 4 4 (1 - u) = _root_.GD.N0106.N0428.N0765.N1542.d005413 4 4 (1 - u)
  rw [_root_.GD.N0106.N0428.N0765.N1542.d005418, _root_.GD.N0106.N0428.N0765.N1542.d005417, _root_.GD.N0106.N0428.N0765.N1542.d005416]
  ring




def d005420 : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 ≤ 1 ∧ 0 < p.2 ∧ p.2 ≤ 1 - p.1}

theorem d005421 : MeasurableSet _root_.GD.N0106.N0428.N0765.N1542.d005420 := by
  unfold _root_.GD.N0106.N0428.N0765.N1542.d005420
  simp only [Set.setOf_and]
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))))

theorem d005422 : _root_.GD.N0106.N0428.N0765.N1542.d005420 ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  rintro ⟨u, v⟩ ⟨h1, h2, h3, h4⟩
  exact ⟨⟨h1.le, h2⟩, ⟨h3.le, by linarith⟩⟩

theorem d005423 : volume _root_.GD.N0106.N0428.N0765.N1542.d005420 ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono _root_.GD.N0106.N0428.N0765.N1542.d005422)
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc]
  simp

theorem d005424 {u v : ℝ} : (v, u) ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420 ↔ (u, v) ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420 := by
  simp only [_root_.GD.N0106.N0428.N0765.N1542.d005420, Set.mem_setOf_eq]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨h3, by linarith, h1, by linarith⟩


theorem d005425 (F : ℝ → ℝ → ℝ) :
    (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u), F u v) =
      ∫ u, ∫ v, _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry F) (u, v) := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun u => ?_)
  show (Ioc (0 : ℝ) 1).indicator (fun u => ∫ v in (0 : ℝ)..(1 - u), F u v) u =
    ∫ v, _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry F) (u, v)
  by_cases hu : u ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem hu, intervalIntegral.integral_of_le (by linarith [hu.2]),
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun v => ?_)
    show (Ioc (0 : ℝ) (1 - u)).indicator (fun v => F u v) v = _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry F) (u, v)
    by_cases hv : v ∈ Ioc (0 : ℝ) (1 - u)
    · rw [indicator_of_mem hv, indicator_of_mem (show (u, v) ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420 from ⟨hu.1, hu.2, hv.1, hv.2⟩)]
      rfl
    · rw [indicator_of_notMem hv,
        indicator_of_notMem (show (u, v) ∉ _root_.GD.N0106.N0428.N0765.N1542.d005420 from fun h => hv ⟨h.2.2.1, h.2.2.2⟩)]
  · rw [indicator_of_notMem hu]
    have : ∀ v, _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry F) (u, v) = 0 := fun v =>
      indicator_of_notMem (show (u, v) ∉ _root_.GD.N0106.N0428.N0765.N1542.d005420 from fun h => hu ⟨h.1, h.2.1⟩) _
    simp only [this, MeasureTheory.integral_zero]


theorem d005426 (F : ℝ → ℝ → ℝ) (hF : Measurable (Function.uncurry F)) {C : ℝ}
    (hC : ∀ p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420, |Function.uncurry F p| ≤ C) :
    (∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..(1 - u), F u v) =
      ∫ v in (0 : ℝ)..1, ∫ u in (0 : ℝ)..(1 - v), F u v := by
  rw [_root_.GD.N0106.N0428.N0765.N1542.d005425, _root_.GD.N0106.N0428.N0765.N1542.d005425 (fun v u => F u v)]
  have hint : Integrable (Function.uncurry fun u v => _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry F) (u, v))
      (volume.prod volume) := by
    have : (Function.uncurry fun u v => _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry F) (u, v)) =
        _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry F) := by
      funext ⟨a, b⟩; rfl
    rw [this, ← Measure.volume_eq_prod, integrable_indicator_iff _root_.GD.N0106.N0428.N0765.N1542.d005421]
    refine Integrable.mono' (integrableOn_const (C := C) (hs := _root_.GD.N0106.N0428.N0765.N1542.d005423))
      hF.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem _root_.GD.N0106.N0428.N0765.N1542.d005421] with p hp
    rw [Real.norm_eq_abs]
    exact hC p hp
  rw [integral_integral_swap hint]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun v =>
    MeasureTheory.integral_congr_ae (Eventually.of_forall fun u => ?_))
  show _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry F) (u, v) =
    _root_.GD.N0106.N0428.N0765.N1542.d005420.indicator (Function.uncurry fun v u => F u v) (v, u)
  by_cases h : (u, v) ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420
  · rw [indicator_of_mem h, indicator_of_mem (_root_.GD.N0106.N0428.N0765.N1542.d005424.mpr h)]
    rfl
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (_root_.GD.N0106.N0428.N0765.N1542.d005424.mp h'))]




def d005427 : ℝ := ∫ s in (0 : ℝ)..1, Real.sqrt s * (1 - s) ^ 4

theorem d005428 : 0 < _root_.GD.N0106.N0428.N0765.N1542.d005427 :=
  intervalIntegral_pos_of_pos_on (Continuous.intervalIntegrable (by fun_prop) _ _)
    (fun s hs => mul_pos (Real.sqrt_pos.mpr hs.1) (pow_pos (by linarith [hs.2]) 4)) one_pos

theorem d005429 {M : ℝ} (hM : 0 ≤ M) :
    (∫ u in (0 : ℝ)..M, Real.sqrt u * (M - u) ^ 4) = M ^ ((11 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1542.d005427 := by
  rcases eq_or_lt_of_le hM with h0 | hMpos
  · subst h0
    simp [Real.zero_rpow (by norm_num : ((11 : ℝ) / 2) ≠ 0)]
  · have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (c := M)
      (fun u => Real.sqrt u * (M - u) ^ 4) hMpos.ne'
    rw [mul_zero, mul_one, smul_eq_mul] at h
    have h4 : M ^ (4 : ℝ) = M ^ 4 := by exact_mod_cast Real.rpow_natCast M 4
    have h2 : (∫ x in (0 : ℝ)..1, Real.sqrt (M * x) * (M - M * x) ^ 4) = M ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1542.d005427 := by
      unfold _root_.GD.N0106.N0428.N0765.N1542.d005427
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [Real.sqrt_mul hM, show M - M * x = M * (1 - x) by ring, mul_pow, Real.sqrt_eq_rpow M,
        show ((9 : ℝ) / 2) = 1 / 2 + 4 by norm_num, Real.rpow_add hMpos, h4]
      ring
    try simp only at h
    rw [h2] at h
    have h3 : (∫ x in (0 : ℝ)..M, Real.sqrt x * (M - x) ^ 4) = M * (M ^ ((9 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1542.d005427) := by
      rw [h, ← mul_assoc, mul_inv_cancel₀ hMpos.ne', one_mul]
    rw [h3, ← mul_assoc, show ((11 : ℝ) / 2) = 1 + 9 / 2 by norm_num, Real.rpow_add hMpos,
      Real.rpow_one]


theorem d005430 (n : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (∫ v in (0 : ℝ)..1, v ^ (n + 1) * (1 - v) ^ q) =
      ((n + 1 : ℝ) / (q + 1)) * ∫ v in (0 : ℝ)..1, v ^ n * (1 - v) ^ (q + 1) := by
  have hq1 : q + 1 ≠ 0 := by linarith
  have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => v ^ (n + 1)) ((n + 1 : ℝ) * x ^ n) x := by
    intro x _
    have h := hasDerivAt_pow (n + 1) x
    refine h.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hw : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => -((1 - v) ^ (q + 1) / (q + 1))) ((1 - x) ^ q) x := by
    intro x _
    have h1 : HasDerivAt (fun v : ℝ => 1 - v) (-1) x := (hasDerivAt_id' x).const_sub 1
    have h2 := ((h1.rpow_const (p := q + 1) (Or.inr (by linarith))).div_const (q + 1)).neg
    refine h2.congr_deriv ?_
    rw [show q + 1 - 1 = q by ring]
    field_simp
  have hcont : Continuous fun x : ℝ => (1 - x) ^ q :=
    (Real.continuous_rpow_const hq).comp (continuous_const.sub continuous_id)
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hw
    (Continuous.intervalIntegrable (by fun_prop) 0 1) (hcont.intervalIntegrable 0 1)
  simp only [one_pow, sub_self, Real.zero_rpow hq1, zero_div, neg_zero, mul_zero,
    zero_pow (Nat.succ_ne_zero _), zero_mul, sub_zero, zero_sub] at key
  rw [key, ← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  field_simp


def d005431 : ℝ := ∫ v in (0 : ℝ)..1, v ^ 4 * (1 - v) ^ ((11 : ℝ) / 2)

theorem d005432 : 0 < _root_.GD.N0106.N0428.N0765.N1542.d005431 := by
  unfold _root_.GD.N0106.N0428.N0765.N1542.d005431
  refine intervalIntegral_pos_of_pos_on ?_ (fun v hv => ?_) one_pos
  · exact (Continuous.intervalIntegrable (continuous_pow 4 |>.mul
      ((Real.continuous_rpow_const (by norm_num)).comp (continuous_const.sub continuous_id))) 0 1)
  · exact mul_pos (pow_pos hv.1 4) (Real.rpow_pos_of_pos (by linarith [hv.2]) _)

theorem d005433 : (∫ v in (0 : ℝ)..1, v ^ 5 * (1 - v) ^ ((9 : ℝ) / 2)) = 10 / 11 * _root_.GD.N0106.N0428.N0765.N1542.d005431 := by
  have h := _root_.GD.N0106.N0428.N0765.N1542.d005430 4 (q := (9 : ℝ) / 2) (by norm_num)
  norm_num at h
  rw [h]
  rfl

theorem d005434 : (∫ v in (0 : ℝ)..1, v ^ 6 * (1 - v) ^ ((7 : ℝ) / 2)) = 40 / 33 * _root_.GD.N0106.N0428.N0765.N1542.d005431 := by
  have h := _root_.GD.N0106.N0428.N0765.N1542.d005430 5 (q := (7 : ℝ) / 2) (by norm_num)
  norm_num at h
  rw [h, _root_.GD.N0106.N0428.N0765.N1542.d005433]
  ring



theorem d005435 : Measurable fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005383
  exact ((Real.continuous_sqrt.measurable.comp measurable_fst).mul (measurable_snd.pow_const 4)).mul
    (((measurable_const.sub measurable_fst).sub measurable_snd).pow_const 4)

theorem d005436 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005383
  have : 0 ≤ 1 - p.1 - p.2 := by linarith
  positivity

theorem d005437 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420) : _root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005383
  have hw0 : 0 ≤ 1 - p.1 - p.2 := by linarith
  have hw1 : 1 - p.1 - p.2 ≤ 1 := by linarith
  have hs : Real.sqrt p.1 ≤ 1 := Real.sqrt_le_one.mpr h2
  have hv : p.2 ^ 4 ≤ 1 := pow_le_one₀ h3.le (by linarith)
  have hw : (1 - p.1 - p.2) ^ 4 ≤ 1 := pow_le_one₀ hw0 hw1
  calc Real.sqrt p.1 * p.2 ^ 4 * (1 - p.1 - p.2) ^ 4 ≤ 1 * 1 * 1 := by
        gcongr
    _ = 1 := by norm_num


theorem d005438 {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∫ u in (0 : ℝ)..(1 - v), _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v)) = _root_.GD.N0106.N0428.N0765.N1542.d005427 * (v ^ 4 * (1 - v) ^ ((11 : ℝ) / 2)) := by
  have h : ∀ u, _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) = v ^ 4 * (Real.sqrt u * ((1 - v) - u) ^ 4) := by
    intro u; unfold _root_.GD.N0106.N0428.N0765.N1543.d005383; ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, _root_.GD.N0106.N0428.N0765.N1542.d005429 (by linarith)]
  ring


theorem d005439 : _root_.GD.N0106.N0428.N0765.N1543.d005384 = _root_.GD.N0106.N0428.N0765.N1542.d005427 * _root_.GD.N0106.N0428.N0765.N1542.d005431 := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005384 _root_.GD.N0106.N0428.N0765.N1542.d005431
  rw [_root_.GD.N0106.N0428.N0765.N1542.d005426 (fun u v => _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v)) _root_.GD.N0106.N0428.N0765.N1542.d005435 (C := 1)
    (fun p hp => by
      show |_root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2)| ≤ 1
      rw [abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1542.d005436 hp)]; exact _root_.GD.N0106.N0428.N0765.N1542.d005437 hp)]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v hv => ?_
  rw [uIcc_of_le zero_le_one] at hv
  exact _root_.GD.N0106.N0428.N0765.N1542.d005438 hv.1 hv.2

theorem d005440 : 0 < _root_.GD.N0106.N0428.N0765.N1543.d005384 := by
  rw [_root_.GD.N0106.N0428.N0765.N1542.d005439]; exact mul_pos _root_.GD.N0106.N0428.N0765.N1542.d005428 _root_.GD.N0106.N0428.N0765.N1542.d005432

theorem d005441 : _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun _ _ _ => 1) = 1 := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005385
  rw [div_eq_one_iff_eq _root_.GD.N0106.N0428.N0765.N1542.d005440.ne']
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005384
  simp only [mul_one]


theorem d005442 : _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun _ v w => (v / w - 1) ^ 2) = 1 := by
  conv_rhs => rw [← _root_.GD.N0106.N0428.N0765.N1542.d005441]
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005385
  congr 1
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only
  exact _root_.GD.N0106.N0428.N0765.N1542.d005419 u


theorem d005443 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1542.d005420) :
    |_root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) * (11 / 8 * p.2 / (1 - p.2) - 1) ^ 2| ≤ 6 := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  set u := p.1
  set v := p.2
  set w := 1 - u - v with hw
  have hw0 : 0 ≤ w := by rw [hw]; linarith
  have h1v : 0 < 1 - v := by linarith
  have hwv : w ≤ 1 - v := by rw [hw]; linarith
  have hx0 : 0 ≤ v / (1 - v) := div_nonneg h3.le h1v.le
  have hwx : w * (v / (1 - v)) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one h1v]
    nlinarith
  have hw1 : w ≤ 1 := by linarith
  have hA : w ^ 4 * (v / (1 - v)) ^ 2 ≤ 1 := by
    have : w ^ 4 * (v / (1 - v)) ^ 2 = w ^ 2 * (w * (v / (1 - v))) ^ 2 := by ring
    rw [this]
    have hw2 : w ^ 2 ≤ 1 := pow_le_one₀ hw0 hw1
    have := pow_le_one₀ (mul_nonneg hw0 hx0) hwx (n := 2)
    nlinarith [mul_nonneg (sq_nonneg w) (sq_nonneg (w * (v / (1 - v))))]
  have hB : w ^ 4 ≤ 1 := pow_le_one₀ hw0 hw1
  have hsu : Real.sqrt u * v ^ 4 ≤ 1 := by
    have hs : Real.sqrt u ≤ 1 := Real.sqrt_le_one.mpr h2
    have hv : v ^ 4 ≤ 1 := pow_le_one₀ h3.le (by linarith)
    nlinarith [Real.sqrt_nonneg u, pow_nonneg h3.le 4]
  have hsu0 : 0 ≤ Real.sqrt u * v ^ 4 := mul_nonneg (Real.sqrt_nonneg u) (pow_nonneg h3.le 4)
  have hsq : (11 / 8 * v / (1 - v) - 1) ^ 2 ≤ 2 * (121 / 64) * (v / (1 - v)) ^ 2 + 2 := by
    have : 11 / 8 * v / (1 - v) = 11 / 8 * (v / (1 - v)) := by ring
    rw [this]
    nlinarith [sq_nonneg (11 / 8 * (v / (1 - v)) + 1)]
  have hnn : 0 ≤ _root_.GD.N0106.N0428.N0765.N1543.d005383 u v w * (11 / 8 * v / (1 - v) - 1) ^ 2 := by
    unfold _root_.GD.N0106.N0428.N0765.N1543.d005383
    exact mul_nonneg (mul_nonneg hsu0 (pow_nonneg hw0 4)) (sq_nonneg _)
  rw [abs_of_nonneg hnn]
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005383
  calc Real.sqrt u * v ^ 4 * w ^ 4 * (11 / 8 * v / (1 - v) - 1) ^ 2
      ≤ Real.sqrt u * v ^ 4 * w ^ 4 * (2 * (121 / 64) * (v / (1 - v)) ^ 2 + 2) :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg hsu0 (pow_nonneg hw0 4))
    _ = Real.sqrt u * v ^ 4 * (2 * (121 / 64) * (w ^ 4 * (v / (1 - v)) ^ 2) + 2 * w ^ 4) := by ring
    _ ≤ 1 * (2 * (121 / 64) * 1 + 2 * 1) := by gcongr
    _ ≤ 6 := by norm_num

theorem d005444 :
    Measurable fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) * (11 / 8 * p.2 / (1 - p.2) - 1) ^ 2 :=
  _root_.GD.N0106.N0428.N0765.N1542.d005435.mul ((((measurable_const.mul measurable_snd).div
    (measurable_const.sub measurable_snd)).sub measurable_const).pow_const 2)


theorem d005445 {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∫ u in (0 : ℝ)..(1 - v), _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * (11 / 8 * v / (1 - v) - 1) ^ 2) =
      _root_.GD.N0106.N0428.N0765.N1542.d005427 * (121 / 64 * (v ^ 6 * (1 - v) ^ ((7 : ℝ) / 2)) - 11 / 4 * (v ^ 5 * (1 - v) ^ ((9 : ℝ) / 2)) +
        v ^ 4 * (1 - v) ^ ((11 : ℝ) / 2)) := by
  have h : ∀ u, _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * (11 / 8 * v / (1 - v) - 1) ^ 2 =
      (v ^ 4 * (11 / 8 * v / (1 - v) - 1) ^ 2) * (Real.sqrt u * ((1 - v) - u) ^ 4) := by
    intro u; unfold _root_.GD.N0106.N0428.N0765.N1543.d005383; ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, _root_.GD.N0106.N0428.N0765.N1542.d005429 (by linarith)]
  rcases eq_or_lt_of_le hv1 with h1 | h1
  · subst h1
    simp [Real.zero_rpow (by norm_num : ((11 : ℝ) / 2) ≠ 0),
      Real.zero_rpow (by norm_num : ((9 : ℝ) / 2) ≠ 0), Real.zero_rpow (by norm_num : ((7 : ℝ) / 2) ≠ 0)]
  · have hpos : 0 < 1 - v := by linarith
    have e9 : (1 - v) ^ ((9 : ℝ) / 2) = (1 - v) * (1 - v) ^ ((7 : ℝ) / 2) := by
      rw [show ((9 : ℝ) / 2) = 1 + 7 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one]
    have e11 : (1 - v) ^ ((11 : ℝ) / 2) = (1 - v) ^ 2 * (1 - v) ^ ((7 : ℝ) / 2) := by
      rw [show ((11 : ℝ) / 2) = 2 + 7 / 2 by norm_num, Real.rpow_add hpos,
        show ((1 - v) ^ (2 : ℝ)) = (1 - v) ^ 2 by exact_mod_cast Real.rpow_natCast (1 - v) 2]
    rw [e9, e11]
    field_simp
    ring


theorem d005446 : _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w => (11 / 8 * v / (u + w) - 1) ^ 2) = 19 / 24 := by
  unfold _root_.GD.N0106.N0428.N0765.N1543.d005385
  rw [div_eq_iff _root_.GD.N0106.N0428.N0765.N1542.d005440.ne', _root_.GD.N0106.N0428.N0765.N1542.d005439]
  have hre : ∀ u v : ℝ, _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * (11 / 8 * v / (u + (1 - u - v)) - 1) ^ 2 =
      _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * (11 / 8 * v / (1 - v) - 1) ^ 2 := by
    intro u v; rw [show u + (1 - u - v) = 1 - v by ring]
  simp_rw [hre]
  rw [_root_.GD.N0106.N0428.N0765.N1542.d005426 (fun u v => _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * (11 / 8 * v / (1 - v) - 1) ^ 2)
    _root_.GD.N0106.N0428.N0765.N1542.d005444 (C := 6) (fun p hp => by
      show |_root_.GD.N0106.N0428.N0765.N1543.d005383 p.1 p.2 (1 - p.1 - p.2) * (11 / 8 * p.2 / (1 - p.2) - 1) ^ 2| ≤ 6
      exact _root_.GD.N0106.N0428.N0765.N1542.d005443 hp)]
  have hin : (∫ v in (0 : ℝ)..1, ∫ u in (0 : ℝ)..(1 - v),
      _root_.GD.N0106.N0428.N0765.N1543.d005383 u v (1 - u - v) * (11 / 8 * v / (1 - v) - 1) ^ 2) =
      ∫ v in (0 : ℝ)..1, _root_.GD.N0106.N0428.N0765.N1542.d005427 * (121 / 64 * (v ^ 6 * (1 - v) ^ ((7 : ℝ) / 2)) -
        11 / 4 * (v ^ 5 * (1 - v) ^ ((9 : ℝ) / 2)) + v ^ 4 * (1 - v) ^ ((11 : ℝ) / 2)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le zero_le_one] at hv
    exact _root_.GD.N0106.N0428.N0765.N1542.d005445 hv.1 hv.2
  have c7 : Continuous fun v : ℝ => v ^ 6 * (1 - v) ^ ((7 : ℝ) / 2) :=
    (continuous_pow 6).mul ((Real.continuous_rpow_const (by norm_num)).comp (continuous_const.sub continuous_id))
  have c9 : Continuous fun v : ℝ => v ^ 5 * (1 - v) ^ ((9 : ℝ) / 2) :=
    (continuous_pow 5).mul ((Real.continuous_rpow_const (by norm_num)).comp (continuous_const.sub continuous_id))
  have c11 : Continuous fun v : ℝ => v ^ 4 * (1 - v) ^ ((11 : ℝ) / 2) :=
    (continuous_pow 4).mul ((Real.continuous_rpow_const (by norm_num)).comp (continuous_const.sub continuous_id))
  rw [hin, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((c7.intervalIntegrable 0 1 |>.const_mul _).sub
      (c9.intervalIntegrable 0 1 |>.const_mul _)) (c11.intervalIntegrable 0 1),
    intervalIntegral.integral_sub (c7.intervalIntegrable 0 1 |>.const_mul _)
      (c9.intervalIntegrable 0 1 |>.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, _root_.GD.N0106.N0428.N0765.N1542.d005434, _root_.GD.N0106.N0428.N0765.N1542.d005433]
  change _root_.GD.N0106.N0428.N0765.N1542.d005427 * (121 / 64 * (40 / 33 * _root_.GD.N0106.N0428.N0765.N1542.d005431) - 11 / 4 * (10 / 11 * _root_.GD.N0106.N0428.N0765.N1542.d005431) + _root_.GD.N0106.N0428.N0765.N1542.d005431) = 19 / 24 * (_root_.GD.N0106.N0428.N0765.N1542.d005427 * _root_.GD.N0106.N0428.N0765.N1542.d005431)
  ring


theorem d005447 :
    1 / 11 * (_root_.GD.N0106.N0428.N0765.N1543.d005385 (fun _ v w => (v / w - 1) ^ 2) -
      _root_.GD.N0106.N0428.N0765.N1543.d005385 (fun u v w => (11 / 8 * v / (u + w) - 1) ^ 2)) = 5 / 264 := by
  rw [_root_.GD.N0106.N0428.N0765.N1542.d005442, _root_.GD.N0106.N0428.N0765.N1542.d005446]
  norm_num

end

end GD.N0106.N0428.N0765.N1542
