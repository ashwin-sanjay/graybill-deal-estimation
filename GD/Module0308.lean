import GD.Module0307
import GD.Module0209
import Mathlib.MeasureTheory.Function.Holder











open MeasureTheory Set
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0720.N1316

open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1379

noncomputable section

abbrev d004440 (k : ℕ) := ℝ × (Fin (k + 1) → Ioo (0 : ℝ) 1)

variable {k : ℕ}

def d004441 (q : _root_.GD.N0232.N0720.N1316.d004440 k) (x : _root_.GD.N0232.N0720.N1341.d004414 k) : ℝ :=
  ∑ i, x i ^ 2 / (q.2 i).1

def d004442 (q : _root_.GD.N0232.N0720.N1316.d004440 k) (x : _root_.GD.N0232.N0720.N1341.d004414 k) : ℝ :=
  ∑ i, x i * q.1 / (q.2 i).1

def d004443 (q : _root_.GD.N0232.N0720.N1316.d004440 k) : ℝ :=
  (∏ i, Real.sqrt (2 * Real.pi * (q.2 i).1))⁻¹

def d004444 (q : _root_.GD.N0232.N0720.N1316.d004440 k) : ℝ :=
  _root_.GD.N0232.N0720.N1316.d004443 q * Real.exp (∑ i, -(q.1 ^ 2) / (2 * (q.2 i).1))

def d004445 (q : _root_.GD.N0232.N0720.N1316.d004440 k) (x : _root_.GD.N0232.N0720.N1341.d004414 k) : ℝ :=
  _root_.GD.N0232.N0720.N1316.d004443 q * Real.exp (∑ i, -((x i - q.1) ^ 2) / (2 * (q.2 i).1))

theorem d004446 (q : _root_.GD.N0232.N0720.N1316.d004440 k) : 0 < _root_.GD.N0232.N0720.N1316.d004443 q := by
  apply inv_pos.mpr
  exact Finset.prod_pos (fun i _ ↦ Real.sqrt_pos.mpr (by
    have h := (q.2 i).2.1
    positivity))

theorem d004447 (q : _root_.GD.N0232.N0720.N1316.d004440 k) : 0 < _root_.GD.N0232.N0720.N1316.d004444 q :=
  mul_pos (_root_.GD.N0232.N0720.N1316.d004446 q) (Real.exp_pos _)

theorem d004448 (q : _root_.GD.N0232.N0720.N1316.d004440 k) (x : _root_.GD.N0232.N0720.N1341.d004414 k) :
    ‖x‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1316.d004441 q x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  apply (le_div_iff₀ (q.2 i).2.1).mpr
  exact mul_le_of_le_one_right (sq_nonneg _) (q.2 i).2.2.le

@[fun_prop]
theorem d004449 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1316.d004440 k × _root_.GD.N0232.N0720.N1341.d004414 k ↦ _root_.GD.N0232.N0720.N1316.d004441 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1316.d004441
  apply continuous_finsetSum
  intro i _
  exact Continuous.div (by fun_prop) (by fun_prop) (fun p ↦ (p.1.2 i).2.1.ne')

@[fun_prop]
theorem d004450 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1316.d004440 k × _root_.GD.N0232.N0720.N1341.d004414 k ↦ _root_.GD.N0232.N0720.N1316.d004442 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1316.d004442
  apply continuous_finsetSum
  intro i _
  exact Continuous.div (by fun_prop) (by fun_prop) (fun p ↦ (p.1.2 i).2.1.ne')

@[fun_prop]
theorem d004451 : Continuous (_root_.GD.N0232.N0720.N1316.d004443 (k := k)) := by
  unfold _root_.GD.N0232.N0720.N1316.d004443
  apply Continuous.inv₀ (by fun_prop)
  intro q
  exact (Finset.prod_pos (fun i _ ↦ Real.sqrt_pos.mpr (by
    have h := (q.2 i).2.1
    positivity))).ne'

@[fun_prop]
theorem d004452 : Continuous (_root_.GD.N0232.N0720.N1316.d004444 (k := k)) := by
  have hexponent : Continuous (fun q : _root_.GD.N0232.N0720.N1316.d004440 k ↦
      ∑ i, -(q.1 ^ 2) / (2 * (q.2 i).1)) := by
    apply continuous_finsetSum
    intro i _
    exact Continuous.div (by fun_prop) (by fun_prop)
      (fun q ↦ mul_ne_zero (by norm_num) (q.2 i).2.1.ne')
  exact _root_.GD.N0232.N0720.N1316.d004451.mul (Real.continuous_exp.comp hexponent)

theorem d004453 (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) (u : (_root_.GD.N0232.N0720.N1341.d004415 k)) : 1 ≤ _root_.GD.N0232.N0720.N1316.d004441 q u := by
  have hu : ‖(u : (_root_.GD.N0232.N0720.N1341.d004414 k))‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  simpa only [hu, one_pow] using _root_.GD.N0232.N0720.N1316.d004448 q u

theorem d004454 (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) (u : (_root_.GD.N0232.N0720.N1341.d004415 k)) : 0 < _root_.GD.N0232.N0720.N1316.d004441 q u :=
  lt_of_lt_of_le zero_lt_one (_root_.GD.N0232.N0720.N1316.d004453 q u)

def d004455 (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ) where
  toFun u := _root_.GD.N0232.N0720.N1316.d004442 q u
  continuous_toFun := _root_.GD.N0232.N0720.N1316.d004450.comp (continuous_const.prodMk continuous_subtype_val)

@[fun_prop]
theorem d004456 (n : ℕ) :
    Continuous (fun p : (_root_.GD.N0232.N0720.N1316.d004440 k) × (_root_.GD.N0232.N0720.N1341.d004415 k) ↦
      _root_.GD.N0232.N0720.N1377.d002852 n (_root_.GD.N0232.N0720.N1316.d004441 p.1 p.2) (_root_.GD.N0232.N0720.N1316.d004442 p.1 p.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hparam : Continuous (fun q : (_root_.GD.N0232.N0720.N1316.d004440 k) × (_root_.GD.N0232.N0720.N1341.d004415 k) ↦
      (_root_.GD.N0232.N0720.N1316.d004441 q.1 q.2, _root_.GD.N0232.N0720.N1316.d004442 q.1 q.2)) :=
    (_root_.GD.N0232.N0720.N1316.d004449.prodMk _root_.GD.N0232.N0720.N1316.d004450).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  exact (_root_.GD.N0232.N0720.N1379.d002889 n
    (p := (_root_.GD.N0232.N0720.N1316.d004441 p.1 p.2, _root_.GD.N0232.N0720.N1316.d004442 p.1 p.2))
    (_root_.GD.N0232.N0720.N1316.d004454 p.1 p.2)).continuousAt.comp
      (f := fun q : (_root_.GD.N0232.N0720.N1316.d004440 k) × (_root_.GD.N0232.N0720.N1341.d004415 k) ↦ (_root_.GD.N0232.N0720.N1316.d004441 q.1 q.2, _root_.GD.N0232.N0720.N1316.d004442 q.1 q.2))
      hparam.continuousAt


def d004457 (n : ℕ) (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ) where
  toFun u := _root_.GD.N0232.N0720.N1377.d002852 n (_root_.GD.N0232.N0720.N1316.d004441 q u) (_root_.GD.N0232.N0720.N1316.d004442 q u)
  continuous_toFun := by
    have hsection : Continuous (fun u : (_root_.GD.N0232.N0720.N1341.d004415 k) ↦ (q, u)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using! (_root_.GD.N0232.N0720.N1316.d004456 n).comp hsection

@[fun_prop]
theorem d004458 (n : ℕ) :
    Continuous (_root_.GD.N0232.N0720.N1316.d004457 (k := k) n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact _root_.GD.N0232.N0720.N1316.d004456 n

theorem d004459 (q : _root_.GD.N0232.N0720.N1316.d004440 k) (u : _root_.GD.N0232.N0720.N1341.d004415 k) (r : ℝ) :
    _root_.GD.N0232.N0720.N1316.d004445 q (r • (u : _root_.GD.N0232.N0720.N1341.d004414 k)) =
      _root_.GD.N0232.N0720.N1316.d004444 q * Real.exp
        (-_root_.GD.N0232.N0720.N1316.d004441 q u / 2 * r ^ 2 + _root_.GD.N0232.N0720.N1316.d004442 q u * r) := by
  have he : (∑ i, -((r * (u : _root_.GD.N0232.N0720.N1341.d004414 k) i - q.1) ^ 2) /
      (2 * (q.2 i).1)) =
      (∑ i, -(q.1 ^ 2) / (2 * (q.2 i).1)) +
        (-_root_.GD.N0232.N0720.N1316.d004441 q u / 2 * r ^ 2 + _root_.GD.N0232.N0720.N1316.d004442 q u * r) := by
    unfold _root_.GD.N0232.N0720.N1316.d004441 _root_.GD.N0232.N0720.N1316.d004442
    calc
      _ = ∑ i, (-(q.1 ^ 2) / (2 * (q.2 i).1) +
          (-( (u : _root_.GD.N0232.N0720.N1341.d004414 k) i ^ 2 / (q.2 i).1) / 2 * r ^ 2 +
            ((u : _root_.GD.N0232.N0720.N1341.d004414 k) i * q.1 / (q.2 i).1) * r)) := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [(q.2 i).2.1.ne']
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp only [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_neg_distrib]
  simp only [_root_.GD.N0232.N0720.N1316.d004445, _root_.GD.N0232.N0720.N1316.d004444, PiLp.smul_apply, smul_eq_mul,
    he, Real.exp_add]
  ring


theorem d004460 (n : ℕ) {A : ℝ} (hA : 0 < A) (b : ℝ) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ _root_.GD.N0232.N0720.N1377.d002851 n A b r.1)
      (Measure.volumeIoiPow k) := by
  rw [_root_.GD.N0232.N0720.N1341.d004425]
  have heq : (fun r : ℝ ↦ r ^ k * _root_.GD.N0232.N0720.N1377.d002851 n A b r) =
      _root_.GD.N0232.N0720.N1377.d002851 (n + k) A b := by
    funext r
    simp only [_root_.GD.N0232.N0720.N1377.d002851, pow_add]
    ring
  rw [heq]
  exact _root_.GD.N0232.N0720.N1377.d002860 (n + k) hA b

theorem d004461 (n : ℕ) (A b : ℝ) :
    (∫ r : Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1377.d002851 n A b r.1 ∂Measure.volumeIoiPow k) =
      _root_.GD.N0232.N0720.N1377.d002852 (n + k) A b := by
  rw [_root_.GD.N0232.N0720.N1341.d004424]
  unfold _root_.GD.N0232.N0720.N1377.d002852
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  simp only [_root_.GD.N0232.N0720.N1377.d002851, pow_add]
  ring

theorem d004462 (n : ℕ) (M : ℝ) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ _root_.GD.N0232.N0720.N1377.d002857 n 1 M r.1)
      (Measure.volumeIoiPow k) := by
  rw [_root_.GD.N0232.N0720.N1341.d004425]
  have heq : (fun r : ℝ ↦ r ^ k * _root_.GD.N0232.N0720.N1377.d002857 n 1 M r) =
      _root_.GD.N0232.N0720.N1377.d002857 (n + k) 1 M := by
    funext r
    simp only [_root_.GD.N0232.N0720.N1377.d002857, pow_add]
    ring
  rw [heq]
  exact _root_.GD.N0232.N0720.N1377.d002858 (n + k) (show (0 : ℝ) < 1 by norm_num) M



theorem d004463 (n : ℕ) (q : (_root_.GD.N0232.N0720.N1316.d004440 k))
    (f : (_root_.GD.N0232.N0720.N1341.d004415 k) → ℝ) (hf : Integrable f (_root_.GD.N0232.N0720.N1341.d004416 k)) :
    Integrable (fun p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ) ↦
      f p.1 * _root_.GD.N0232.N0720.N1377.d002851 n (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1)
      ((_root_.GD.N0232.N0720.N1341.d004416 k).prod (Measure.volumeIoiPow k)) := by
  have hcont : Continuous (fun p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ) ↦
      _root_.GD.N0232.N0720.N1377.d002851 n (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1) := by
    have ha : Continuous (fun p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ) ↦ _root_.GD.N0232.N0720.N1316.d004441 q p.1) :=
      _root_.GD.N0232.N0720.N1316.d004449.comp
        (continuous_const.prodMk (continuous_subtype_val.comp continuous_fst))
    have hb : Continuous (fun p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ) ↦ _root_.GD.N0232.N0720.N1316.d004442 q p.1) :=
      _root_.GD.N0232.N0720.N1316.d004450.comp
        (continuous_const.prodMk (continuous_subtype_val.comp continuous_fst))
    unfold _root_.GD.N0232.N0720.N1377.d002851
    fun_prop
  apply (hf.norm.mul_prod (_root_.GD.N0232.N0720.N1316.d004462 n ‖_root_.GD.N0232.N0720.N1316.d004455 q‖)).mono'
    (hf.aestronglyMeasurable.comp_fst.mul hcont.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun p ↦ by
    change ‖f p.1 * _root_.GD.N0232.N0720.N1377.d002851 n (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply _root_.GD.N0232.N0720.N1379.d002886 n zero_lt_one
      (_root_.GD.N0232.N0720.N1316.d004453 q p.1) _ p.2.2.le
    exact (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, _root_.GD.N0232.N0720.N1316.d004455] using!
        (_root_.GD.N0232.N0720.N1316.d004455 q).norm_coe_le_norm p.1))

theorem d004464 (n : ℕ) (q : (_root_.GD.N0232.N0720.N1316.d004440 k))
    (f : (_root_.GD.N0232.N0720.N1341.d004415 k) → ℝ) (hf : Integrable f (_root_.GD.N0232.N0720.N1341.d004416 k)) :
    (∫ p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ),
      f p.1 * _root_.GD.N0232.N0720.N1377.d002851 n (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1
        ∂(_root_.GD.N0232.N0720.N1341.d004416 k).prod (Measure.volumeIoiPow k)) =
      ∫ u : (_root_.GD.N0232.N0720.N1341.d004415 k), f u * _root_.GD.N0232.N0720.N1316.d004457 (n + k) q u ∂(_root_.GD.N0232.N0720.N1341.d004416 k) := by
  rw [integral_prod _ (_root_.GD.N0232.N0720.N1316.d004463 n q f hf)]
  simp_rw [integral_const_mul, _root_.GD.N0232.N0720.N1316.d004461]
  rfl

def d004465 (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) (p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ)) : ℝ :=
  _root_.GD.N0232.N0720.N1316.d004444 q *
    (h p.1 ^ 2 * _root_.GD.N0232.N0720.N1377.d002851 2 (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1 -
      2 * q.1 * (h p.1 * _root_.GD.N0232.N0720.N1377.d002851 1 (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1) +
      q.1 ^ 2 * _root_.GD.N0232.N0720.N1377.d002851 0 (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1)

theorem d004466 (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) (p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ)) :
    (_root_.GD.N0232.N0720.N1341.d004418 h (p.2.1 • (p.1 : (_root_.GD.N0232.N0720.N1341.d004414 k))) - q.1) ^ 2 *
        _root_.GD.N0232.N0720.N1316.d004445 q (p.2.1 • (p.1 : (_root_.GD.N0232.N0720.N1341.d004414 k))) = _root_.GD.N0232.N0720.N1316.d004465 q h p := by
  rw [_root_.GD.N0232.N0720.N1341.d004421, _root_.GD.N0232.N0720.N1316.d004459]
  simp only [_root_.GD.N0232.N0720.N1316.d004465, _root_.GD.N0232.N0720.N1377.d002851, pow_zero, pow_one]
  ring

theorem d004467 (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) :
    Integrable (_root_.GD.N0232.N0720.N1316.d004465 q h) ((_root_.GD.N0232.N0720.N1341.d004416 k).prod (Measure.volumeIoiPow k)) := by
  have h2 := _root_.GD.N0232.N0720.N1316.d004463 2 q (fun u ↦ h u ^ 2)
    (Lp.memLp h).integrable_sq
  have h1 := _root_.GD.N0232.N0720.N1316.d004463 1 q h
    ((Lp.memLp h).integrable (by norm_num))
  have h0 := _root_.GD.N0232.N0720.N1316.d004463 0 q (fun _ ↦ 1)
    (integrable_const 1)
  simpa only [_root_.GD.N0232.N0720.N1316.d004465, one_mul] using!
    ((h2.sub (h1.const_mul (2 * q.1))).add (h0.const_mul (q.1 ^ 2))).const_mul
      (_root_.GD.N0232.N0720.N1316.d004444 q)


theorem d004468 (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) :
    Integrable (fun x ↦ (_root_.GD.N0232.N0720.N1341.d004418 h x - q.1) ^ 2 * _root_.GD.N0232.N0720.N1316.d004445 q x) := by
  rw [_root_.GD.N0232.N0720.N1341.d004423]
  exact (_root_.GD.N0232.N0720.N1316.d004467 q h).congr
    (Filter.Eventually.of_forall (fun p ↦ (_root_.GD.N0232.N0720.N1316.d004466 q h p).symm))

def d004469 (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) : ℝ :=
  ∫ x, (_root_.GD.N0232.N0720.N1341.d004418 h x - q.1) ^ 2 * _root_.GD.N0232.N0720.N1316.d004445 q x



theorem d004470 (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) :
    _root_.GD.N0232.N0720.N1316.d004469 q h = _root_.GD.N0232.N0720.N1316.d004444 q *
      ((∫ u : (_root_.GD.N0232.N0720.N1341.d004415 k), h u ^ 2 * _root_.GD.N0232.N0720.N1316.d004457 (k + 2) q u ∂(_root_.GD.N0232.N0720.N1341.d004416 k)) -
        2 * q.1 * (∫ u : (_root_.GD.N0232.N0720.N1341.d004415 k), h u * _root_.GD.N0232.N0720.N1316.d004457 (k + 1) q u ∂(_root_.GD.N0232.N0720.N1341.d004416 k)) +
        q.1 ^ 2 * (∫ u : (_root_.GD.N0232.N0720.N1341.d004415 k), _root_.GD.N0232.N0720.N1316.d004457 k q u ∂(_root_.GD.N0232.N0720.N1341.d004416 k))) := by
  have h2 := _root_.GD.N0232.N0720.N1316.d004463 2 q (fun u ↦ h u ^ 2)
    (Lp.memLp h).integrable_sq
  have h1 := _root_.GD.N0232.N0720.N1316.d004463 1 q h
    ((Lp.memLp h).integrable (by norm_num))
  have h0 := _root_.GD.N0232.N0720.N1316.d004463 0 q (fun _ ↦ 1)
    (integrable_const 1)
  have hz : (∫ p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ),
      _root_.GD.N0232.N0720.N1377.d002851 0 (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1
        ∂(_root_.GD.N0232.N0720.N1341.d004416 k).prod (Measure.volumeIoiPow k)) =
      ∫ u : (_root_.GD.N0232.N0720.N1341.d004415 k), _root_.GD.N0232.N0720.N1316.d004457 k q u ∂(_root_.GD.N0232.N0720.N1341.d004416 k) := by
    simpa only [one_mul, Nat.zero_add] using
      _root_.GD.N0232.N0720.N1316.d004464 0 q (fun _ ↦ 1) (integrable_const 1)
  unfold _root_.GD.N0232.N0720.N1316.d004469
  rw [_root_.GD.N0232.N0720.N1341.d004422]
  simp_rw [_root_.GD.N0232.N0720.N1316.d004466]
  unfold _root_.GD.N0232.N0720.N1316.d004465
  rw [integral_const_mul, integral_add
    (f := fun p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ) ↦
      h p.1 ^ 2 * _root_.GD.N0232.N0720.N1377.d002851 2 (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1 -
        2 * q.1 * (h p.1 * _root_.GD.N0232.N0720.N1377.d002851 1 (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1))
    (g := fun p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ) ↦
      q.1 ^ 2 * _root_.GD.N0232.N0720.N1377.d002851 0 (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1)
    (h2.sub (h1.const_mul _))
    (by simpa only [one_mul] using h0.const_mul (q.1 ^ 2)),
    integral_sub
      (f := fun p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ) ↦
        h p.1 ^ 2 * _root_.GD.N0232.N0720.N1377.d002851 2 (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1)
      (g := fun p : (_root_.GD.N0232.N0720.N1341.d004415 k) × Ioi (0 : ℝ) ↦
        2 * q.1 * (h p.1 * _root_.GD.N0232.N0720.N1377.d002851 1 (_root_.GD.N0232.N0720.N1316.d004441 q p.1) (_root_.GD.N0232.N0720.N1316.d004442 q p.1) p.2.1))
      h2 (h1.const_mul _), integral_const_mul, integral_const_mul,
    _root_.GD.N0232.N0720.N1316.d004464 2 q _ (Lp.memLp h).integrable_sq,
    _root_.GD.N0232.N0720.N1316.d004464 1 q _ ((Lp.memLp h).integrable (by norm_num)), hz]
  simp only [Nat.add_comm]





def d004471 (a : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) : (_root_.GD.N0232.N0720.N1341.d004417 k) :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL (_root_.GD.N0232.N0720.N1341.d004416 k) ∞ 2 2
    (ContinuousMap.toLp ∞ (_root_.GD.N0232.N0720.N1341.d004416 k) ℝ a) h

theorem d004472 (a : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) :
    _root_.GD.N0232.N0720.N1316.d004471 a h =ᵐ[(_root_.GD.N0232.N0720.N1341.d004416 k)] fun u ↦ a u * h u := by
  change (ContinuousLinearMap.mul ℝ ℝ).holder 2
    (ContinuousMap.toLp ∞ (_root_.GD.N0232.N0720.N1341.d004416 k) ℝ a) h =ᵐ[(_root_.GD.N0232.N0720.N1341.d004416 k)] _
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
      (r := 2) (ContinuousMap.toLp ∞ (_root_.GD.N0232.N0720.N1341.d004416 k) ℝ a) h,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℝ) (_root_.GD.N0232.N0720.N1341.d004416 k) a] with u hu ha
  simpa only [ContinuousLinearMap.mul_apply', ha] using hu

@[fun_prop]
theorem d004473 :
    Continuous (fun p : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ) × (_root_.GD.N0232.N0720.N1341.d004417 k) ↦ _root_.GD.N0232.N0720.N1316.d004471 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1316.d004471
  fun_prop

def d004474 (a : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) : ℝ :=
  inner ℝ (_root_.GD.N0232.N0720.N1316.d004471 a h) h

def d004475 (a : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) : ℝ :=
  inner ℝ (ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 k) ℝ a) h

theorem d004476 (a : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) :
    _root_.GD.N0232.N0720.N1316.d004474 a h = ∫ u : (_root_.GD.N0232.N0720.N1341.d004415 k), h u ^ 2 * a u ∂(_root_.GD.N0232.N0720.N1341.d004416 k) := by
  rw [_root_.GD.N0232.N0720.N1316.d004474, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1316.d004472 a h] with u hu
  simp [hu, pow_two, mul_assoc, mul_comm]

theorem d004477 (a : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) :
    _root_.GD.N0232.N0720.N1316.d004475 a h = ∫ u : (_root_.GD.N0232.N0720.N1341.d004415 k), h u * a u ∂(_root_.GD.N0232.N0720.N1341.d004416 k) := by
  rw [_root_.GD.N0232.N0720.N1316.d004475, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (_root_.GD.N0232.N0720.N1341.d004416 k) a] with u hu
  simp only [Real.inner_apply]
  rw [hu, mul_comm]

@[fun_prop]
theorem d004478 :
    Continuous (fun p : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ) × (_root_.GD.N0232.N0720.N1341.d004417 k) ↦ _root_.GD.N0232.N0720.N1316.d004474 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1316.d004474
  exact _root_.GD.N0232.N0720.N1316.d004473.inner continuous_snd

@[fun_prop]
theorem d004479 :
    Continuous (fun p : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ) × (_root_.GD.N0232.N0720.N1341.d004417 k) ↦ _root_.GD.N0232.N0720.N1316.d004475 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1316.d004475
  fun_prop

theorem d004480 :
    Continuous (fun a : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ) ↦ ∫ u, a u ∂(_root_.GD.N0232.N0720.N1341.d004416 k)) := by
  have heq : (fun a : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ) ↦ ∫ u, a u ∂(_root_.GD.N0232.N0720.N1341.d004416 k)) =
      fun a : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ) ↦
        ∫ u, (ContinuousMap.toLp 1 (_root_.GD.N0232.N0720.N1341.d004416 k) ℝ a) u ∂(_root_.GD.N0232.N0720.N1341.d004416 k) := by
    funext a
    exact (integral_congr_ae
      (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) (_root_.GD.N0232.N0720.N1341.d004416 k) a)).symm
  rw [heq]
  exact MeasureTheory.continuous_integral.comp
    (ContinuousMap.toLp 1 (_root_.GD.N0232.N0720.N1341.d004416 k) ℝ).continuous

theorem d004481 (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) :
    _root_.GD.N0232.N0720.N1316.d004469 q h = _root_.GD.N0232.N0720.N1316.d004444 q *
      (_root_.GD.N0232.N0720.N1316.d004474 (_root_.GD.N0232.N0720.N1316.d004457 (k + 2) q) h -
        2 * q.1 * _root_.GD.N0232.N0720.N1316.d004475 (_root_.GD.N0232.N0720.N1316.d004457 (k + 1) q) h +
        q.1 ^ 2 * (∫ u, _root_.GD.N0232.N0720.N1316.d004457 k q u ∂(_root_.GD.N0232.N0720.N1341.d004416 k))) := by
  rw [_root_.GD.N0232.N0720.N1316.d004470, _root_.GD.N0232.N0720.N1316.d004476, _root_.GD.N0232.N0720.N1316.d004477]

set_option maxHeartbeats 800000 in


theorem d004482 :
    Continuous (fun p : (_root_.GD.N0232.N0720.N1316.d004440 k) × (_root_.GD.N0232.N0720.N1341.d004417 k) ↦ _root_.GD.N0232.N0720.N1316.d004469 p.1 p.2) := by
  simp_rw [_root_.GD.N0232.N0720.N1316.d004481]
  have hcoef (n : ℕ) : Continuous (fun p : (_root_.GD.N0232.N0720.N1316.d004440 k) × (_root_.GD.N0232.N0720.N1341.d004417 k) ↦
      _root_.GD.N0232.N0720.N1316.d004457 n p.1) := by
    simpa only [Function.comp_def] using!
      (_root_.GD.N0232.N0720.N1316.d004458 n).comp
        (continuous_fst : Continuous (fun p : (_root_.GD.N0232.N0720.N1316.d004440 k) × (_root_.GD.N0232.N0720.N1341.d004417 k) ↦ p.1))
  have hquad : Continuous (fun p : (_root_.GD.N0232.N0720.N1316.d004440 k) × (_root_.GD.N0232.N0720.N1341.d004417 k) ↦
      _root_.GD.N0232.N0720.N1316.d004474 (_root_.GD.N0232.N0720.N1316.d004457 (k + 2) p.1) p.2) := by
    have harg : Continuous (fun p : (_root_.GD.N0232.N0720.N1316.d004440 k) × (_root_.GD.N0232.N0720.N1341.d004417 k) ↦
        (_root_.GD.N0232.N0720.N1316.d004457 (k + 2) p.1, p.2)) := (hcoef (k + 2)).prodMk continuous_snd
    simpa only [Function.comp_def] using! _root_.GD.N0232.N0720.N1316.d004478.comp harg
  have hlinear : Continuous (fun p : (_root_.GD.N0232.N0720.N1316.d004440 k) × (_root_.GD.N0232.N0720.N1341.d004417 k) ↦
      _root_.GD.N0232.N0720.N1316.d004475 (_root_.GD.N0232.N0720.N1316.d004457 (k + 1) p.1) p.2) := by
    have harg : Continuous (fun p : (_root_.GD.N0232.N0720.N1316.d004440 k) × (_root_.GD.N0232.N0720.N1341.d004417 k) ↦
        (_root_.GD.N0232.N0720.N1316.d004457 (k + 1) p.1, p.2)) := (hcoef (k + 1)).prodMk continuous_snd
    simpa only [Function.comp_def] using! _root_.GD.N0232.N0720.N1316.d004479.comp harg
  have hconstant : Continuous (fun p : (_root_.GD.N0232.N0720.N1316.d004440 k) × (_root_.GD.N0232.N0720.N1341.d004417 k) ↦
      ∫ u, _root_.GD.N0232.N0720.N1316.d004457 k p.1 u ∂(_root_.GD.N0232.N0720.N1341.d004416 k)) := by
    simpa only [Function.comp_def] using! _root_.GD.N0232.N0720.N1316.d004480.comp (hcoef k)
  fun_prop

theorem d004483 (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) : Continuous (_root_.GD.N0232.N0720.N1316.d004469 q) :=
  _root_.GD.N0232.N0720.N1316.d004482.comp (continuous_const.prodMk continuous_id)

theorem d004484 (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) : Continuous (fun q ↦ _root_.GD.N0232.N0720.N1316.d004469 q h) :=
  _root_.GD.N0232.N0720.N1316.d004482.comp (continuous_id.prodMk continuous_const)

def d004485 (a : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ)) : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ) where
  toFun u := Real.sqrt (a u)
  continuous_toFun := Real.continuous_sqrt.comp a.continuous

theorem d004486 (a : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ))
    (ha : ∀ u, 0 ≤ a u) (h : (_root_.GD.N0232.N0720.N1341.d004417 k)) :
    _root_.GD.N0232.N0720.N1316.d004474 a h = ‖_root_.GD.N0232.N0720.N1316.d004471 (_root_.GD.N0232.N0720.N1316.d004485 a) h‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1316.d004476,
    ← real_inner_self_eq_norm_sq (_root_.GD.N0232.N0720.N1316.d004471 (_root_.GD.N0232.N0720.N1316.d004485 a) h), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1316.d004472 (_root_.GD.N0232.N0720.N1316.d004485 a) h] with u hu
  simp only [hu, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, mul_pow]
  change h u ^ 2 * a u = Real.sqrt (a u) ^ 2 * h u ^ 2
  rw [Real.sq_sqrt (ha u), mul_comm]

theorem d004487 (a : C((_root_.GD.N0232.N0720.N1341.d004415 k), ℝ)) (ha : ∀ u, 0 ≤ a u) :
    ConvexOn ℝ univ (_root_.GD.N0232.N0720.N1316.d004474 a) := by
  have hnorm : ConvexOn ℝ univ (fun h : (_root_.GD.N0232.N0720.N1341.d004417 k) ↦ ‖h‖ ^ 2) :=
    convexOn_univ_norm.pow (fun h _ ↦ norm_nonneg h) 2
  let op : (_root_.GD.N0232.N0720.N1341.d004417 k) →L[ℝ] (_root_.GD.N0232.N0720.N1341.d004417 k) :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL (_root_.GD.N0232.N0720.N1341.d004416 k) ∞ 2 2
      (ContinuousMap.toLp ∞ (_root_.GD.N0232.N0720.N1341.d004416 k) ℝ (_root_.GD.N0232.N0720.N1316.d004485 a))
  have hop : ConvexOn ℝ univ (fun h : (_root_.GD.N0232.N0720.N1341.d004417 k) ↦
      ‖_root_.GD.N0232.N0720.N1316.d004471 (_root_.GD.N0232.N0720.N1316.d004485 a) h‖ ^ 2) := by
    simpa only [Set.preimage_univ, Function.comp_def, op, _root_.GD.N0232.N0720.N1316.d004471] using!
      hnorm.comp_linearMap op.toLinearMap
  change ConvexOn ℝ univ (fun h : (_root_.GD.N0232.N0720.N1341.d004417 k) ↦ _root_.GD.N0232.N0720.N1316.d004474 a h)
  simpa only [_root_.GD.N0232.N0720.N1316.d004486 a ha] using hop



theorem d004488 (q : (_root_.GD.N0232.N0720.N1316.d004440 k)) : ConvexOn ℝ univ (_root_.GD.N0232.N0720.N1316.d004469 q) := by
  let ell : (_root_.GD.N0232.N0720.N1341.d004417 k) →ₗ[ℝ] ℝ :=
    (-2 * q.1) • (innerSL ℝ (ContinuousMap.toLp 2 (_root_.GD.N0232.N0720.N1341.d004416 k) ℝ
      (_root_.GD.N0232.N0720.N1316.d004457 (k + 1) q))).toLinearMap
  have hquad := _root_.GD.N0232.N0720.N1316.d004487 (_root_.GD.N0232.N0720.N1316.d004457 (k + 2) q)
    (fun u ↦ (_root_.GD.N0232.N0720.N1377.d002861 (k + 2) (_root_.GD.N0232.N0720.N1316.d004454 q u) (_root_.GD.N0232.N0720.N1316.d004442 q u)).le)
  have hsum := (hquad.add (ell.convexOn convex_univ)).add_const
    (q.1 ^ 2 * (∫ u, _root_.GD.N0232.N0720.N1316.d004457 k q u ∂(_root_.GD.N0232.N0720.N1341.d004416 k)))
  have hscaled := hsum.smul (_root_.GD.N0232.N0720.N1316.d004447 q).le
  convert! hscaled using 1
  ext h
  rw [_root_.GD.N0232.N0720.N1316.d004481]
  simp only [Pi.add_apply, smul_eq_mul, ell, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, _root_.GD.N0232.N0720.N1316.d004475]
  ring

def d004489 (k : ℕ) : _root_.GD.N0232.N0720.N1316.d004440 k :=
  (0, fun _ ↦ ⟨1 / 2, by constructor <;> norm_num⟩)

theorem d004490 (x : _root_.GD.N0232.N0720.N1341.d004414 k) :
    _root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0720.N1316.d004489 k) x =
      _root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 k) * _root_.GD.N0232.N0720.N1341.d004426 x := by
  unfold _root_.GD.N0232.N0720.N1316.d004445 _root_.GD.N0232.N0720.N1341.d004426
  congr 1
  apply congrArg Real.exp
  norm_num [_root_.GD.N0232.N0720.N1316.d004489, Finset.sum_neg_distrib, EuclideanSpace.real_norm_sq_eq]

theorem d004491 (h : _root_.GD.N0232.N0720.N1341.d004417 k) :
    _root_.GD.N0232.N0720.N1316.d004469 (_root_.GD.N0232.N0720.N1316.d004489 k) h =
      (_root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 k) * _root_.GD.N0232.N0720.N1341.d004428 k) * ‖h‖ ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1316.d004469
  simp_rw [_root_.GD.N0232.N0720.N1316.d004490]
  change (∫ x : _root_.GD.N0232.N0720.N1341.d004414 k, (_root_.GD.N0232.N0720.N1341.d004418 h x - 0) ^ 2 *
      (_root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 k) * _root_.GD.N0232.N0720.N1341.d004426 x)) = _
  simp only [sub_zero]
  have he : (fun x : _root_.GD.N0232.N0720.N1341.d004414 k ↦ _root_.GD.N0232.N0720.N1341.d004418 h x ^ 2 *
      (_root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 k) * _root_.GD.N0232.N0720.N1341.d004426 x)) =
      (fun x ↦ _root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 k) *
        (_root_.GD.N0232.N0720.N1341.d004418 h x ^ 2 * _root_.GD.N0232.N0720.N1341.d004426 x)) := by
    funext x
    ring
  rw [he, integral_const_mul]
  change _root_.GD.N0232.N0720.N1316.d004443 (_root_.GD.N0232.N0720.N1316.d004489 k) * _root_.GD.N0232.N0720.N1341.d004435 h = _
  rw [_root_.GD.N0232.N0720.N1341.d004437]
  ring

end
end GD.N0232.N0720.N1316

#print axioms _root_.GD.N0232.N0720.N1316.d004468
#print axioms _root_.GD.N0232.N0720.N1316.d004470
#print axioms _root_.GD.N0232.N0720.N1316.d004482
#print axioms _root_.GD.N0232.N0720.N1316.d004488
#print axioms _root_.GD.N0232.N0720.N1316.d004491
