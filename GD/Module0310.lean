import GD.Module0309
import GD.Module0209
import Mathlib.MeasureTheory.Function.Holder














open MeasureTheory Set
open scoped Topology ENNReal

namespace GD.N0232.N0720.N1372

open _root_.GD.N0232.N0720.N1393 _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1379

noncomputable section

abbrev d004518 := ℝ × Ioo (0 : ℝ) 1

def d004519 (q : _root_.GD.N0232.N0720.N1372.d004518) : ℝ := q.2.1 * (1 - q.2.1)

def d004520 (q : _root_.GD.N0232.N0720.N1372.d004518) (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ :=
  (x 0 ^ 2 + x 1 ^ 2) / q.2.1 + (x 2 ^ 2 + x 3 ^ 2) / (1 - q.2.1)

def d004521 (q : _root_.GD.N0232.N0720.N1372.d004518) (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ :=
  (x 0 / q.2.1 + x 2 / (1 - q.2.1)) * q.1

def d004522 (q : _root_.GD.N0232.N0720.N1372.d004518) : ℝ :=
  (4 * Real.pi ^ 2 * _root_.GD.N0232.N0720.N1372.d004519 q)⁻¹ *
    Real.exp (-(q.1 ^ 2) / (2 * _root_.GD.N0232.N0720.N1372.d004519 q))


def d004523 (q : _root_.GD.N0232.N0720.N1372.d004518) (x : _root_.GD.N0232.N0720.N1393.d004492) : ℝ :=
  (4 * Real.pi ^ 2 * _root_.GD.N0232.N0720.N1372.d004519 q)⁻¹ *
    Real.exp (-((x 0 - q.1) ^ 2 + x 1 ^ 2) / (2 * q.2.1) -
      ((x 2 - q.1) ^ 2 + x 3 ^ 2) / (2 * (1 - q.2.1)))

theorem d004524 (q : _root_.GD.N0232.N0720.N1372.d004518) : 0 < _root_.GD.N0232.N0720.N1372.d004519 q :=
  mul_pos q.2.2.1 (sub_pos.mpr q.2.2.2)

theorem d004525 (q : _root_.GD.N0232.N0720.N1372.d004518) : 0 < _root_.GD.N0232.N0720.N1372.d004522 q := by
  have hv := _root_.GD.N0232.N0720.N1372.d004524 q
  unfold _root_.GD.N0232.N0720.N1372.d004522
  exact mul_pos (inv_pos.mpr (by positivity)) (Real.exp_pos _)

theorem d004526 (q : _root_.GD.N0232.N0720.N1372.d004518) (x : _root_.GD.N0232.N0720.N1393.d004492) :
    ‖x‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1372.d004520 q x := by
  have hleft : x 0 ^ 2 + x 1 ^ 2 ≤ (x 0 ^ 2 + x 1 ^ 2) / q.2.1 := by
    apply (le_div_iff₀ q.2.2.1).mpr
    exact mul_le_of_le_one_right (by positivity) q.2.2.2.le
  have hright : x 2 ^ 2 + x 3 ^ 2 ≤ (x 2 ^ 2 + x 3 ^ 2) / (1 - q.2.1) := by
    apply (le_div_iff₀ (sub_pos.mpr q.2.2.2)).mpr
    exact mul_le_of_le_one_right (by positivity) (by linarith [q.2.2.1])
  have hnorm := EuclideanSpace.real_norm_sq_eq x
  norm_num [Fin.sum_univ_succ] at hnorm
  change ‖x‖ ^ 2 = x 0 ^ 2 + (x 1 ^ 2 + (x 2 ^ 2 + x 3 ^ 2)) at hnorm
  unfold _root_.GD.N0232.N0720.N1372.d004520
  linarith

theorem d004527 (q : _root_.GD.N0232.N0720.N1372.d004518) (u : _root_.GD.N0232.N0720.N1393.d004493) : 1 ≤ _root_.GD.N0232.N0720.N1372.d004520 q u := by
  have hu : ‖(u : _root_.GD.N0232.N0720.N1393.d004492)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  simpa only [hu, one_pow] using _root_.GD.N0232.N0720.N1372.d004526 q u

theorem d004528 (q : _root_.GD.N0232.N0720.N1372.d004518) (u : _root_.GD.N0232.N0720.N1393.d004493) : 0 < _root_.GD.N0232.N0720.N1372.d004520 q u :=
  lt_of_lt_of_le zero_lt_one (_root_.GD.N0232.N0720.N1372.d004527 q u)

@[fun_prop]
theorem d004529 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004492 ↦ _root_.GD.N0232.N0720.N1372.d004520 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1372.d004520
  apply Continuous.add
  · exact Continuous.div (by fun_prop) (by fun_prop) (fun p ↦ p.1.2.2.1.ne')
  · exact Continuous.div (by fun_prop) (by fun_prop)
      (fun p ↦ (sub_pos.mpr p.1.2.2.2).ne')

@[fun_prop]
theorem d004530 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004492 ↦ _root_.GD.N0232.N0720.N1372.d004521 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1372.d004521
  apply Continuous.mul _ (by fun_prop)
  apply Continuous.add
  · exact Continuous.div (by fun_prop) (by fun_prop) (fun p ↦ p.1.2.2.1.ne')
  · exact Continuous.div (by fun_prop) (by fun_prop)
      (fun p ↦ (sub_pos.mpr p.1.2.2.2).ne')

@[fun_prop]
theorem d004531 : Continuous _root_.GD.N0232.N0720.N1372.d004522 := by
  have hv : Continuous _root_.GD.N0232.N0720.N1372.d004519 := by unfold _root_.GD.N0232.N0720.N1372.d004519; fun_prop
  unfold _root_.GD.N0232.N0720.N1372.d004522
  fun_prop (disch := intro q; have h := _root_.GD.N0232.N0720.N1372.d004524 q; positivity)

def d004532 (q : _root_.GD.N0232.N0720.N1372.d004518) : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) where
  toFun u := _root_.GD.N0232.N0720.N1372.d004521 q u
  continuous_toFun := _root_.GD.N0232.N0720.N1372.d004530.comp (continuous_const.prodMk continuous_subtype_val)

@[fun_prop]
theorem d004533 (n : ℕ) :
    Continuous (fun p : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004493 ↦
      _root_.GD.N0232.N0720.N1377.d002852 n (_root_.GD.N0232.N0720.N1372.d004520 p.1 p.2) (_root_.GD.N0232.N0720.N1372.d004521 p.1 p.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hparam : Continuous (fun q : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004493 ↦
      (_root_.GD.N0232.N0720.N1372.d004520 q.1 q.2, _root_.GD.N0232.N0720.N1372.d004521 q.1 q.2)) :=
    (_root_.GD.N0232.N0720.N1372.d004529.prodMk _root_.GD.N0232.N0720.N1372.d004530).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  exact (_root_.GD.N0232.N0720.N1379.d002889 n
    (p := (_root_.GD.N0232.N0720.N1372.d004520 p.1 p.2, _root_.GD.N0232.N0720.N1372.d004521 p.1 p.2))
    (_root_.GD.N0232.N0720.N1372.d004528 p.1 p.2)).continuousAt.comp
      (f := fun q : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004493 ↦ (_root_.GD.N0232.N0720.N1372.d004520 q.1 q.2, _root_.GD.N0232.N0720.N1372.d004521 q.1 q.2))
      hparam.continuousAt


def d004534 (n : ℕ) (q : _root_.GD.N0232.N0720.N1372.d004518) : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) where
  toFun u := _root_.GD.N0232.N0720.N1377.d002852 n (_root_.GD.N0232.N0720.N1372.d004520 q u) (_root_.GD.N0232.N0720.N1372.d004521 q u)
  continuous_toFun := by
    have hsection : Continuous (fun u : _root_.GD.N0232.N0720.N1393.d004493 ↦ (q, u)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def] using! (_root_.GD.N0232.N0720.N1372.d004533 n).comp hsection

@[fun_prop]
theorem d004535 (n : ℕ) : Continuous (_root_.GD.N0232.N0720.N1372.d004534 n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact _root_.GD.N0232.N0720.N1372.d004533 n



theorem d004536 (q : _root_.GD.N0232.N0720.N1372.d004518) (u : _root_.GD.N0232.N0720.N1393.d004493) (r : ℝ) :
    _root_.GD.N0232.N0720.N1372.d004523 q (r • (u : _root_.GD.N0232.N0720.N1393.d004492)) =
      _root_.GD.N0232.N0720.N1372.d004522 q * Real.exp
        (-_root_.GD.N0232.N0720.N1372.d004520 q u / 2 * r ^ 2 + _root_.GD.N0232.N0720.N1372.d004521 q u * r) := by
  have ht : q.2.1 ≠ 0 := q.2.2.1.ne'
  have hot : 1 - q.2.1 ≠ 0 := (sub_pos.mpr q.2.2.2).ne'
  have he :
      -((r * (u : _root_.GD.N0232.N0720.N1393.d004492) 0 - q.1) ^ 2 + (r * (u : _root_.GD.N0232.N0720.N1393.d004492) 1) ^ 2) /
          (2 * q.2.1) -
        ((r * (u : _root_.GD.N0232.N0720.N1393.d004492) 2 - q.1) ^ 2 + (r * (u : _root_.GD.N0232.N0720.N1393.d004492) 3) ^ 2) /
          (2 * (1 - q.2.1)) =
      -(q.1 ^ 2) / (2 * _root_.GD.N0232.N0720.N1372.d004519 q) +
        (-_root_.GD.N0232.N0720.N1372.d004520 q u / 2 * r ^ 2 + _root_.GD.N0232.N0720.N1372.d004521 q u * r) := by
    unfold _root_.GD.N0232.N0720.N1372.d004519 _root_.GD.N0232.N0720.N1372.d004520 _root_.GD.N0232.N0720.N1372.d004521
    field_simp [ht, hot]
    ring
  simp only [_root_.GD.N0232.N0720.N1372.d004523, _root_.GD.N0232.N0720.N1372.d004522, PiLp.smul_apply, smul_eq_mul, he,
    Real.exp_add]
  ring


theorem d004537 (n : ℕ) {A : ℝ} (hA : 0 < A) (b : ℝ) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ _root_.GD.N0232.N0720.N1377.d002851 n A b r.1)
      (Measure.volumeIoiPow 3) := by
  rw [_root_.GD.N0232.N0720.N1393.d004503]
  have heq : (fun r : ℝ ↦ r ^ 3 * _root_.GD.N0232.N0720.N1377.d002851 n A b r) =
      _root_.GD.N0232.N0720.N1377.d002851 (n + 3) A b := by
    funext r
    simp only [_root_.GD.N0232.N0720.N1377.d002851, pow_add]
    ring
  rw [heq]
  exact _root_.GD.N0232.N0720.N1377.d002860 (n + 3) hA b

theorem d004538 (n : ℕ) (A b : ℝ) :
    (∫ r : Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1377.d002851 n A b r.1 ∂Measure.volumeIoiPow 3) =
      _root_.GD.N0232.N0720.N1377.d002852 (n + 3) A b := by
  rw [_root_.GD.N0232.N0720.N1393.d004502]
  unfold _root_.GD.N0232.N0720.N1377.d002852
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  simp only [_root_.GD.N0232.N0720.N1377.d002851, pow_add]
  ring

theorem d004539 (n : ℕ) (M : ℝ) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ _root_.GD.N0232.N0720.N1377.d002857 n 1 M r.1)
      (Measure.volumeIoiPow 3) := by
  rw [_root_.GD.N0232.N0720.N1393.d004503]
  have heq : (fun r : ℝ ↦ r ^ 3 * _root_.GD.N0232.N0720.N1377.d002857 n 1 M r) =
      _root_.GD.N0232.N0720.N1377.d002857 (n + 3) 1 M := by
    funext r
    simp only [_root_.GD.N0232.N0720.N1377.d002857, pow_add]
    ring
  rw [heq]
  exact _root_.GD.N0232.N0720.N1377.d002858 (n + 3) (show (0 : ℝ) < 1 by norm_num) M



theorem d004540 (n : ℕ) (q : _root_.GD.N0232.N0720.N1372.d004518)
    (f : _root_.GD.N0232.N0720.N1393.d004493 → ℝ) (hf : Integrable f _root_.GD.N0232.N0720.N1393.d004494) :
    Integrable (fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦
      f p.1 * _root_.GD.N0232.N0720.N1377.d002851 n (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1)
      (_root_.GD.N0232.N0720.N1393.d004494.prod (Measure.volumeIoiPow 3)) := by
  have hcont : Continuous (fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦
      _root_.GD.N0232.N0720.N1377.d002851 n (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1) := by
    have ha : Continuous (fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦ _root_.GD.N0232.N0720.N1372.d004520 q p.1) :=
      _root_.GD.N0232.N0720.N1372.d004529.comp
        (continuous_const.prodMk (continuous_subtype_val.comp continuous_fst))
    have hb : Continuous (fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦ _root_.GD.N0232.N0720.N1372.d004521 q p.1) :=
      _root_.GD.N0232.N0720.N1372.d004530.comp
        (continuous_const.prodMk (continuous_subtype_val.comp continuous_fst))
    unfold _root_.GD.N0232.N0720.N1377.d002851
    fun_prop
  apply (hf.norm.mul_prod (_root_.GD.N0232.N0720.N1372.d004539 n ‖_root_.GD.N0232.N0720.N1372.d004532 q‖)).mono'
    (hf.aestronglyMeasurable.comp_fst.mul hcont.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun p ↦ by
    change ‖f p.1 * _root_.GD.N0232.N0720.N1377.d002851 n (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply _root_.GD.N0232.N0720.N1379.d002886 n zero_lt_one
      (_root_.GD.N0232.N0720.N1372.d004527 q p.1) _ p.2.2.le
    exact (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, _root_.GD.N0232.N0720.N1372.d004532] using!
        (_root_.GD.N0232.N0720.N1372.d004532 q).norm_coe_le_norm p.1))

theorem d004541 (n : ℕ) (q : _root_.GD.N0232.N0720.N1372.d004518)
    (f : _root_.GD.N0232.N0720.N1393.d004493 → ℝ) (hf : Integrable f _root_.GD.N0232.N0720.N1393.d004494) :
    (∫ p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ),
      f p.1 * _root_.GD.N0232.N0720.N1377.d002851 n (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1
        ∂_root_.GD.N0232.N0720.N1393.d004494.prod (Measure.volumeIoiPow 3)) =
      ∫ u : _root_.GD.N0232.N0720.N1393.d004493, f u * _root_.GD.N0232.N0720.N1372.d004534 (n + 3) q u ∂_root_.GD.N0232.N0720.N1393.d004494 := by
  rw [integral_prod _ (_root_.GD.N0232.N0720.N1372.d004540 n q f hf)]
  simp_rw [integral_const_mul, _root_.GD.N0232.N0720.N1372.d004538]
  rfl

def d004542 (q : _root_.GD.N0232.N0720.N1372.d004518) (h : _root_.GD.N0232.N0720.N1393.d004495) (p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ)) : ℝ :=
  _root_.GD.N0232.N0720.N1372.d004522 q *
    (h p.1 ^ 2 * _root_.GD.N0232.N0720.N1377.d002851 2 (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1 -
      2 * q.1 * (h p.1 * _root_.GD.N0232.N0720.N1377.d002851 1 (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1) +
      q.1 ^ 2 * _root_.GD.N0232.N0720.N1377.d002851 0 (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1)

theorem d004543 (q : _root_.GD.N0232.N0720.N1372.d004518) (h : _root_.GD.N0232.N0720.N1393.d004495) (p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ)) :
    (_root_.GD.N0232.N0720.N1393.d004496 h (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1393.d004492)) - q.1) ^ 2 *
        _root_.GD.N0232.N0720.N1372.d004523 q (p.2.1 • (p.1 : _root_.GD.N0232.N0720.N1393.d004492)) = _root_.GD.N0232.N0720.N1372.d004542 q h p := by
  rw [_root_.GD.N0232.N0720.N1393.d004499, _root_.GD.N0232.N0720.N1372.d004536]
  simp only [_root_.GD.N0232.N0720.N1372.d004542, _root_.GD.N0232.N0720.N1377.d002851, pow_zero, pow_one]
  ring

theorem d004544 (q : _root_.GD.N0232.N0720.N1372.d004518) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    Integrable (_root_.GD.N0232.N0720.N1372.d004542 q h) (_root_.GD.N0232.N0720.N1393.d004494.prod (Measure.volumeIoiPow 3)) := by
  have h2 := _root_.GD.N0232.N0720.N1372.d004540 2 q (fun u ↦ h u ^ 2)
    (Lp.memLp h).integrable_sq
  have h1 := _root_.GD.N0232.N0720.N1372.d004540 1 q h
    ((Lp.memLp h).integrable (by norm_num))
  have h0 := _root_.GD.N0232.N0720.N1372.d004540 0 q (fun _ ↦ 1)
    (integrable_const 1)
  simpa only [_root_.GD.N0232.N0720.N1372.d004542, one_mul] using!
    ((h2.sub (h1.const_mul (2 * q.1))).add (h0.const_mul (q.1 ^ 2))).const_mul
      (_root_.GD.N0232.N0720.N1372.d004522 q)


theorem d004545 (q : _root_.GD.N0232.N0720.N1372.d004518) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    Integrable (fun x ↦ (_root_.GD.N0232.N0720.N1393.d004496 h x - q.1) ^ 2 * _root_.GD.N0232.N0720.N1372.d004523 q x) := by
  rw [_root_.GD.N0232.N0720.N1393.d004501]
  exact (_root_.GD.N0232.N0720.N1372.d004544 q h).congr
    (Filter.Eventually.of_forall (fun p ↦ (_root_.GD.N0232.N0720.N1372.d004543 q h p).symm))

def d004546 (q : _root_.GD.N0232.N0720.N1372.d004518) (h : _root_.GD.N0232.N0720.N1393.d004495) : ℝ :=
  ∫ x, (_root_.GD.N0232.N0720.N1393.d004496 h x - q.1) ^ 2 * _root_.GD.N0232.N0720.N1372.d004523 q x



theorem d004547 (q : _root_.GD.N0232.N0720.N1372.d004518) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1372.d004546 q h = _root_.GD.N0232.N0720.N1372.d004522 q *
      ((∫ u : _root_.GD.N0232.N0720.N1393.d004493, h u ^ 2 * _root_.GD.N0232.N0720.N1372.d004534 5 q u ∂_root_.GD.N0232.N0720.N1393.d004494) -
        2 * q.1 * (∫ u : _root_.GD.N0232.N0720.N1393.d004493, h u * _root_.GD.N0232.N0720.N1372.d004534 4 q u ∂_root_.GD.N0232.N0720.N1393.d004494) +
        q.1 ^ 2 * (∫ u : _root_.GD.N0232.N0720.N1393.d004493, _root_.GD.N0232.N0720.N1372.d004534 3 q u ∂_root_.GD.N0232.N0720.N1393.d004494)) := by
  have h2 := _root_.GD.N0232.N0720.N1372.d004540 2 q (fun u ↦ h u ^ 2)
    (Lp.memLp h).integrable_sq
  have h1 := _root_.GD.N0232.N0720.N1372.d004540 1 q h
    ((Lp.memLp h).integrable (by norm_num))
  have h0 := _root_.GD.N0232.N0720.N1372.d004540 0 q (fun _ ↦ 1)
    (integrable_const 1)
  have hz : (∫ p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ),
      _root_.GD.N0232.N0720.N1377.d002851 0 (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1
        ∂_root_.GD.N0232.N0720.N1393.d004494.prod (Measure.volumeIoiPow 3)) =
      ∫ u : _root_.GD.N0232.N0720.N1393.d004493, _root_.GD.N0232.N0720.N1372.d004534 3 q u ∂_root_.GD.N0232.N0720.N1393.d004494 := by
    simpa only [one_mul, Nat.reduceAdd] using
      _root_.GD.N0232.N0720.N1372.d004541 0 q (fun _ ↦ 1) (integrable_const 1)
  unfold _root_.GD.N0232.N0720.N1372.d004546
  rw [_root_.GD.N0232.N0720.N1393.d004500]
  simp_rw [_root_.GD.N0232.N0720.N1372.d004543]
  unfold _root_.GD.N0232.N0720.N1372.d004542
  rw [integral_const_mul, integral_add
    (f := fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦
      h p.1 ^ 2 * _root_.GD.N0232.N0720.N1377.d002851 2 (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1 -
        2 * q.1 * (h p.1 * _root_.GD.N0232.N0720.N1377.d002851 1 (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1))
    (g := fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦
      q.1 ^ 2 * _root_.GD.N0232.N0720.N1377.d002851 0 (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1)
    (h2.sub (h1.const_mul _))
    (by simpa only [one_mul] using h0.const_mul (q.1 ^ 2)),
    integral_sub
      (f := fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦
        h p.1 ^ 2 * _root_.GD.N0232.N0720.N1377.d002851 2 (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1)
      (g := fun p : _root_.GD.N0232.N0720.N1393.d004493 × Ioi (0 : ℝ) ↦
        2 * q.1 * (h p.1 * _root_.GD.N0232.N0720.N1377.d002851 1 (_root_.GD.N0232.N0720.N1372.d004520 q p.1) (_root_.GD.N0232.N0720.N1372.d004521 q p.1) p.2.1))
      h2 (h1.const_mul _), integral_const_mul, integral_const_mul,
    _root_.GD.N0232.N0720.N1372.d004541 2 q _ (Lp.memLp h).integrable_sq,
    _root_.GD.N0232.N0720.N1372.d004541 1 q _ ((Lp.memLp h).integrable (by norm_num)), hz]





def d004548 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (h : _root_.GD.N0232.N0720.N1393.d004495) : _root_.GD.N0232.N0720.N1393.d004495 :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL _root_.GD.N0232.N0720.N1393.d004494 ∞ 2 2
    (ContinuousMap.toLp ∞ _root_.GD.N0232.N0720.N1393.d004494 ℝ a) h

theorem d004549 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1372.d004548 a h =ᵐ[_root_.GD.N0232.N0720.N1393.d004494] fun u ↦ a u * h u := by
  change (ContinuousLinearMap.mul ℝ ℝ).holder 2
    (ContinuousMap.toLp ∞ _root_.GD.N0232.N0720.N1393.d004494 ℝ a) h =ᵐ[_root_.GD.N0232.N0720.N1393.d004494] _
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
      (r := 2) (ContinuousMap.toLp ∞ _root_.GD.N0232.N0720.N1393.d004494 ℝ a) h,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℝ) _root_.GD.N0232.N0720.N1393.d004494 a] with u hu ha
  simpa only [ContinuousLinearMap.mul_apply', ha] using hu

@[fun_prop]
theorem d004550 :
    Continuous (fun p : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) × _root_.GD.N0232.N0720.N1393.d004495 ↦ _root_.GD.N0232.N0720.N1372.d004548 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1372.d004548
  fun_prop

def d004551 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (h : _root_.GD.N0232.N0720.N1393.d004495) : ℝ :=
  inner ℝ (_root_.GD.N0232.N0720.N1372.d004548 a h) h

def d004552 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (h : _root_.GD.N0232.N0720.N1393.d004495) : ℝ :=
  inner ℝ (ContinuousMap.toLp 2 _root_.GD.N0232.N0720.N1393.d004494 ℝ a) h

theorem d004553 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1372.d004551 a h = ∫ u : _root_.GD.N0232.N0720.N1393.d004493, h u ^ 2 * a u ∂_root_.GD.N0232.N0720.N1393.d004494 := by
  rw [_root_.GD.N0232.N0720.N1372.d004551, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1372.d004549 a h] with u hu
  simp [hu, pow_two, mul_assoc, mul_comm]

theorem d004554 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1372.d004552 a h = ∫ u : _root_.GD.N0232.N0720.N1393.d004493, h u * a u ∂_root_.GD.N0232.N0720.N1393.d004494 := by
  rw [_root_.GD.N0232.N0720.N1372.d004552, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) _root_.GD.N0232.N0720.N1393.d004494 a] with u hu
  simp only [Real.inner_apply]
  rw [hu, mul_comm]

@[fun_prop]
theorem d004555 :
    Continuous (fun p : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) × _root_.GD.N0232.N0720.N1393.d004495 ↦ _root_.GD.N0232.N0720.N1372.d004551 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1372.d004551
  exact _root_.GD.N0232.N0720.N1372.d004550.inner continuous_snd

@[fun_prop]
theorem d004556 :
    Continuous (fun p : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) × _root_.GD.N0232.N0720.N1393.d004495 ↦ _root_.GD.N0232.N0720.N1372.d004552 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1372.d004552
  fun_prop

theorem d004557 :
    Continuous (fun a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) ↦ ∫ u, a u ∂_root_.GD.N0232.N0720.N1393.d004494) := by
  have heq : (fun a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) ↦ ∫ u, a u ∂_root_.GD.N0232.N0720.N1393.d004494) =
      fun a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) ↦
        ∫ u, (ContinuousMap.toLp 1 _root_.GD.N0232.N0720.N1393.d004494 ℝ a) u ∂_root_.GD.N0232.N0720.N1393.d004494 := by
    funext a
    exact (integral_congr_ae
      (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) _root_.GD.N0232.N0720.N1393.d004494 a)).symm
  rw [heq]
  exact MeasureTheory.continuous_integral.comp
    (ContinuousMap.toLp 1 _root_.GD.N0232.N0720.N1393.d004494 ℝ).continuous

theorem d004558 (q : _root_.GD.N0232.N0720.N1372.d004518) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1372.d004546 q h = _root_.GD.N0232.N0720.N1372.d004522 q *
      (_root_.GD.N0232.N0720.N1372.d004551 (_root_.GD.N0232.N0720.N1372.d004534 5 q) h -
        2 * q.1 * _root_.GD.N0232.N0720.N1372.d004552 (_root_.GD.N0232.N0720.N1372.d004534 4 q) h +
        q.1 ^ 2 * (∫ u, _root_.GD.N0232.N0720.N1372.d004534 3 q u ∂_root_.GD.N0232.N0720.N1393.d004494)) := by
  rw [_root_.GD.N0232.N0720.N1372.d004547, _root_.GD.N0232.N0720.N1372.d004553, _root_.GD.N0232.N0720.N1372.d004554]

set_option maxHeartbeats 800000 in


theorem d004559 :
    Continuous (fun p : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004495 ↦ _root_.GD.N0232.N0720.N1372.d004546 p.1 p.2) := by
  simp_rw [_root_.GD.N0232.N0720.N1372.d004558]
  have hcoef (n : ℕ) : Continuous (fun p : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004495 ↦
      _root_.GD.N0232.N0720.N1372.d004534 n p.1) := by
    simpa only [Function.comp_def] using!
      (_root_.GD.N0232.N0720.N1372.d004535 n).comp
        (continuous_fst : Continuous (fun p : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004495 ↦ p.1))
  have hquad : Continuous (fun p : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004495 ↦
      _root_.GD.N0232.N0720.N1372.d004551 (_root_.GD.N0232.N0720.N1372.d004534 5 p.1) p.2) := by
    have harg : Continuous (fun p : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004495 ↦
        (_root_.GD.N0232.N0720.N1372.d004534 5 p.1, p.2)) := (hcoef 5).prodMk continuous_snd
    simpa only [Function.comp_def] using! _root_.GD.N0232.N0720.N1372.d004555.comp harg
  have hlinear : Continuous (fun p : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004495 ↦
      _root_.GD.N0232.N0720.N1372.d004552 (_root_.GD.N0232.N0720.N1372.d004534 4 p.1) p.2) := by
    have harg : Continuous (fun p : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004495 ↦
        (_root_.GD.N0232.N0720.N1372.d004534 4 p.1, p.2)) := (hcoef 4).prodMk continuous_snd
    simpa only [Function.comp_def] using! _root_.GD.N0232.N0720.N1372.d004556.comp harg
  have hconstant : Continuous (fun p : _root_.GD.N0232.N0720.N1372.d004518 × _root_.GD.N0232.N0720.N1393.d004495 ↦
      ∫ u, _root_.GD.N0232.N0720.N1372.d004534 3 p.1 u ∂_root_.GD.N0232.N0720.N1393.d004494) := by
    simpa only [Function.comp_def] using! _root_.GD.N0232.N0720.N1372.d004557.comp (hcoef 3)
  fun_prop

theorem d004560 (q : _root_.GD.N0232.N0720.N1372.d004518) : Continuous (_root_.GD.N0232.N0720.N1372.d004546 q) :=
  _root_.GD.N0232.N0720.N1372.d004559.comp (continuous_const.prodMk continuous_id)

theorem d004561 (h : _root_.GD.N0232.N0720.N1393.d004495) : Continuous (fun q ↦ _root_.GD.N0232.N0720.N1372.d004546 q h) :=
  _root_.GD.N0232.N0720.N1372.d004559.comp (continuous_id.prodMk continuous_const)

def d004562 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ) where
  toFun u := Real.sqrt (a u)
  continuous_toFun := Real.continuous_sqrt.comp a.continuous

theorem d004563 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ))
    (ha : ∀ u, 0 ≤ a u) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1372.d004551 a h = ‖_root_.GD.N0232.N0720.N1372.d004548 (_root_.GD.N0232.N0720.N1372.d004562 a) h‖ ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1372.d004553,
    ← real_inner_self_eq_norm_sq (_root_.GD.N0232.N0720.N1372.d004548 (_root_.GD.N0232.N0720.N1372.d004562 a) h), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1372.d004549 (_root_.GD.N0232.N0720.N1372.d004562 a) h] with u hu
  simp only [hu, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, mul_pow]
  change h u ^ 2 * a u = Real.sqrt (a u) ^ 2 * h u ^ 2
  rw [Real.sq_sqrt (ha u), mul_comm]

theorem d004564 (a : C(_root_.GD.N0232.N0720.N1393.d004493, ℝ)) (ha : ∀ u, 0 ≤ a u) :
    ConvexOn ℝ univ (_root_.GD.N0232.N0720.N1372.d004551 a) := by
  have hnorm : ConvexOn ℝ univ (fun h : _root_.GD.N0232.N0720.N1393.d004495 ↦ ‖h‖ ^ 2) :=
    convexOn_univ_norm.pow (fun h _ ↦ norm_nonneg h) 2
  let op : _root_.GD.N0232.N0720.N1393.d004495 →L[ℝ] _root_.GD.N0232.N0720.N1393.d004495 :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL _root_.GD.N0232.N0720.N1393.d004494 ∞ 2 2
      (ContinuousMap.toLp ∞ _root_.GD.N0232.N0720.N1393.d004494 ℝ (_root_.GD.N0232.N0720.N1372.d004562 a))
  have hop : ConvexOn ℝ univ (fun h : _root_.GD.N0232.N0720.N1393.d004495 ↦
      ‖_root_.GD.N0232.N0720.N1372.d004548 (_root_.GD.N0232.N0720.N1372.d004562 a) h‖ ^ 2) := by
    simpa only [Set.preimage_univ, Function.comp_def, op, _root_.GD.N0232.N0720.N1372.d004548] using!
      hnorm.comp_linearMap op.toLinearMap
  change ConvexOn ℝ univ (fun h : _root_.GD.N0232.N0720.N1393.d004495 ↦ _root_.GD.N0232.N0720.N1372.d004551 a h)
  simpa only [_root_.GD.N0232.N0720.N1372.d004563 a ha] using hop



theorem d004565 (q : _root_.GD.N0232.N0720.N1372.d004518) : ConvexOn ℝ univ (_root_.GD.N0232.N0720.N1372.d004546 q) := by
  let ell : _root_.GD.N0232.N0720.N1393.d004495 →ₗ[ℝ] ℝ :=
    (-2 * q.1) • (innerSL ℝ (ContinuousMap.toLp 2 _root_.GD.N0232.N0720.N1393.d004494 ℝ
      (_root_.GD.N0232.N0720.N1372.d004534 4 q))).toLinearMap
  have hquad := _root_.GD.N0232.N0720.N1372.d004564 (_root_.GD.N0232.N0720.N1372.d004534 5 q)
    (fun u ↦ (_root_.GD.N0232.N0720.N1377.d002861 5 (_root_.GD.N0232.N0720.N1372.d004528 q u) (_root_.GD.N0232.N0720.N1372.d004521 q u)).le)
  have hsum := (hquad.add (ell.convexOn convex_univ)).add_const
    (q.1 ^ 2 * (∫ u, _root_.GD.N0232.N0720.N1372.d004534 3 q u ∂_root_.GD.N0232.N0720.N1393.d004494))
  have hscaled := hsum.smul (_root_.GD.N0232.N0720.N1372.d004525 q).le
  convert! hscaled using 1
  ext h
  rw [_root_.GD.N0232.N0720.N1372.d004558]
  simp only [Pi.add_apply, smul_eq_mul, ell, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, _root_.GD.N0232.N0720.N1372.d004552]
  ring

def d004566 : _root_.GD.N0232.N0720.N1372.d004518 := (0, ⟨1 / 2, by constructor <;> norm_num⟩)

theorem d004567 (x : _root_.GD.N0232.N0720.N1393.d004492) :
    _root_.GD.N0232.N0720.N1372.d004523 _root_.GD.N0232.N0720.N1372.d004566 x = _root_.GD.N0232.N0720.N1393.d004504 x := by
  have hc : 4 * Real.pi ^ 2 * _root_.GD.N0232.N0720.N1372.d004519 _root_.GD.N0232.N0720.N1372.d004566 = Real.pi ^ 2 := by
    norm_num [_root_.GD.N0232.N0720.N1372.d004519, _root_.GD.N0232.N0720.N1372.d004566] <;> ring
  have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ] <;> ring
  unfold _root_.GD.N0232.N0720.N1372.d004523 _root_.GD.N0232.N0720.N1393.d004504
  rw [hc]
  congr 1
  apply congrArg Real.exp
  norm_num [_root_.GD.N0232.N0720.N1372.d004566]
  rw [hn]
  ring



theorem d004568 (h : _root_.GD.N0232.N0720.N1393.d004495) :
    _root_.GD.N0232.N0720.N1372.d004546 _root_.GD.N0232.N0720.N1372.d004566 h = _root_.GD.N0232.N0720.N1393.d004506 * ‖h‖ ^ 2 := by
  have heq : _root_.GD.N0232.N0720.N1372.d004546 _root_.GD.N0232.N0720.N1372.d004566 h = _root_.GD.N0232.N0720.N1393.d004513 h := by
    unfold _root_.GD.N0232.N0720.N1372.d004546 _root_.GD.N0232.N0720.N1393.d004513
    simp_rw [_root_.GD.N0232.N0720.N1372.d004567]
    simp only [_root_.GD.N0232.N0720.N1372.d004566, sub_zero]
  rw [heq, _root_.GD.N0232.N0720.N1393.d004515]

end

end GD.N0232.N0720.N1372

#print axioms _root_.GD.N0232.N0720.N1372.d004545
#print axioms _root_.GD.N0232.N0720.N1372.d004547
#print axioms _root_.GD.N0232.N0720.N1372.d004559
#print axioms _root_.GD.N0232.N0720.N1372.d004565
#print axioms _root_.GD.N0232.N0720.N1372.d004568
