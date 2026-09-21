import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic










open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1377

noncomputable section

def d002851 (n : ℕ) (A b r : ℝ) : ℝ :=
  r ^ n * Real.exp (-A / 2 * r ^ 2 + b * r)

def d002852 (n : ℕ) (A b : ℝ) : ℝ :=
  ∫ r in Ioi 0, _root_.GD.N0232.N0720.N1377.d002851 n A b r

theorem d002853 (n : ℕ) (A b : ℝ) :
    Continuous (_root_.GD.N0232.N0720.N1377.d002851 n A b) := by
  unfold _root_.GD.N0232.N0720.N1377.d002851
  fun_prop

theorem d002854 (n : ℕ) (A b : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ _root_.GD.N0232.N0720.N1377.d002851 n A b r := by
  exact mul_nonneg (pow_nonneg hr _) (Real.exp_pos _).le

theorem d002855 (n : ℕ) (A b : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < _root_.GD.N0232.N0720.N1377.d002851 n A b r := by
  exact mul_pos (pow_pos hr _) (Real.exp_pos _)


theorem d002856 {A : ℝ} (hA : 0 < A) (b r : ℝ) :
    -A / 2 * r ^ 2 + b * r ≤ b ^ 2 / A - (A / 4) * r ^ 2 := by
  have hs : 0 ≤ A / 4 * (r - 2 * b / A) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  have heq : A / 4 * (r - 2 * b / A) ^ 2 =
      A / 4 * r ^ 2 - b * r + b ^ 2 / A := by
    field_simp [hA.ne']
    ring
  rw [heq] at hs
  linarith

def d002857 (n : ℕ) (A b r : ℝ) : ℝ :=
  Real.exp (b ^ 2 / A) * (r ^ n * Real.exp (-(A / 4) * r ^ 2))

theorem d002858 (n : ℕ) {A : ℝ} (hA : 0 < A) (b : ℝ) :
    IntegrableOn (_root_.GD.N0232.N0720.N1377.d002857 n A b) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun r : ℝ ↦ r ^ n * Real.exp (-(A / 4) * r ^ 2)) (Ioi 0) := by
    simpa only [Real.rpow_natCast] using
      (integrableOn_rpow_mul_exp_neg_mul_sq
        (show 0 < A / 4 by positivity)
        (show (-1 : ℝ) < (n : ℝ) from lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)))
  exact hbase.const_mul _

theorem d002859 (n : ℕ) {A : ℝ} (hA : 0 < A)
    (b : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ‖_root_.GD.N0232.N0720.N1377.d002851 n A b r‖ ≤ _root_.GD.N0232.N0720.N1377.d002857 n A b r := by
  rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1377.d002854 n A b hr)]
  unfold _root_.GD.N0232.N0720.N1377.d002851 _root_.GD.N0232.N0720.N1377.d002857
  calc
    r ^ n * Real.exp (-A / 2 * r ^ 2 + b * r) ≤
        r ^ n * Real.exp (b ^ 2 / A - (A / 4) * r ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (_root_.GD.N0232.N0720.N1377.d002856 hA b r)) (pow_nonneg hr _)
    _ = Real.exp (b ^ 2 / A) *
        (r ^ n * Real.exp (-(A / 4) * r ^ 2)) := by
      rw [sub_eq_add_neg, Real.exp_add]
      simp only [neg_mul]
      ring

theorem d002860 (n : ℕ) {A : ℝ} (hA : 0 < A) (b : ℝ) :
    IntegrableOn (_root_.GD.N0232.N0720.N1377.d002851 n A b) (Ioi 0) := by
  apply (_root_.GD.N0232.N0720.N1377.d002858 n hA b).mono'
    (_root_.GD.N0232.N0720.N1377.d002853 n A b).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact _root_.GD.N0232.N0720.N1377.d002859 n hA b hr.le

theorem d002861 (n : ℕ) {A : ℝ} (hA : 0 < A) (b : ℝ) :
    0 < _root_.GD.N0232.N0720.N1377.d002852 n A b := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioi 0)] _root_.GD.N0232.N0720.N1377.d002851 n A b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact _root_.GD.N0232.N0720.N1377.d002854 n A b hr.le
  apply (setIntegral_pos_iff_support_of_nonneg_ae hn
    (_root_.GD.N0232.N0720.N1377.d002860 n hA b)).2
  calc
      0 < volume (Ioo (1 : ℝ) 2) := by simp
      _ ≤ volume (Function.support (_root_.GD.N0232.N0720.N1377.d002851 n A b) ∩ Ioi 0) := by
        apply measure_mono
        intro r hr
        have hr0 : 0 < r := lt_trans zero_lt_one hr.1
        exact ⟨ne_of_gt (_root_.GD.N0232.N0720.N1377.d002855 n A b hr0), hr0⟩

theorem d002862 (n : ℕ) (A b r : ℝ) :
    HasDerivAt (fun c ↦ _root_.GD.N0232.N0720.N1377.d002851 n A c r)
      (_root_.GD.N0232.N0720.N1377.d002851 (n + 1) A b r) b := by
  have he : HasDerivAt (fun c : ℝ ↦ -A / 2 * r ^ 2 + c * r) r b := by
    simpa using ((hasDerivAt_id b).mul_const r).const_add (-A / 2 * r ^ 2)
  have hd := he.exp.const_mul (r ^ n)
  have hvalue : r ^ n * (Real.exp (-A / 2 * r ^ 2 + b * r) * r) =
      _root_.GD.N0232.N0720.N1377.d002851 (n + 1) A b r := by
    simp only [_root_.GD.N0232.N0720.N1377.d002851, pow_succ]
    ring
  rw [hvalue] at hd
  exact hd


theorem d002863 (n : ℕ) {A : ℝ} (hA : 0 < A) (b : ℝ) :
    HasDerivAt (_root_.GD.N0232.N0720.N1377.d002852 n A) (_root_.GD.N0232.N0720.N1377.d002852 (n + 1) A b) b := by
  let M : ℝ := |b| + 1
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun c r ↦ _root_.GD.N0232.N0720.N1377.d002851 n A c r)
    (F' := fun c r ↦ _root_.GD.N0232.N0720.N1377.d002851 (n + 1) A c r)
    (μ := volume.restrict (Ioi 0))
    (s := Ioo (b - 1) (b + 1))
    (bound := _root_.GD.N0232.N0720.N1377.d002857 (n + 1) A M)
    (Ioo_mem_nhds (by linarith) (by linarith))
    ?_ (_root_.GD.N0232.N0720.N1377.d002860 n hA b)
    (_root_.GD.N0232.N0720.N1377.d002853 (n + 1) A b).aestronglyMeasurable
    ?_ (_root_.GD.N0232.N0720.N1377.d002858 (n + 1) hA M) ?_).2
  · exact Eventually.of_forall fun c ↦
      (_root_.GD.N0232.N0720.N1377.d002853 n A c).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    intro c hc
    have hcM : c ≤ M := by
      dsimp [M]
      linarith [le_abs_self b, hc.2]
    have hle : _root_.GD.N0232.N0720.N1377.d002851 (n + 1) A c r ≤ _root_.GD.N0232.N0720.N1377.d002851 (n + 1) A M r := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr.le _)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hcM hr.le]
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1377.d002854 _ A c hr.le)]
    have hmajor := _root_.GD.N0232.N0720.N1377.d002859 (n + 1) hA M hr.le
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1377.d002854 _ A M hr.le)] at hmajor
    exact hle.trans hmajor
  · exact ae_of_all _ fun r c _ ↦ _root_.GD.N0232.N0720.N1377.d002862 n A c r

theorem d002864 (n : ℕ) (A b r : ℝ) :
    HasDerivAt (fun a ↦ _root_.GD.N0232.N0720.N1377.d002851 n a b r)
      (-(1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002851 (n + 2) A b r) A := by
  have he : HasDerivAt (fun a : ℝ ↦ -a / 2 * r ^ 2 + b * r)
      (-r ^ 2 / 2) A := by
    convert! (((hasDerivAt_id' A).neg.div_const 2).mul_const (r ^ 2)).add_const (b * r)
      using 1
    all_goals first | rfl | ring
  have hd := he.exp.const_mul (r ^ n)
  have hvalue : r ^ n * (Real.exp (-A / 2 * r ^ 2 + b * r) * (-r ^ 2 / 2)) =
      -(1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002851 (n + 2) A b r := by
    simp only [_root_.GD.N0232.N0720.N1377.d002851, pow_add]
    ring
  rw [hvalue] at hd
  exact hd


theorem d002865 (n : ℕ) {A : ℝ} (hA : 0 < A) (b : ℝ) :
    HasDerivAt (fun a ↦ _root_.GD.N0232.N0720.N1377.d002852 n a b)
      (-(1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 (n + 2) A b) A := by
  have hbnd : IntegrableOn
      (fun r ↦ (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002857 (n + 2) (A / 2) b r) (Ioi 0) :=
    (_root_.GD.N0232.N0720.N1377.d002858 (n + 2) (show 0 < A / 2 by positivity) b).const_mul _
  have hbound : ∀ᵐ r ∂volume.restrict (Ioi 0), ∀ a ∈ Ioo (A / 2) (2 * A),
      ‖-(1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002851 (n + 2) a b r‖ ≤
        (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002857 (n + 2) (A / 2) b r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    intro a ha
    have hle : _root_.GD.N0232.N0720.N1377.d002851 (n + 2) a b r ≤ _root_.GD.N0232.N0720.N1377.d002851 (n + 2) (A / 2) b r := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr.le _)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr ha.1.le) (sq_nonneg r)]
    rw [norm_mul, Real.norm_eq_abs (-(1 / 2 : ℝ)), abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1377.d002854 _ a b hr.le)]
    have hmajor := _root_.GD.N0232.N0720.N1377.d002859 (n + 2) (show 0 < A / 2 by positivity) b hr.le
    rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1377.d002854 _ (A / 2) b hr.le)] at hmajor
    exact hle.trans hmajor
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun a r ↦ _root_.GD.N0232.N0720.N1377.d002851 n a b r)
    (F' := fun a r ↦ -(1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002851 (n + 2) a b r)
    (μ := volume.restrict (Ioi 0)) (s := Ioo (A / 2) (2 * A))
    (bound := fun r ↦ (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002857 (n + 2) (A / 2) b r)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun a ↦ (_root_.GD.N0232.N0720.N1377.d002853 n a b).aestronglyMeasurable)
    (_root_.GD.N0232.N0720.N1377.d002860 n hA b)
    ((_root_.GD.N0232.N0720.N1377.d002853 (n + 2) A b).const_mul _).aestronglyMeasurable
    hbound hbnd (ae_of_all _ fun r a _ ↦ _root_.GD.N0232.N0720.N1377.d002864 n a b r)).2
  simpa only [_root_.GD.N0232.N0720.N1377.d002852, integral_const_mul] using hd


theorem d002866 (n : ℕ) (A b : ℝ) {s : ℝ} (hs : 0 < s) :
    _root_.GD.N0232.N0720.N1377.d002852 n (s ^ 2 * A) (s * b) =
      (s ^ (n + 1))⁻¹ * _root_.GD.N0232.N0720.N1377.d002852 n A b := by
  have hpoint (r : ℝ) : _root_.GD.N0232.N0720.N1377.d002851 n (s ^ 2 * A) (s * b) r =
      (s ^ n)⁻¹ * _root_.GD.N0232.N0720.N1377.d002851 n A b (s * r) := by
    have he : -(s ^ 2 * A) / 2 * r ^ 2 + s * b * r =
        -A / 2 * (s * r) ^ 2 + b * (s * r) := by ring
    unfold _root_.GD.N0232.N0720.N1377.d002851
    rw [he]
    simp only [mul_pow]
    field_simp [hs.ne']
  calc
    _root_.GD.N0232.N0720.N1377.d002852 n (s ^ 2 * A) (s * b) =
        (s ^ n)⁻¹ * ∫ r in Ioi 0, _root_.GD.N0232.N0720.N1377.d002851 n A b (s * r) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ hpoint)
    _ = (s ^ n)⁻¹ * (s⁻¹ * _root_.GD.N0232.N0720.N1377.d002852 n A b) := by
      rw [integral_comp_mul_left_Ioi _ _ hs]
      simp only [mul_zero, smul_eq_mul, _root_.GD.N0232.N0720.N1377.d002852]
    _ = (s ^ (n + 1))⁻¹ * _root_.GD.N0232.N0720.N1377.d002852 n A b := by
      rw [pow_succ, mul_inv]
      ring

end

end GD.N0232.N0720.N1377
