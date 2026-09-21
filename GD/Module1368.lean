import GD.Module0468
import GD.Module0802

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0052
noncomputable section

private theorem d022043 {a b : ℝ≥0∞} {C v : ℝ}
    (hC : 0 ≤ C) (hv : 0 ≤ v)
    (ha : a ≤ ENNReal.ofReal (C * v)) (hb : b ≤ ENNReal.ofReal (C * v)) :
    a + b ≤ ENNReal.ofReal (2 * C * v) := by
  calc
    a + b ≤ ENNReal.ofReal (C * v) + ENNReal.ofReal (C * v) := add_le_add ha hb
    _ = ENNReal.ofReal (2 * C * v) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hC hv) (mul_nonneg hC hv)]
      congr 1
      ring



theorem d022044
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : ℝ)
    (e01 e02 e12 : Ω → ℝ)
    (h01 : Measurable e01) (h02 : Measurable e02) (h12 : Measurable e12)
    {C v0 v1 v2 : ℝ} (hC : 0 ≤ C)
    (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2)
    (b01 : _root_.GD.N0052.d007228 P μ e01 ≤ ENNReal.ofReal (C * min v0 v1))
    (b02 : _root_.GD.N0052.d007228 P μ e02 ≤ ENNReal.ofReal (C * min v0 v2))
    (b12 : _root_.GD.N0052.d007228 P μ e12 ≤ ENNReal.ofReal (C * min v1 v2)) :
    _root_.GD.N0052.d007228 P μ (_root_.GD.N0052.d007226 e01 e02 e12) ≤
      ENNReal.ofReal (2 * C * min v0 (min v1 v2)) := by
  have b01a := b01.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (min_le_left v0 v1) hC))
  have b01b := b01.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (min_le_right v0 v1) hC))
  have b02a := b02.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (min_le_left v0 v2) hC))
  have b02b := b02.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (min_le_right v0 v2) hC))
  have b12a := b12.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (min_le_left v1 v2) hC))
  have b12b := b12.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (min_le_right v1 v2) hC))
  have r0 := (_root_.GD.N0052.d007229 P μ e01 e02 e12 h01 h02).trans
    (_root_.GD.N0052.d022043 hC hv0 b01a b02a)
  have r1 := (_root_.GD.N0052.d007230 P μ e01 e02 e12 h01 h12).trans
    (_root_.GD.N0052.d022043 hC hv1 b01b b12a)
  have r2 := (_root_.GD.N0052.d007231 P μ e01 e02 e12 h02 h12).trans
    (_root_.GD.N0052.d022043 hC hv2 b02b b12b)
  rcases le_total v0 (min v1 v2) with h | h
  · simpa only [min_eq_left h] using r0
  · rw [min_eq_right h]
    rcases le_total v1 v2 with h12 | h21
    · simpa only [min_eq_left h12] using r1
    · simpa only [min_eq_right h21] using r2


theorem d022045 {v0 v1 v2 : ℝ}
    (h0 : 0 < v0) (h1 : 0 < v1) (h2 : 0 < v2) :
    min v0 (min v1 v2) ≤ 3 * (v0⁻¹ + v1⁻¹ + v2⁻¹)⁻¹ := by
  let m := min v0 (min v1 v2)
  have hm : 0 < m := lt_min h0 (lt_min h1 h2)
  have h0m : m ≤ v0 := min_le_left _ _
  have h1m : m ≤ v1 := (min_le_right _ _).trans (min_le_left _ _)
  have h2m : m ≤ v2 := (min_le_right _ _).trans (min_le_right _ _)
  have hi0 := one_div_le_one_div_of_le hm h0m
  have hi1 := one_div_le_one_div_of_le hm h1m
  have hi2 := one_div_le_one_div_of_le hm h2m
  simp only [one_div] at hi0 hi1 hi2
  have hsum : v0⁻¹ + v1⁻¹ + v2⁻¹ ≤ 3 * m⁻¹ := by linarith
  have hp : 0 < v0⁻¹ + v1⁻¹ + v2⁻¹ := by positivity
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hp).mpr
  calc
    m * (v0⁻¹ + v1⁻¹ + v2⁻¹) ≤ m * (3 * m⁻¹) :=
      mul_le_mul_of_nonneg_left hsum hm.le
    _ = 3 := by field_simp

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962

def d022046 (sizes : Fin 3 → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 3) (i : Fin 3) : ℝ :=
  θ.scale i ^ 2 / (sizes i : ℝ)

theorem d022047 (sizes : Fin 3 → ℕ)
    (hn : ∀ i, 0 < sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 3) (i : Fin 3) :
    0 < _root_.GD.N0052.d022046 sizes θ i := by
  unfold _root_.GD.N0052.d022046
  exact div_pos (sq_pos_of_pos (θ.scale_pos i)) (Nat.cast_pos.mpr (hn i))

theorem d022048 (sizes : Fin 3 → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 3) :
    _root_.GD.N0232.N0719.N0963.d012141 3 sizes θ =
      ((_root_.GD.N0052.d022046 sizes θ 0)⁻¹ +
       (_root_.GD.N0052.d022046 sizes θ 1)⁻¹ +
       (_root_.GD.N0052.d022046 sizes θ 2)⁻¹)⁻¹ := by
  simp only [_root_.GD.N0232.N0719.N0963.d012141, _root_.GD.N0232.N0719.N0838.d012097,
    _root_.GD.N0232.N0719.N0838.d012096, _root_.GD.N0052.d022046,
    inv_div, Fin.sum_univ_three]




theorem d022049 (sizes : Fin 3 → ℕ) (hn : ∀ i, 0 < sizes i)
    (e01 e02 e12 : _root_.GD.N0232.N0719.N0859.d010811 3 sizes → ℝ)
    (h01 : Measurable e01) (h02 : Measurable e02) (h12 : Measurable e12)
    {C : ℝ} (hC : 0 ≤ C)
    (b01 : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 3, _root_.GD.N0232.N0719.N0859.d010840 3 sizes θ e01 ≤
      ENNReal.ofReal (C * min (_root_.GD.N0052.d022046 sizes θ 0) (_root_.GD.N0052.d022046 sizes θ 1)))
    (b02 : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 3, _root_.GD.N0232.N0719.N0859.d010840 3 sizes θ e02 ≤
      ENNReal.ofReal (C * min (_root_.GD.N0052.d022046 sizes θ 0) (_root_.GD.N0052.d022046 sizes θ 2)))
    (b12 : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 3, _root_.GD.N0232.N0719.N0859.d010840 3 sizes θ e12 ≤
      ENNReal.ofReal (C * min (_root_.GD.N0052.d022046 sizes θ 1) (_root_.GD.N0052.d022046 sizes θ 2))) :
    Measurable (_root_.GD.N0052.d007226 e01 e02 e12) ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 3, _root_.GD.N0232.N0719.N0962.d012186 3 sizes θ (_root_.GD.N0052.d007226 e01 e02 e12) ≤
        ENNReal.ofReal (6 * C) := by
  refine ⟨_root_.GD.N0052.d007227 h01 h02 h12, ?_⟩
  intro θ
  apply (_root_.GD.N0232.N0719.N0962.d012192 3 sizes (by decide) hn (6 * C) (by positivity) θ _).mpr
  have hr := _root_.GD.N0052.d022044 (_root_.GD.N0232.N0719.N0859.d010812 3 sizes θ) θ.location e01 e02 e12
    h01 h02 h12 hC
    (_root_.GD.N0052.d022047 sizes hn θ 0).le
    (_root_.GD.N0052.d022047 sizes hn θ 1).le
    (_root_.GD.N0052.d022047 sizes hn θ 2).le (b01 θ) (b02 θ) (b12 θ)
  have hm := _root_.GD.N0052.d022045
    (_root_.GD.N0052.d022047 sizes hn θ 0)
    (_root_.GD.N0052.d022047 sizes hn θ 1)
    (_root_.GD.N0052.d022047 sizes hn θ 2)
  rw [← _root_.GD.N0052.d022048] at hm
  apply hr.trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * C by positivity)]

end
end GD.N0052

#print axioms _root_.GD.N0052.d022044
#print axioms _root_.GD.N0052.d022045
#print axioms _root_.GD.N0052.d022048
#print axioms _root_.GD.N0052.d022049
