import GD.Module1429
import GD.Module0253

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0051
noncomputable section

abbrev d022792 : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

def d022793 (r : ℝ) (z : ℝ × ℝ) : ℝ :=
  (2 * (z.1 ^ 2 + z.2 ^ 2)) ^ r

def d022794 (r : ℝ) : ℝ := ∫ z, _root_.GD.N0051.d022793 r z ∂_root_.GD.N0051.d022792

theorem d022795 {x y r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hr : 0 ≤ r) :
    (x + y) ^ r ≤ 2 ^ r * (x ^ r + y ^ r) := by
  rcases le_total x y with h | h
  · have hh : (x + y) ^ r ≤ (2 * y) ^ r :=
      Real.rpow_le_rpow (by positivity) (by linarith) hr
    rw [Real.mul_rpow (by norm_num) hy] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (Real.rpow_nonneg hx _)) (by positivity))
  · have hh : (x + y) ^ r ≤ (2 * x) ^ r :=
      Real.rpow_le_rpow (by positivity) (by linarith) hr
    rw [Real.mul_rpow (by norm_num) hx] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (Real.rpow_nonneg hy _)) (by positivity))

theorem d022796 {r : ℝ} (hr : 0 ≤ r) :
    Integrable (fun x : ℝ => (x ^ 2) ^ r) (gaussianReal 0 1) := by
  have hh := (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := 1)
    (ENNReal.ofReal (2 * r)) ENNReal.ofReal_ne_top).integrable_norm_rpow'
  simp only [ENNReal.toReal_ofReal (show 0 ≤ 2 * r by positivity), id_eq] at hh
  convert hh using 1
  funext x
  rw [Real.norm_eq_abs, Real.rpow_mul (abs_nonneg x), Real.rpow_two, sq_abs]

theorem d022797 {r : ℝ} (hr : 0 ≤ r) :
    Integrable (_root_.GD.N0051.d022793 r) _root_.GD.N0051.d022792 := by
  have hi := _root_.GD.N0051.d022796 hr
  apply (((hi.comp_fst (gaussianReal 0 1)).add
    (hi.comp_snd (gaussianReal 0 1))).const_mul ((2 : ℝ) ^ r * 2 ^ r)).mono'
  · unfold _root_.GD.N0051.d022793
    fun_prop
  · apply ae_of_all
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold _root_.GD.N0051.d022793; positivity)]
    unfold _root_.GD.N0051.d022793
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    have hh := mul_le_mul_of_nonneg_left
      (_root_.GD.N0051.d022795 (sq_nonneg z.1) (sq_nonneg z.2) hr) (by positivity : 0 ≤ (2 : ℝ) ^ r)
    simpa only [mul_assoc, Pi.add_apply] using hh

theorem d022798 (r : ℝ) : 0 ≤ _root_.GD.N0051.d022794 r :=
  integral_nonneg fun z => by unfold _root_.GD.N0051.d022793; positivity

theorem d022799 {v w r : ℝ}
    (hv : 0 < v) (hw : 0 < w) (hvw : v ≤ w) (hr : 0 ≤ r) (z : ℝ × ℝ) :
    (((Real.sqrt w * z.2 - Real.sqrt v * z.1) ^ 2) / w) ^ r ≤ _root_.GD.N0051.d022793 r z := by
  unfold _root_.GD.N0051.d022793
  apply Real.rpow_le_rpow (by positivity) _ hr
  apply (div_le_iff₀ hw).mpr
  have hdiff : (Real.sqrt w * z.2 - Real.sqrt v * z.1) ^ 2 ≤
      2 * (w * z.2 ^ 2 + v * z.1 ^ 2) := by
    nlinarith [sq_nonneg (Real.sqrt w * z.2 + Real.sqrt v * z.1),
      Real.sq_sqrt hv.le, Real.sq_sqrt hw.le]
  have hh := mul_le_mul_of_nonneg_right hvw (sq_nonneg z.1)
  nlinarith

theorem d022800 {v w r : ℝ}
    (hv : 0 < v) (hw : 0 < w) (hvw : v ≤ w) (hr : 0 ≤ r) :
    Integrable (fun z : ℝ × ℝ =>
      (((Real.sqrt w * z.2 - Real.sqrt v * z.1) ^ 2) / w) ^ r) _root_.GD.N0051.d022792 ∧
    (∫ z : ℝ × ℝ, (((Real.sqrt w * z.2 - Real.sqrt v * z.1) ^ 2) / w) ^ r
      ∂_root_.GD.N0051.d022792) ≤ _root_.GD.N0051.d022794 r := by
  have hi : Integrable (fun z : ℝ × ℝ =>
      (((Real.sqrt w * z.2 - Real.sqrt v * z.1) ^ 2) / w) ^ r) _root_.GD.N0051.d022792 :=
    (_root_.GD.N0051.d022797 hr).mono' (by fun_prop) (by
      apply ae_of_all
      intro z
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact _root_.GD.N0051.d022799 hv hw hvw hr z)
  exact ⟨hi, integral_mono hi (_root_.GD.N0051.d022797 hr)
    (_root_.GD.N0051.d022799 hv hw hvw hr)⟩

#print axioms _root_.GD.N0051.d022797
#print axioms _root_.GD.N0051.d022800
end
end GD.N0051
