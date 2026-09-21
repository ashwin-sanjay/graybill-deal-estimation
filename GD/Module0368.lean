import GD.Module0360
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic






















set_option autoImplicit false
set_option warningAsError true

open Complex

namespace GD.N0106.N0428.N0765.N1585
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1539 ProbabilityTheory



theorem d005526 {θ : ℝ} (hθ : |θ| ≤ Real.pi) : 0 ≤ Real.cos (θ / 2) := by
  have h := abs_le.mp hθ
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> linarith

theorem d005527 {θ : ℝ} (hθ : |θ| < Real.pi / 2) : 0 < Real.cos (θ / 2) := by
  have h := abs_lt.mp hθ
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]


theorem d005528 {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hθ : |θ| ≤ Real.pi) :
    Real.cos (θ / 2) * (x + y) ≤ ‖(x : ℂ) + (y : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ := by
  have hc := _root_.GD.N0106.N0428.N0765.N1585.d005526 hθ
  have hre : ((x : ℂ) + (y : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re =
      x + y * Real.cos θ := by
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_re]
    ring
  have him : ((x : ℂ) + (y : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im = y * Real.sin θ := by
    rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.ofReal_im]
    ring
  have hcs : Real.cos (θ / 2) ^ 2 = 1 / 2 + Real.cos θ / 2 := by
    rw [Real.cos_sq, show 2 * (θ / 2) = θ by ring]
  have hs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    linarith [Real.cos_sq_add_sin_sq θ]
  have key : (x + y * Real.cos θ) * (x + y * Real.cos θ) +
      (y * Real.sin θ) * (y * Real.sin θ) - (1 / 2 + Real.cos θ / 2) * (x + y) ^ 2 =
      (1 - Real.cos θ) * (x - y) ^ 2 / 2 := by
    linear_combination (y ^ 2) * hs
  have hprod : 0 ≤ (1 - Real.cos θ) * (x - y) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr (Real.cos_le_one θ)) (sq_nonneg _)
  rw [Complex.norm_def]
  apply (Real.le_sqrt (mul_nonneg hc (add_nonneg hx hy)) (Complex.normSq_nonneg _)).mpr
  rw [Complex.normSq_apply, hre, him, mul_pow, hcs]
  linarith [key, hprod]




def d005529 (a b : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) * z) / ((beta a b : ℂ) * (1 + Complex.exp z) ^ ((a + b : ℝ) : ℂ))

theorem d005530 (a b x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1585.d005529 a b (x : ℂ) = ((_root_.GD.N0106.N0428.N0765.N1539.d005373 a b x : ℝ) : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1585.d005529 _root_.GD.N0106.N0428.N0765.N1539.d005373
  have h1 : Complex.exp ((a : ℂ) * (x : ℂ)) = ((Real.exp (a * x) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_exp]
  have h2 : (1 : ℂ) + Complex.exp (x : ℂ) = ((1 + Real.exp x : ℝ) : ℂ) := by
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_exp]
  rw [h1, h2, ← Complex.ofReal_cpow (by positivity), Complex.ofReal_div, Complex.ofReal_mul]

theorem d005531 (z : ℂ) :
    Complex.exp z = ((Real.exp z.re : ℝ) : ℂ) * Complex.exp ((z.im : ℂ) * Complex.I) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [Complex.exp_add, ← Complex.ofReal_exp]


theorem d005532 {z : ℂ} (hz : |z.im| ≤ Real.pi) :
    Real.cos (z.im / 2) * (1 + Real.exp z.re) ≤ ‖(1 : ℂ) + Complex.exp z‖ := by
  have h := _root_.GD.N0106.N0428.N0765.N1585.d005528 (x := 1) (y := Real.exp z.re) zero_le_one (Real.exp_pos _).le hz
  rw [Complex.ofReal_one] at h
  rw [_root_.GD.N0106.N0428.N0765.N1585.d005531 z]
  exact h

theorem d005533 {z : ℂ} (hz : |z.im| < Real.pi / 2) :
    0 < ((1 : ℂ) + Complex.exp z).re := by
  rw [Complex.add_re, Complex.one_re, Complex.exp_re]
  have hc := Real.cos_pos_of_mem_Ioo (abs_lt.mp hz)
  have := mul_pos (Real.exp_pos z.re) hc
  linarith

theorem d005534 {z : ℂ} (hz : |z.im| < Real.pi / 2) :
    (1 : ℂ) + Complex.exp z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (_root_.GD.N0106.N0428.N0765.N1585.d005533 hz)

theorem d005535 (a : ℝ) (z : ℂ) :
    ‖Complex.exp ((a : ℂ) * z)‖ = Real.exp (a * z.re) := by
  rw [Complex.norm_exp, Complex.re_ofReal_mul]


theorem d005536 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {z : ℂ}
    (hz : |z.im| < Real.pi / 2) :
    ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 a b z‖ ≤ Real.cos (z.im / 2) ^ (-(a + b)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 a b z.re := by
  have hc := _root_.GD.N0106.N0428.N0765.N1585.d005527 hz
  have hm : 0 < 1 + Real.exp z.re := by positivity
  have hB := beta_pos ha hb
  have hab : 0 ≤ a + b := by linarith
  have hlow := _root_.GD.N0106.N0428.N0765.N1585.d005532 (le_of_lt (lt_trans hz (by linarith [Real.pi_pos])))
  have hpow : (Real.cos (z.im / 2) * (1 + Real.exp z.re)) ^ (a + b) ≤
      ‖(1 : ℂ) + Complex.exp z‖ ^ (a + b) :=
    Real.rpow_le_rpow (mul_pos hc hm).le hlow hab
  have hnorm : ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 a b z‖ =
      Real.exp (a * z.re) / (beta a b * ‖(1 : ℂ) + Complex.exp z‖ ^ (a + b)) := by
    unfold _root_.GD.N0106.N0428.N0765.N1585.d005529
    rw [Complex.norm_div, norm_mul, Complex.norm_cpow_real, Complex.norm_of_nonneg hB.le,
      _root_.GD.N0106.N0428.N0765.N1585.d005535]
  have hcs : 0 < Real.cos (z.im / 2) ^ (a + b) := Real.rpow_pos_of_pos hc _
  have hms : 0 < (1 + Real.exp z.re) ^ (a + b) := Real.rpow_pos_of_pos hm _
  rw [hnorm]
  calc Real.exp (a * z.re) / (beta a b * ‖(1 : ℂ) + Complex.exp z‖ ^ (a + b))
      ≤ Real.exp (a * z.re) /
          (beta a b * (Real.cos (z.im / 2) * (1 + Real.exp z.re)) ^ (a + b)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le
          (mul_pos hB (Real.rpow_pos_of_pos (mul_pos hc hm) _))
          (mul_le_mul_of_nonneg_left hpow hB.le)
    _ = Real.cos (z.im / 2) ^ (-(a + b)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 a b z.re := by
        unfold _root_.GD.N0106.N0428.N0765.N1539.d005373
        rw [Real.mul_rpow hc.le hm.le, Real.rpow_neg hc.le]
        field_simp [hcs.ne', hms.ne', hB.ne'] <;> ring


theorem d005537 {z : ℂ} (hz : |z.im| < Real.pi / 2) :
    ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 ((3 : ℝ) / 2) 10 z‖ ≤
      Real.cos (z.im / 2) ^ (-((23 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 z.re := by
  have h := _root_.GD.N0106.N0428.N0765.N1585.d005536 (a := (3 : ℝ) / 2) (b := 10) (by norm_num) (by norm_num) hz
  rw [show (3 : ℝ) / 2 + 10 = 23 / 2 by norm_num] at h
  exact h


theorem d005538 {z : ℂ} (hz : |z.im| < Real.pi / 2) :
    ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 (5 : ℝ) 5 z‖ ≤
      Real.cos (z.im / 2) ^ (-(10 : ℝ)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 (5 : ℝ) 5 z.re := by
  have h := _root_.GD.N0106.N0428.N0765.N1585.d005536 (a := (5 : ℝ)) (b := 5) (by norm_num) (by norm_num) hz
  rw [show (5 : ℝ) + 5 = 10 by norm_num] at h
  exact h


theorem d005539 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    DifferentiableOn ℂ (_root_.GD.N0106.N0428.N0765.N1585.d005529 a b) {z : ℂ | |z.im| < Real.pi / 2} := by
  intro z hz
  have hslit := _root_.GD.N0106.N0428.N0765.N1585.d005534 hz
  have hnum : DifferentiableAt ℂ (fun t : ℂ => Complex.exp ((a : ℂ) * t)) z := by fun_prop
  have hbase : DifferentiableAt ℂ (fun t : ℂ => (1 : ℂ) + Complex.exp t) z := by fun_prop
  have hpow : DifferentiableAt ℂ
      (fun t : ℂ => ((1 : ℂ) + Complex.exp t) ^ ((a + b : ℝ) : ℂ)) z :=
    hbase.cpow_const hslit
  have hden : DifferentiableAt ℂ
      (fun t : ℂ => (beta a b : ℂ) * ((1 : ℂ) + Complex.exp t) ^ ((a + b : ℝ) : ℂ)) z :=
    (differentiableAt_const _).mul hpow
  have hne : (beta a b : ℂ) * ((1 : ℂ) + Complex.exp z) ^ ((a + b : ℝ) : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (beta_pos ha hb).ne'
    · rw [Ne, Complex.cpow_eq_zero_iff]
      rintro ⟨h0, _⟩
      exact Complex.slitPlane_ne_zero hslit h0
  unfold _root_.GD.N0106.N0428.N0765.N1585.d005529
  exact (hnum.div hden hne).differentiableWithinAt




def d005540 (eta : ℝ) (z : ℂ) : ℂ := Complex.exp z / (Complex.exp z + eta)


def d005541 (eta : ℝ) (z₁ z₂ : ℂ) : ℂ :=
  10 * (1 + eta) * Complex.exp z₁ * (1 + Complex.exp z₂) / (Complex.exp z₂ + eta)

theorem d005542 {eta : ℝ} (heta : 0 ≤ eta) {z : ℂ} (hz : |z.im| ≤ Real.pi) :
    Real.cos (z.im / 2) * (Real.exp z.re + eta) ≤ ‖Complex.exp z + eta‖ := by
  have h := _root_.GD.N0106.N0428.N0765.N1585.d005528 (x := eta) (y := Real.exp z.re) heta (Real.exp_pos _).le hz
  rw [_root_.GD.N0106.N0428.N0765.N1585.d005531 z, add_comm _ (eta : ℂ), add_comm (Real.exp z.re) eta]
  exact h


theorem d005543 {eta : ℝ} (heta : 0 < eta) {z : ℂ} (hz : |z.im| < Real.pi / 2) :
    ‖_root_.GD.N0106.N0428.N0765.N1585.d005540 eta z‖ ≤ (Real.cos (z.im / 2))⁻¹ := by
  have hc := _root_.GD.N0106.N0428.N0765.N1585.d005527 hz
  have he := Real.exp_pos z.re
  have hlow := _root_.GD.N0106.N0428.N0765.N1585.d005542 heta.le (le_of_lt (lt_trans hz (by linarith [Real.pi_pos])))
  have hden : 0 < Real.cos (z.im / 2) * (Real.exp z.re + eta) := by positivity
  unfold _root_.GD.N0106.N0428.N0765.N1585.d005540
  rw [Complex.norm_div, Complex.norm_exp]
  calc Real.exp z.re / ‖Complex.exp z + eta‖
      ≤ Real.exp z.re / (Real.cos (z.im / 2) * (Real.exp z.re + eta)) :=
        div_le_div_of_nonneg_left he.le hden hlow
    _ ≤ (Real.cos (z.im / 2))⁻¹ := by
        rw [div_le_iff₀ hden]
        rw [show (Real.cos (z.im / 2))⁻¹ * (Real.cos (z.im / 2) * (Real.exp z.re + eta)) =
          Real.exp z.re + eta by field_simp]
        linarith


theorem d005544 {eta : ℝ} (heta : 0 < eta) (z₁ : ℂ) {z₂ : ℂ}
    (hz : |z₂.im| < Real.pi / 2) :
    ‖_root_.GD.N0106.N0428.N0765.N1585.d005541 eta z₁ z₂‖ ≤ (Real.cos (z₂.im / 2))⁻¹ *
      (10 * (1 + eta) * Real.exp z₁.re * (1 + Real.exp z₂.re) / (Real.exp z₂.re + eta)) := by
  have hc := _root_.GD.N0106.N0428.N0765.N1585.d005527 hz
  have he1 := Real.exp_pos z₁.re
  have he2 := Real.exp_pos z₂.re
  have hlow := _root_.GD.N0106.N0428.N0765.N1585.d005542 heta.le (le_of_lt (lt_trans hz (by linarith [Real.pi_pos])))
  have hden : 0 < Real.cos (z₂.im / 2) * (Real.exp z₂.re + eta) := by positivity
  have hnum : ‖(10 : ℂ) * (1 + eta) * Complex.exp z₁ * (1 + Complex.exp z₂)‖ ≤
      10 * (1 + eta) * Real.exp z₁.re * (1 + Real.exp z₂.re) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp]
    have h10 : ‖(10 : ℂ)‖ = 10 := by simp
    have h1e : ‖(1 : ℂ) + (eta : ℂ)‖ = 1 + eta := by
      rw [show (1 : ℂ) + (eta : ℂ) = ((1 + eta : ℝ) : ℂ) by push_cast <;> ring,
        Complex.norm_of_nonneg (by linarith)]
    have hsum : ‖(1 : ℂ) + Complex.exp z₂‖ ≤ 1 + Real.exp z₂.re := by
      calc ‖(1 : ℂ) + Complex.exp z₂‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp z₂‖ := norm_add_le _ _
        _ = 1 + Real.exp z₂.re := by rw [norm_one, Complex.norm_exp]
    rw [h10, h1e]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hnn : 0 ≤ 10 * (1 + eta) * Real.exp z₁.re * (1 + Real.exp z₂.re) := by positivity
  unfold _root_.GD.N0106.N0428.N0765.N1585.d005541
  rw [Complex.norm_div]
  calc ‖(10 : ℂ) * (1 + eta) * Complex.exp z₁ * (1 + Complex.exp z₂)‖ / ‖Complex.exp z₂ + eta‖
      ≤ (10 * (1 + eta) * Real.exp z₁.re * (1 + Real.exp z₂.re)) /
          (Real.cos (z₂.im / 2) * (Real.exp z₂.re + eta)) :=
        div_le_div₀ hnn hnum hden hlow
    _ = (Real.cos (z₂.im / 2))⁻¹ *
          (10 * (1 + eta) * Real.exp z₁.re * (1 + Real.exp z₂.re) / (Real.exp z₂.re + eta)) := by
        field_simp <;> ring





theorem d005545 {G H : ℂ} {g K o : ℝ} (hG : ‖G‖ ≤ g) (hH : ‖H‖ ≤ K)
    (ho0 : 0 ≤ o) (ho1 : o ≤ 1) :
    ‖(G - o) ^ 2 - (H - o) ^ 2‖ ≤ (g + 1) ^ 2 + (K + 1) ^ 2 := by
  have hg0 : 0 ≤ g := (norm_nonneg _).trans hG
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hH
  have hoc : ‖(o : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg ho0]; exact ho1
  have h1 : ‖G - o‖ ≤ g + 1 := by
    calc ‖G - (o : ℂ)‖ ≤ ‖G‖ + ‖(o : ℂ)‖ := norm_sub_le _ _
      _ ≤ g + 1 := add_le_add hG hoc
  have h2 : ‖H - o‖ ≤ K + 1 := by
    calc ‖H - (o : ℂ)‖ ≤ ‖H‖ + ‖(o : ℂ)‖ := norm_sub_le _ _
      _ ≤ K + 1 := add_le_add hH hoc
  calc ‖(G - o) ^ 2 - (H - o) ^ 2‖ ≤ ‖(G - o) ^ 2‖ + ‖(H - o) ^ 2‖ := norm_sub_le _ _
    _ = ‖G - o‖ ^ 2 + ‖H - o‖ ^ 2 := by rw [norm_pow, norm_pow]
    _ ≤ (g + 1) ^ 2 + (K + 1) ^ 2 :=
        add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2) (pow_le_pow_left₀ (norm_nonneg _) h2 2)



theorem d005546 {eta : ℝ} (heta : 0 < eta) {z₁ z₂ : ℂ}
    (h₁ : |z₁.im| < Real.pi / 2) (h₂ : |z₂.im| < Real.pi / 2) {H : ℂ} {K : ℝ} (hH : ‖H‖ ≤ K)
    {o : ℝ} (ho0 : 0 ≤ o) (ho1 : o ≤ 1) :
    ‖_root_.GD.N0106.N0428.N0765.N1585.d005529 ((3 : ℝ) / 2) 10 z₁ * _root_.GD.N0106.N0428.N0765.N1585.d005529 (5 : ℝ) 5 z₂ *
        ((_root_.GD.N0106.N0428.N0765.N1585.d005540 eta z₂ - o) ^ 2 - (H - o) ^ 2)‖ ≤
      (Real.cos (z₁.im / 2) ^ (-((23 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 z₁.re) *
        (Real.cos (z₂.im / 2) ^ (-(10 : ℝ)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 (5 : ℝ) 5 z₂.re) *
        (((Real.cos (z₂.im / 2))⁻¹ + 1) ^ 2 + (K + 1) ^ 2) := by
  rw [norm_mul, norm_mul]
  have hA := _root_.GD.N0106.N0428.N0765.N1585.d005537 h₁
  have hB := _root_.GD.N0106.N0428.N0765.N1585.d005538 h₂
  have hC := _root_.GD.N0106.N0428.N0765.N1585.d005545 (_root_.GD.N0106.N0428.N0765.N1585.d005543 heta h₂) hH ho0 ho1
  have hA0 : 0 ≤ Real.cos (z₁.im / 2) ^ (-((23 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 z₁.re :=
    mul_nonneg (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1585.d005527 h₁).le _)
      (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) _).le
  have hB0 : 0 ≤ Real.cos (z₂.im / 2) ^ (-(10 : ℝ)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 (5 : ℝ) 5 z₂.re :=
    mul_nonneg (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1585.d005527 h₂).le _)
      (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) _).le
  exact mul_le_mul (mul_le_mul hA hB (norm_nonneg _) hA0) hC (norm_nonneg _)
    (mul_nonneg hA0 hB0)

end
end GD.N0106.N0428.N0765.N1585

#print axioms _root_.GD.N0106.N0428.N0765.N1585.d005528
#print axioms _root_.GD.N0106.N0428.N0765.N1585.d005530
#print axioms _root_.GD.N0106.N0428.N0765.N1585.d005536
#print axioms _root_.GD.N0106.N0428.N0765.N1585.d005539
#print axioms _root_.GD.N0106.N0428.N0765.N1585.d005543
#print axioms _root_.GD.N0106.N0428.N0765.N1585.d005544
#print axioms _root_.GD.N0106.N0428.N0765.N1585.d005546
