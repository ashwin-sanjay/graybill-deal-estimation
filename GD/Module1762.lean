import GD.Module1741
import GD.Module1305
import GD.Module0368
import GD.Module1318
import GD.Module1298
import GD.Module1761
import GD.Module0364
















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set

namespace GD.N0106.N0428.N0765.N1512
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1539 _root_.GD.N0106.N0428.N0765.N1585 _root_.GD.N0106.N0428.N0765.N1627 _root_.GD.N0106.N0428.N0765.N1529
open _root_.GD.N0106.N0428.N0765.N1607 _root_.GD.N0106.N0428.N0765.N1521
open _root_.GD.N0106.N0428.N0765.N1550
open _root_.GD.N0232.N0720.N1249




def d029143 (k : ℕ) (K : ℝ) : ℝ := K * (1 + K) * (K + 1 / 2) ^ k


def d029144 (k : ℕ) (H : ℂ) : ℂ := H * (1 - H) * (H - 1 / 2) ^ k

theorem d029145 (k : ℕ) (h : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1512.d029144 k (h : ℂ) = ((_root_.GD.N0232.N0720.N1249.d002197 k h : ℝ) : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1512.d029144 _root_.GD.N0232.N0720.N1249.d002197
  push_cast <;> ring

theorem d029146 {H : ℂ} {K : ℝ} (hH : ‖H‖ ≤ K) (k : ℕ) :
    ‖_root_.GD.N0106.N0428.N0765.N1512.d029144 k H‖ ≤ _root_.GD.N0106.N0428.N0765.N1512.d029143 k K := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hH
  have h1 : ‖(1 : ℂ) - H‖ ≤ 1 + K := by
    calc ‖(1 : ℂ) - H‖ ≤ ‖(1 : ℂ)‖ + ‖H‖ := norm_sub_le _ _
      _ ≤ 1 + K := by rw [norm_one]; exact _root_.add_le_add le_rfl hH
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
    norm_num [norm_div]
  have h2 : ‖H - 1 / 2‖ ≤ K + 1 / 2 := by
    calc ‖H - (1 / 2 : ℂ)‖ ≤ ‖H‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ K + 1 / 2 := by rw [h12]; exact _root_.add_le_add hH le_rfl
  unfold _root_.GD.N0106.N0428.N0765.N1512.d029144 _root_.GD.N0106.N0428.N0765.N1512.d029143
  rw [norm_mul, norm_mul, norm_pow]
  exact mul_le_mul (mul_le_mul hH h1 (norm_nonneg _) hK0)
    (pow_le_pow_left₀ (norm_nonneg _) h2 k) (pow_nonneg (norm_nonneg _) k)
    (mul_nonneg hK0 (by linarith))

theorem d029147 {H : ℂ} {K : ℝ} (hH : ‖H‖ ≤ K) (k : ℕ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1512.d029143 k K :=
  (norm_nonneg _).trans (_root_.GD.N0106.N0428.N0765.N1512.d029146 hH k)



theorem d029148 {eta : ℝ} (heta : 0 < eta) {H : ℂ} {K : ℝ} (hH : ‖H‖ ≤ K) :
    ‖H - (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta : ℂ)‖ ≤ K + 1 := by
  have ho := _root_.GD.N0106.N0428.N0765.N1607.d012680 eta heta
  calc ‖H - (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta : ℂ)‖ ≤ ‖H‖ + ‖(_root_.GD.N0106.N0428.N0765.N1607.d012678 eta : ℂ)‖ := norm_sub_le _ _
    _ ≤ K + 1 := by
      rw [Complex.norm_of_nonneg ho.1]
      exact _root_.add_le_add hH ho.2


theorem d029149 {eta : ℝ} (heta : 1 ≤ eta) (a b : ℝ) :
    10 * (1 + eta) * Real.exp a * (1 + Real.exp b) / (Real.exp b + eta) ≤
      10 * (1 + eta) * Real.exp a := by
  have heta0 : 0 < eta := by linarith
  have hb := Real.exp_pos b
  have hden : 0 < Real.exp b + eta := by linarith
  have hX : 0 ≤ 10 * (1 + eta) * Real.exp a := by positivity
  rw [div_le_iff₀ hden]
  nlinarith [mul_nonneg hX (sub_nonneg.mpr heta)]


theorem d029150 {eta : ℝ} (heta : 1 ≤ eta) (z₁ : ℂ) {z₂ : ℂ}
    (hz : |z₂.im| < Real.pi / 2) :
    ‖_root_.GD.N0106.N0428.N0765.N1585.d005541 eta z₁ z₂‖ ≤ (Real.cos (z₂.im / 2))⁻¹ * (10 * (1 + eta) * Real.exp z₁.re) := by
  have heta0 : 0 < eta := by linarith
  refine (_root_.GD.N0106.N0428.N0765.N1585.d005544 heta0 z₁ hz).trans ?_
  exact mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1512.d029149 heta z₁.re z₂.re)
    (inv_nonneg.mpr (_root_.GD.N0106.N0428.N0765.N1585.d005527 hz).le)

theorem d029151 {z : ℂ} (hz : |z.im| < Real.pi / 2) :
    0 ≤ Real.cos (z.im / 2) ^ (-((23 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 z.re :=
  mul_nonneg (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1585.d005527 hz).le _)
    (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) _).le

theorem d029152 {z : ℂ} (hz : |z.im| < Real.pi / 2) :
    0 ≤ Real.cos (z.im / 2) ^ (-(10 : ℝ)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 (5 : ℝ) 5 z.re :=
  mul_nonneg (Real.rpow_nonneg (_root_.GD.N0106.N0428.N0765.N1585.d005527 hz).le _)
    (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) _).le




def d029153 (k : ℕ) (eta : ℝ) (H z₁ z₂ : ℂ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1585.d005529 ((3 : ℝ) / 2) 10 z₁ * _root_.GD.N0106.N0428.N0765.N1585.d005529 (5 : ℝ) 5 z₂ *
    ((H - (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta : ℂ)) * (-_root_.GD.N0106.N0428.N0765.N1512.d029144 k H))


def d029154 (k : ℕ) (eta : ℝ) (H z₁ z₂ : ℂ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1585.d005529 ((3 : ℝ) / 2) 10 z₁ * _root_.GD.N0106.N0428.N0765.N1585.d005529 (5 : ℝ) 5 z₂ *
    ((H - (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta : ℂ)) * (_root_.GD.N0106.N0428.N0765.N1512.d029144 k H * _root_.GD.N0106.N0428.N0765.N1585.d005541 eta z₁ z₂))

theorem d029155 {eta : ℝ} (heta : 0 < eta) {z₁ z₂ : ℂ}
    (h₁ : |z₁.im| < Real.pi / 2) (h₂ : |z₂.im| < Real.pi / 2) {H : ℂ} {K : ℝ} (hH : ‖H‖ ≤ K)
    (k : ℕ) :
    ‖_root_.GD.N0106.N0428.N0765.N1512.d029153 k eta H z₁ z₂‖ ≤
      (Real.cos (z₁.im / 2) ^ (-((23 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 z₁.re) *
        (Real.cos (z₂.im / 2) ^ (-(10 : ℝ)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 (5 : ℝ) 5 z₂.re) *
        ((K + 1) * _root_.GD.N0106.N0428.N0765.N1512.d029143 k K) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hH
  have hA := _root_.GD.N0106.N0428.N0765.N1585.d005537 h₁
  have hB := _root_.GD.N0106.N0428.N0765.N1585.d005538 h₂
  have hA0 := _root_.GD.N0106.N0428.N0765.N1512.d029151 h₁
  have hB0 := _root_.GD.N0106.N0428.N0765.N1512.d029152 h₂
  have hC : ‖(H - (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta : ℂ)) * (-_root_.GD.N0106.N0428.N0765.N1512.d029144 k H)‖ ≤ (K + 1) * _root_.GD.N0106.N0428.N0765.N1512.d029143 k K := by
    rw [norm_mul, norm_neg]
    exact mul_le_mul (_root_.GD.N0106.N0428.N0765.N1512.d029148 heta hH) (_root_.GD.N0106.N0428.N0765.N1512.d029146 hH k)
      (norm_nonneg _) (by linarith)
  unfold _root_.GD.N0106.N0428.N0765.N1512.d029153
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hA hB (norm_nonneg _) hA0) hC (norm_nonneg _) (mul_nonneg hA0 hB0)

theorem d029156 {eta : ℝ} (heta : 1 ≤ eta) {z₁ z₂ : ℂ}
    (h₁ : |z₁.im| < Real.pi / 2) (h₂ : |z₂.im| < Real.pi / 2) {H : ℂ} {K : ℝ} (hH : ‖H‖ ≤ K)
    (k : ℕ) :
    ‖_root_.GD.N0106.N0428.N0765.N1512.d029154 k eta H z₁ z₂‖ ≤
      (Real.cos (z₁.im / 2) ^ (-((23 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 z₁.re) *
        (Real.cos (z₂.im / 2) ^ (-(10 : ℝ)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 (5 : ℝ) 5 z₂.re) *
        ((K + 1) * _root_.GD.N0106.N0428.N0765.N1512.d029143 k K * ((Real.cos (z₂.im / 2))⁻¹ * (10 * (1 + eta) * Real.exp z₁.re))) := by
  have heta0 : 0 < eta := by linarith
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hH
  have hQ0 := _root_.GD.N0106.N0428.N0765.N1512.d029147 hH k
  have hA := _root_.GD.N0106.N0428.N0765.N1585.d005537 h₁
  have hB := _root_.GD.N0106.N0428.N0765.N1585.d005538 h₂
  have hA0 := _root_.GD.N0106.N0428.N0765.N1512.d029151 h₁
  have hB0 := _root_.GD.N0106.N0428.N0765.N1512.d029152 h₂
  have hC : ‖(H - (_root_.GD.N0106.N0428.N0765.N1607.d012678 eta : ℂ)) * (_root_.GD.N0106.N0428.N0765.N1512.d029144 k H * _root_.GD.N0106.N0428.N0765.N1585.d005541 eta z₁ z₂)‖ ≤
      (K + 1) * _root_.GD.N0106.N0428.N0765.N1512.d029143 k K * ((Real.cos (z₂.im / 2))⁻¹ * (10 * (1 + eta) * Real.exp z₁.re)) := by
    rw [norm_mul, norm_mul, ← mul_assoc]
    exact mul_le_mul
      (mul_le_mul (_root_.GD.N0106.N0428.N0765.N1512.d029148 heta0 hH) (_root_.GD.N0106.N0428.N0765.N1512.d029146 hH k)
        (norm_nonneg _) (by linarith))
      (_root_.GD.N0106.N0428.N0765.N1512.d029150 heta z₁ h₂) (norm_nonneg _) (mul_nonneg (by linarith) hQ0)
  unfold _root_.GD.N0106.N0428.N0765.N1512.d029154
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul hA hB (norm_nonneg _) hA0) hC (norm_nonneg _) (mul_nonneg hA0 hB0)




def d029157 (α x : ℝ) : ℝ := Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 x


def d029158 (β y : ℝ) : ℝ := Real.cos (β / 2) ^ (-(10 : ℝ)) * _root_.GD.N0106.N0428.N0765.N1539.d005373 (5 : ℝ) 5 y


def d029159 (α eta x : ℝ) : ℝ :=
  Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) * (10 * (1 + eta)) *
    (Real.exp x * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 x)

theorem d029160 (α : ℝ) : Integrable (_root_.GD.N0106.N0428.N0765.N1512.d029157 α) := by
  unfold _root_.GD.N0106.N0428.N0765.N1512.d029157
  exact (_root_.GD.N0106.N0428.N0765.N1539.d005379 (by norm_num) (by norm_num)).const_mul _

theorem d029161 (β : ℝ) : Integrable (_root_.GD.N0106.N0428.N0765.N1512.d029158 β) := by
  unfold _root_.GD.N0106.N0428.N0765.N1512.d029158
  exact (_root_.GD.N0106.N0428.N0765.N1539.d005379 (by norm_num) (by norm_num)).const_mul _

theorem d029162 (α : ℝ) : (∫ x, _root_.GD.N0106.N0428.N0765.N1512.d029157 α x) = Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) := by
  unfold _root_.GD.N0106.N0428.N0765.N1512.d029157
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1539.d005380 (by norm_num) (by norm_num), mul_one]

theorem d029163 (β : ℝ) : (∫ y, _root_.GD.N0106.N0428.N0765.N1512.d029158 β y) = Real.cos (β / 2) ^ (-(10 : ℝ)) := by
  unfold _root_.GD.N0106.N0428.N0765.N1512.d029158
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1539.d005380 (by norm_num) (by norm_num), mul_one]



theorem d029164 : beta ((5 : ℝ) / 2) 9 = beta ((3 : ℝ) / 2) 10 / 6 := by
  have hL := _root_.GD.N0235.d004038 (α := (3 : ℝ) / 2) (β := 9)
    (by norm_num) (by norm_num)
  have hR := _root_.GD.N0235.d004039 (α := (3 : ℝ) / 2) (β := 9)
    (by norm_num) (by norm_num)
  norm_num at hL hR
  rw [hL, hR]
  ring


theorem d029165 (x : ℝ) :
    Real.exp x * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 x = (1 / 6 : ℝ) * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((5 : ℝ) / 2) 9 x := by
  unfold _root_.GD.N0106.N0428.N0765.N1539.d005373
  rw [_root_.GD.N0106.N0428.N0765.N1512.d029164, show (3 : ℝ) / 2 + 10 = 23 / 2 by norm_num,
    show (5 : ℝ) / 2 + 9 = 23 / 2 by norm_num]
  have hB : 0 < beta ((3 : ℝ) / 2) 10 := beta_pos (by norm_num) (by norm_num)
  have hP : 0 < (1 + Real.exp x) ^ ((23 : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have he : Real.exp x * Real.exp (3 / 2 * x) = Real.exp (5 / 2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_div_assoc, he]
  field_simp [hB.ne', hP.ne'] <;> ring

theorem d029166 :
    Integrable (fun x : ℝ => Real.exp x * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 x) := by
  have h : (fun x : ℝ => Real.exp x * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 x) =
      fun x => (1 / 6 : ℝ) * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((5 : ℝ) / 2) 9 x := funext _root_.GD.N0106.N0428.N0765.N1512.d029165
  rw [h]
  exact (_root_.GD.N0106.N0428.N0765.N1539.d005379 (by norm_num) (by norm_num)).const_mul _

theorem d029167 :
    (∫ x, Real.exp x * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 x) = 1 / 6 := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1512.d029165]
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1539.d005380 (by norm_num) (by norm_num), mul_one]

theorem d029168 (α eta : ℝ) : Integrable (_root_.GD.N0106.N0428.N0765.N1512.d029159 α eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1512.d029159
  exact _root_.GD.N0106.N0428.N0765.N1512.d029166.const_mul _


theorem d029169 (α eta : ℝ) :
    (∫ x, _root_.GD.N0106.N0428.N0765.N1512.d029159 α eta x) = Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) * (10 * (1 + eta)) * (1 / 6) := by
  unfold _root_.GD.N0106.N0428.N0765.N1512.d029159
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1512.d029167]

theorem d029170 (α β C : ℝ) :
    Integrable (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029157 α q.1 * (C * _root_.GD.N0106.N0428.N0765.N1512.d029158 β q.2)) := by
  rw [Measure.volume_eq_prod]
  exact (_root_.GD.N0106.N0428.N0765.N1512.d029160 α).mul_prod ((_root_.GD.N0106.N0428.N0765.N1512.d029161 β).const_mul C)

theorem d029171 (α β C : ℝ) :
    (∫ q : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1512.d029157 α q.1 * (C * _root_.GD.N0106.N0428.N0765.N1512.d029158 β q.2)) =
      Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) * (C * Real.cos (β / 2) ^ (-(10 : ℝ))) := by
  rw [Measure.volume_eq_prod, integral_prod_mul (f := _root_.GD.N0106.N0428.N0765.N1512.d029157 α) (g := fun y => C * _root_.GD.N0106.N0428.N0765.N1512.d029158 β y),
    integral_const_mul, _root_.GD.N0106.N0428.N0765.N1512.d029162, _root_.GD.N0106.N0428.N0765.N1512.d029163]

theorem d029172 (α β C eta : ℝ) :
    Integrable (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029159 α eta q.1 * (C * _root_.GD.N0106.N0428.N0765.N1512.d029158 β q.2)) := by
  rw [Measure.volume_eq_prod]
  exact (_root_.GD.N0106.N0428.N0765.N1512.d029168 α eta).mul_prod ((_root_.GD.N0106.N0428.N0765.N1512.d029161 β).const_mul C)

theorem d029173 (α β C eta : ℝ) :
    (∫ q : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1512.d029159 α eta q.1 * (C * _root_.GD.N0106.N0428.N0765.N1512.d029158 β q.2)) =
      Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) * (10 * (1 + eta)) * (1 / 6) *
        (C * Real.cos (β / 2) ^ (-(10 : ℝ))) := by
  rw [Measure.volume_eq_prod,
    integral_prod_mul (f := _root_.GD.N0106.N0428.N0765.N1512.d029159 α eta) (g := fun y => C * _root_.GD.N0106.N0428.N0765.N1512.d029158 β y),
    integral_const_mul, _root_.GD.N0106.N0428.N0765.N1512.d029169, _root_.GD.N0106.N0428.N0765.N1512.d029163]



theorem d029174 (k : Fin 5) (h z : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1627.d021101 (k, 0) h z = -_root_.GD.N0232.N0720.N1249.d002197 k.val h := rfl

theorem d029175 (k : Fin 5) (h z : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1627.d021101 (k, 1) h z = _root_.GD.N0232.N0720.N1249.d002197 k.val h * z := rfl


theorem d029176 {eta : ℝ} (heta : 0 < eta) (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1529.d020801 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q) =
      10 * (1 + eta) * Real.exp q.1 * (1 + Real.exp q.2) / (Real.exp q.2 + eta) := by
  have h0 : _root_.GD.N0106.N0428.N0765.N1521.d020862 q 0 = Real.sigmoid q.1 := rfl
  have h1 : _root_.GD.N0106.N0428.N0765.N1521.d020862 q 1 = (1 - Real.sigmoid q.1) * Real.sigmoid q.2 := rfl
  have h2 : _root_.GD.N0106.N0428.N0765.N1521.d020862 q 2 = (1 - Real.sigmoid q.1) * (1 - Real.sigmoid q.2) := rfl
  have ha : (1 + Real.exp q.1) ≠ 0 := by positivity
  have hb : (1 + Real.exp q.2) ≠ 0 := by positivity
  have hbe : Real.exp q.2 + eta ≠ 0 := by positivity
  have hden : (1 - Real.sigmoid q.1) * Real.sigmoid q.2 +
      eta * ((1 - Real.sigmoid q.1) * (1 - Real.sigmoid q.2)) =
      (Real.exp q.2 + eta) / ((1 + Real.exp q.1) * (1 + Real.exp q.2)) := by
    rw [_root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005370, _root_.GD.N0106.N0428.N0765.N1539.d005369]
    field_simp <;> ring
  unfold _root_.GD.N0106.N0428.N0765.N1529.d020801
  rw [h0, h1, h2, hden, _root_.GD.N0106.N0428.N0765.N1539.d005369]
  field_simp <;> ring

theorem d029177 (eta a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1585.d005541 eta (a : ℂ) (b : ℂ) =
      ((10 * (1 + eta) * Real.exp a * (1 + Real.exp b) / (Real.exp b + eta) : ℝ) : ℂ) := by
  unfold _root_.GD.N0106.N0428.N0765.N1585.d005541
  push_cast <;> ring



theorem d029178 (k : Fin 5) (eta : ℝ) (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1512.d029153 k.val eta (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q) : ℂ) (q.1 : ℂ) (q.2 : ℂ) =
      ((_root_.GD.N0106.N0428.N0765.N1521.d020868 q * _root_.GD.N0106.N0428.N0765.N1627.d021104 (k, 0) eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q) : ℝ) : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1512.d029153, _root_.GD.N0106.N0428.N0765.N1627.d021104, _root_.GD.N0106.N0428.N0765.N1627.d021102, _root_.GD.N0106.N0428.N0765.N1512.d029174,
    _root_.GD.N0106.N0428.N0765.N1521.d020868, _root_.GD.N0106.N0428.N0765.N1585.d005530, _root_.GD.N0106.N0428.N0765.N1585.d005530, _root_.GD.N0106.N0428.N0765.N1512.d029145]
  push_cast <;> ring


theorem d029179 (k : Fin 5) {eta : ℝ} (heta : 0 < eta) (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1512.d029154 k.val eta (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q) : ℂ) (q.1 : ℂ) (q.2 : ℂ) =
      ((_root_.GD.N0106.N0428.N0765.N1521.d020868 q * _root_.GD.N0106.N0428.N0765.N1627.d021104 (k, 1) eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q) : ℝ) : ℂ) := by
  rw [_root_.GD.N0106.N0428.N0765.N1512.d029154, _root_.GD.N0106.N0428.N0765.N1627.d021104, _root_.GD.N0106.N0428.N0765.N1627.d021102, _root_.GD.N0106.N0428.N0765.N1512.d029175,
    _root_.GD.N0106.N0428.N0765.N1521.d020868, _root_.GD.N0106.N0428.N0765.N1585.d005530, _root_.GD.N0106.N0428.N0765.N1585.d005530, _root_.GD.N0106.N0428.N0765.N1512.d029145,
    _root_.GD.N0106.N0428.N0765.N1512.d029177, _root_.GD.N0106.N0428.N0765.N1512.d029176 heta q]
  push_cast <;> ring



theorem d029180 (location eta : ℝ) (heta : 0 < eta) (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    _root_.GD.N0106.N0428.N0765.N1627.d021105 location eta j =
      ((1 + eta) / 11) *
        ∫ q : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1521.d020868 q * _root_.GD.N0106.N0428.N0765.N1627.d021104 j eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q) := by
  rw [_root_.GD.N0106.N0428.N0765.N1627.d021114 location eta heta j,
    _root_.GD.N0106.N0428.N0765.N1521.d020870 (_root_.GD.N0106.N0428.N0765.N1627.d021104 j eta) (_root_.GD.N0106.N0428.N0765.N1627.d021108 j eta)]




open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1672



def d029181 (eta : ℝ) (z w : ℂ) : ℂ :=
  ((eta⁻¹ : ℝ) : ℂ) * _root_.GD.N0106.N0428.N0765.N1677.d028883 eta⁻¹ z w

theorem d029182 {eta : ℝ} (heta : 0 < eta) {z w : ℂ}
    (hs : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    _root_.GD.N0106.N0428.N0765.N1512.d029181 eta z w = _root_.GD.N0106.N0428.N0765.N1538.d021244 eta⁻¹ z.re w.re z.im w.im /
      _root_.GD.N0106.N0428.N0765.N1538.d021243 eta⁻¹ z.re w.re z.im w.im := by
  have h := _root_.GD.N0106.N0428.N0765.N1672.d021429 (inv_pos.mpr heta) z.re w.re z.im w.im
    (_root_.GD.N0106.N0428.N0765.N1538.d021233 hs)
  simp only [_root_.GD.N0106.N0428.N0765.N1538.d021247, inv_inv] at h
  unfold _root_.GD.N0106.N0428.N0765.N1512.d029181 _root_.GD.N0106.N0428.N0765.N1677.d028883
  rw [← h, ← mul_assoc]
  have hi : ((eta⁻¹ : ℝ) : ℂ) * (eta : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ heta.ne', Complex.ofReal_one]
  rw [hi, one_mul]

def d029183 (α β : ℝ) : ℝ := (_root_.GD.N0106.N0428.N0765.N1538.d021231 α β)⁻¹

theorem d029184 {eta : ℝ} (heta : 0 < eta) {z w : ℂ}
    (hs : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    ‖_root_.GD.N0106.N0428.N0765.N1512.d029181 eta z w‖ ≤ _root_.GD.N0106.N0428.N0765.N1512.d029183 z.im w.im := by
  rw [_root_.GD.N0106.N0428.N0765.N1512.d029182 heta hs]
  exact _root_.GD.N0106.N0428.N0765.N1583.d021339 heta z.re w.re z.im w.im hs

theorem d029185 {eta : ℝ} (heta : 0 < eta) (a b : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1512.d029181 eta (a : ℂ) (b : ℂ) = (_root_.GD.N0106.N0428.N0765.N1529.d020799 eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 (a, b)) : ℂ) := by
  have hs : _root_.GD.N0106.N0428.N0765.N1677.d028882 (a : ℂ) (b : ℂ) := by
    simpa [_root_.GD.N0106.N0428.N0765.N1677.d028882, _root_.GD.N0106.N0428.N0765.N1538.d021192] using Real.pi_pos
  rw [_root_.GD.N0106.N0428.N0765.N1512.d029182 heta hs]
  exact _root_.GD.N0106.N0428.N0765.N1583.d021340 heta a b

theorem d029186 {eta : ℝ} (heta : 0 < eta) {z w : ℂ}
    (hs : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1512.d029181 eta q w) z :=
  (_root_.GD.N0106.N0428.N0765.N1677.d028888 (inv_pos.mpr heta).le hs).differentiableAt.const_mul _

theorem d029187 {eta : ℝ} (heta : 0 < eta) {z w : ℂ}
    (hs : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1512.d029181 eta z q) w :=
  (_root_.GD.N0106.N0428.N0765.N1677.d028889 (inv_pos.mpr heta).le hs).differentiableAt.const_mul _

theorem d029188 {eta : ℝ} (heta : 0 < eta) {w : ℂ}
    (hw : |w.im| < Real.pi / 2) : Complex.exp w + (eta : ℂ) ≠ 0 := by
  have hc : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo (abs_lt.mp hw)
  have hp : 0 < (Complex.exp w + (eta : ℂ)).re := by
    simp only [Complex.add_re, Complex.exp_re, Complex.ofReal_re]
    positivity
  exact fun h => hp.ne' (by rw [h]; rfl)

theorem d029189 (eta : ℝ) (z w : ℂ) :
    DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1585.d005541 eta q w) z := by
  unfold _root_.GD.N0106.N0428.N0765.N1585.d005541
  fun_prop

theorem d029190 {eta : ℝ} (heta : 0 < eta) (z : ℂ) {w : ℂ}
    (hw : |w.im| < Real.pi / 2) :
    DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1585.d005541 eta z q) w := by
  have hn : DifferentiableAt ℂ
      (fun q : ℂ => 10 * (1 + (eta : ℂ)) * Complex.exp z * (1 + Complex.exp q)) w := by
    fun_prop
  have hd : DifferentiableAt ℂ (fun q : ℂ => Complex.exp q + (eta : ℂ)) w := by fun_prop
  exact hn.div hd (_root_.GD.N0106.N0428.N0765.N1512.d029188 heta hw)


def d029191 (channel : Bool) (k : ℕ) (eta : ℝ) (z w : ℂ) : ℂ :=
  (((1 + eta) / 11 : ℝ) : ℂ) *
    if channel then _root_.GD.N0106.N0428.N0765.N1512.d029154 k eta (_root_.GD.N0106.N0428.N0765.N1512.d029181 eta z w) z w
    else _root_.GD.N0106.N0428.N0765.N1512.d029153 k eta (_root_.GD.N0106.N0428.N0765.N1512.d029181 eta z w) z w

theorem d029192 (channel : Bool) (k : ℕ) {eta : ℝ}
    (heta : 0 < eta) {z w : ℂ} (hs : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta q w) z := by
  have hphase := (_root_.GD.N0106.N0428.N0765.N1537.d021535 hs).1
  have hopen : IsOpen {q : ℂ | |q.im| < Real.pi / 2} :=
    isOpen_Iio.preimage (continuous_abs.comp Complex.continuous_im)
  have hd := ((_root_.GD.N0106.N0428.N0765.N1585.d005539 (a := (3 : ℝ) / 2) (b := 10)
    (by norm_num) (by norm_num)) z hphase).differentiableAt (hopen.mem_nhds hphase)
  have hH := _root_.GD.N0106.N0428.N0765.N1512.d029186 heta hs
  have hq : DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1512.d029144 k (_root_.GD.N0106.N0428.N0765.N1512.d029181 eta q w)) z := by
    unfold _root_.GD.N0106.N0428.N0765.N1512.d029144
    fun_prop
  have hF := _root_.GD.N0106.N0428.N0765.N1512.d029189 eta z w
  cases channel <;> simp only [_root_.GD.N0106.N0428.N0765.N1512.d029191, Bool.false_eq_true, ↓reduceIte,
    _root_.GD.N0106.N0428.N0765.N1512.d029153, _root_.GD.N0106.N0428.N0765.N1512.d029154]
  · exact (((hd.mul_const _).mul ((hH.sub_const _).mul hq.neg)).const_mul _)
  · exact (((hd.mul_const _).mul ((hH.sub_const _).mul (hq.mul hF))).const_mul _)

theorem d029193 (channel : Bool) (k : ℕ) {eta : ℝ}
    (heta : 0 < eta) {z w : ℂ} (hs : _root_.GD.N0106.N0428.N0765.N1677.d028882 z w) :
    DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta z q) w := by
  have hphase := (_root_.GD.N0106.N0428.N0765.N1537.d021535 hs).2
  have hopen : IsOpen {q : ℂ | |q.im| < Real.pi / 2} :=
    isOpen_Iio.preimage (continuous_abs.comp Complex.continuous_im)
  have hd := ((_root_.GD.N0106.N0428.N0765.N1585.d005539 (a := (5 : ℝ)) (b := 5)
    (by norm_num) (by norm_num)) w hphase).differentiableAt (hopen.mem_nhds hphase)
  have hH := _root_.GD.N0106.N0428.N0765.N1512.d029187 heta hs
  have hq : DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1512.d029144 k (_root_.GD.N0106.N0428.N0765.N1512.d029181 eta z q)) w := by
    unfold _root_.GD.N0106.N0428.N0765.N1512.d029144
    fun_prop
  have hF := _root_.GD.N0106.N0428.N0765.N1512.d029190 heta z hphase
  cases channel <;> simp only [_root_.GD.N0106.N0428.N0765.N1512.d029191, Bool.false_eq_true, ↓reduceIte,
    _root_.GD.N0106.N0428.N0765.N1512.d029153, _root_.GD.N0106.N0428.N0765.N1512.d029154]
  · exact (((hd.const_mul _).mul ((hH.sub_const _).mul hq.neg)).const_mul _)
  · exact (((hd.const_mul _).mul ((hH.sub_const _).mul (hq.mul hF))).const_mul _)

def d029194 (channel : Bool) (k : ℕ) (eta α β : ℝ) (q : ℝ × ℝ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1512.d029191 channel k eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β)

theorem d029195 (eta α β : ℝ) :
    Measurable (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1512.d029181 eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β)) := by
  have h := (_root_.GD.N0106.N0428.N0765.N1675.d021518 eta⁻¹ α β).const_mul
    ((eta⁻¹ : ℝ) : ℂ)
  simpa only [_root_.GD.N0106.N0428.N0765.N1512.d029181, _root_.GD.N0106.N0428.N0765.N1677.d028883,
    _root_.GD.N0106.N0428.N0765.N1675.d021510, _root_.GD.N0106.N0428.N0765.N1550.d005476, _root_.GD.N0106.N0428.N0765.N1550.d005477] using h

theorem d029196 (channel : Bool) (k : ℕ) (eta α β : ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β) := by
  have hz : Measurable (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) := by unfold _root_.GD.N0106.N0428.N0765.N1550.d005473; fun_prop
  have hw : Measurable (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) := by unfold _root_.GD.N0106.N0428.N0765.N1550.d005473; fun_prop
  have hA := (_root_.GD.N0106.N0428.N0765.N1537.d021548 ((3 : ℝ) / 2) 10).comp hz
  have hB := (_root_.GD.N0106.N0428.N0765.N1537.d021548 5 5).comp hw
  have hH := _root_.GD.N0106.N0428.N0765.N1512.d029195 eta α β
  have hF : Measurable (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1585.d005541 eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β)) := by
    unfold _root_.GD.N0106.N0428.N0765.N1585.d005541
    fun_prop
  cases channel <;> unfold _root_.GD.N0106.N0428.N0765.N1512.d029194 _root_.GD.N0106.N0428.N0765.N1512.d029191 _root_.GD.N0106.N0428.N0765.N1512.d029153 _root_.GD.N0106.N0428.N0765.N1512.d029154 _root_.GD.N0106.N0428.N0765.N1512.d029144 <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

def d029197 (k : ℕ) (eta α β : ℝ) : ℝ :=
  (1 + eta) / 11 * ((_root_.GD.N0106.N0428.N0765.N1512.d029183 α β + 1) * _root_.GD.N0106.N0428.N0765.N1512.d029143 k (_root_.GD.N0106.N0428.N0765.N1512.d029183 α β))

def d029198 (channel : Bool) (k : ℕ) (eta α β : ℝ) (q : ℝ × ℝ) : ℝ :=
  if channel then _root_.GD.N0106.N0428.N0765.N1512.d029159 α eta q.1 *
    ((_root_.GD.N0106.N0428.N0765.N1512.d029197 k eta α β * (Real.cos (β / 2))⁻¹) * _root_.GD.N0106.N0428.N0765.N1512.d029158 β q.2)
  else _root_.GD.N0106.N0428.N0765.N1512.d029157 α q.1 * (_root_.GD.N0106.N0428.N0765.N1512.d029197 k eta α β * _root_.GD.N0106.N0428.N0765.N1512.d029158 β q.2)

def d029199 (channel : Bool) (k : ℕ) (eta α β : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1512.d029197 k eta α β *
    (Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) * Real.cos (β / 2) ^ (-(10 : ℝ))) *
    if channel then (Real.cos (β / 2))⁻¹ * ((5 / 3) * (1 + eta)) else 1

theorem d029200 (channel : Bool) (k : ℕ) (eta α β : ℝ) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1512.d029198 channel k eta α β) := by
  cases channel
  · exact _root_.GD.N0106.N0428.N0765.N1512.d029170 α β _
  · exact _root_.GD.N0106.N0428.N0765.N1512.d029172 α β _ eta

theorem d029201 (channel : Bool) (k : ℕ) (eta α β : ℝ) :
    (∫ q, _root_.GD.N0106.N0428.N0765.N1512.d029198 channel k eta α β q) = _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta α β := by
  cases channel <;> simp only [_root_.GD.N0106.N0428.N0765.N1512.d029198, _root_.GD.N0106.N0428.N0765.N1512.d029199, Bool.false_eq_true, ↓reduceIte]
  · rw [_root_.GD.N0106.N0428.N0765.N1512.d029171]
    ring
  · rw [_root_.GD.N0106.N0428.N0765.N1512.d029173]
    ring

theorem d029202 (channel : Bool) (k : ℕ) {eta α β : ℝ}
    (heta : 1 ≤ eta) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (q : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β q‖ ≤ _root_.GD.N0106.N0428.N0765.N1512.d029198 channel k eta α β q := by
  have he : 0 < eta := lt_of_lt_of_le zero_lt_one heta
  have hN : 0 ≤ (1 + eta) / 11 := by positivity
  obtain ⟨hα, hβ⟩ := _root_.GD.N0106.N0428.N0765.N1537.d021535 hs
  have hp : _root_.GD.N0106.N0428.N0765.N1677.d028882 (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β) := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1677.d028882, _root_.GD.N0106.N0428.N0765.N1550.d005477] using hs
  have hH : ‖_root_.GD.N0106.N0428.N0765.N1512.d029181 eta (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (_root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β)‖ ≤ _root_.GD.N0106.N0428.N0765.N1512.d029183 α β := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using _root_.GD.N0106.N0428.N0765.N1512.d029184 he hp
  cases channel
  · have hb := _root_.GD.N0106.N0428.N0765.N1512.d029155 he (z₁ := _root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (z₂ := _root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β)
      (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hα) (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hβ) hH k
    simp only [_root_.GD.N0106.N0428.N0765.N1550.d005476, _root_.GD.N0106.N0428.N0765.N1550.d005477] at hb
    simp only [_root_.GD.N0106.N0428.N0765.N1512.d029194, _root_.GD.N0106.N0428.N0765.N1512.d029191, _root_.GD.N0106.N0428.N0765.N1512.d029198, Bool.false_eq_true, ↓reduceIte, norm_mul,
      Complex.norm_of_nonneg hN]
    calc _ ≤ (1 + eta) / 11 * _ := mul_le_mul_of_nonneg_left hb hN
      _ = _ := by unfold _root_.GD.N0106.N0428.N0765.N1512.d029157 _root_.GD.N0106.N0428.N0765.N1512.d029158 _root_.GD.N0106.N0428.N0765.N1512.d029197; ring
  · have hb := _root_.GD.N0106.N0428.N0765.N1512.d029156 heta (z₁ := _root_.GD.N0106.N0428.N0765.N1550.d005473 q.1 α) (z₂ := _root_.GD.N0106.N0428.N0765.N1550.d005473 q.2 β)
      (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hα) (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hβ) hH k
    simp only [_root_.GD.N0106.N0428.N0765.N1550.d005476, _root_.GD.N0106.N0428.N0765.N1550.d005477] at hb
    simp only [_root_.GD.N0106.N0428.N0765.N1512.d029194, _root_.GD.N0106.N0428.N0765.N1512.d029191, _root_.GD.N0106.N0428.N0765.N1512.d029198, ↓reduceIte, norm_mul, Complex.norm_of_nonneg hN]
    calc _ ≤ (1 + eta) / 11 * _ := mul_le_mul_of_nonneg_left hb hN
      _ = _ := by unfold _root_.GD.N0106.N0428.N0765.N1512.d029159 _root_.GD.N0106.N0428.N0765.N1512.d029158 _root_.GD.N0106.N0428.N0765.N1512.d029197; ring



theorem d029203 (channel : Bool) (k : ℕ) {eta α β : ℝ}
    (heta : 1 ≤ eta) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β) :=
  Integrable.mono' (_root_.GD.N0106.N0428.N0765.N1512.d029200 channel k eta α β)
    (_root_.GD.N0106.N0428.N0765.N1512.d029196 channel k eta α β).aestronglyMeasurable
    (Filter.Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1512.d029202 channel k heta hs))



theorem d029204 (channel : Bool) (k : ℕ) {eta α β : ℝ}
    (heta : 1 ≤ eta) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    (∫ q, ‖_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β q‖) ≤ _root_.GD.N0106.N0428.N0765.N1512.d029199 channel k eta α β := by
  rw [← _root_.GD.N0106.N0428.N0765.N1512.d029201]
  exact integral_mono_ae (_root_.GD.N0106.N0428.N0765.N1512.d029203 channel k heta hs).norm
    (_root_.GD.N0106.N0428.N0765.N1512.d029200 channel k eta α β)
    (Filter.Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1512.d029202 channel k heta hs))

theorem d029205 (channel : Bool) (k : Fin 5) {eta : ℝ} (heta : 0 < eta)
    (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1512.d029191 channel k.val eta (q.1 : ℂ) (q.2 : ℂ) =
      (((1 + eta) / 11 * (_root_.GD.N0106.N0428.N0765.N1521.d020868 q *
        _root_.GD.N0106.N0428.N0765.N1627.d021104 (k, if channel then 1 else 0) eta (_root_.GD.N0106.N0428.N0765.N1521.d020862 q)) : ℝ) : ℂ) := by
  rcases q with ⟨a, b⟩
  rw [_root_.GD.N0106.N0428.N0765.N1512.d029191, _root_.GD.N0106.N0428.N0765.N1512.d029185 heta]
  cases channel <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [_root_.GD.N0106.N0428.N0765.N1512.d029178]
    simp only [Complex.ofReal_mul]
  · rw [_root_.GD.N0106.N0428.N0765.N1512.d029179 k heta]
    simp only [Complex.ofReal_mul]



theorem d029206 (channel : Bool) (k : Fin 5)
    (location : ℝ) {eta : ℝ} (heta : 0 < eta) :
    (∫ q, _root_.GD.N0106.N0428.N0765.N1512.d029194 channel k.val eta 0 0 q) =
      (_root_.GD.N0106.N0428.N0765.N1627.d021105 location eta (k, if channel then 1 else 0) : ℂ) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1512.d029194, _root_.GD.N0106.N0428.N0765.N1550.d005478, _root_.GD.N0106.N0428.N0765.N1512.d029205 channel k heta]
  rw [_root_.integral_complex_ofReal, integral_const_mul,
    ← _root_.GD.N0106.N0428.N0765.N1512.d029180 location eta heta]



private theorem d029207 {a b j r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hrL : r ≤ a + j) (hrR : r ≤ b - j) (x : ℝ) :
    Real.exp (j * x) * _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x ≤
      (beta a b)⁻¹ * Real.exp (-r * |x|) := by
  have hB : 0 ≤ (beta a b)⁻¹ := (inv_pos.mpr (beta_pos ha hb)).le
  by_cases hx : x ≤ 0
  · refine (_root_.GD.N0106.N0428.N0765.N1688.d029141 ha hb j x).trans ?_
    apply mul_le_mul_of_nonneg_left _ hB
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonpos hx]
    nlinarith
  · have hx0 : 0 ≤ x := (lt_of_not_ge hx).le
    refine (_root_.GD.N0106.N0428.N0765.N1688.d029142 ha hb j x).trans ?_
    apply mul_le_mul_of_nonneg_left _ hB
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hx0]
    nlinarith

def d029208 (channel : Bool) (x : ℝ) : ℝ :=
  if channel then Real.exp x * _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 x
  else _root_.GD.N0106.N0428.N0765.N1539.d005373 ((3 : ℝ) / 2) 10 x

def d029209 (channel : Bool) : ℝ := if channel then 5 / 2 else 3 / 2

theorem d029210 (channel : Bool) : 0 < _root_.GD.N0106.N0428.N0765.N1512.d029209 channel := by
  cases channel <;> norm_num [_root_.GD.N0106.N0428.N0765.N1512.d029209]

theorem d029211 (channel : Bool) (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1512.d029208 channel x ≤ (beta ((3 : ℝ) / 2) 10)⁻¹ *
      Real.exp (-_root_.GD.N0106.N0428.N0765.N1512.d029209 channel * |x|) := by
  cases channel
  · simpa only [_root_.GD.N0106.N0428.N0765.N1512.d029208, _root_.GD.N0106.N0428.N0765.N1512.d029209, Bool.false_eq_true, ↓reduceIte,
      zero_mul, Real.exp_zero, one_mul] using
      (_root_.GD.N0106.N0428.N0765.N1512.d029207 (a := (3 : ℝ) / 2) (b := 10) (j := 0) (r := 3 / 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) x)
  · simpa only [_root_.GD.N0106.N0428.N0765.N1512.d029208, _root_.GD.N0106.N0428.N0765.N1512.d029209, ↓reduceIte, one_mul] using
      (_root_.GD.N0106.N0428.N0765.N1512.d029207 (a := (3 : ℝ) / 2) (b := 10) (j := 1) (r := 5 / 2)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) x)

theorem d029212 (y : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 y ≤ (beta (5 : ℝ) 5)⁻¹ * Real.exp (-5 * |y|) := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using
    (_root_.GD.N0106.N0428.N0765.N1512.d029207 (a := (5 : ℝ)) (b := 5) (j := 0) (r := 5)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) y)

def d029213 (channel : Bool) (k : ℕ) (eta α β : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1512.d029197 k eta α β *
    (Real.cos (α / 2) ^ (-((23 : ℝ) / 2)) * Real.cos (β / 2) ^ (-(10 : ℝ))) *
    if channel then (Real.cos (β / 2))⁻¹ * (10 * (1 + eta)) else 1

def d029214 (channel : Bool) (k : ℕ) (eta α β : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1512.d029213 channel k eta α β *
    (beta ((3 : ℝ) / 2) 10)⁻¹ * (beta (5 : ℝ) 5)⁻¹

theorem d029215 (channel : Bool) (k : ℕ) (eta α β : ℝ)
    (q : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1512.d029198 channel k eta α β q =
      _root_.GD.N0106.N0428.N0765.N1512.d029213 channel k eta α β * _root_.GD.N0106.N0428.N0765.N1512.d029208 channel q.1 * _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 q.2 := by
  cases channel <;> simp only [_root_.GD.N0106.N0428.N0765.N1512.d029198, _root_.GD.N0106.N0428.N0765.N1512.d029213, _root_.GD.N0106.N0428.N0765.N1512.d029208,
    Bool.false_eq_true, ↓reduceIte, _root_.GD.N0106.N0428.N0765.N1512.d029157, _root_.GD.N0106.N0428.N0765.N1512.d029158, _root_.GD.N0106.N0428.N0765.N1512.d029159] <;> ring

theorem d029216 (channel : Bool) (k : ℕ) {eta α β : ℝ}
    (heta : 1 ≤ eta) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1512.d029213 channel k eta α β := by
  have he : 0 < eta := lt_of_lt_of_le zero_lt_one heta
  have hK : 0 < _root_.GD.N0106.N0428.N0765.N1512.d029183 α β := inv_pos.mpr (_root_.GD.N0106.N0428.N0765.N1538.d021232 hs)
  obtain ⟨hα, hβ⟩ := _root_.GD.N0106.N0428.N0765.N1537.d021535 hs
  have hcα := _root_.GD.N0106.N0428.N0765.N1585.d005527 hα
  have hcβ := _root_.GD.N0106.N0428.N0765.N1585.d005527 hβ
  cases channel <;> simp only [_root_.GD.N0106.N0428.N0765.N1512.d029213, _root_.GD.N0106.N0428.N0765.N1512.d029197, _root_.GD.N0106.N0428.N0765.N1512.d029143,
    Bool.false_eq_true, ↓reduceIte] <;> positivity




theorem d029217 (channel : Bool) (k : ℕ) {eta α β : ℝ}
    (heta : 1 ≤ eta) (hs : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (q : ℝ × ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β q‖ ≤ _root_.GD.N0106.N0428.N0765.N1512.d029214 channel k eta α β *
      Real.exp (-_root_.GD.N0106.N0428.N0765.N1512.d029209 channel * |q.1|) * Real.exp (-5 * |q.2|) := by
  have hC := _root_.GD.N0106.N0428.N0765.N1512.d029216 channel k heta hs
  have hA := _root_.GD.N0106.N0428.N0765.N1512.d029211 channel q.1
  have hB := _root_.GD.N0106.N0428.N0765.N1512.d029212 q.2
  have hρ : 0 ≤ _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 q.2 := (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) _).le
  have hbA : 0 < beta ((3 : ℝ) / 2) 10 := beta_pos (by norm_num) (by norm_num)
  calc
    ‖_root_.GD.N0106.N0428.N0765.N1512.d029194 channel k eta α β q‖ ≤ _root_.GD.N0106.N0428.N0765.N1512.d029198 channel k eta α β q :=
      _root_.GD.N0106.N0428.N0765.N1512.d029202 channel k heta hs q
    _ = _root_.GD.N0106.N0428.N0765.N1512.d029213 channel k eta α β * _root_.GD.N0106.N0428.N0765.N1512.d029208 channel q.1 * _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 q.2 :=
      _root_.GD.N0106.N0428.N0765.N1512.d029215 channel k eta α β q
    _ ≤ (_root_.GD.N0106.N0428.N0765.N1512.d029213 channel k eta α β *
        ((beta ((3 : ℝ) / 2) 10)⁻¹ * Real.exp (-_root_.GD.N0106.N0428.N0765.N1512.d029209 channel * |q.1|))) *
        ((beta (5 : ℝ) 5)⁻¹ * Real.exp (-5 * |q.2|)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hA hC) hB hρ
        (mul_nonneg hC (by positivity))
    _ = _ := by unfold _root_.GD.N0106.N0428.N0765.N1512.d029214; ring

end
end GD.N0106.N0428.N0765.N1512

#print axioms _root_.GD.N0106.N0428.N0765.N1512.d029192
#print axioms _root_.GD.N0106.N0428.N0765.N1512.d029193
#print axioms _root_.GD.N0106.N0428.N0765.N1512.d029203
#print axioms _root_.GD.N0106.N0428.N0765.N1512.d029204
#print axioms _root_.GD.N0106.N0428.N0765.N1512.d029206
#print axioms _root_.GD.N0106.N0428.N0765.N1512.d029217
