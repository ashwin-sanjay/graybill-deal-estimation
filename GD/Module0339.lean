import GD.Module0190
import Mathlib







set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open scoped BigOperators Polynomial

namespace GD.N0106.N0428.N0766.N1692.N1761
noncomputable section

open _root_.GD.N0232.N0720.N1254 Polynomial


def d005030 (gamma : ℝ) : Fin 4 → ℝ[X] :=
  let r := _root_.GD.N0232.N0720.N1254.d002513 gamma gamma
  ![C (1 / (2 * gamma)) * X,
    1 - C (r / gamma ^ 2) * X ^ 2,
    C (-4 * r / gamma) * X + C (2 * r * (r + 1) / gamma ^ 3) * X ^ 3,
    C (-r / (8 * gamma ^ 2)) * X + C (r / (8 * gamma ^ 4)) * X ^ 3]

def d005031 (gamma : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let r := _root_.GD.N0232.N0720.N1254.d002513 gamma gamma
  ![![0, 1, 0, 0],
    ![1 / (2 * gamma), 0, -4 * r / gamma, -r / (8 * gamma ^ 2)],
    ![0, -r / gamma ^ 2, 0, 0],
    ![0, 0, 2 * r * (r + 1) / gamma ^ 3, r / (8 * gamma ^ 4)]]


theorem d005032 (gamma : ℝ) (i j : Fin 4) :
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma i j = (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j).coeff i.val := by
  fin_cases i <;> fin_cases j
  · change (0 : ℝ) = (C (1 / (2 * gamma)) * X : ℝ[X]).coeff 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (1 : ℝ) = (1 - C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * X ^ 2 : ℝ[X]).coeff 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (C (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) * X + C (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) * X ^ 3 : ℝ[X]).coeff 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (C (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) * X + C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) * X ^ 3 : ℝ[X]).coeff 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (1 / (2 * gamma) : ℝ) = (C (1 / (2 * gamma)) * X : ℝ[X]).coeff 1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (1 - C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * X ^ 2 : ℝ[X]).coeff 1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma : ℝ) = (C (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) * X + C (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) * X ^ 3 : ℝ[X]).coeff 1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2) : ℝ) = (C (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) * X + C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) * X ^ 3 : ℝ[X]).coeff 1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (C (1 / (2 * gamma)) * X : ℝ[X]).coeff 2
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2 : ℝ) = (1 - C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * X ^ 2 : ℝ[X]).coeff 2
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (C (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) * X + C (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) * X ^ 3 : ℝ[X]).coeff 2
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (C (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) * X + C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) * X ^ 3 : ℝ[X]).coeff 2
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (C (1 / (2 * gamma)) * X : ℝ[X]).coeff 3
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (1 - C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * X ^ 2 : ℝ[X]).coeff 3
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3 : ℝ) = (C (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) * X + C (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) * X ^ 3 : ℝ[X]).coeff 3
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4) : ℝ) = (C (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) * X + C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) * X ^ 3 : ℝ[X]).coeff 3
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring

theorem d005033 (gamma : ℝ) (j : Fin 4)
    {n : ℕ} (hn : 4 ≤ n) : (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j).coeff n = 0 := by
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have h3 : n ≠ 3 := by omega
  fin_cases j
  · change (C (1 / (2 * gamma)) * X : ℝ[X]).coeff n = 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one]
    simp [h0, h1, h2, h3]
  · change (1 - C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * X ^ 2 : ℝ[X]).coeff n = 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one]
    simp [h0, h1, h2, h3]
  · change (C (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) * X + C (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) * X ^ 3 : ℝ[X]).coeff n = 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one]
    simp [h0, h1, h2, h3]
  · change (C (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) * X + C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) * X ^ 3 : ℝ[X]).coeff n = 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one]
    simp [h0, h1, h2, h3]



theorem d005034 {gamma : ℝ} (hgamma : 0 < gamma) (e : ℝ) (j : Fin 4) :
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma j).eval (gamma - 2 * gamma * e) =
      ![_root_.GD.N0232.N0720.N1254.d002537 gamma gamma e, _root_.GD.N0232.N0720.N1254.d002538 gamma gamma e,
        _root_.GD.N0232.N0720.N1254.d002539 gamma gamma e, _root_.GD.N0232.N0720.N1254.d002540 gamma gamma e] j := by
  have hg : gamma ≠ 0 := hgamma.ne'
  fin_cases j <;>
    simp [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030, _root_.GD.N0232.N0720.N1254.d002537, _root_.GD.N0232.N0720.N1254.d002538, _root_.GD.N0232.N0720.N1254.d002539, _root_.GD.N0232.N0720.N1254.d002540,
      _root_.GD.N0232.N0720.N1254.d002513, _root_.GD.N0232.N0720.N1254.d002512, _root_.GD.N0232.N0720.N1254.d002515, _root_.GD.N0232.N0720.N1254.d002514, _root_.GD.N0232.N0720.N1254.d002516, _root_.GD.N0232.N0720.N1254.d002517, _root_.GD.N0232.N0720.N1254.d002510] <;>
    field_simp [hg] <;> ring

def d005035 (gamma : ℝ) : Fin 5 → ℝ[X] :=
  ![_root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 0, _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 1,
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 2, _root_.GD.N0106.N0428.N0766.N1692.N1761.d005030 gamma 3, 1]

def d005036 (gamma : ℝ) : Matrix (Fin 4) (Fin 5) ℝ :=
  let r := _root_.GD.N0232.N0720.N1254.d002513 gamma gamma
  ![![0, 1, 0, 0, 1],
    ![1 / (2 * gamma), 0, -4 * r / gamma, -r / (8 * gamma ^ 2), 0],
    ![0, -r / gamma ^ 2, 0, 0, 0],
    ![0, 0, 2 * r * (r + 1) / gamma ^ 3, r / (8 * gamma ^ 4), 0]]

theorem d005037 (gamma : ℝ) (i : Fin 4) (j : Fin 5) :
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma i j = (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005035 gamma j).coeff i.val := by
  fin_cases i <;> fin_cases j
  · change (0 : ℝ) = (C (1 / (2 * gamma)) * X : ℝ[X]).coeff 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (1 : ℝ) = (1 - C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * X ^ 2 : ℝ[X]).coeff 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (C (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) * X + C (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) * X ^ 3 : ℝ[X]).coeff 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (C (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) * X + C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) * X ^ 3 : ℝ[X]).coeff 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (1 : ℝ) = (1 : ℝ[X]).coeff 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (1 / (2 * gamma) : ℝ) = (C (1 / (2 * gamma)) * X : ℝ[X]).coeff 1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (1 - C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * X ^ 2 : ℝ[X]).coeff 1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma : ℝ) = (C (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) * X + C (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) * X ^ 3 : ℝ[X]).coeff 1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2) : ℝ) = (C (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) * X + C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) * X ^ 3 : ℝ[X]).coeff 1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (1 : ℝ[X]).coeff 1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (C (1 / (2 * gamma)) * X : ℝ[X]).coeff 2
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2 : ℝ) = (1 - C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * X ^ 2 : ℝ[X]).coeff 2
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (C (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) * X + C (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) * X ^ 3 : ℝ[X]).coeff 2
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (C (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) * X + C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) * X ^ 3 : ℝ[X]).coeff 2
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (1 : ℝ[X]).coeff 2
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (C (1 / (2 * gamma)) * X : ℝ[X]).coeff 3
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (1 - C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * X ^ 2 : ℝ[X]).coeff 3
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3 : ℝ) = (C (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) * X + C (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) * X ^ 3 : ℝ[X]).coeff 3
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4) : ℝ) = (C (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) * X + C ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) * X ^ 3 : ℝ[X]).coeff 3
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring
  · change (0 : ℝ) = (1 : ℝ[X]).coeff 3
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;> norm_num <;> ring

theorem d005038 (gamma : ℝ) (i j : Fin 4) :
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma i j.castSucc = _root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem d005039 (gamma : ℝ) (i : Fin 4) :
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma i 4 = if i = 0 then 1 else 0 := by
  fin_cases i <;> rfl



def d005040 : Fin 3 → Fin 4 := ![0, 1, 3]

def d005041 (gamma : ℝ) : Matrix (Fin 4) (Fin 3) ℝ :=
  ![![1, 0, 0], ![0, 1, 0], ![-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2, 0, 0], ![0, 0, 1]]

theorem d005042 (gamma : ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma =
      _root_.GD.N0106.N0428.N0766.N1692.N1761.d005041 gamma * (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).submatrix _root_.GD.N0106.N0428.N0766.N1692.N1761.d005040 id := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j
  · change (0 : ℝ) = (1) * (0) + ((0) * (1 / (2 * gamma)) + ((0) * (0) + 0))
    ring
  · change (1 : ℝ) = (1) * (1) + ((0) * (0) + ((0) * (0) + 0))
    ring
  · change (0 : ℝ) = (1) * (0) + ((0) * (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) + ((0) * (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) + 0))
    ring
  · change (0 : ℝ) = (1) * (0) + ((0) * (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) + ((0) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) + 0))
    ring
  · change (1 / (2 * gamma) : ℝ) = (0) * (0) + ((1) * (1 / (2 * gamma)) + ((0) * (0) + 0))
    ring
  · change (0 : ℝ) = (0) * (1) + ((1) * (0) + ((0) * (0) + 0))
    ring
  · change (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma : ℝ) = (0) * (0) + ((1) * (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) + ((0) * (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) + 0))
    ring
  · change (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2) : ℝ) = (0) * (0) + ((1) * (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) + ((0) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) + 0))
    ring
  · change (0 : ℝ) = (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * (0) + ((0) * (1 / (2 * gamma)) + ((0) * (0) + 0))
    ring
  · change (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2 : ℝ) = (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * (1) + ((0) * (0) + ((0) * (0) + 0))
    ring
  · change (0 : ℝ) = (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * (0) + ((0) * (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) + ((0) * (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) + 0))
    ring
  · change (0 : ℝ) = (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma ^ 2) * (0) + ((0) * (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) + ((0) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) + 0))
    ring
  · change (0 : ℝ) = (0) * (0) + ((0) * (1 / (2 * gamma)) + ((1) * (0) + 0))
    ring
  · change (0 : ℝ) = (0) * (1) + ((0) * (0) + ((1) * (0) + 0))
    ring
  · change (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3 : ℝ) = (0) * (0) + ((0) * (-4 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / gamma) + ((1) * (2 * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) + 1) / gamma ^ 3) + 0))
    ring
  · change ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4) : ℝ) = (0) * (0) + ((0) * (-(_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 2)) + ((1) * ((_root_.GD.N0232.N0720.N1254.d002513 gamma gamma) / (8 * gamma ^ 4)) + 0))
    ring

theorem d005043 (gamma : ℝ) :
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).rank ≤ 3 := by
  calc
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).rank =
        (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005041 gamma * (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).submatrix _root_.GD.N0106.N0428.N0766.N1692.N1761.d005040 id).rank :=
      congrArg Matrix.rank (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005042 gamma)
    _ ≤ (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005041 gamma).rank := Matrix.rank_mul_le_left _ _
    _ ≤ 3 := by simpa using Matrix.rank_le_card_width (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005041 gamma)

def d005044 : Fin 3 → Fin 4 := ![1, 0, 2]

def d005045 (gamma : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).submatrix _root_.GD.N0106.N0428.N0766.N1692.N1761.d005040 _root_.GD.N0106.N0428.N0766.N1692.N1761.d005044

theorem d005046 (gamma : ℝ) :
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005045 gamma).det =
      (1 / (2 * gamma)) *
        (2 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma + 1) / gamma ^ 3) := by
  rw [Matrix.det_fin_three]
  simp [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005045, _root_.GD.N0106.N0428.N0766.N1692.N1761.d005031, _root_.GD.N0106.N0428.N0766.N1692.N1761.d005040, _root_.GD.N0106.N0428.N0766.N1692.N1761.d005044, Matrix.submatrix] <;> ring

theorem d005047 {gamma : ℝ} (hgamma : 0 < gamma) :
    0 < (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005045 gamma).det := by
  have hr : 0 < _root_.GD.N0232.N0720.N1254.d002513 gamma gamma := by
    unfold _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002510
    linarith
  rw [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005046]
  positivity


theorem d005048 {gamma : ℝ} (hgamma : 0 < gamma) :
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).rank = 3 := by
  have hunit : IsUnit (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005045 gamma) :=
    (Matrix.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.mpr (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005047 hgamma).ne')
  have hm : (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005045 gamma).rank = 3 := by
    simpa using Matrix.rank_of_isUnit (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005045 gamma) hunit
  have hle := Matrix.rank_submatrix_le (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma) _root_.GD.N0106.N0428.N0766.N1692.N1761.d005040 _root_.GD.N0106.N0428.N0766.N1692.N1761.d005044
  change (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005045 gamma).rank ≤ (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).rank at hle
  rw [hm] at hle
  exact le_antisymm (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005043 gamma) hle


def d005049 : Fin 4 → Fin 5 := ![4, 0, 1, 2]

def d005050 (gamma : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma).submatrix id _root_.GD.N0106.N0428.N0766.N1692.N1761.d005049

theorem d005051 (gamma : ℝ) :
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005050 gamma).det =
      (1 / (2 * gamma)) * (-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2) *
        (2 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma + 1) / gamma ^ 3) := by
  have htri : (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005050 gamma).BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num at hij
  rw [Matrix.det_of_upperTriangular htri]
  simp only [Fin.prod_univ_succ]
  change 1 * ((1 / (2 * gamma)) *
    ((-_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2) *
      ((2 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma + 1) / gamma ^ 3) * 1))) = _
  ring

theorem d005052 {gamma : ℝ} (hgamma : 0 < gamma) :
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005050 gamma).det < 0 := by
  have hr : 0 < _root_.GD.N0232.N0720.N1254.d002513 gamma gamma := by
    unfold _root_.GD.N0232.N0720.N1254.d002513 _root_.GD.N0232.N0720.N1254.d002510
    linarith
  have ha : 0 < 1 / (2 * gamma) := by positivity
  have hb : -_root_.GD.N0232.N0720.N1254.d002513 gamma gamma / gamma ^ 2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos hr) (sq_pos_of_pos hgamma)
  have hc : 0 < 2 * _root_.GD.N0232.N0720.N1254.d002513 gamma gamma * (_root_.GD.N0232.N0720.N1254.d002513 gamma gamma + 1) / gamma ^ 3 := by
    positivity
  rw [_root_.GD.N0106.N0428.N0766.N1692.N1761.d005051]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha hb) hc


theorem d005053 {gamma : ℝ} (hgamma : 0 < gamma) :
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma).rank = 4 := by
  have hunit : IsUnit (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005050 gamma) :=
    (Matrix.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.mpr (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005052 hgamma).ne)
  have hm : (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005050 gamma).rank = 4 := by
    simpa using Matrix.rank_of_isUnit (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005050 gamma) hunit
  have hle := Matrix.rank_submatrix_le (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma) id _root_.GD.N0106.N0428.N0766.N1692.N1761.d005049
  change (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005050 gamma).rank ≤ (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma).rank at hle
  rw [hm] at hle
  apply le_antisymm ?_ hle
  simpa using Matrix.rank_le_card_height (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma)

theorem d005054 {gamma : ℝ} (hgamma : 0 < gamma) :
    (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005031 gamma).rank = 3 ∧ (_root_.GD.N0106.N0428.N0766.N1692.N1761.d005036 gamma).rank = 4 :=
  ⟨_root_.GD.N0106.N0428.N0766.N1692.N1761.d005048 hgamma, _root_.GD.N0106.N0428.N0766.N1692.N1761.d005053 hgamma⟩

end
end GD.N0106.N0428.N0766.N1692.N1761

#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005032
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005033
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005034
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005037
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005048
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005053
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1761.d005054
