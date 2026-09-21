import Mathlib







namespace GD.N0209

set_option maxHeartbeats 800000

noncomputable def d007517 (x y : ℝ) : ℝ :=
  x * y / (x + y)

theorem d007518 (x y v : ℝ) (h : x + y ≠ 0) :
    x * v ^ 2 + y * (1 - v) ^ 2 =
      (x + y) * (v - y / (x + y)) ^ 2 + _root_.GD.N0209.d007517 x y := by
  unfold _root_.GD.N0209.d007517
  field_simp [h]
  <;> ring

theorem d007519 {x y a b : ℝ}
    (hx : 0 < x) (hy : 0 < y) (ha : 0 < a) (hb : 0 < b)
    (hxa : x ≤ a) (hyb : y ≤ b) :
    _root_.GD.N0209.d007517 x y ≤ _root_.GD.N0209.d007517 a b := by
  unfold _root_.GD.N0209.d007517
  apply (div_le_div_iff₀ (by linarith : 0 < x + y)
    (by linarith : 0 < a + b)).2
  have h₁ : 0 ≤ x * a * (b - y) :=
    mul_nonneg (mul_nonneg hx.le ha.le) (sub_nonneg.mpr hyb)
  have h₂ : 0 ≤ y * b * (a - x) :=
    mul_nonneg (mul_nonneg hy.le hb.le) (sub_nonneg.mpr hxa)
  nlinarith

structure d007520 (z B x : ℝ) where
  C : ℝ
  J : ℝ
  w : ℝ
  c : ℝ
  D : ℝ
  E : ℝ
  w_nonneg : 0 ≤ w
  w_le_one : w ≤ 1
  c_nonneg : 0 ≤ c
  c_le_one : c ≤ 1
  D_nonneg : 0 ≤ D
  J_le : J ≤ z
  C_le : C ≤ z
  continuum_lower : w * (J - D) ≤ C
  discrete_lower : c * C - E ≤ B
  truncation : z - J ≤ 2 * x ^ 2 + 3 * x ^ 3
  window_error : 1 - w ≤ 7 * x ^ 2 + 6 * x
  mass_error : D ≤ 2 * x ^ 2
  mesh_error : 1 - c ≤ 2 * x + (7 / 2 : ℝ) * x ^ 4
  quadrature_error : E ≤ 5 * x

theorem d007521 {z B x : ℝ} (hz : z ≤ 1)
    (s : _root_.GD.N0209.d007520 z B x) :
    z - B ≤
      13 * x + 11 * x ^ 2 + 3 * x ^ 3 + (7 / 2 : ℝ) * x ^ 4 := by
  have hwJ := mul_le_mul_of_nonneg_left s.J_le
    (sub_nonneg.mpr s.w_le_one)
  have hwD := mul_le_mul_of_nonneg_right s.w_le_one s.D_nonneg
  have hcC := mul_le_mul_of_nonneg_left s.C_le
    (sub_nonneg.mpr s.c_le_one)
  have hwz := mul_le_mul_of_nonneg_left hz
    (sub_nonneg.mpr s.w_le_one)
  have hcz := mul_le_mul_of_nonneg_left hz
    (sub_nonneg.mpr s.c_le_one)
  nlinarith [s.continuum_lower, s.discrete_lower, s.truncation,
    s.window_error, s.mass_error, s.mesh_error, s.quadrature_error]

theorem d007522 {x : ℝ}
    (hx : 0 < x) (hupper : x ≤ 1 / 16) :
    13 * x + 11 * x ^ 2 + 3 * x ^ 3 + (7 / 2 : ℝ) * x ^ 4
      < 14 * x := by
  have hgap : 0 ≤ (1 / 16 : ℝ) - x := sub_nonneg.mpr hupper
  have h₂step := mul_nonneg hx.le hgap
  have h₂ : x ^ 2 ≤ x / 16 := by nlinarith
  have h₃step := mul_nonneg (sq_nonneg x) hgap
  have h₃ : x ^ 3 ≤ x / 256 := by nlinarith
  have h₄step := mul_nonneg (pow_nonneg hx.le 3) hgap
  have h₄ : x ^ 4 ≤ x / 4096 := by nlinarith
  nlinarith

theorem d007523 {z B : ℝ} (hz : z ≤ 1)
    (N : ℕ) (hN : 16 ≤ N)
    (s : _root_.GD.N0209.d007520 z B (1 / (N : ℝ))) :
    z - B < 14 / (N : ℝ) := by
  have hNR : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hx : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hupper : (1 : ℝ) / (N : ℝ) ≤ 1 / 16 := by
    apply (div_le_div_iff₀ hNpos
      (by norm_num : (0 : ℝ) < 16)).2
    nlinarith
  have h :=
    lt_of_le_of_lt (_root_.GD.N0209.d007521 hz s)
      (_root_.GD.N0209.d007522 hx hupper)
  simpa [div_eq_mul_inv] using h

theorem d007524 {P : Type*}
    (z : ℝ) (B : P → ℝ) (phat : ℕ → P)
    (hz : z ≤ 1)
    (hw : ∀ N : ℕ, 16 ≤ N →
      _root_.GD.N0209.d007520 z (B (phat N)) (1 / (N : ℝ))) :
    (∀ n : ℕ, 0 < n →
      z - 1 / (n : ℝ) < B (phat (16 * n))) ∧
    ¬ (∃ ε : ℝ, 0 < ε ∧ ∀ p : P, B p ≤ z - ε) := by
  have hseq : ∀ n : ℕ, 0 < n →
      z - 1 / (n : ℝ) < B (phat (16 * n)) := by
    intro n hn
    have hN : 16 ≤ 16 * n := by omega
    have hr :=
      _root_.GD.N0209.d007523 hz (16 * n) hN (hw (16 * n) hN)
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hfrac :
        (14 : ℝ) / ((16 * n : ℕ) : ℝ) < 1 / (n : ℝ) := by
      push_cast
      apply (div_lt_div_iff₀
        (by positivity : (0 : ℝ) < 16 * (n : ℝ)) hnR).2
      nlinarith
    linarith
  refine ⟨hseq, ?_⟩
  rintro ⟨ε, hε, hall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  have hsmall : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) < ε := by
    have hmul : (1 : ℝ) < (n : ℝ) * ε :=
      (div_lt_iff₀ hε).mp hn
    apply (div_lt_iff₀
      (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))).2
    push_cast
    nlinarith
  have hs := hseq (n + 1) (by omega)
  have hu := hall (phat (16 * (n + 1)))
  linarith

theorem d007525 {P : Type*}
    (z : ℝ) (B : P → ℝ) (phat : ℕ → P)
    (hz : z ≤ 1)
    (hw : ∀ N : ℕ, 16 ≤ N →
      _root_.GD.N0209.d007520 z (B (phat N)) (1 / (N : ℝ))) :
    ∃ ps : {n : ℕ // 0 < n} → P,
      ∀ n : {n : ℕ // 0 < n},
        z - 1 / (n.val : ℝ) < B (ps n) := by
  refine ⟨fun n => phat (16 * n.val), ?_⟩
  intro n
  exact (_root_.GD.N0209.d007524 z B phat hz hw).1 n.val n.property

theorem d007526 {P : Type*} {z β : ℝ} {B : P → ℝ}
    (hgap : ¬ (∃ ε : ℝ, 0 < ε ∧ ∀ p : P, B p ≤ z - ε))
    (hupper : β ≤ z) (hlower : ∀ p : P, B p ≤ β) :
    β = z := by
  apply le_antisymm hupper
  by_contra h
  have hlt : β < z := lt_of_not_ge h
  apply hgap
  refine ⟨z - β, sub_pos.mpr hlt, ?_⟩
  intro p
  have hp := hlower p
  linarith

#print axioms _root_.GD.N0209.d007518
#print axioms _root_.GD.N0209.d007519
#print axioms _root_.GD.N0209.d007523
#print axioms _root_.GD.N0209.d007524
#print axioms _root_.GD.N0209.d007525
#print axioms _root_.GD.N0209.d007526

end GD.N0209
