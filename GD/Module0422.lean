import Mathlib























namespace GD.N0134



@[ext] structure d006518 where
  alpha : ℚ
  beta : ℚ
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta

namespace d006518

def d006519 (D : _root_.GD.N0134.d006518) : ℚ :=
  D.alpha + D.beta

def d006520 (D : _root_.GD.N0134.d006518) : ℚ :=
  D.alpha / D.d006519

def d006521 (D : _root_.GD.N0134.d006518) : ℚ :=
  D.beta / D.d006519

def d006522 (D : _root_.GD.N0134.d006518) : ℚ :=
  D.alpha * D.beta / D.d006519

def d006523 (D : _root_.GD.N0134.d006518) : ℚ :=
  min D.alpha D.beta / D.d006519

def d006524 (D : _root_.GD.N0134.d006518) : ℚ :=
  D.d006519 + 3 / 2

def d006525 (D : _root_.GD.N0134.d006518) : _root_.GD.N0134.d006518 where
  alpha := D.beta
  beta := D.alpha
  alpha_pos := D.beta_pos
  beta_pos := D.alpha_pos

theorem d006526 (D : _root_.GD.N0134.d006518) : 0 < D.d006519 := by
  exact add_pos D.alpha_pos D.beta_pos

theorem d006527 (D : _root_.GD.N0134.d006518) : 0 < D.d006520 := by
  exact div_pos D.alpha_pos D.d006526

theorem d006528 (D : _root_.GD.N0134.d006518) : 0 < D.d006521 := by
  exact div_pos D.beta_pos D.d006526

theorem d006529 (D : _root_.GD.N0134.d006518) :
    D.d006520 + D.d006521 = 1 := by
  unfold _root_.GD.N0134.d006518.d006520 _root_.GD.N0134.d006518.d006521 _root_.GD.N0134.d006518.d006519
  field_simp [ne_of_gt (add_pos D.alpha_pos D.beta_pos)]

theorem d006530 (D : _root_.GD.N0134.d006518) : D.d006520 < 1 := by
  nlinarith [D.d006528, D.d006529]

theorem d006531 (D : _root_.GD.N0134.d006518) : 0 < D.d006522 := by
  exact div_pos (mul_pos D.alpha_pos D.beta_pos) D.d006526

theorem d006532 (D : _root_.GD.N0134.d006518) : 0 < D.d006523 := by
  exact div_pos (lt_min D.alpha_pos D.beta_pos) D.d006526

theorem d006533 (D : _root_.GD.N0134.d006518) :
    D.d006523 ≤ D.d006520 := by
  unfold _root_.GD.N0134.d006518.d006523 _root_.GD.N0134.d006518.d006520
  exact
    (div_le_div_iff_of_pos_right D.d006526).2
      (min_le_left D.alpha D.beta)

theorem d006534 (D : _root_.GD.N0134.d006518) :
    D.d006523 ≤ D.d006521 := by
  unfold _root_.GD.N0134.d006518.d006523 _root_.GD.N0134.d006518.d006521
  exact
    (div_le_div_iff_of_pos_right D.d006526).2
      (min_le_right D.alpha D.beta)

@[simp] theorem d006535 (D : _root_.GD.N0134.d006518) :
    D.d006525.d006519 = D.d006519 := by
  simp [_root_.GD.N0134.d006518.d006525, _root_.GD.N0134.d006518.d006519, add_comm]

@[simp] theorem d006536 (D : _root_.GD.N0134.d006518) :
    D.d006525.d006522 = D.d006522 := by
  simp [_root_.GD.N0134.d006518.d006525, _root_.GD.N0134.d006518.d006522, _root_.GD.N0134.d006518.d006519, add_comm, mul_comm]

@[simp] theorem d006537 (D : _root_.GD.N0134.d006518) :
    D.d006525.d006523 = D.d006523 := by
  simp [_root_.GD.N0134.d006518.d006525, _root_.GD.N0134.d006518.d006523, _root_.GD.N0134.d006518.d006519, add_comm, min_comm]

@[simp] theorem d006538 (D : _root_.GD.N0134.d006518) :
    D.d006525.d006520 = 1 - D.d006520 := by
  rw [show D.d006525.d006520 = D.d006521 by
    simp [_root_.GD.N0134.d006518.d006525, _root_.GD.N0134.d006518.d006520, _root_.GD.N0134.d006518.d006521, _root_.GD.N0134.d006518.d006519, add_comm]]
  nlinarith [D.d006529]

@[simp] theorem d006539 (D : _root_.GD.N0134.d006518) :
    D.d006525.d006524 = D.d006524 := by
  simp [_root_.GD.N0134.d006518.d006524]

end d006518

def d006540 (m : ℕ) : ℚ :=
  ((m - 1 : ℕ) : ℚ) / 2

theorem d006541 (m : ℕ) :
    2 * _root_.GD.N0134.d006540 m = ((m - 1 : ℕ) : ℚ) := by
  unfold _root_.GD.N0134.d006540
  ring

theorem d006542 {m : ℕ} (hm : 2 ≤ m) :
    0 < _root_.GD.N0134.d006540 m := by
  have hm1 : 0 < m - 1 := by omega
  exact div_pos (by exact_mod_cast hm1) (by norm_num)

def d006543 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0134.d006518 where
  alpha := _root_.GD.N0134.d006540 m
  beta := _root_.GD.N0134.d006540 n
  alpha_pos := _root_.GD.N0134.d006542 hm
  beta_pos := _root_.GD.N0134.d006542 hn

theorem d006544
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    2 * (_root_.GD.N0134.d006543 m n hm hn).alpha = ((m - 1 : ℕ) : ℚ)
      ∧ 2 * (_root_.GD.N0134.d006543 m n hm hn).beta = ((n - 1 : ℕ) : ℚ) := by
  constructor <;> simp [_root_.GD.N0134.d006543, _root_.GD.N0134.d006541]

theorem d006545
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0134.d006543 n m hn hm = (_root_.GD.N0134.d006543 m n hm hn).d006525 := by
  apply _root_.GD.N0134.d006518.ext <;> rfl



def d006546 (k : ℕ) : ℚ :=
  2 ^ k

theorem d006547 (k : ℕ) : 0 < _root_.GD.N0134.d006546 k := by
  exact pow_pos (by norm_num) k

theorem d006548 (k : ℕ) : 1 ≤ _root_.GD.N0134.d006546 k := by
  exact one_le_pow₀ (by norm_num)

set_option maxHeartbeats 800000 in









theorem d006549
    (C₁ C₂ Cstar : ℚ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCstar : 0 < Cstar) :
    ∃ k : ℕ,
      C₁ / _root_.GD.N0134.d006546 k + C₂ / (_root_.GD.N0134.d006546 k) ^ 2 ≤ Cstar / 4 := by
  obtain ⟨k, hk⟩ :=
    pow_unbounded_of_one_lt
      (8 * (C₁ + C₂) / Cstar : ℚ)
      (by norm_num : (1 : ℚ) < 2)
  refine ⟨k, ?_⟩
  have hNpos : 0 < _root_.GD.N0134.d006546 k := _root_.GD.N0134.d006547 k
  have hNone : 1 ≤ _root_.GD.N0134.d006546 k := _root_.GD.N0134.d006548 k
  have hsum : 0 ≤ C₁ + C₂ := add_nonneg hC₁ hC₂
  have hbudget :
      8 * (C₁ + C₂) < Cstar * _root_.GD.N0134.d006546 k := by
    have hscaled :=
      (div_lt_iff₀ hCstar).1
        (show 8 * (C₁ + C₂) / Cstar < _root_.GD.N0134.d006546 k by
          simpa [_root_.GD.N0134.d006546] using hk)
    nlinarith
  have hquad :
      C₂ / (_root_.GD.N0134.d006546 k) ^ 2 ≤ C₂ / _root_.GD.N0134.d006546 k := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hNpos) hNpos]
    have hNN : _root_.GD.N0134.d006546 k ≤ (_root_.GD.N0134.d006546 k) ^ 2 := by
      have hprod :
          0 ≤ _root_.GD.N0134.d006546 k * (_root_.GD.N0134.d006546 k - 1) :=
        mul_nonneg hNpos.le (sub_nonneg.mpr hNone)
      nlinarith
    exact mul_le_mul_of_nonneg_left hNN hC₂
  have hlinear :
      (C₁ + C₂) / _root_.GD.N0134.d006546 k ≤ Cstar / 8 := by
    apply le_of_lt
    rw [div_lt_div_iff₀ hNpos (by norm_num : (0 : ℚ) < 8)]
    nlinarith
  calc
    C₁ / _root_.GD.N0134.d006546 k + C₂ / (_root_.GD.N0134.d006546 k) ^ 2
        ≤ C₁ / _root_.GD.N0134.d006546 k + C₂ / _root_.GD.N0134.d006546 k :=
      add_le_add (le_refl _) hquad
    _ = (C₁ + C₂) / _root_.GD.N0134.d006546 k := by ring
    _ ≤ Cstar / 8 := hlinear
    _ ≤ Cstar / 4 := by nlinarith



def d006550 (D : _root_.GD.N0134.d006518) (k : ℕ) : ℚ :=
  D.d006523 / (16 * _root_.GD.N0134.d006546 k)

def d006551 (D : _root_.GD.N0134.d006518) (k : ℕ) : ℚ :=
  D.d006522 / (8 * _root_.GD.N0134.d006546 k)

def d006552 (p : ℚ × ℚ) : Prop :=
  0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2

def d006553 (D : _root_.GD.N0134.d006518) (k : ℕ) : List (ℚ × ℚ) :=
  [ (D.d006520 - _root_.GD.N0134.d006550 D k, _root_.GD.N0134.d006551 D k),
    (D.d006520, _root_.GD.N0134.d006551 D k),
    (D.d006520 + _root_.GD.N0134.d006550 D k, _root_.GD.N0134.d006551 D k),
    (D.d006520, 2 * _root_.GD.N0134.d006551 D k) ]

def d006554 (D : _root_.GD.N0134.d006518) (k : ℕ) : List (ℚ × ℚ) :=
  [ (D.d006520 + _root_.GD.N0134.d006550 D k, _root_.GD.N0134.d006551 D k),
    (D.d006520 - _root_.GD.N0134.d006550 D k, _root_.GD.N0134.d006551 D k),
    (D.d006520 + 2 * _root_.GD.N0134.d006550 D k, _root_.GD.N0134.d006551 D k),
    (D.d006520 - 2 * _root_.GD.N0134.d006550 D k, _root_.GD.N0134.d006551 D k),
    (D.d006520 + _root_.GD.N0134.d006550 D k, 2 * _root_.GD.N0134.d006551 D k),
    (D.d006520 - _root_.GD.N0134.d006550 D k, 2 * _root_.GD.N0134.d006551 D k) ]

theorem d006555 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    0 < _root_.GD.N0134.d006550 D k := by
  exact
    div_pos D.d006532
      (mul_pos (by norm_num) (_root_.GD.N0134.d006547 k))

theorem d006556 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    0 < _root_.GD.N0134.d006551 D k := by
  exact
    div_pos D.d006531
      (mul_pos (by norm_num) (_root_.GD.N0134.d006547 k))

theorem d006557 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    2 * _root_.GD.N0134.d006550 D k < D.d006523 := by
  unfold _root_.GD.N0134.d006550
  rw [show 2 * (D.d006523 / (16 * _root_.GD.N0134.d006546 k)) =
    (2 * D.d006523) / (16 * _root_.GD.N0134.d006546 k) by ring]
  rw [div_lt_iff₀
    (mul_pos (by norm_num : (0 : ℚ) < 16) (_root_.GD.N0134.d006547 k))]
  have hN := _root_.GD.N0134.d006548 k
  have hLam := D.d006532
  nlinarith

theorem d006558 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    0 < D.d006520 - 2 * _root_.GD.N0134.d006550 D k
      ∧ D.d006520 + 2 * _root_.GD.N0134.d006550 D k < 1 := by
  have hh := _root_.GD.N0134.d006557 D k
  constructor
  · nlinarith [D.d006533]
  · nlinarith [D.d006534,
      D.d006529]

theorem d006559 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    ∀ p ∈ _root_.GD.N0134.d006553 D k, _root_.GD.N0134.d006552 p := by
  have hm := _root_.GD.N0134.d006558 D k
  have hh := _root_.GD.N0134.d006555 D k
  have hη := _root_.GD.N0134.d006556 D k
  intro p hp
  simp [_root_.GD.N0134.d006553] at hp
  rcases hp with rfl | rfl | rfl | rfl
  all_goals
    simp only [_root_.GD.N0134.d006552]
    constructor
    · nlinarith
    constructor <;> nlinarith [_root_.GD.N0134.d006518.d006527 D,
      _root_.GD.N0134.d006518.d006530 D]

theorem d006560 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    ∀ p ∈ _root_.GD.N0134.d006554 D k, _root_.GD.N0134.d006552 p := by
  have hm := _root_.GD.N0134.d006558 D k
  have hh := _root_.GD.N0134.d006555 D k
  have hη := _root_.GD.N0134.d006556 D k
  intro p hp
  simp [_root_.GD.N0134.d006554] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [_root_.GD.N0134.d006552]
    constructor
    · nlinarith
    constructor <;> nlinarith [_root_.GD.N0134.d006518.d006527 D,
      _root_.GD.N0134.d006518.d006530 D]

@[simp] theorem d006561 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    _root_.GD.N0134.d006550 D.d006525 k = _root_.GD.N0134.d006550 D k := by
  simp [_root_.GD.N0134.d006550]

@[simp] theorem d006562 (D : _root_.GD.N0134.d006518) (k : ℕ) :
    _root_.GD.N0134.d006551 D.d006525 k = _root_.GD.N0134.d006551 D k := by
  simp [_root_.GD.N0134.d006551]






theorem d006563
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (C₁ C₂ Cstar : ℚ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hCstar : 0 < Cstar) :
    ∃ k : ℕ,
      C₁ / _root_.GD.N0134.d006546 k + C₂ / (_root_.GD.N0134.d006546 k) ^ 2 ≤ Cstar / 4
        ∧ (∀ p ∈ _root_.GD.N0134.d006553 (_root_.GD.N0134.d006543 m n hm hn) k,
            _root_.GD.N0134.d006552 p)
        ∧ (∀ p ∈ _root_.GD.N0134.d006554 (_root_.GD.N0134.d006543 m n hm hn) k,
            _root_.GD.N0134.d006552 p) := by
  obtain ⟨k, hk⟩ :=
    _root_.GD.N0134.d006549 C₁ C₂ Cstar hC₁ hC₂ hCstar
  exact ⟨k, hk,
    _root_.GD.N0134.d006559 (_root_.GD.N0134.d006543 m n hm hn) k,
    _root_.GD.N0134.d006560 (_root_.GD.N0134.d006543 m n hm hn) k⟩

end GD.N0134
