import GD.Module0255



























namespace GD.N0232.N0719.N0891

noncomputable section

open _root_.GD.N0232.N0719.N0892


def d003696 (p v : ℝ) : ℝ := p * v

theorem d003697
    {p₁ p₂ p₃ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1) :
    p₁ ≤ 1 ∧ p₂ ≤ 1 ∧ p₃ ≤ 1 := by
  constructor
  · linarith
  constructor <;> linarith

theorem d003698
    {p v : ℝ} (hp : 0 ≤ p) (hv : 0 ≤ v) :
    0 ≤ _root_.GD.N0232.N0719.N0891.d003696 p v := by
  exact mul_nonneg hp hv

theorem d003699
    {p v V : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hv : 0 ≤ v) (hvV : v ≤ V) :
    _root_.GD.N0232.N0719.N0891.d003696 p v ≤ V := by
  have hpv : p * v ≤ 1 * v :=
    mul_le_mul_of_nonneg_right hp1 hv
  exact hpv.trans (by simpa using hvV)




theorem d003700
    {p₁ p₂ p₃ v₁ v₂ v₃ V : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hv₁V : v₁ ≤ V) (hv₂V : v₂ ≤ V) (hv₃V : v₃ ≤ V) :
    _root_.GD.N0232.N0719.N0892.d003669 p₁ p₂ p₃
        (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂) (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) ≤ V := by
  obtain ⟨hp₁1, hp₂1, hp₃1⟩ :=
    _root_.GD.N0232.N0719.N0891.d003697 hp₁ hp₂ hp₃ hsum
  have hcp₁ : 0 ≤ 1 - p₁ := sub_nonneg.mpr hp₁1
  have hcp₂ : 0 ≤ 1 - p₂ := sub_nonneg.mpr hp₂1
  have hcp₃ : 0 ≤ 1 - p₃ := sub_nonneg.mpr hp₃1
  have hterm₁ :
      (1 - p₁) * _root_.GD.N0232.N0719.N0891.d003696 p₁ v₁ ≤ p₁ * v₁ := by
    unfold _root_.GD.N0232.N0719.N0891.d003696
    have h : (1 - p₁) * p₁ ≤ 1 * p₁ :=
      mul_le_mul_of_nonneg_right (by linarith) hp₁
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right h hv₁
  have hterm₂ :
      (1 - p₂) * _root_.GD.N0232.N0719.N0891.d003696 p₂ v₂ ≤ p₂ * v₂ := by
    unfold _root_.GD.N0232.N0719.N0891.d003696
    have h : (1 - p₂) * p₂ ≤ 1 * p₂ :=
      mul_le_mul_of_nonneg_right (by linarith) hp₂
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right h hv₂
  have hterm₃ :
      (1 - p₃) * _root_.GD.N0232.N0719.N0891.d003696 p₃ v₃ ≤ p₃ * v₃ := by
    unfold _root_.GD.N0232.N0719.N0891.d003696
    have h : (1 - p₃) * p₃ ≤ 1 * p₃ :=
      mul_le_mul_of_nonneg_right (by linarith) hp₃
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right h hv₃
  have havg :
      p₁ * v₁ + p₂ * v₂ + p₃ * v₃ ≤
        p₁ * V + p₂ * V + p₃ * V := by
    exact add_le_add
      (add_le_add
        (mul_le_mul_of_nonneg_left hv₁V hp₁)
        (mul_le_mul_of_nonneg_left hv₂V hp₂))
      (mul_le_mul_of_nonneg_left hv₃V hp₃)
  unfold _root_.GD.N0232.N0719.N0892.d003669
  calc
    (1 - p₁) * _root_.GD.N0232.N0719.N0891.d003696 p₁ v₁ +
          (1 - p₂) * _root_.GD.N0232.N0719.N0891.d003696 p₂ v₂ +
          (1 - p₃) * _root_.GD.N0232.N0719.N0891.d003696 p₃ v₃
        ≤ p₁ * v₁ + p₂ * v₂ + p₃ * v₃ :=
      add_le_add (add_le_add hterm₁ hterm₂) hterm₃
    _ ≤ p₁ * V + p₂ * V + p₃ * V := havg
    _ = V := by
      calc
        p₁ * V + p₂ * V + p₃ * V =
            (p₁ + p₂ + p₃) * V := by ring
        _ = V := by rw [hsum, one_mul]


theorem d003701
    {p₁ p₂ p₃ v₁ v₂ v₃ V : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hv₁V : v₁ ≤ V) (hv₂V : v₂ ≤ V) (hv₃V : v₃ ≤ V) :
    _root_.GD.N0232.N0719.N0892.d003670 p₁ p₂ p₃
        (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂) (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) ≤
      V ^ 2 := by
  obtain ⟨hp₁1, hp₂1, hp₃1⟩ :=
    _root_.GD.N0232.N0719.N0891.d003697 hp₁ hp₂ hp₃ hsum
  have hV : 0 ≤ V := hv₁.trans hv₁V
  have hd₁ :
      _root_.GD.N0232.N0719.N0891.d003696 p₁ v₁ ≤ V :=
    _root_.GD.N0232.N0719.N0891.d003699 hp₁ hp₁1 hv₁ hv₁V
  have hd₂ :
      _root_.GD.N0232.N0719.N0891.d003696 p₂ v₂ ≤ V :=
    _root_.GD.N0232.N0719.N0891.d003699 hp₂ hp₂1 hv₂ hv₂V
  have hd₃ :
      _root_.GD.N0232.N0719.N0891.d003696 p₃ v₃ ≤ V :=
    _root_.GD.N0232.N0719.N0891.d003699 hp₃ hp₃1 hv₃ hv₃V
  have hd₁0 := _root_.GD.N0232.N0719.N0891.d003698 hp₁ hv₁
  have hd₂0 := _root_.GD.N0232.N0719.N0891.d003698 hp₂ hv₂
  have hd₃0 := _root_.GD.N0232.N0719.N0891.d003698 hp₃ hv₃
  have h12 :
      _root_.GD.N0232.N0719.N0891.d003696 p₁ v₁ * _root_.GD.N0232.N0719.N0891.d003696 p₂ v₂ ≤ V ^ 2 := by
    nlinarith [mul_le_mul hd₁ hd₂ hd₂0 hV]
  have h13 :
      _root_.GD.N0232.N0719.N0891.d003696 p₁ v₁ * _root_.GD.N0232.N0719.N0891.d003696 p₃ v₃ ≤ V ^ 2 := by
    nlinarith [mul_le_mul hd₁ hd₃ hd₃0 hV]
  have h23 :
      _root_.GD.N0232.N0719.N0891.d003696 p₂ v₂ * _root_.GD.N0232.N0719.N0891.d003696 p₃ v₃ ≤ V ^ 2 := by
    nlinarith [mul_le_mul hd₂ hd₃ hd₃0 hV]
  unfold _root_.GD.N0232.N0719.N0892.d003670
  calc
    p₃ * _root_.GD.N0232.N0719.N0891.d003696 p₁ v₁ * _root_.GD.N0232.N0719.N0891.d003696 p₂ v₂ +
          p₂ * _root_.GD.N0232.N0719.N0891.d003696 p₁ v₁ * _root_.GD.N0232.N0719.N0891.d003696 p₃ v₃ +
          p₁ * _root_.GD.N0232.N0719.N0891.d003696 p₂ v₂ * _root_.GD.N0232.N0719.N0891.d003696 p₃ v₃
        ≤ p₃ * V ^ 2 + p₂ * V ^ 2 + p₁ * V ^ 2 := by
      exact add_le_add
        (add_le_add
          (by simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left h12 hp₃)
          (by simpa [mul_assoc] using
            mul_le_mul_of_nonneg_left h13 hp₂))
        (by simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left h23 hp₁)
    _ = V ^ 2 := by
      rw [← add_mul]
      nlinarith [hsum]



theorem d003702
    {p₁ p₂ p₃ v₁ v₂ v₃ V t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hv₁V : v₁ ≤ V) (hv₂V : v₂ ≤ V) (hv₃V : v₃ ≤ V)
    (ht : 0 ≤ t) (htV : 4 * V * t ≤ 1) :
    _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃
        (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂) (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) t ≤
      7 / 4 := by
  have hV : 0 ≤ V := hv₁.trans hv₁V
  have hL :=
    _root_.GD.N0232.N0719.N0891.d003700 hp₁ hp₂ hp₃ hsum
      hv₁ hv₂ hv₃ hv₁V hv₂V hv₃V
  have hP :=
    _root_.GD.N0232.N0719.N0891.d003701 hp₁ hp₂ hp₃ hsum
      hv₁ hv₂ hv₃ hv₁V hv₂V hv₃V
  have hL0 :=
    _root_.GD.N0232.N0719.N0892.d003678 hp₁ hp₂ hp₃ hsum
      (_root_.GD.N0232.N0719.N0891.d003698 hp₁ hv₁)
      (_root_.GD.N0232.N0719.N0891.d003698 hp₂ hv₂)
      (_root_.GD.N0232.N0719.N0891.d003698 hp₃ hv₃)
  have hP0 :=
    _root_.GD.N0232.N0719.N0892.d003679 hp₁ hp₂ hp₃
      (_root_.GD.N0232.N0719.N0891.d003698 hp₁ hv₁)
      (_root_.GD.N0232.N0719.N0891.d003698 hp₂ hv₂)
      (_root_.GD.N0232.N0719.N0891.d003698 hp₃ hv₃)
  have hLt :
      _root_.GD.N0232.N0719.N0892.d003669 p₁ p₂ p₃
          (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂) (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) * t
        ≤ V * t :=
    mul_le_mul_of_nonneg_right hL ht
  have hPt :
      _root_.GD.N0232.N0719.N0892.d003670 p₁ p₂ p₃
          (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂) (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) * t ^ 2
        ≤ V ^ 2 * t ^ 2 :=
    mul_le_mul_of_nonneg_right hP (sq_nonneg t)
  have hVt : 0 ≤ V * t := mul_nonneg hV ht
  have hVt_le : V * t ≤ 1 / 4 := by nlinarith
  have hVt_sq : (V * t) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hVt hVt_le 2
  unfold _root_.GD.N0232.N0719.N0892.d003671
  have hrewrite : V ^ 2 * t ^ 2 = (V * t) ^ 2 := by ring
  rw [hrewrite] at hPt
  nlinarith

theorem d003703
    {p₁ p₂ p₃ v₁ v₂ v₃ V t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hv₁V : v₁ ≤ V) (hv₂V : v₂ ≤ V) (hv₃V : v₃ ≤ V)
    (ht : 0 ≤ t) (htV : 4 * V * t ≤ 1) :
    _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃
        (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂) (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) t ≤
      2 := by
  have h :=
    _root_.GD.N0232.N0719.N0891.d003702
      hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ hv₁V hv₂V hv₃V ht htV
  norm_num at h ⊢
  linarith



theorem d003704
    {p₁ p₂ p₃ v₁ v₂ v₃ V t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hv₁V : v₁ ≤ V) (hv₂V : v₂ ≤ V) (hv₃V : v₃ ≤ V)
    (ht : 0 ≤ t) (htV : 4 * V * t ≤ 1) :
    let D :=
      _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃
        (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂) (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) t
    D ^ 2 * Real.sqrt D ≤ 8 := by
  dsimp
  let D :=
    _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃
      (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂) (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) t
  have hD1 : 1 ≤ D :=
    _root_.GD.N0232.N0719.N0892.d003680 hp₁ hp₂ hp₃ hsum
      (_root_.GD.N0232.N0719.N0891.d003698 hp₁ hv₁)
      (_root_.GD.N0232.N0719.N0891.d003698 hp₂ hv₂)
      (_root_.GD.N0232.N0719.N0891.d003698 hp₃ hv₃) ht
  have hD2 : D ≤ 2 :=
    _root_.GD.N0232.N0719.N0891.d003703
      hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ hv₁V hv₂V hv₃V ht htV
  have hsqrt : Real.sqrt D ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hDsq : D ^ 2 ≤ 4 := by nlinarith [sq_nonneg (D - 2)]
  have hsqrt0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  calc
    D ^ 2 * Real.sqrt D ≤ 4 * Real.sqrt D :=
      mul_le_mul_of_nonneg_right hDsq hsqrt0
    _ ≤ 4 * 2 := mul_le_mul_of_nonneg_left hsqrt (by norm_num)
    _ = 8 := by norm_num


def d003705
    (p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t /
    (_root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t ^ 2 *
      Real.sqrt
        (_root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t))



theorem d003706
    {p₁ p₂ p₃ v₁ v₂ v₃ V t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hv₁V : v₁ ≤ V) (hv₂V : v₂ ≤ V) (hv₃V : v₃ ≤ V)
    (ht : 0 ≤ t) (htV : 4 * V * t ≤ 1)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) :
    _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃
          (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂) (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) / 8 ≤
      _root_.GD.N0232.N0719.N0891.d003705 p₁ p₂ p₃
        (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂) (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) t := by
  let d₁ := _root_.GD.N0232.N0719.N0891.d003696 p₁ v₁
  let d₂ := _root_.GD.N0232.N0719.N0891.d003696 p₂ v₂
  let d₃ := _root_.GD.N0232.N0719.N0891.d003696 p₃ v₃
  let D := _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t
  let N := _root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t
  let den := D ^ 2 * Real.sqrt D
  have hd₁ : 0 ≤ d₁ := _root_.GD.N0232.N0719.N0891.d003698 hp₁ hv₁
  have hd₂ : 0 ≤ d₂ := _root_.GD.N0232.N0719.N0891.d003698 hp₂ hv₂
  have hd₃ : 0 ≤ d₃ := _root_.GD.N0232.N0719.N0891.d003698 hp₃ hv₃
  have hD : 0 < D :=
    _root_.GD.N0232.N0719.N0892.d003681 hp₁ hp₂ hp₃ hsum hd₁ hd₂ hd₃ ht
  have hden : 0 < den := by
    dsimp [den]
    exact mul_pos (sq_pos_of_pos hD) (Real.sqrt_pos.2 hD)
  have hden8 : den ≤ 8 := by
    dsimp [den, D, d₁, d₂, d₃]
    exact _root_.GD.N0232.N0719.N0891.d003704
      hp₁ hp₂ hp₃ hsum hv₁ hv₂ hv₃ hv₁V hv₂V hv₃V ht htV
  have hA0 : 0 ≤ _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ :=
    _root_.GD.N0232.N0719.N0892.d003674 h₁₂ h₁₃ h₂₃
  have hN :
      _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ ≤ N := by
    dsimp [N, _root_.GD.N0232.N0719.N0892.d003672]
    have hA1 := _root_.GD.N0232.N0719.N0892.d003676 hd₁ hd₂ hd₃ h₁₂ h₁₃ h₂₃
    nlinarith
  have hcross :
      _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ * den ≤ 8 * N := by
    calc
      _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ * den
          ≤ _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ * 8 :=
        mul_le_mul_of_nonneg_left hden8 hA0
      _ ≤ 8 * N := by nlinarith
  dsimp [_root_.GD.N0232.N0719.N0891.d003705, d₁, d₂, d₃, D, N, den] at *
  exact (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) hden).2
    (by nlinarith)



theorem d003707
    {τ t : ℝ} (hτ : 0 ≤ τ) (ht : 0 ≤ t)
    (hτt : 4 * τ * t ≤ 1) :
    (3 / 4 : ℝ) ≤ Real.exp (-t * τ) := by
  have hexp := Real.add_one_le_exp (-t * τ)
  nlinarith









theorem d003708
    {p₁ p₂ p₃ v₁ v₂ v₃ V τ t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hv₁V : v₁ ≤ V) (hv₂V : v₂ ≤ V) (hv₃V : v₃ ≤ V)
    (hV : 0 < V) (hτ : 0 ≤ τ)
    (ht : 0 ≤ t)
    (htop : t ≤ 1 / (4 * (τ + V)))
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) :
    (3 / 32 : ℝ) *
        _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃
          (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂) (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) ≤
      Real.exp (-t * τ) *
        _root_.GD.N0232.N0719.N0891.d003705 p₁ p₂ p₃
          (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂)
          (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) t := by
  have hτV : 0 < τ + V := add_pos_of_nonneg_of_pos hτ hV
  have hden : 0 < 4 * (τ + V) := by positivity
  have hscaled : 4 * (τ + V) * t ≤ 1 := by
    have := (le_div_iff₀ hden).1 htop
    nlinarith
  have htV : 4 * V * t ≤ 1 := by
    have hτt : 0 ≤ 4 * τ * t := by positivity
    nlinarith
  have htτ : 4 * τ * t ≤ 1 := by
    have hVt : 0 ≤ 4 * V * t := by positivity
    nlinarith
  have hkernel :=
    _root_.GD.N0232.N0719.N0891.d003706
      hp₁ hp₂ hp₃ hsum
      hv₁ hv₂ hv₃ hv₁V hv₂V hv₃V
      ht htV h₁₂ h₁₃ h₂₃
  have hexp := _root_.GD.N0232.N0719.N0891.d003707 hτ ht htτ
  have hA0 :
      0 ≤ _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃
        (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂) (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) :=
    _root_.GD.N0232.N0719.N0892.d003674 h₁₂ h₁₃ h₂₃
  have hmul :
      (3 / 4 : ℝ) *
          (_root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃
            (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂)
            (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) / 8) ≤
        Real.exp (-t * τ) *
          _root_.GD.N0232.N0719.N0891.d003705 p₁ p₂ p₃
            (_root_.GD.N0232.N0719.N0891.d003696 p₁ v₁) (_root_.GD.N0232.N0719.N0891.d003696 p₂ v₂)
            (_root_.GD.N0232.N0719.N0891.d003696 p₃ v₃) t := by
    exact mul_le_mul hexp hkernel
      (div_nonneg hA0 (by norm_num))
      (Real.exp_pos _).le
  convert hmul using 1 <;> ring

end

end GD.N0232.N0719.N0891
