import GD.Module0252
























namespace GD.N0232.N0719.N1019

noncomputable section

open _root_.GD.N0232.N0719.N1016


def d003789
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) : ℝ :=
  p₁ * z₁ + p₂ * z₂ + p₃ * z₃


def d003790
    (p₁ p₂ p₃ z₁ z₂ z₃ : ℝ) : ℝ :=
  let m := _root_.GD.N0232.N0719.N1019.d003789 p₁ p₂ p₃ z₁ z₂ z₃
  p₁ * (z₁ - m) ^ 2 +
    p₂ * (z₂ - m) ^ 2 +
    p₃ * (z₃ - m) ^ 2



def d003791 (z₁ z₂ z₃ : ℝ) : ℝ :=
  (z₁ - z₃) ^ 2 + (z₂ - z₃) ^ 2




def d003792
    (p₁ p₂ p₃ v₁ v₂ v₃ : ℝ) : ℝ :=
  p₁ * p₂ * (v₁ + v₂) +
    p₁ * p₃ * (v₁ + v₃) +
    p₂ * p₃ * (v₂ + v₃)

theorem d003793
    {p₁ p₂ p₃ v₁ v₂ v₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1) :
    _root_.GD.N0232.N0719.N1019.d003792 p₁ p₂ p₃ v₁ v₂ v₃ =
      p₁ * (1 - p₁) * v₁ +
        p₂ * (1 - p₂) * v₂ +
        p₃ * (1 - p₃) * v₃ := by
  have hp₃ : p₃ = 1 - p₁ - p₂ := by linarith
  subst p₃
  unfold _root_.GD.N0232.N0719.N1019.d003792
  ring



theorem d003794
    {p₁ p₂ p₃ v₁ v₂ v₃ V : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (hv₃ : 0 ≤ v₃)
    (hv₁V : v₁ ≤ V) (hv₂V : v₂ ≤ V) (hv₃V : v₃ ≤ V) :
    _root_.GD.N0232.N0719.N1019.d003792 p₁ p₂ p₃ v₁ v₂ v₃ ≤ V := by
  have hp₁1 : p₁ ≤ 1 := by linarith
  have hp₂1 : p₂ ≤ 1 := by linarith
  have hp₃1 : p₃ ≤ 1 := by linarith
  rw [_root_.GD.N0232.N0719.N1019.d003793 hsum]
  have h1 :
      p₁ * (1 - p₁) * v₁ ≤ p₁ * v₁ := by
    have := mul_le_mul_of_nonneg_left (sub_le_self 1 hp₁) hp₁
    exact mul_le_mul_of_nonneg_right (by simpa using this) hv₁
  have h2 :
      p₂ * (1 - p₂) * v₂ ≤ p₂ * v₂ := by
    have := mul_le_mul_of_nonneg_left (sub_le_self 1 hp₂) hp₂
    exact mul_le_mul_of_nonneg_right (by simpa using this) hv₂
  have h3 :
      p₃ * (1 - p₃) * v₃ ≤ p₃ * v₃ := by
    have := mul_le_mul_of_nonneg_left (sub_le_self 1 hp₃) hp₃
    exact mul_le_mul_of_nonneg_right (by simpa using this) hv₃
  have hv :
      p₁ * v₁ + p₂ * v₂ + p₃ * v₃ ≤
        p₁ * V + p₂ * V + p₃ * V := by
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left hv₁V hp₁)
      (mul_le_mul_of_nonneg_left hv₂V hp₂))
      (mul_le_mul_of_nonneg_left hv₃V hp₃)
  nlinarith

theorem d003795
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1) :
    _root_.GD.N0232.N0719.N1019.d003790 p₁ p₂ p₃ z₁ z₂ z₃ =
      p₁ * p₂ * (z₁ - z₂) ^ 2 +
        p₁ * p₃ * (z₁ - z₃) ^ 2 +
        p₂ * p₃ * (z₂ - z₃) ^ 2 := by
  have hp₃ : p₃ = 1 - p₁ - p₂ := by linarith
  subst p₃
  simp only [_root_.GD.N0232.N0719.N1019.d003790, _root_.GD.N0232.N0719.N1019.d003789]
  ring

theorem d003796
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) :
    0 ≤ _root_.GD.N0232.N0719.N1019.d003790 p₁ p₂ p₃ z₁ z₂ z₃ := by
  unfold _root_.GD.N0232.N0719.N1019.d003790
  exact
    add_nonneg
      (add_nonneg
        (mul_nonneg hp₁ (sq_nonneg _))
        (mul_nonneg hp₂ (sq_nonneg _)))
      (mul_nonneg hp₃ (sq_nonneg _))



theorem d003797
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (hp₁ : (1 / 5 : ℝ) ≤ p₁)
    (hp₂ : (1 / 5 : ℝ) ≤ p₂)
    (hp₃ : (1 / 5 : ℝ) ≤ p₃) :
    _root_.GD.N0232.N0719.N1019.d003791 z₁ z₂ z₃ ≤
      25 * _root_.GD.N0232.N0719.N1019.d003790 p₁ p₂ p₃ z₁ z₂ z₃ := by
  have hp₁0 : 0 ≤ p₁ := le_trans (by norm_num) hp₁
  have hp₂0 : 0 ≤ p₂ := le_trans (by norm_num) hp₂
  have hp₃0 : 0 ≤ p₃ := le_trans (by norm_num) hp₃
  have h13 : (1 / 25 : ℝ) ≤ p₁ * p₃ := by
    have h :=
      mul_le_mul hp₁ hp₃ (by norm_num : (0 : ℝ) ≤ 1 / 5) hp₁0
    norm_num at h ⊢
    exact h
  have h23 : (1 / 25 : ℝ) ≤ p₂ * p₃ := by
    have h :=
      mul_le_mul hp₂ hp₃ (by norm_num : (0 : ℝ) ≤ 1 / 5) hp₂0
    norm_num at h ⊢
    exact h
  rw [_root_.GD.N0232.N0719.N1019.d003795 hsum]
  unfold _root_.GD.N0232.N0719.N1019.d003791
  have h12nonneg :
      0 ≤ p₁ * p₂ * (z₁ - z₂) ^ 2 :=
    mul_nonneg (mul_nonneg hp₁0 hp₂0) (sq_nonneg _)
  have h13mul :
      (1 / 25 : ℝ) * (z₁ - z₃) ^ 2 ≤
        p₁ * p₃ * (z₁ - z₃) ^ 2 :=
    mul_le_mul_of_nonneg_right h13 (sq_nonneg _)
  have h23mul :
      (1 / 25 : ℝ) * (z₂ - z₃) ^ 2 ≤
        p₂ * p₃ * (z₂ - z₃) ^ 2 :=
    mul_le_mul_of_nonneg_right h23 (sq_nonneg _)
  nlinarith

private theorem d003798
    (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤
      4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c),
    sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

private theorem d003799
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x + y) :
    0 ≤ x / (x + y) ∧ x / (x + y) ≤ 1 := by
  constructor
  · exact div_nonneg hx hxy.le
  · exact (div_le_one hxy).2 (by linarith)

private theorem d003800
    {p₁ p₂ p₃ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃) :
    0 ≤
        p₁ / 3 *
          (1 / (p₁ + p₂) + 1 / (p₁ + p₃)) ∧
      p₁ / 3 *
          (1 / (p₁ + p₂) + 1 / (p₁ + p₃)) ≤ 1 := by
  have h12 := _root_.GD.N0232.N0719.N1019.d003799 hp₁ hp₂ h₁₂
  have h13 := _root_.GD.N0232.N0719.N1019.d003799 hp₁ hp₃ h₁₃
  have hrewrite :
      p₁ / 3 *
          (1 / (p₁ + p₂) + 1 / (p₁ + p₃)) =
        (p₁ / (p₁ + p₂) + p₁ / (p₁ + p₃)) / 3 := by
    field_simp [ne_of_gt h₁₂, ne_of_gt h₁₃]
  rw [hrewrite]
  constructor
  · positivity
  · nlinarith

private theorem d003801
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    c ^ 2 ≤ 1 := by
  nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]

private theorem d003802
    (u w : ℝ) :
    u ^ 6 ≤ (u ^ 2 + w ^ 2) ^ 3 ∧
    u ^ 4 * w ^ 2 ≤ (u ^ 2 + w ^ 2) ^ 3 ∧
    u ^ 2 * w ^ 4 ≤ (u ^ 2 + w ^ 2) ^ 3 ∧
    w ^ 6 ≤ (u ^ 2 + w ^ 2) ^ 3 := by
  let M := u ^ 2 + w ^ 2
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hu : u ^ 2 ≤ M := by
    dsimp [M]
    nlinarith [sq_nonneg w]
  have hw : w ^ 2 ≤ M := by
    dsimp [M]
    nlinarith [sq_nonneg u]
  have hu3 : (u ^ 2) ^ 3 ≤ M ^ 3 :=
    pow_le_pow_left₀ (sq_nonneg u) hu 3
  have hw3 : (w ^ 2) ^ 3 ≤ M ^ 3 :=
    pow_le_pow_left₀ (sq_nonneg w) hw 3
  have hu2 : (u ^ 2) ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg u) hu 2
  have hw2 : (w ^ 2) ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg w) hw 2
  have humix :
      (u ^ 2) ^ 2 * w ^ 2 ≤ M ^ 2 * M :=
    mul_le_mul hu2 hw (sq_nonneg _) (sq_nonneg _)
  have hwmix :
      u ^ 2 * (w ^ 2) ^ 2 ≤ M * M ^ 2 :=
    mul_le_mul hu hw2 (sq_nonneg _) hM
  dsimp [M] at *
  constructor
  · convert hu3 using 1 <;> ring
  constructor
  · convert humix using 1 <;> ring
  constructor
  · convert hwmix using 1 <;> ring
  · convert hw3 using 1 <;> ring




theorem d003803
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (h₁₂ : 0 < p₁ + p₂)
    (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) :
    _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ ^ 2 ≤
      16 * _root_.GD.N0232.N0719.N1019.d003791 z₁ z₂ z₃ ^ 3 := by
  let u := z₁ - z₃
  let w := z₂ - z₃
  let c₁ :=
    p₁ / 3 * (1 / (p₁ + p₂) + 1 / (p₁ + p₃))
  let c₂ := p₁ / (p₁ + p₂)
  let c₃ := p₂ / (p₁ + p₂)
  let c₄ :=
    p₂ / 3 * (1 / (p₁ + p₂) + 1 / (p₂ + p₃))
  have hc₁ : 0 ≤ c₁ ∧ c₁ ≤ 1 := by
    simpa [c₁] using
      _root_.GD.N0232.N0719.N1019.d003800 hp₁ hp₂ hp₃ h₁₂ h₁₃
  have hc₂ : 0 ≤ c₂ ∧ c₂ ≤ 1 := by
    simpa [c₂] using _root_.GD.N0232.N0719.N1019.d003799 hp₁ hp₂ h₁₂
  have hc₃ : 0 ≤ c₃ ∧ c₃ ≤ 1 := by
    simpa [c₃, add_comm] using
      _root_.GD.N0232.N0719.N1019.d003799 hp₂ hp₁ (by linarith)
  have hc₄ : 0 ≤ c₄ ∧ c₄ ≤ 1 := by
    simpa [c₄, add_comm] using
      _root_.GD.N0232.N0719.N1019.d003800 hp₂ hp₁ hp₃ (by linarith) h₂₃
  have hcubic_repr :
      _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ =
        -c₁ * u ^ 3 + c₂ * u ^ 2 * w +
          c₃ * u * w ^ 2 - c₄ * w ^ 3 := by
    dsimp [_root_.GD.N0232.N0719.N1016.d003609, c₁, c₂, c₃, c₄, u, w]
    ring
  have hcontrast_repr :
      _root_.GD.N0232.N0719.N1019.d003791 z₁ z₂ z₃ = u ^ 2 + w ^ 2 := by
    rfl
  rw [hcubic_repr, hcontrast_repr]
  have hfour :=
    _root_.GD.N0232.N0719.N1019.d003798
      (-c₁ * u ^ 3) (c₂ * u ^ 2 * w)
      (c₃ * u * w ^ 2) (-c₄ * w ^ 3)
  have hc₁sq := _root_.GD.N0232.N0719.N1019.d003801 hc₁.1 hc₁.2
  have hc₂sq := _root_.GD.N0232.N0719.N1019.d003801 hc₂.1 hc₂.2
  have hc₃sq := _root_.GD.N0232.N0719.N1019.d003801 hc₃.1 hc₃.2
  have hc₄sq := _root_.GD.N0232.N0719.N1019.d003801 hc₄.1 hc₄.2
  have hm := _root_.GD.N0232.N0719.N1019.d003802 u w
  have ht₁ :
      (-c₁ * u ^ 3) ^ 2 ≤ (u ^ 2 + w ^ 2) ^ 3 := by
    calc
      (-c₁ * u ^ 3) ^ 2 = c₁ ^ 2 * u ^ 6 := by ring
      _ ≤ 1 * u ^ 6 :=
        mul_le_mul_of_nonneg_right hc₁sq (by positivity)
      _ ≤ (u ^ 2 + w ^ 2) ^ 3 := by simpa using hm.1
  have ht₂ :
      (c₂ * u ^ 2 * w) ^ 2 ≤ (u ^ 2 + w ^ 2) ^ 3 := by
    calc
      (c₂ * u ^ 2 * w) ^ 2 =
          c₂ ^ 2 * (u ^ 4 * w ^ 2) := by ring
      _ ≤ 1 * (u ^ 4 * w ^ 2) :=
        mul_le_mul_of_nonneg_right hc₂sq (by positivity)
      _ ≤ (u ^ 2 + w ^ 2) ^ 3 := by simpa using hm.2.1
  have ht₃ :
      (c₃ * u * w ^ 2) ^ 2 ≤ (u ^ 2 + w ^ 2) ^ 3 := by
    calc
      (c₃ * u * w ^ 2) ^ 2 =
          c₃ ^ 2 * (u ^ 2 * w ^ 4) := by ring
      _ ≤ 1 * (u ^ 2 * w ^ 4) :=
        mul_le_mul_of_nonneg_right hc₃sq (by positivity)
      _ ≤ (u ^ 2 + w ^ 2) ^ 3 := by simpa using hm.2.2.1
  have ht₄ :
      (-c₄ * w ^ 3) ^ 2 ≤ (u ^ 2 + w ^ 2) ^ 3 := by
    calc
      (-c₄ * w ^ 3) ^ 2 = c₄ ^ 2 * w ^ 6 := by ring
      _ ≤ 1 * w ^ 6 :=
        mul_le_mul_of_nonneg_right hc₄sq (by positivity)
      _ ≤ (u ^ 2 + w ^ 2) ^ 3 := by simpa using hm.2.2.2
  calc
    (-c₁ * u ^ 3 + c₂ * u ^ 2 * w +
        c₃ * u * w ^ 2 - c₄ * w ^ 3) ^ 2 ≤
        4 * (((-c₁ * u ^ 3) ^ 2) +
          (c₂ * u ^ 2 * w) ^ 2 +
          (c₃ * u * w ^ 2) ^ 2 +
          (-c₄ * w ^ 3) ^ 2) := by
      convert hfour using 1 <;> ring
    _ ≤ 4 * (((u ^ 2 + w ^ 2) ^ 3) +
          (u ^ 2 + w ^ 2) ^ 3 +
          (u ^ 2 + w ^ 2) ^ 3 +
          (u ^ 2 + w ^ 2) ^ 3) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (add_le_add ht₁ ht₂) ht₃) ht₄)
        (by norm_num)
    _ = 16 * (u ^ 2 + w ^ 2) ^ 3 := by ring


theorem d003804
    {p₁ p₂ p₃ z₁ z₂ z₃ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (hp₁ : (1 / 5 : ℝ) ≤ p₁)
    (hp₂ : (1 / 5 : ℝ) ≤ p₂)
    (hp₃ : (1 / 5 : ℝ) ≤ p₃) :
    _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ ^ 2 ≤
      250000 * _root_.GD.N0232.N0719.N1019.d003790 p₁ p₂ p₃ z₁ z₂ z₃ ^ 3 := by
  have hp₁0 : 0 ≤ p₁ := le_trans (by norm_num) hp₁
  have hp₂0 : 0 ≤ p₂ := le_trans (by norm_num) hp₂
  have hp₃0 : 0 ≤ p₃ := le_trans (by norm_num) hp₃
  have h₁₂ : 0 < p₁ + p₂ := by linarith
  have h₁₃ : 0 < p₁ + p₃ := by linarith
  have h₂₃ : 0 < p₂ + p₃ := by linarith
  have hc :=
    _root_.GD.N0232.N0719.N1019.d003803
      (z₁ := z₁) (z₂ := z₂) (z₃ := z₃)
      hp₁0 hp₂0 hp₃0 h₁₂ h₁₃ h₂₃
  have hcontrast :=
    _root_.GD.N0232.N0719.N1019.d003797
      (z₁ := z₁) (z₂ := z₂) (z₃ := z₃)
      hsum hp₁ hp₂ hp₃
  have hcontrast0 : 0 ≤ _root_.GD.N0232.N0719.N1019.d003791 z₁ z₂ z₃ := by
    unfold _root_.GD.N0232.N0719.N1019.d003791
    positivity
  have hpow :
      _root_.GD.N0232.N0719.N1019.d003791 z₁ z₂ z₃ ^ 3 ≤
        (25 * _root_.GD.N0232.N0719.N1019.d003790 p₁ p₂ p₃ z₁ z₂ z₃) ^ 3 :=
    pow_le_pow_left₀ hcontrast0 hcontrast 3
  calc
    _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ ^ 2 ≤
        16 * _root_.GD.N0232.N0719.N1019.d003791 z₁ z₂ z₃ ^ 3 := hc
    _ ≤ 16 *
        (25 * _root_.GD.N0232.N0719.N1019.d003790 p₁ p₂ p₃ z₁ z₂ z₃) ^ 3 :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = 250000 * _root_.GD.N0232.N0719.N1019.d003790 p₁ p₂ p₃ z₁ z₂ z₃ ^ 3 := by ring


theorem d003805
    {p₁ p₂ p₃ z₁ z₂ z₃ τ : ℝ}
    (hsum : p₁ + p₂ + p₃ = 1)
    (hp₁ : (1 / 5 : ℝ) ≤ p₁)
    (hp₂ : (1 / 5 : ℝ) ≤ p₂)
    (hp₃ : (1 / 5 : ℝ) ≤ p₃)
    (hτ : 0 ≤ τ) :
    (_root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ /
        (τ + _root_.GD.N0232.N0719.N1019.d003790 p₁ p₂ p₃ z₁ z₂ z₃)) ^ 2 ≤
      250000 * _root_.GD.N0232.N0719.N1019.d003790 p₁ p₂ p₃ z₁ z₂ z₃ := by
  let Q := _root_.GD.N0232.N0719.N1019.d003790 p₁ p₂ p₃ z₁ z₂ z₃
  have hp₁0 : 0 ≤ p₁ := le_trans (by norm_num) hp₁
  have hp₂0 : 0 ≤ p₂ := le_trans (by norm_num) hp₂
  have hp₃0 : 0 ≤ p₃ := le_trans (by norm_num) hp₃
  have hQ : 0 ≤ Q := _root_.GD.N0232.N0719.N1019.d003796 hp₁0 hp₂0 hp₃0
  by_cases hQ0 : Q = 0
  · have hcubic :
        _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ = 0 := by
      have hg :=
        _root_.GD.N0232.N0719.N1019.d003804
          (z₁ := z₁) (z₂ := z₂) (z₃ := z₃) hsum hp₁ hp₂ hp₃
      dsimp [Q] at hQ0
      rw [hQ0] at hg
      exact sq_eq_zero_iff.mp
        (le_antisymm (by simpa using hg) (sq_nonneg _))
    simp [Q, hQ0, hcubic]
  · have hQpos : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hQ0)
    have hden : 0 < τ + Q := add_pos_of_nonneg_of_pos hτ hQpos
    have hcubic :=
      _root_.GD.N0232.N0719.N1019.d003804
        (z₁ := z₁) (z₂ := z₂) (z₃ := z₃) hsum hp₁ hp₂ hp₃
    have hQsq : Q ^ 2 ≤ (τ + Q) ^ 2 := by
      exact pow_le_pow_left₀ hQ (le_add_of_nonneg_left hτ) 2
    have hscaled :
        250000 * Q ^ 3 ≤
          (250000 * Q) * (τ + Q) ^ 2 := by
      have hmul :=
        mul_le_mul_of_nonneg_left hQsq
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 250000) hQ)
      calc
        250000 * Q ^ 3 =
            (250000 * Q) * Q ^ 2 := by ring
        _ ≤ (250000 * Q) * (τ + Q) ^ 2 := hmul
    have hnum :
        _root_.GD.N0232.N0719.N1016.d003609 p₁ p₂ p₃ z₁ z₂ z₃ ^ 2 ≤
          (250000 * Q) * (τ + Q) ^ 2 := by
      exact hcubic.trans (by simpa [Q] using hscaled)
    rw [div_pow]
    exact (div_le_iff₀ (sq_pos_of_pos hden)).2 (by
      simpa [Q, mul_assoc] using hnum)

end

end GD.N0232.N0719.N1019
