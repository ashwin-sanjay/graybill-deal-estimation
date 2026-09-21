import GD.Module0252
































namespace GD.N0232.N0719.N0892

noncomputable section

open _root_.GD.N0232.N0719.N1016



def d003667
    (p₁ p₂ p₃ d₁ d₂ d₃ : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1016.d003608 p₁ p₂ p₃ d₁ d₂ d₃



def d003668
    (p₁ p₂ p₃ d₁ d₂ d₃ : ℝ) : ℝ :=
  d₃ * (d₁ - d₂) ^ 2 / (p₁ + p₂) +
    d₂ * (d₁ - d₃) ^ 2 / (p₁ + p₃) +
    d₁ * (d₂ - d₃) ^ 2 / (p₂ + p₃)


def d003669
    (p₁ p₂ p₃ d₁ d₂ d₃ : ℝ) : ℝ :=
  (1 - p₁) * d₁ + (1 - p₂) * d₂ + (1 - p₃) * d₃


def d003670
    (p₁ p₂ p₃ d₁ d₂ d₃ : ℝ) : ℝ :=
  p₃ * d₁ * d₂ + p₂ * d₁ * d₃ + p₁ * d₂ * d₃


def d003671
    (p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ) : ℝ :=
  1 +
    2 * _root_.GD.N0232.N0719.N0892.d003669 p₁ p₂ p₃ d₁ d₂ d₃ * t +
    4 * _root_.GD.N0232.N0719.N0892.d003670 p₁ p₂ p₃ d₁ d₂ d₃ * t ^ 2


def d003672
    (p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ +
    2 * t * _root_.GD.N0232.N0719.N0892.d003668 p₁ p₂ p₃ d₁ d₂ d₃



def d003673
    (p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ) : ℝ :=
  -_root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t /
    _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t ^ ((5 : ℝ) / 2)

theorem d003674
    {p₁ p₂ p₃ d₁ d₂ d₃ : ℝ}
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) :
    0 ≤ _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ := by
  exact _root_.GD.N0232.N0719.N1016.d003619 h₁₂ h₁₃ h₂₃

theorem d003675
    {p₁ p₂ p₃ d₁ d₂ d₃ : ℝ}
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) :
    _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ = 0 ↔
      d₁ = d₂ ∧ d₁ = d₃ := by
  exact _root_.GD.N0232.N0719.N1016.d003620 h₁₂ h₁₃ h₂₃

theorem d003676
    {p₁ p₂ p₃ d₁ d₂ d₃ : ℝ}
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) :
    0 ≤ _root_.GD.N0232.N0719.N0892.d003668 p₁ p₂ p₃ d₁ d₂ d₃ := by
  have h12 :
      0 ≤ d₃ * (d₁ - d₂) ^ 2 / (p₁ + p₂) :=
    div_nonneg (mul_nonneg hd₃ (sq_nonneg _)) h₁₂.le
  have h13 :
      0 ≤ d₂ * (d₁ - d₃) ^ 2 / (p₁ + p₃) :=
    div_nonneg (mul_nonneg hd₂ (sq_nonneg _)) h₁₃.le
  have h23 :
      0 ≤ d₁ * (d₂ - d₃) ^ 2 / (p₂ + p₃) :=
    div_nonneg (mul_nonneg hd₁ (sq_nonneg _)) h₂₃.le
  exact add_nonneg (add_nonneg h12 h13) h23

theorem d003677
    {p₁ p₂ p₃ d₁ d₂ d₃ : ℝ}
    (h₁₂ : p₁ + p₂ ≠ 0) (h₁₃ : p₁ + p₃ ≠ 0)
    (h₂₃ : p₂ + p₃ ≠ 0)
    (hbal : d₁ = d₂ ∧ d₁ = d₃) :
    _root_.GD.N0232.N0719.N0892.d003668 p₁ p₂ p₃ d₁ d₂ d₃ = 0 := by
  rcases hbal with ⟨rfl, rfl⟩
  simp [_root_.GD.N0232.N0719.N0892.d003668, h₁₂, h₁₃, h₂₃]

theorem d003678
    {p₁ p₂ p₃ d₁ d₂ d₃ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃) :
    0 ≤ _root_.GD.N0232.N0719.N0892.d003669 p₁ p₂ p₃ d₁ d₂ d₃ := by
  have hcp₁ : 0 ≤ 1 - p₁ := by linarith
  have hcp₂ : 0 ≤ 1 - p₂ := by linarith
  have hcp₃ : 0 ≤ 1 - p₃ := by linarith
  exact
    add_nonneg
      (add_nonneg (mul_nonneg hcp₁ hd₁) (mul_nonneg hcp₂ hd₂))
      (mul_nonneg hcp₃ hd₃)

theorem d003679
    {p₁ p₂ p₃ d₁ d₂ d₃ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃) :
    0 ≤ _root_.GD.N0232.N0719.N0892.d003670 p₁ p₂ p₃ d₁ d₂ d₃ := by
  exact
    add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg hp₃ hd₁) hd₂)
        (mul_nonneg (mul_nonneg hp₂ hd₁) hd₃))
      (mul_nonneg (mul_nonneg hp₁ hd₂) hd₃)

theorem d003680
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (ht : 0 ≤ t) :
    1 ≤ _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t := by
  have hL :
      0 ≤ _root_.GD.N0232.N0719.N0892.d003669 p₁ p₂ p₃ d₁ d₂ d₃ :=
    _root_.GD.N0232.N0719.N0892.d003678 hp₁ hp₂ hp₃ hsum hd₁ hd₂ hd₃
  have hP :
      0 ≤ _root_.GD.N0232.N0719.N0892.d003670 p₁ p₂ p₃ d₁ d₂ d₃ :=
    _root_.GD.N0232.N0719.N0892.d003679 hp₁ hp₂ hp₃ hd₁ hd₂ hd₃
  have hlinear :
      0 ≤ 2 * _root_.GD.N0232.N0719.N0892.d003669 p₁ p₂ p₃ d₁ d₂ d₃ * t :=
    mul_nonneg (mul_nonneg (by norm_num) hL) ht
  have hquadratic :
      0 ≤ 4 * _root_.GD.N0232.N0719.N0892.d003670 p₁ p₂ p₃ d₁ d₂ d₃ * t ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) hP) (sq_nonneg t)
  simp only [_root_.GD.N0232.N0719.N0892.d003671]
  linarith

theorem d003681
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (ht : 0 ≤ t) :
    0 < _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t :=
  lt_of_lt_of_le zero_lt_one
    (_root_.GD.N0232.N0719.N0892.d003680 hp₁ hp₂ hp₃ hsum hd₁ hd₂ hd₃ ht)

theorem d003682
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) (ht : 0 ≤ t) :
    0 ≤ _root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t := by
  have hA0 : 0 ≤ _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ :=
    _root_.GD.N0232.N0719.N0892.d003674 h₁₂ h₁₃ h₂₃
  have hA1 : 0 ≤ _root_.GD.N0232.N0719.N0892.d003668 p₁ p₂ p₃ d₁ d₂ d₃ :=
    _root_.GD.N0232.N0719.N0892.d003676 hd₁ hd₂ hd₃ h₁₂ h₁₃ h₂₃
  have htilt :
      0 ≤ 2 * t * _root_.GD.N0232.N0719.N0892.d003668 p₁ p₂ p₃ d₁ d₂ d₃ :=
    mul_nonneg (mul_nonneg (by norm_num) ht) hA1
  exact add_nonneg hA0 htilt

theorem d003683
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) (ht : 0 ≤ t) :
    _root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t = 0 ↔
      d₁ = d₂ ∧ d₁ = d₃ := by
  constructor
  · intro hzero
    have hA0 : 0 ≤ _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ :=
      _root_.GD.N0232.N0719.N0892.d003674 h₁₂ h₁₃ h₂₃
    have hA1 : 0 ≤ _root_.GD.N0232.N0719.N0892.d003668 p₁ p₂ p₃ d₁ d₂ d₃ :=
      _root_.GD.N0232.N0719.N0892.d003676 hd₁ hd₂ hd₃ h₁₂ h₁₃ h₂₃
    have htilt :
        0 ≤ 2 * t * _root_.GD.N0232.N0719.N0892.d003668 p₁ p₂ p₃ d₁ d₂ d₃ :=
      mul_nonneg (mul_nonneg (by norm_num) ht) hA1
    have hA0zero : _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ = 0 := by
      change
        _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ +
            2 * t * _root_.GD.N0232.N0719.N0892.d003668 p₁ p₂ p₃ d₁ d₂ d₃ = 0 at hzero
      exact (add_eq_zero_iff_of_nonneg hA0 htilt).mp hzero |>.1
    exact (_root_.GD.N0232.N0719.N0892.d003675 h₁₂ h₁₃ h₂₃).mp hA0zero
  · intro hbal
    have hA0zero :
        _root_.GD.N0232.N0719.N0892.d003667 p₁ p₂ p₃ d₁ d₂ d₃ = 0 :=
      (_root_.GD.N0232.N0719.N0892.d003675 h₁₂ h₁₃ h₂₃).mpr hbal
    have hA1zero :
        _root_.GD.N0232.N0719.N0892.d003668 p₁ p₂ p₃ d₁ d₂ d₃ = 0 :=
      _root_.GD.N0232.N0719.N0892.d003677
        (ne_of_gt h₁₂) (ne_of_gt h₁₃) (ne_of_gt h₂₃) hbal
    simp [_root_.GD.N0232.N0719.N0892.d003672, hA0zero, hA1zero]

theorem d003684
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) (ht : 0 ≤ t)
    (hmismatch : ¬(d₁ = d₂ ∧ d₁ = d₃)) :
    0 < _root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t := by
  have hnonneg :=
    _root_.GD.N0232.N0719.N0892.d003682
      hd₁ hd₂ hd₃ h₁₂ h₁₃ h₂₃ ht
  exact lt_of_le_of_ne hnonneg
    (fun hzero =>
      hmismatch
        ((_root_.GD.N0232.N0719.N0892.d003683
          hd₁ hd₂ hd₃ h₁₂ h₁₃ h₂₃ ht).mp hzero.symm))

theorem d003685
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (ht : 0 ≤ t) :
    0 <
      _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t ^ ((5 : ℝ) / 2) := by
  exact Real.rpow_pos_of_pos
    (_root_.GD.N0232.N0719.N0892.d003681 hp₁ hp₂ hp₃ hsum hd₁ hd₂ hd₃ ht) _

theorem d003686
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) (ht : 0 ≤ t) :
    _root_.GD.N0232.N0719.N0892.d003673 p₁ p₂ p₃ d₁ d₂ d₃ t ≤ 0 := by
  have hnum :
      0 ≤ _root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t :=
    _root_.GD.N0232.N0719.N0892.d003682 hd₁ hd₂ hd₃ h₁₂ h₁₃ h₂₃ ht
  have hden :
      0 <
        _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t ^ ((5 : ℝ) / 2) :=
    _root_.GD.N0232.N0719.N0892.d003685 hp₁ hp₂ hp₃ hsum hd₁ hd₂ hd₃ ht
  simp only [_root_.GD.N0232.N0719.N0892.d003673]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hnum) hden.le

theorem d003687
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) (ht : 0 ≤ t) :
    _root_.GD.N0232.N0719.N0892.d003673 p₁ p₂ p₃ d₁ d₂ d₃ t = 0 ↔
      d₁ = d₂ ∧ d₁ = d₃ := by
  have hden :
      _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t ^ ((5 : ℝ) / 2) ≠ 0 :=
    (_root_.GD.N0232.N0719.N0892.d003685 hp₁ hp₂ hp₃ hsum hd₁ hd₂ hd₃ ht).ne'
  simp only [_root_.GD.N0232.N0719.N0892.d003673, div_eq_zero_iff, neg_eq_zero, hden,
    or_false]
  exact
    _root_.GD.N0232.N0719.N0892.d003683
      hd₁ hd₂ hd₃ h₁₂ h₁₃ h₂₃ ht

theorem d003688
    {p₁ p₂ p₃ d₁ d₂ d₃ t : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hsum : p₁ + p₂ + p₃ = 1)
    (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) (hd₃ : 0 ≤ d₃)
    (h₁₂ : 0 < p₁ + p₂) (h₁₃ : 0 < p₁ + p₃)
    (h₂₃ : 0 < p₂ + p₃) (ht : 0 ≤ t)
    (hmismatch : ¬(d₁ = d₂ ∧ d₁ = d₃)) :
    _root_.GD.N0232.N0719.N0892.d003673 p₁ p₂ p₃ d₁ d₂ d₃ t < 0 := by
  have hnum :
      0 < _root_.GD.N0232.N0719.N0892.d003672 p₁ p₂ p₃ d₁ d₂ d₃ t :=
    _root_.GD.N0232.N0719.N0892.d003684
      hd₁ hd₂ hd₃ h₁₂ h₁₃ h₂₃ ht hmismatch
  have hden :
      0 <
        _root_.GD.N0232.N0719.N0892.d003671 p₁ p₂ p₃ d₁ d₂ d₃ t ^ ((5 : ℝ) / 2) :=
    _root_.GD.N0232.N0719.N0892.d003685 hp₁ hp₂ hp₃ hsum hd₁ hd₂ hd₃ ht
  simp only [_root_.GD.N0232.N0719.N0892.d003673]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hnum) hden

end

end GD.N0232.N0719.N0892
