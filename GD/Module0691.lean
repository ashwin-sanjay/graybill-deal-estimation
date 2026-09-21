import GD.Module0689
























namespace GD.N0232.N0719.N1005

noncomputable section

open _root_.GD.N0232.N0719.N1015
open _root_.GD.N0232.N0719.N0900


def d010114 (gamma : ℝ) : ℝ := gamma⁻¹

theorem d010115 {gamma : ℝ} (hgamma : 0 < gamma) :
    0 < _root_.GD.N0232.N0719.N1005.d010114 gamma := by
  exact inv_pos.mpr hgamma



theorem d010116
    {gamma C B alpha : ℝ}
    (hgamma : 0 < gamma)
    (hcapacity : B ≤ gamma * (-C)) :
    2 * (alpha / gamma) * C + (alpha / gamma) ^ 2 * B ≤
      (alpha * (2 - alpha) / gamma) * C := by
  have hscaled :
      (alpha / gamma) ^ 2 * B ≤
        (alpha / gamma) ^ 2 * (gamma * (-C)) :=
    mul_le_mul_of_nonneg_left hcapacity (sq_nonneg (alpha / gamma))
  calc
    2 * (alpha / gamma) * C + (alpha / gamma) ^ 2 * B ≤
        2 * (alpha / gamma) * C +
          (alpha / gamma) ^ 2 * (gamma * (-C)) :=
      add_le_add_right hscaled _
    _ = (alpha * (2 - alpha) / gamma) * C := by
      field_simp [ne_of_gt hgamma]
      ring



theorem d010117
    {gamma C B : ℝ}
    (hgamma : 0 < gamma)
    (hcapacity : B ≤ gamma * (-C)) :
    2 * _root_.GD.N0232.N0719.N1005.d010114 gamma * C + _root_.GD.N0232.N0719.N1005.d010114 gamma ^ 2 * B ≤
      _root_.GD.N0232.N0719.N1005.d010114 gamma * C := by
  have h := _root_.GD.N0232.N0719.N1005.d010116
    (gamma := gamma) (C := C) (B := B) (alpha := 1)
    hgamma hcapacity
  unfold _root_.GD.N0232.N0719.N1005.d010114
  convert h using 1 <;>
    field_simp [ne_of_gt hgamma] <;> ring



theorem d010118
    {gamma C B : ℝ}
    (hgamma : 0 < gamma)
    (hcross : C < 0)
    (hcapacity : B ≤ gamma * (-C)) :
    2 * _root_.GD.N0232.N0719.N1005.d010114 gamma * C + _root_.GD.N0232.N0719.N1005.d010114 gamma ^ 2 * B < 0 := by
  exact lt_of_le_of_lt
    (_root_.GD.N0232.N0719.N1005.d010117 hgamma hcapacity)
    (mul_neg_of_pos_of_neg (_root_.GD.N0232.N0719.N1005.d010115 hgamma) hcross)


theorem d010119 (alpha : ℝ) :
    alpha * (2 - alpha) = 1 - (alpha - 1) ^ 2 := by
  ring



theorem d010120 (alpha : ℝ) :
    alpha * (2 - alpha) ≤ 1 := by
  rw [_root_.GD.N0232.N0719.N1005.d010119]
  exact sub_le_self 1 (sq_nonneg (alpha - 1))



theorem d010121 (alpha : ℝ) :
    alpha * (2 - alpha) = 1 ↔ alpha = 1 := by
  rw [_root_.GD.N0232.N0719.N1005.d010119]
  constructor
  · intro h
    have hsquare : (alpha - 1) ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · rintro rfl
    norm_num



theorem d010122
    {alpha : ℝ} (halpha0 : 0 < alpha) (halpha2 : alpha < 2) :
    0 < alpha * (2 - alpha) :=
  mul_pos halpha0 (sub_pos.mpr halpha2)





theorem d010123
    {gamma C B : ℝ}
    (hgamma : 0 < gamma) (hcross : C < 0)
    (hcapacity : B ≤ gamma * (-C)) :
    2 * gamma⁻¹ * C + gamma⁻¹ ^ 2 * B <
      2 * (1 / (1 + gamma)) * C +
        (1 / (1 + gamma)) ^ 2 * B := by
  let e1 : ℝ := gamma⁻¹
  let e0 : ℝ := 1 / (1 + gamma)
  have hden : 0 < 1 + gamma := by linarith
  have he1 : 0 < e1 := by
    exact inv_pos.mpr hgamma
  have he0 : 0 < e0 := by
    exact one_div_pos.mpr hden
  have horder : e0 < e1 := by
    dsimp [e0, e1]
    simpa only [one_div] using
      (one_div_lt_one_div_of_lt hgamma
        (show gamma < 1 + gamma by linarith))
  have hfrac : gamma / (1 + gamma) < 1 :=
    (div_lt_one hden).2 (by linarith)
  have hfactor : gamma * (e1 + e0) < 2 := by
    calc
      gamma * (e1 + e0) = 1 + gamma / (1 + gamma) := by
        dsimp [e1, e0]
        field_simp [ne_of_gt hgamma, ne_of_gt hden]
      _ < 2 := by linarith
  have hscaled :
      B * (e1 + e0) ≤ gamma * (-C) * (e1 + e0) :=
    mul_le_mul_of_nonneg_right hcapacity (add_nonneg he1.le he0.le)
  have hupper : gamma * (-C) * (e1 + e0) < 2 * (-C) := by
    calc
      gamma * (-C) * (e1 + e0) =
          (gamma * (e1 + e0)) * (-C) := by ring
      _ < 2 * (-C) :=
        mul_lt_mul_of_pos_right hfactor (neg_pos.mpr hcross)
  have hbracket : 2 * C + B * (e1 + e0) < 0 := by
    nlinarith [hscaled.trans_lt hupper]
  have hdiff :
      (2 * e1 * C + e1 ^ 2 * B) -
          (2 * e0 * C + e0 ^ 2 * B) =
        (e1 - e0) * (2 * C + B * (e1 + e0)) := by
    ring
  have hproduct :
      (e1 - e0) * (2 * C + B * (e1 + e0)) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr horder) hbracket
  dsimp [e1, e0] at hdiff hproduct ⊢
  nlinarith




theorem d010124
    {gamma C alpha : ℝ} (hgamma : 0 < gamma) :
    2 * (alpha / gamma) * C +
        (alpha / gamma) ^ 2 * (gamma * (-C)) =
      (alpha * (2 - alpha) / gamma) * C := by
  field_simp [ne_of_gt hgamma]
  ring



def d010125
    {k : ℕ} {sizes : Fin k → ℕ}
    {Theta : Type*}
    {law : Theta → MeasureTheory.Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Theta → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Theta law target triangle) : ℝ :=
  _root_.GD.N0232.N0719.N1005.d010114 cert.gamma

theorem d010126
    {k : ℕ} {sizes : Fin k → ℕ}
    {Theta : Type*}
    {law : Theta → MeasureTheory.Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Theta → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Theta law target triangle)
    (hgamma : 0 < cert.gamma) (theta : Theta) :
    2 * _root_.GD.N0232.N0719.N1005.d010125 cert *
          _root_.GD.N0232.N0719.N1015.d010080 (law theta) (target theta) triangle +
        _root_.GD.N0232.N0719.N1005.d010125 cert ^ 2 *
          _root_.GD.N0232.N0719.N1015.d010081 (law theta) triangle < 0 := by
  exact _root_.GD.N0232.N0719.N1005.d010118 hgamma
    (cert.cross_negative theta) (cert.energy_le theta)


theorem d010127
    {k : ℕ} {sizes : Fin k → ℕ}
    {Theta : Type*}
    {law : Theta → MeasureTheory.Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)}
    {target : Theta → ℝ}
    {triangle : Fin 3 ↪ Fin k}
    (cert : _root_.GD.N0232.N0719.N1015.d010082 Theta law target triangle)
    (hgamma : 0 < cert.gamma) (theta : Theta) :
    2 * _root_.GD.N0232.N0719.N1005.d010125 cert *
          _root_.GD.N0232.N0719.N1015.d010080 (law theta) (target theta) triangle +
        _root_.GD.N0232.N0719.N1005.d010125 cert ^ 2 *
          _root_.GD.N0232.N0719.N1015.d010081 (law theta) triangle ≤
      _root_.GD.N0232.N0719.N1005.d010125 cert *
        _root_.GD.N0232.N0719.N1015.d010080 (law theta) (target theta) triangle := by
  exact _root_.GD.N0232.N0719.N1005.d010117 hgamma (cert.energy_le theta)

end

end GD.N0232.N0719.N1005
