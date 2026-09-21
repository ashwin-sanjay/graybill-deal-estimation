import GD.Module0392







set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set intervalIntegral

namespace GD.N0203
noncomputable section
open _root_.GD.N0179

def d007246 (a b u : ℝ) : ℝ := ∫ x in a..b, _root_.GD.N0179.d006018 u x

def d007247 (x y : ℝ) : ℝ := x * y / (x + y)

def d007248 (η a b : ℝ) : ℝ := (a / η) * Real.sqrt (a / η) + 8 / b ^ 2

def d007249 (η a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ u in η..(1 - η), _root_.GD.N0203.d007247 (_root_.GD.N0203.d007246 a b u) (_root_.GD.N0203.d007246 a b (1 - u))

def d007250 (η a b : ℝ) : ℝ :=
  ∫ u in η..(1 - η), _root_.GD.N0203.d007246 a b u + _root_.GD.N0203.d007246 a b (1 - u)

theorem d007251 {x y X Y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hX : x ≤ X) (hY : y ≤ Y) :
    _root_.GD.N0203.d007247 x y ≤ _root_.GD.N0203.d007247 X Y := by
  unfold _root_.GD.N0203.d007247
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  have hXp : 0 < X := hx.trans_le hX
  have hYp : 0 < Y := hy.trans_le hY
  have h₁ : 0 ≤ x * X * (Y - y) :=
    mul_nonneg (mul_nonneg hx.le hXp.le) (sub_nonneg.mpr hY)
  have h₂ : 0 ≤ y * Y * (X - x) :=
    mul_nonneg (mul_nonneg hy.le hYp.le) (sub_nonneg.mpr hX)
  nlinarith

theorem d007252 (c x y : ℝ) :
    _root_.GD.N0203.d007247 (c * x) (c * y) = c * _root_.GD.N0203.d007247 x y := by
  unfold _root_.GD.N0203.d007247
  by_cases hc : c = 0
  · simp [hc]
  · by_cases hxy : x + y = 0
    · simp [show c * x + c * y = c * (x + y) by ring, hxy]
    · field_simp

theorem d007253 {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    _root_.GD.N0203.d007247 (1 / u ^ 2) (1 / (1 - u) ^ 2) =
      1 / (u ^ 2 + (1 - u) ^ 2) := by
  unfold _root_.GD.N0203.d007247
  have hsum := _root_.GD.N0179.d006047 u
  have h1 : 1 - u ≠ 0 := by linarith
  field_simp
  ring

theorem d007254 {a b u : ℝ} (hu : 0 < u) (ha : 0 < a) (hab : a ≤ b) :
    _root_.GD.N0203.d007246 a b u = _root_.GD.N0179.d006021 u b - _root_.GD.N0179.d006021 u a :=
  _root_.GD.N0179.d006039 hu ha hab

theorem d007255 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (_root_.GD.N0203.d007246 a b) (Ioi 0) := by
  have hp : ∀ x : ℝ, 0 < x → ContinuousOn (fun u => _root_.GD.N0179.d006021 u x) (Ioi 0) := by
    intro x hx
    unfold _root_.GD.N0179.d006021 _root_.GD.N0179.d006019 _root_.GD.N0179.d006020
    apply ContinuousOn.div
    · apply ContinuousOn.div_const
      apply ContinuousOn.sub
      · apply ContinuousOn.const_mul
        apply ContinuousOn.pow
        apply ContinuousOn.sqrt
        apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro u hu
          have : 0 < u := hu
          positivity
      · apply ContinuousOn.const_mul
        apply ContinuousOn.pow
        apply ContinuousOn.sqrt
        apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro u hu
          have : 0 < u := hu
          positivity
    · fun_prop
    · intro u hu
      exact pow_ne_zero 2 (ne_of_gt hu)
  exact ((hp b (ha.trans_le hab)).sub (hp a ha)).congr
    (fun u hu => _root_.GD.N0203.d007254 hu ha hab)

theorem d007256 {η a b u : ℝ} (hη : 0 < η) (ha : 0 < a) (hab : a ≤ b)
    (hηu : η ≤ u) (hu1 : u < 1) :
    (1 - _root_.GD.N0203.d007248 η a b) / u ^ 2 ≤ _root_.GD.N0203.d007246 a b u ∧ _root_.GD.N0203.d007246 a b u ≤ 1 / u ^ 2 := by
  have hu : 0 < u := hη.trans_le hηu
  have hratio : a / u ≤ a / η := div_le_div_of_nonneg_left ha.le hη hηu
  have htail : (a / u) * Real.sqrt (a / u) ≤ (a / η) * Real.sqrt (a / η) :=
    mul_le_mul hratio (Real.sqrt_le_sqrt hratio) (Real.sqrt_nonneg _)
      (div_nonneg ha.le hη.le)
  obtain ⟨hl, hr⟩ := _root_.GD.N0179.d006044 hu hu1 ha hab
  refine ⟨?_, hr⟩
  apply le_trans _ hl
  apply div_le_div_of_nonneg_right _ (sq_nonneg u)
  unfold _root_.GD.N0203.d007248
  linarith

theorem d007257 {η a b u : ℝ} (hη : 0 < η) (ha : 0 < a) (hab : a ≤ b)
    (hθ : _root_.GD.N0203.d007248 η a b < 1) (hηu : η ≤ u) (hu1 : u < 1) :
    0 < _root_.GD.N0203.d007246 a b u :=
  lt_of_lt_of_le (div_pos (sub_pos.mpr hθ) (sq_pos_of_pos (hη.trans_le hηu)))
    (_root_.GD.N0203.d007256 hη ha hab hηu hu1).1

theorem d007258 {η a b u : ℝ} (hη : 0 < η) (ha : 0 < a)
    (hab : a ≤ b) (hθ : _root_.GD.N0203.d007248 η a b < 1) (hu : u ∈ Icc η (1 - η)) :
    (1 - _root_.GD.N0203.d007248 η a b) * (1 / (u ^ 2 + (1 - u) ^ 2)) ≤
      _root_.GD.N0203.d007247 (_root_.GD.N0203.d007246 a b u) (_root_.GD.N0203.d007246 a b (1 - u)) ∧
    _root_.GD.N0203.d007247 (_root_.GD.N0203.d007246 a b u) (_root_.GD.N0203.d007246 a b (1 - u)) ≤
      1 / (u ^ 2 + (1 - u) ^ 2) := by
  have hu0 : 0 < u := hη.trans_le hu.1
  have hu1 : u < 1 := by linarith [hu.2]
  have hv0 : 0 < 1 - u := by linarith
  have hv1 : 1 - u < 1 := by linarith
  have hηv : η ≤ 1 - u := by linarith [hu.2]
  obtain ⟨hl, hr⟩ := _root_.GD.N0203.d007256 hη ha hab hu.1 hu1
  obtain ⟨hl', hr'⟩ := _root_.GD.N0203.d007256 hη ha hab hηv hv1
  have hpos := _root_.GD.N0203.d007257 hη ha hab hθ hu.1 hu1
  have hpos' := _root_.GD.N0203.d007257 hη ha hab hθ hηv hv1
  constructor
  · have h := _root_.GD.N0203.d007251 (div_pos (sub_pos.mpr hθ) (sq_pos_of_pos hu0))
      (div_pos (sub_pos.mpr hθ) (sq_pos_of_pos hv0)) hl hl'
    rw [show (1 - _root_.GD.N0203.d007248 η a b) / u ^ 2 =
      (1 - _root_.GD.N0203.d007248 η a b) * (1 / u ^ 2) by ring,
      show (1 - _root_.GD.N0203.d007248 η a b) / (1 - u) ^ 2 =
      (1 - _root_.GD.N0203.d007248 η a b) * (1 / (1 - u) ^ 2) by ring,
      _root_.GD.N0203.d007252, _root_.GD.N0203.d007253 hu0 hu1] at h
    exact h
  · simpa only [_root_.GD.N0203.d007253 hu0 hu1] using _root_.GD.N0203.d007251 hpos hpos' hr hr'

theorem d007259 {η a b : ℝ} (hη : 0 < η)
    (hηhalf : η ≤ 1 / 2) (ha : 0 < a) (hab : a ≤ b) (hθ : _root_.GD.N0203.d007248 η a b < 1) :
    IntervalIntegrable (fun u => _root_.GD.N0203.d007247 (_root_.GD.N0203.d007246 a b u) (_root_.GD.N0203.d007246 a b (1 - u)))
      volume η (1 - η) := by
  have hcont : ContinuousOn (_root_.GD.N0203.d007246 a b) (Icc η (1 - η)) :=
    (_root_.GD.N0203.d007255 ha hab).mono (fun u hu => hη.trans_le hu.1)
  have hcont' : ContinuousOn (fun u => _root_.GD.N0203.d007246 a b (1 - u)) (Icc η (1 - η)) := by
    apply (_root_.GD.N0203.d007255 ha hab).comp (by fun_prop)
    intro u hu
    show 0 < 1 - u
    linarith [hu.2]
  have hden : ∀ u ∈ Icc η (1 - η), _root_.GD.N0203.d007246 a b u + _root_.GD.N0203.d007246 a b (1 - u) ≠ 0 := by
    intro u hu
    have hp := _root_.GD.N0203.d007257 hη ha hab hθ hu.1 (by linarith [hu.2])
    have hp' := _root_.GD.N0203.d007257 (u := 1 - u) hη ha hab hθ
      (by linarith [hu.2]) (by linarith [hu.1])
    positivity
  have hc : ContinuousOn (fun u => _root_.GD.N0203.d007247 (_root_.GD.N0203.d007246 a b u) (_root_.GD.N0203.d007246 a b (1 - u)))
      (Icc η (1 - η)) := (hcont.mul hcont').div (hcont.add hcont') hden
  rw [← uIcc_of_le (show η ≤ 1 - η by linarith)] at hc
  exact hc.intervalIntegrable


theorem d007260 {η a b : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) (hθ : _root_.GD.N0203.d007248 η a b < 1) :
    (1 - _root_.GD.N0203.d007248 η a b) * _root_.GD.N0179.d006045 η ≤ _root_.GD.N0203.d007249 η a b ∧
      _root_.GD.N0203.d007249 η a b ≤ _root_.GD.N0179.d006045 η := by
  have hi := _root_.GD.N0203.d007259 hη hηhalf ha hab hθ
  have hj : IntervalIntegrable (fun u : ℝ => 1 / (u ^ 2 + (1 - u) ^ 2))
      volume η (1 - η) := by
    apply Continuous.intervalIntegrable
    exact continuous_const.div (by fun_prop) (fun u => (_root_.GD.N0179.d006047 u).ne')
  have hlo := integral_mono_on (show η ≤ 1 - η by linarith)
    (hj.const_mul (1 - _root_.GD.N0203.d007248 η a b)) hi
    (fun u hu => (_root_.GD.N0203.d007258 hη ha hab hθ hu).1)
  have hup := integral_mono_on (show η ≤ 1 - η by linarith) hi hj
    (fun u hu => (_root_.GD.N0203.d007258 hη ha hab hθ hu).2)
  rw [intervalIntegral.integral_const_mul, _root_.GD.N0179.d006049] at hlo
  rw [_root_.GD.N0179.d006049] at hup
  unfold _root_.GD.N0203.d007249
  constructor <;> linarith


theorem d007261 {η a b : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) (hθ : _root_.GD.N0203.d007248 η a b < 1) :
    0 ≤ Real.pi / 4 - _root_.GD.N0203.d007249 η a b ∧
      Real.pi / 4 - _root_.GD.N0203.d007249 η a b ≤ 2 * η + _root_.GD.N0203.d007248 η a b := by
  obtain ⟨hl, hu⟩ := _root_.GD.N0203.d007260 hη hηhalf ha hab hθ
  have hi := _root_.GD.N0179.d006050 hη.le
  have hdef := _root_.GD.N0179.d006052 hη.le
  have htail : 0 ≤ _root_.GD.N0203.d007248 η a b := by unfold _root_.GD.N0203.d007248; positivity
  have hp : Real.pi / 4 ≤ 1 := by linarith [Real.pi_lt_four]
  have hm := mul_le_mul_of_nonneg_left (hi.trans hp) htail
  constructor <;> nlinarith

end
end GD.N0203

#print axioms _root_.GD.N0203.d007260
#print axioms _root_.GD.N0203.d007261
