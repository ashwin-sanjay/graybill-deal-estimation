import Mathlib



























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set intervalIntegral

namespace GD.N0179
noncomputable section


def d006018 (u x : ℝ) : ℝ :=
  15 * Real.sqrt x / ((x + 2 * u) ^ 3 * Real.sqrt (x + 2 * u))


def d006019 (y : ℝ) : ℝ := (5 * y ^ 3 - 3 * y ^ 5) / 2


def d006020 (u x : ℝ) : ℝ := Real.sqrt (x / (x + 2 * u))


def d006021 (u x : ℝ) : ℝ := _root_.GD.N0179.d006019 (_root_.GD.N0179.d006020 u x) / u ^ 2

theorem d006022 {u x : ℝ} (hx : 0 ≤ x) :
    _root_.GD.N0179.d006020 u x = Real.sqrt x / Real.sqrt (x + 2 * u) := by
  unfold _root_.GD.N0179.d006020
  exact Real.sqrt_div hx _

theorem d006023 (u x : ℝ) : 0 ≤ _root_.GD.N0179.d006020 u x := Real.sqrt_nonneg _

theorem d006024 {u x : ℝ} (hu : 0 < u) (hx : 0 ≤ x) :
    _root_.GD.N0179.d006020 u x ^ 2 = x / (x + 2 * u) := by
  unfold _root_.GD.N0179.d006020
  exact Real.sq_sqrt (div_nonneg hx (by linarith))

theorem d006025 {u x : ℝ} (hu : 0 < u) (hx : 0 ≤ x) :
    _root_.GD.N0179.d006020 u x ≤ 1 := by
  unfold _root_.GD.N0179.d006020
  apply Real.sqrt_le_one.mpr
  rw [div_le_one (by linarith)]
  linarith

theorem d006026 {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ _root_.GD.N0179.d006019 y := by
  unfold _root_.GD.N0179.d006019
  have h3 : 0 ≤ y ^ 3 := pow_nonneg hy0 3
  have h2 : y ^ 2 ≤ 1 := by nlinarith
  nlinarith


theorem d006027 (y : ℝ) :
    1 - _root_.GD.N0179.d006019 y = (1 - y) ^ 2 * (2 + 4 * y + 6 * y ^ 2 + 3 * y ^ 3) / 2 := by
  unfold _root_.GD.N0179.d006019
  ring

theorem d006028 {y : ℝ} (hy0 : 0 ≤ y) :
    _root_.GD.N0179.d006019 y ≤ 1 := by
  have h := _root_.GD.N0179.d006027 y
  have hp : 0 ≤ (1 - y) ^ 2 * (2 + 4 * y + 6 * y ^ 2 + 3 * y ^ 3) / 2 := by positivity
  linarith


theorem d006029 {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - _root_.GD.N0179.d006019 y ≤ 15 / 8 * (1 - y ^ 2) ^ 2 := by
  rw [_root_.GD.N0179.d006027]
  have hsq : 0 ≤ (1 - y) ^ 2 := sq_nonneg _

  have hpoly : 2 + 4 * y + 6 * y ^ 2 + 3 * y ^ 3 ≤ 15 / 4 * (1 + y) ^ 2 := by
    have : 0 ≤ (1 - y) * (7 / 4 + 21 / 4 * y + 3 * y ^ 2) :=
      mul_nonneg (sub_nonneg.mpr hy1) (by positivity)
    nlinarith
  have hfac : (1 - y ^ 2) ^ 2 = (1 - y) ^ 2 * (1 + y) ^ 2 := by ring
  rw [hfac]
  nlinarith [mul_le_mul_of_nonneg_left hpoly hsq]

theorem d006030 {y : ℝ} (hy0 : 0 ≤ y) :
    _root_.GD.N0179.d006019 y ≤ 5 / 2 * y ^ 3 := by
  unfold _root_.GD.N0179.d006019
  have : 0 ≤ y ^ 5 := pow_nonneg hy0 5
  linarith

theorem d006031 {u x : ℝ} (hu : 0 < u) (hx : 0 ≤ x) :
    0 ≤ _root_.GD.N0179.d006021 u x := by
  unfold _root_.GD.N0179.d006021
  exact div_nonneg (_root_.GD.N0179.d006026 (_root_.GD.N0179.d006023 u x) (_root_.GD.N0179.d006025 hu hx))
    (by positivity)

theorem d006032 (u x : ℝ) :
    _root_.GD.N0179.d006021 u x ≤ 1 / u ^ 2 := by
  unfold _root_.GD.N0179.d006021
  exact div_le_div_of_nonneg_right
    (_root_.GD.N0179.d006028 (_root_.GD.N0179.d006023 u x)) (sq_nonneg u)

theorem d006033 (u : ℝ) : _root_.GD.N0179.d006021 u 0 = 0 := by
  unfold _root_.GD.N0179.d006021 _root_.GD.N0179.d006019 _root_.GD.N0179.d006020
  simp


theorem d006034 {u x : ℝ} (hu : 0 < u) (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => y / (y + 2 * u))
      ((1 * (x + 2 * u) - x * 1) / (x + 2 * u) ^ 2) x :=
  (hasDerivAt_id x).div ((hasDerivAt_id x).add_const (2 * u))
    (add_pos_of_nonneg_of_pos hx (mul_pos two_pos hu)).ne'

theorem d006035 {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (_root_.GD.N0179.d006020 u)
      (((1 * (x + 2 * u) - x * 1) / (x + 2 * u) ^ 2) /
        (2 * Real.sqrt (x / (x + 2 * u)))) x := by
  have hpos : 0 < x / (x + 2 * u) := div_pos hx (by positivity)
  exact (_root_.GD.N0179.d006034 hu hx.le).sqrt hpos.ne'


theorem d006036 {u x : ℝ} (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (_root_.GD.N0179.d006021 u) (_root_.GD.N0179.d006018 u x) x := by
  have hy := _root_.GD.N0179.d006035 hu hx
  have h3 := (((hy.pow 3).const_mul 5).sub ((hy.pow 5).const_mul 3)).div_const 2
  have h4 := h3.div_const (u ^ 2)
  refine h4.congr_deriv ?_
  unfold _root_.GD.N0179.d006018
  rw [show Real.sqrt (x / (x + 2 * u)) = _root_.GD.N0179.d006020 u x from rfl, _root_.GD.N0179.d006022 hx.le]
  obtain ⟨s₁, hs₁, rfl⟩ : ∃ s, 0 < s ∧ x = s ^ 2 :=
    ⟨Real.sqrt x, Real.sqrt_pos.2 hx, (Real.sq_sqrt hx.le).symm⟩
  rw [Real.sqrt_sq hs₁.le]
  obtain ⟨s₂, hs₂, hs₂def⟩ : ∃ s, 0 < s ∧ Real.sqrt (s₁ ^ 2 + 2 * u) = s :=
    ⟨_, Real.sqrt_pos.2 (by positivity), rfl⟩
  have hs₂sq : s₂ ^ 2 = s₁ ^ 2 + 2 * u := by
    rw [← hs₂def]; exact Real.sq_sqrt (by positivity)
  rw [hs₂def]
  have hu' : u = (s₂ ^ 2 - s₁ ^ 2) / 2 := by linarith
  subst hu'
  have hne : s₂ ^ 2 - s₁ ^ 2 ≠ 0 := by
    have : 0 < s₂ ^ 2 - s₁ ^ 2 := by nlinarith
    exact this.ne'
  have hs₁ne : s₁ ≠ 0 := hs₁.ne'
  have hs₂ne : s₂ ≠ 0 := hs₂.ne'
  simp only [show (3 : ℕ) - 1 = 2 from rfl, show (5 : ℕ) - 1 = 4 from rfl, div_pow]
  field_simp
  ring

theorem d006037 {u : ℝ} (hu : 0 < u) :
    ContinuousOn (_root_.GD.N0179.d006018 u) (Ici 0) := by
  unfold _root_.GD.N0179.d006018
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    have : 0 < x + 2 * u := by linarith [mem_Ici.mp hx]
    positivity

theorem d006038 {u a b : ℝ} (hu : 0 < u) (ha : 0 < a)
    (hab : a ≤ b) : IntervalIntegrable (_root_.GD.N0179.d006018 u) volume a b := by
  apply (_root_.GD.N0179.d006037 hu).mono ?_ |>.intervalIntegrable
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact mem_Ici.mpr (ha.le.trans hx.1)


theorem d006039 {u a b : ℝ} (hu : 0 < u) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, _root_.GD.N0179.d006018 u x = _root_.GD.N0179.d006021 u b - _root_.GD.N0179.d006021 u a := by
  apply integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact _root_.GD.N0179.d006036 hu (ha.trans_le hx.1)
  · exact _root_.GD.N0179.d006038 hu ha hab


theorem d006040 {u a b : ℝ} (hu : 0 < u) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, _root_.GD.N0179.d006018 u x ≤ 1 / u ^ 2 := by
  rw [_root_.GD.N0179.d006039 hu ha hab]
  linarith [_root_.GD.N0179.d006032 u b, _root_.GD.N0179.d006031 hu ha.le]

theorem d006041 {u a b : ℝ} (hu : 0 < u) (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ ∫ x in a..b, _root_.GD.N0179.d006018 u x := by
  rw [_root_.GD.N0179.d006039 hu ha hab]
  have hmono : _root_.GD.N0179.d006021 u a ≤ _root_.GD.N0179.d006021 u b := by
    have := _root_.GD.N0179.d006039 hu ha hab
    have hnn : 0 ≤ ∫ x in a..b, _root_.GD.N0179.d006018 u x := by
      apply integral_nonneg hab
      intro x hx
      unfold _root_.GD.N0179.d006018
      have : 0 < x + 2 * u := by linarith [hx.1]
      positivity
    linarith
  linarith


theorem d006042 {u a : ℝ} (hu : 0 < u) (ha : 0 < a) :
    u ^ 2 * _root_.GD.N0179.d006021 u a ≤ (a / u) * Real.sqrt (a / u) := by
  unfold _root_.GD.N0179.d006021
  rw [mul_div_cancel₀ _ (by positivity)]
  set y := _root_.GD.N0179.d006020 u a with hy
  set r := Real.sqrt (a / u) with hr
  have hy0 : 0 ≤ y := _root_.GD.N0179.d006023 u a
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = a / u := Real.sq_sqrt (by positivity)

  have hy2 : 2 * y ^ 2 ≤ r ^ 2 := by
    rw [hy, _root_.GD.N0179.d006024 hu ha.le, hr2]
    rw [show 2 * (a / (a + 2 * u)) = a / ((a + 2 * u) / 2) by field_simp]
    apply div_le_div_of_nonneg_left ha.le (by positivity)
    linarith
  have hcube : 5 / 2 * y ^ 3 ≤ r ^ 3 := by
    have h6 : (2 * y ^ 2) ^ 3 ≤ (r ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) hy2 3
    have hsq : (5 / 2 * y ^ 3) ^ 2 ≤ (r ^ 3) ^ 2 := by nlinarith [pow_nonneg hr0 6]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  calc _root_.GD.N0179.d006019 y ≤ 5 / 2 * y ^ 3 := _root_.GD.N0179.d006030 hy0
    _ ≤ r ^ 3 := hcube
    _ = (a / u) * r := by rw [← hr2]; ring


theorem d006043 {u b : ℝ} (hu : 0 < u) (hb : 0 < b) :
    1 / u ^ 2 - _root_.GD.N0179.d006021 u b ≤ 8 / b ^ 2 := by
  unfold _root_.GD.N0179.d006021
  set y := _root_.GD.N0179.d006020 u b with hy
  have hy0 : 0 ≤ y := _root_.GD.N0179.d006023 u b
  have hy1 : y ≤ 1 := _root_.GD.N0179.d006025 hu hb.le
  have hy2 : 1 - y ^ 2 = 2 * u / (b + 2 * u) := by
    rw [hy, _root_.GD.N0179.d006024 hu hb.le]; field_simp; ring
  have hF := _root_.GD.N0179.d006029 hy0 hy1
  rw [hy2] at hF

  have hfrac : 2 * u / (b + 2 * u) ≤ 2 * u / b :=
    div_le_div_of_nonneg_left (by positivity) hb (by linarith)
  have hsq : (2 * u / (b + 2 * u)) ^ 2 ≤ (2 * u / b) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hfrac 2
  have hbound : 1 - _root_.GD.N0179.d006019 y ≤ 8 * u ^ 2 / b ^ 2 := by
    calc 1 - _root_.GD.N0179.d006019 y ≤ 15 / 8 * (2 * u / (b + 2 * u)) ^ 2 := hF
      _ ≤ 15 / 8 * (2 * u / b) ^ 2 := by gcongr
      _ = 15 / 2 * u ^ 2 / b ^ 2 := by ring
      _ ≤ 8 * u ^ 2 / b ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
  have hu2 : 0 < u ^ 2 := by positivity
  rw [show 1 / u ^ 2 - _root_.GD.N0179.d006019 y / u ^ 2 = (1 - _root_.GD.N0179.d006019 y) / u ^ 2 by ring,
    div_le_iff₀ hu2]
  calc 1 - _root_.GD.N0179.d006019 y ≤ 8 * u ^ 2 / b ^ 2 := hbound
    _ = 8 / b ^ 2 * u ^ 2 := by ring



theorem d006044 {u a b : ℝ} (hu : 0 < u) (hu1 : u < 1) (ha : 0 < a) (hab : a ≤ b) :
    (1 - ((a / u) * Real.sqrt (a / u) + 8 / b ^ 2)) / u ^ 2 ≤
        ∫ x in a..b, _root_.GD.N0179.d006018 u x ∧
      ∫ x in a..b, _root_.GD.N0179.d006018 u x ≤ 1 / u ^ 2 := by
  refine ⟨?_, _root_.GD.N0179.d006040 hu ha hab⟩
  rw [_root_.GD.N0179.d006039 hu ha hab]
  have hb : 0 < b := ha.trans_le hab
  have hsmall := _root_.GD.N0179.d006042 hu ha
  have hlarge := _root_.GD.N0179.d006043 hu hb
  have hu2 : 0 < u ^ 2 := by positivity
  rw [div_le_iff₀ hu2, sub_mul]
  have hGa : _root_.GD.N0179.d006021 u a * u ^ 2 ≤ (a / u) * Real.sqrt (a / u) := by linarith
  have h2 : (1 / u ^ 2 - 8 / b ^ 2) * u ^ 2 ≤ _root_.GD.N0179.d006021 u b * u ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hu2.le
  rw [sub_mul, one_div, inv_mul_cancel₀ hu2.ne'] at h2
  have h4 : 8 / b ^ 2 * u ^ 2 ≤ 8 / b ^ 2 :=
    mul_le_of_le_one_right (by positivity) (by nlinarith)
  linarith




def d006045 (η : ℝ) : ℝ := Real.arctan (1 - 2 * η)

theorem d006046 : _root_.GD.N0179.d006045 0 = Real.pi / 4 := by
  unfold _root_.GD.N0179.d006045
  simp [Real.arctan_one]

theorem d006047 (u : ℝ) : 0 < u ^ 2 + (1 - u) ^ 2 := by
  nlinarith [sq_nonneg (2 * u - 1)]

theorem d006048 (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.arctan (2 * v - 1)) (1 / (u ^ 2 + (1 - u) ^ 2)) u := by
  have h := (Real.hasDerivAt_arctan (2 * u - 1)).comp u
    (((hasDerivAt_id u).const_mul 2).sub_const 1)
  refine h.congr_deriv ?_
  have := _root_.GD.N0179.d006047 u
  field_simp
  ring


theorem d006049 (η : ℝ) :
    ∫ u in η..(1 - η), 1 / (u ^ 2 + (1 - u) ^ 2) = 2 * _root_.GD.N0179.d006045 η := by
  rw [integral_eq_sub_of_hasDerivAt (fun u _ => _root_.GD.N0179.d006048 u)]
  · unfold _root_.GD.N0179.d006045
    rw [show 2 * (1 - η) - 1 = 1 - 2 * η by ring, show 2 * η - 1 = -(1 - 2 * η) by ring,
      Real.arctan_neg]
    ring
  · apply Continuous.intervalIntegrable
    apply continuous_const.div (by fun_prop)
    intro u
    exact (_root_.GD.N0179.d006047 u).ne'

theorem d006050 {η : ℝ} (hη : 0 ≤ η) :
    _root_.GD.N0179.d006045 η ≤ Real.pi / 4 := by
  unfold _root_.GD.N0179.d006045
  rw [← Real.arctan_one]
  exact Real.arctan_strictMono.monotone (by linarith)

theorem d006051 {η : ℝ} (hη : η ≤ 1 / 2) : 0 ≤ _root_.GD.N0179.d006045 η := by
  unfold _root_.GD.N0179.d006045
  rw [← Real.arctan_zero]
  exact Real.arctan_strictMono.monotone (by linarith)


theorem d006052 {η : ℝ} (hη : 0 ≤ η) :
    Real.pi / 4 - _root_.GD.N0179.d006045 η ≤ 2 * η := by
  unfold _root_.GD.N0179.d006045
  rw [← Real.arctan_one]
  have hint : ∫ t in (1 - 2 * η)..1, 1 / (1 + t ^ 2) =
      Real.arctan 1 - Real.arctan (1 - 2 * η) := by
    apply integral_eq_sub_of_hasDerivAt (fun t _ => Real.hasDerivAt_arctan t)
    apply Continuous.intervalIntegrable
    apply continuous_const.div (by fun_prop)
    intro t; positivity
  rw [← hint]
  calc ∫ t in (1 - 2 * η)..1, 1 / (1 + t ^ 2) ≤ ∫ t in (1 - 2 * η)..1, (1 : ℝ) := by
        apply integral_mono_on (by linarith)
        · apply Continuous.intervalIntegrable
          apply continuous_const.div (by fun_prop)
          intro t; positivity
        · exact continuous_const.intervalIntegrable _ _
        · intro t _
          rw [div_le_one (by positivity)]
          nlinarith [sq_nonneg t]
    _ = 2 * η := by simp

end
end GD.N0179

#print axioms _root_.GD.N0179.d006036
#print axioms _root_.GD.N0179.d006039
#print axioms _root_.GD.N0179.d006044
#print axioms _root_.GD.N0179.d006049
#print axioms _root_.GD.N0179.d006052
#print axioms _root_.GD.N0179.d006042
#print axioms _root_.GD.N0179.d006043
#print axioms _root_.GD.N0179.d006040
#print axioms _root_.GD.N0179.d006041
#print axioms _root_.GD.N0179.d006046
#print axioms _root_.GD.N0179.d006050
#print axioms _root_.GD.N0179.d006051
