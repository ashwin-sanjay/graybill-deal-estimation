import GD.Module0470

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set intervalIntegral

namespace GD.N0203
noncomputable section


theorem d007262 {η a b : ℝ} (hη : 0 < η)
    (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun u => _root_.GD.N0203.d007246 a b u + _root_.GD.N0203.d007246 a b (1 - u)) (Icc η (1 - η)) := by
  apply ContinuousOn.add
  · exact (_root_.GD.N0203.d007255 ha hab).mono (fun u hu => hη.trans_le hu.1)
  · apply (_root_.GD.N0203.d007255 ha hab).comp (by fun_prop)
    intro u hu
    show 0 < 1 - u
    linarith [hu.2]

theorem d007263 {η : ℝ} (hη : 0 < η) :
    ContinuousOn (fun u : ℝ => 1 / u ^ 2 + 1 / (1 - u) ^ 2) (Icc η (1 - η)) := by
  apply ContinuousOn.add
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    exact pow_ne_zero 2 (ne_of_gt (hη.trans_le hu.1))
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    have hp : 0 < 1 - u := by linarith [hu.2]
    exact pow_ne_zero 2 hp.ne'



theorem d007264 {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    (∫ u : ℝ in η..(1 - η), 1 / u ^ 2 + 1 / (1 - u) ^ 2) =
      2 * (1 / η - 1 / (1 - η)) := by
  have hab : η ≤ 1 - η := by linarith
  have hd : ∀ u ∈ uIcc η (1 - η),
      HasDerivAt (fun v : ℝ => -(1 / v) + 1 / (1 - v))
        (1 / u ^ 2 + 1 / (1 - u) ^ 2) u := by
    intro u hu
    rw [uIcc_of_le hab] at hu
    have hu0 : u ≠ 0 := (hη.trans_le hu.1).ne'
    have hu1 : 1 - u ≠ 0 := ne_of_gt (by linarith [hu.2])
    have hid : HasDerivAt (fun v : ℝ => v) 1 u := hasDerivAt_id u
    have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 u := hasDerivAt_const u 1
    have h := (hid.inv hu0).neg.add ((hconst.sub hid).inv hu1)
    have h' := h.congr_deriv (show -(-1 / u ^ 2) + -(0 - 1) / (1 - u) ^ 2 =
      1 / u ^ 2 + 1 / (1 - u) ^ 2 by ring)
    convert! h' using 1 <;> simp only [one_div]
    funext v
    rfl
  have hi : IntervalIntegrable (fun u : ℝ => 1 / u ^ 2 + 1 / (1 - u) ^ 2)
      volume η (1 - η) := by
    have hc := _root_.GD.N0203.d007263 hη
    rw [← uIcc_of_le hab] at hc
    exact hc.intervalIntegrable
  rw [integral_eq_sub_of_hasDerivAt hd hi]
  simp only [sub_sub_cancel]
  ring



theorem d007265 {η a b : ℝ} (hη : 0 < η) (hηhalf : η < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) (hθ : _root_.GD.N0203.d007248 η a b < 1) :
    0 < _root_.GD.N0203.d007250 η a b ∧ _root_.GD.N0203.d007250 η a b ≤ 2 * (1 / η - 1 / (1 - η)) := by
  have hwin : η < 1 - η := by linarith
  have hc := _root_.GD.N0203.d007262 hη ha hab
  have hpos : ∀ u ∈ Icc η (1 - η), 0 < _root_.GD.N0203.d007246 a b u + _root_.GD.N0203.d007246 a b (1 - u) := by
    intro u hu
    exact add_pos (_root_.GD.N0203.d007257 hη ha hab hθ hu.1 (by linarith [hu.2]))
      (_root_.GD.N0203.d007257 (u := 1 - u) hη ha hab hθ (by linarith [hu.2])
        (by linarith [hu.1]))
  have hi : IntervalIntegrable (fun u => _root_.GD.N0203.d007246 a b u + _root_.GD.N0203.d007246 a b (1 - u))
      volume η (1 - η) := by
    rw [← uIcc_of_le hwin.le] at hc
    exact hc.intervalIntegrable
  have hj : IntervalIntegrable (fun u : ℝ => 1 / u ^ 2 + 1 / (1 - u) ^ 2)
      volume η (1 - η) := by
    have hc' := _root_.GD.N0203.d007263 hη
    rw [← uIcc_of_le hwin.le] at hc'
    exact hc'.intervalIntegrable
  unfold _root_.GD.N0203.d007250
  constructor
  · apply intervalIntegral.integral_pos hwin hc
    · exact fun u hu => (hpos u ⟨hu.1.le, hu.2⟩).le
    · exact ⟨η, ⟨le_rfl, hwin.le⟩, hpos η ⟨le_rfl, hwin.le⟩⟩
  · rw [← _root_.GD.N0203.d007264 hη hηhalf.le]
    apply integral_mono_on hwin.le hi hj
    intro u hu
    exact add_le_add (_root_.GD.N0203.d007256 hη ha hab hu.1 (by linarith [hu.2])).2
      (_root_.GD.N0203.d007256 (u := 1 - u) hη ha hab (by linarith [hu.2])
        (by linarith [hu.1])).2

theorem d007266 {η a b : ℝ} (hη : 0 < η) (hηhalf : η < 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) (hθ : _root_.GD.N0203.d007248 η a b < 1) :
    _root_.GD.N0203.d007250 η a b ≤ 2 / η := by
  have hm := (_root_.GD.N0203.d007265 hη hηhalf ha hab hθ).2
  have hp : 0 < 1 / (1 - η) := one_div_pos.mpr (by linarith)
  rw [show (2 : ℝ) / η = 2 * (1 / η) by ring]
  linarith



theorem d007267 {η a b : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (ha : 0 < a) (hab : a ≤ b) (hθ : _root_.GD.N0203.d007248 η a b < 1) :
    0 ≤ Real.pi / 4 - _root_.GD.N0203.d007249 η a b ∧
      Real.pi / 4 - _root_.GD.N0203.d007249 η a b ≤ 2 * η + (Real.pi / 4) * _root_.GD.N0203.d007248 η a b := by
  obtain ⟨hl, hu⟩ := _root_.GD.N0203.d007260 hη hηhalf ha hab hθ
  have hi := _root_.GD.N0179.d006050 hη.le
  have hdef := _root_.GD.N0179.d006052 hη.le
  have htail : 0 ≤ _root_.GD.N0203.d007248 η a b := by unfold _root_.GD.N0203.d007248; positivity
  have hm := mul_le_mul_of_nonneg_left hi htail
  constructor <;> nlinarith

end
end GD.N0203

#print axioms _root_.GD.N0203.d007265
#print axioms _root_.GD.N0203.d007266
#print axioms _root_.GD.N0203.d007267
