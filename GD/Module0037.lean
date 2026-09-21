import Mathlib.Tactic













namespace GD.N0230.N0672

noncomputable section

open Set

variable {Theta : Type*}


def d000445 (vertex : Theta → ℝ) : ℝ :=
  sInf (Set.range vertex)


def d000446
    (base energy vertex : Theta → ℝ) (a : ℝ) (theta : Theta) : ℝ :=
  base theta + energy theta * (a - vertex theta) ^ 2

theorem d000447
    (vertex : Theta → ℝ) (hbdd : BddBelow (Set.range vertex))
    (theta : Theta) :
    _root_.GD.N0230.N0672.d000445 vertex ≤ vertex theta := by
  exact csInf_le hbdd ⟨theta, rfl⟩

variable [Nonempty Theta]



theorem d000448
    (base energy vertex : Theta → ℝ)
    (henergy : ∀ theta, 0 < energy theta)
    (hbdd : BddBelow (Set.range vertex))
    {a : ℝ} (ha : a < _root_.GD.N0230.N0672.d000445 vertex) :
    ∀ theta,
      _root_.GD.N0230.N0672.d000446 base energy vertex (_root_.GD.N0230.N0672.d000445 vertex) theta <
        _root_.GD.N0230.N0672.d000446 base energy vertex a theta := by
  intro theta
  have hstar : _root_.GD.N0230.N0672.d000445 vertex ≤ vertex theta :=
    _root_.GD.N0230.N0672.d000447 vertex hbdd theta
  have hsquare :
      (_root_.GD.N0230.N0672.d000445 vertex - vertex theta) ^ 2 <
        (a - vertex theta) ^ 2 := by
    nlinarith
  unfold _root_.GD.N0230.N0672.d000446
  simpa only [add_comm] using
    (add_lt_add_left
      (mul_lt_mul_of_pos_left hsquare (henergy theta)) (base theta))




theorem d000449
    (base energy vertex : Theta → ℝ)
    (henergy : ∀ theta, 0 < energy theta)
    (hbdd : BddBelow (Set.range vertex))
    {b : ℝ} (hb : _root_.GD.N0230.N0672.d000445 vertex < b) :
    ∃ theta,
      _root_.GD.N0230.N0672.d000446 base energy vertex (_root_.GD.N0230.N0672.d000445 vertex) theta <
        _root_.GD.N0230.N0672.d000446 base energy vertex b theta := by
  have hmid :
      sInf (Set.range vertex) < (_root_.GD.N0230.N0672.d000445 vertex + b) / 2 := by
    change _root_.GD.N0230.N0672.d000445 vertex < (_root_.GD.N0230.N0672.d000445 vertex + b) / 2
    linarith
  obtain ⟨_, ⟨theta, rfl⟩, htheta⟩ :=
    exists_lt_of_csInf_lt (Set.range_nonempty vertex) hmid
  have hstar : _root_.GD.N0230.N0672.d000445 vertex ≤ vertex theta :=
    _root_.GD.N0230.N0672.d000447 vertex hbdd theta
  have hsquare :
      (_root_.GD.N0230.N0672.d000445 vertex - vertex theta) ^ 2 <
        (b - vertex theta) ^ 2 := by
    nlinarith
  refine ⟨theta, ?_⟩
  unfold _root_.GD.N0230.N0672.d000446
  simpa only [add_comm] using
    (add_lt_add_left
      (mul_lt_mul_of_pos_left hsquare (henergy theta)) (base theta))



theorem d000450
    (base energy vertex : Theta → ℝ)
    (henergy : ∀ theta, 0 < energy theta)
    (hbdd : BddBelow (Set.range vertex))
    {b : ℝ} (hb : _root_.GD.N0230.N0672.d000445 vertex < b) :
    ¬ ∀ theta,
      _root_.GD.N0230.N0672.d000446 base energy vertex b theta ≤
        _root_.GD.N0230.N0672.d000446 base energy vertex (_root_.GD.N0230.N0672.d000445 vertex) theta := by
  obtain ⟨theta, htheta⟩ :=
    _root_.GD.N0230.N0672.d000449
      base energy vertex henergy hbdd hb
  intro hall
  exact (not_le_of_gt htheta) (hall theta)



theorem d000451
    {base cross energy a : ℝ} (henergy : energy ≠ 0) :
    base + 2 * a * cross + a ^ 2 * energy =
      (base - cross ^ 2 / energy) +
        energy * (a - (-cross / energy)) ^ 2 := by
  field_simp [henergy]
  ring

end

end GD.N0230.N0672

#print axioms _root_.GD.N0230.N0672.d000448
#print axioms _root_.GD.N0230.N0672.d000449
#print axioms _root_.GD.N0230.N0672.d000450
#print axioms _root_.GD.N0230.N0672.d000451
