import GD.Module1565










set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory

namespace GD.N0106.N0428.N0770.N1723
noncomputable section

open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0232.N0720.N1437

theorem d024288 :
    _root_.GD.N0106.N0428.N0770.N1725.d024116 = (1 / 100000 : ℝ) ∧ _root_.GD.N0106.N0428.N0770.N1725.d024117 = (1 / 250 : ℝ) ∧
      _root_.GD.N0106.N0428.N0770.N1725.d024118 = (1 / 10 ^ 12 : ℝ) ∧ _root_.GD.N0106.N0428.N0770.N1725.d024119 = (1 / 10000 : ℝ) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem d024289 :
    Measurable _root_.GD.N0106.N0428.N0770.N1725.d024130 ∧ Measurable _root_.GD.N0106.N0428.N0770.N1725.d024131 ∧
      (∀ p : ℝ × ℝ, |_root_.GD.N0106.N0428.N0770.N1725.d024130 p| < 1 ∧ |_root_.GD.N0106.N0428.N0770.N1725.d024131 p| ≤ 7) ∧
      (∀ p : ℝ × ℝ, _root_.GD.N0106.N0428.N0770.N1725.d024130 (1 - p.1, p.2) = -_root_.GD.N0106.N0428.N0770.N1725.d024130 p ∧
        _root_.GD.N0106.N0428.N0770.N1725.d024131 (1 - p.1, p.2) = -_root_.GD.N0106.N0428.N0770.N1725.d024131 p) :=
  ⟨_root_.GD.N0106.N0428.N0770.N1725.d024137, _root_.GD.N0106.N0428.N0770.N1725.d024138, fun p => ⟨_root_.GD.N0106.N0428.N0770.N1725.d024142 p, _root_.GD.N0106.N0428.N0770.N1725.d024143 p⟩,
    fun p => ⟨_root_.GD.N0106.N0428.N0770.N1725.d024146 p, _root_.GD.N0106.N0428.N0770.N1725.d024147 p⟩⟩

theorem d024290 :
    Measurable (fun p : ℝ × ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024158 p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
      Measurable (fun p : ℝ × ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024159 p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  ⟨_root_.GD.N0106.N0428.N0770.N1725.d024168 _root_.GD.N0106.N0428.N0770.N1725.d024117 0, _root_.GD.N0106.N0428.N0770.N1725.d024168 _root_.GD.N0106.N0428.N0770.N1725.d024117 _root_.GD.N0106.N0428.N0770.N1725.d024119⟩

theorem d024291 :
    _root_.GD.N0232.N0720.N1437.d003000 _root_.GD.N0106.N0428.N0770.N1725.d024158 ∧ _root_.GD.N0232.N0720.N1437.d003000 _root_.GD.N0106.N0428.N0770.N1725.d024159 :=
  ⟨_root_.GD.N0106.N0428.N0770.N1725.d024165 _root_.GD.N0106.N0428.N0770.N1725.d024117 0, _root_.GD.N0106.N0428.N0770.N1725.d024165 _root_.GD.N0106.N0428.N0770.N1725.d024117 _root_.GD.N0106.N0428.N0770.N1725.d024119⟩

theorem d024292 (a t xbar ybar vx vy : ℝ)
    (hV : vx + vy = 0) :
    _root_.GD.N0106.N0428.N0770.N1725.d024156 a t xbar ybar vx vy = (xbar + ybar) / 2 := by
  rw [_root_.GD.N0106.N0428.N0770.N1725.d024162]
  simp only [_root_.GD.N0106.N0428.N0770.N1725.d024155, hV, if_true, _root_.GD.N0106.N0428.N0770.N1725.d024154, _root_.GD.N0106.N0428.N0770.N1725.d024148, _root_.GD.N0106.N0428.N0770.N1725.d024149,
    mul_zero, add_zero]
  ring

theorem d024293 (xbar ybar vx vy : ℝ) (hV : vx + vy = 0) :
    _root_.GD.N0106.N0428.N0770.N1725.d024158 xbar ybar vx vy = (xbar + ybar) / 2 ∧
      _root_.GD.N0106.N0428.N0770.N1725.d024159 xbar ybar vx vy = (xbar + ybar) / 2 :=
  ⟨_root_.GD.N0106.N0428.N0770.N1723.d024292 _root_.GD.N0106.N0428.N0770.N1725.d024117 0 xbar ybar vx vy hV,
    _root_.GD.N0106.N0428.N0770.N1723.d024292 _root_.GD.N0106.N0428.N0770.N1725.d024117 _root_.GD.N0106.N0428.N0770.N1725.d024119 xbar ybar vx vy hV⟩

theorem d024294 (xbar ybar vx vy : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024158 xbar ybar vx vy = _root_.GD.N0106.N0428.N0770.N1725.d024157 xbar ybar vx vy +
      (1 / 250 : ℝ) * (xbar - ybar) * _root_.GD.N0106.N0428.N0770.N1725.d024130 (_root_.GD.N0106.N0428.N0770.N1725.d024155 xbar ybar vx vy) ∧
    _root_.GD.N0106.N0428.N0770.N1725.d024159 xbar ybar vx vy = _root_.GD.N0106.N0428.N0770.N1725.d024158 xbar ybar vx vy +
      (1 / 10000 : ℝ) * (xbar - ybar) * _root_.GD.N0106.N0428.N0770.N1725.d024131 (_root_.GD.N0106.N0428.N0770.N1725.d024155 xbar ybar vx vy) :=
  ⟨_root_.GD.N0106.N0428.N0770.N1725.d024163 xbar ybar vx vy,
    _root_.GD.N0106.N0428.N0770.N1725.d024164 xbar ybar vx vy⟩

end
end GD.N0106.N0428.N0770.N1723

#print axioms _root_.GD.N0106.N0428.N0770.N1723.d024288
#print axioms _root_.GD.N0106.N0428.N0770.N1723.d024289
#print axioms _root_.GD.N0106.N0428.N0770.N1723.d024290
#print axioms _root_.GD.N0106.N0428.N0770.N1723.d024291
#print axioms _root_.GD.N0106.N0428.N0770.N1723.d024292
#print axioms _root_.GD.N0106.N0428.N0770.N1723.d024293
#print axioms _root_.GD.N0106.N0428.N0770.N1723.d024294
