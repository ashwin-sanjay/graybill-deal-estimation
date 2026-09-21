import GD.Module1616









set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1730
noncomputable section
open _root_.GD.N0106.N0428.N0770.N1725 _root_.GD.N0106.N0428.N0770.N1728 _root_.GD.N0106.N0428.N0770.N1733

def d027616 (m q : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024130 p + m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024130 p ^ 2

def d027617 (m q : ℝ) : ℝ :=
  (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * ∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1730.d027616 m q p ∂(volume.prod volume)

theorem d027618 (m q : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1730.d027617 m q = (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
      ∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1730.d027616 m q p ∂(volume.prod volume) := by
  unfold _root_.GD.N0106.N0428.N0770.N1730.d027617
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  simp [_root_.GD.N0106.N0428.N0770.N1730.d027616, _root_.GD.N0106.N0428.N0770.N1733.d027576 hp]

theorem d027619 (m q : ℝ) :
    (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1730.d027616 m q p) =
      fun p => ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
        (2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i * ((p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1733.d027568 i p) +
          m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1733.d027568 i p ^ 2)) := by
  funext p
  rw [_root_.GD.N0106.N0428.N0770.N1730.d027616, _root_.GD.N0106.N0428.N0770.N1733.d027574, _root_.GD.N0106.N0428.N0770.N1733.d027569]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d027620 (m : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hgeom : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, 0 < _root_.GD.N0106.N0428.N0770.N1733.d027580 i ∧ _root_.GD.N0106.N0428.N0770.N1733.d027581 i < 1 ∧ 0 < _root_.GD.N0106.N0428.N0770.N1733.d027582 i) :
    (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1730.d027616 m q p ∂(volume.prod volume)) =
      ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
        (2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i *
          (∫ p, (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1733.d027568 i p ∂(volume.prod volume)) +
          m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 *
            (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1733.d027568 i p ^ 2 ∂(volume.prod volume))) := by
  have hi : ∀ i ∈ (Finset.univ : Finset _root_.GD.N0106.N0428.N0770.N1728.d024386),
      Integrable (fun p : ℝ × ℝ =>
        2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i * ((p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1733.d027568 i p) +
          m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1733.d027568 i p ^ 2))
        (volume.prod volume) := fun i _ =>
    ((_root_.GD.N0106.N0428.N0770.N1733.d027587 hq (hgeom i).1 (hgeom i).2.1 (hgeom i).2.2).const_mul _).add
      ((_root_.GD.N0106.N0428.N0770.N1733.d027588 hq (hgeom i).1 (hgeom i).2.1 (hgeom i).2.2).const_mul _)
  rw [_root_.GD.N0106.N0428.N0770.N1730.d027619, integral_finsetSum _ hi]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_add
    ((_root_.GD.N0106.N0428.N0770.N1733.d027587 hq (hgeom i).1 (hgeom i).2.1 (hgeom i).2.2).const_mul _)
    ((_root_.GD.N0106.N0428.N0770.N1733.d027588 hq (hgeom i).1 (hgeom i).2.1 (hgeom i).2.2).const_mul _),
    integral_const_mul, integral_const_mul]

theorem d027621 (m : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hgeom : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, 0 < _root_.GD.N0106.N0428.N0770.N1733.d027580 i ∧ _root_.GD.N0106.N0428.N0770.N1733.d027581 i < 1 ∧ 0 < _root_.GD.N0106.N0428.N0770.N1733.d027582 i) :
    _root_.GD.N0106.N0428.N0770.N1730.d027617 m q - _root_.GD.N0106.N0428.N0770.N1728.d024396 m q = ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
      (2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i * ((_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
          (∫ p, (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1733.d027568 i p ∂(volume.prod volume)) -
          ((_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i)) +
        m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * ((_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
          (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1733.d027568 i p ^ 2 ∂(volume.prod volume)) -
          (4 / 9) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i))) := by
  rw [_root_.GD.N0106.N0428.N0770.N1730.d027618, _root_.GD.N0106.N0428.N0770.N1730.d027620 m hq hgeom,
    _root_.GD.N0106.N0428.N0770.N1728.d024407, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d027622 (m : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hgeom : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, 0 < _root_.GD.N0106.N0428.N0770.N1733.d027580 i ∧ _root_.GD.N0106.N0428.N0770.N1733.d027581 i < 1 ∧ 0 < _root_.GD.N0106.N0428.N0770.N1733.d027582 i)
    {err1 err2 : _root_.GD.N0106.N0428.N0770.N1728.d024386 → ℝ}
    (h1 : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, |(_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
        (∫ p, (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1733.d027568 i p ∂(volume.prod volume)) -
        ((_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i)| ≤ err1 i)
    (h2 : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, |(_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
        (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1733.d027568 i p ^ 2 ∂(volume.prod volume)) -
        (4 / 9) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i)| ≤ err2 i) :
    |_root_.GD.N0106.N0428.N0770.N1730.d027617 m q - _root_.GD.N0106.N0428.N0770.N1728.d024396 m q| ≤ ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
      (2 * |_root_.GD.N0106.N0428.N0770.N1728.d024390 i| * err1 i +
        |m| * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * err2 i) := by
  rw [_root_.GD.N0106.N0428.N0770.N1730.d027621 m hq hgeom]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro i _
  have hc : |m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2| =
      |m| * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos _root_.GD.N0106.N0428.N0770.N1725.d024122, abs_of_nonneg (sq_nonneg (_root_.GD.N0106.N0428.N0770.N1728.d024390 i))]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul (2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i), abs_mul (2 : ℝ) (_root_.GD.N0106.N0428.N0770.N1728.d024390 i),
    abs_two, abs_mul (m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2), hc]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (h1 i) (by positivity))
    (mul_le_mul_of_nonneg_left (h2 i)
      (mul_nonneg (mul_nonneg (abs_nonneg _) _root_.GD.N0106.N0428.N0770.N1725.d024122.le) (sq_nonneg _)))


theorem d027623 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (1 / 2)) :
    |_root_.GD.N0106.N0428.N0770.N1730.d027617 3 q - _root_.GD.N0106.N0428.N0770.N1728.d024398 q| < 718 / 1000000 := by
  have hq1 : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1, hq.2.trans (by norm_num)⟩
  have h := _root_.GD.N0106.N0428.N0770.N1730.d027622 3 hq1 _root_.GD.N0106.N0428.N0770.N1734.d027602
    (fun i => (_root_.GD.N0106.N0428.N0770.N1734.d027611 hq i).1)
    (fun i => (_root_.GD.N0106.N0428.N0770.N1734.d027611 hq i).2)
  have hh : |_root_.GD.N0106.N0428.N0770.N1730.d027617 3 q - _root_.GD.N0106.N0428.N0770.N1728.d024398 q| ≤ ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
      (2 * |_root_.GD.N0106.N0428.N0770.N1728.d024390 i| * _root_.GD.N0106.N0428.N0770.N1734.d027600 i +
        3 * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * _root_.GD.N0106.N0428.N0770.N1734.d027601 i) := by
    simpa only [_root_.GD.N0106.N0428.N0770.N1728.d024398, abs_of_pos (by norm_num : (0 : ℝ) < 3)] using h
  exact hh.trans_lt _root_.GD.N0106.N0428.N0770.N1734.d027613

end
end GD.N0106.N0428.N0770.N1730

#print axioms _root_.GD.N0106.N0428.N0770.N1730.d027620
#print axioms _root_.GD.N0106.N0428.N0770.N1730.d027622
#print axioms _root_.GD.N0106.N0428.N0770.N1730.d027623
