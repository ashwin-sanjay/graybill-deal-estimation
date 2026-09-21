import GD.Module1791
import GD.Module1776
import GD.Module1788









set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace GD.N0106.N0428.N0765.N1571

open _root_.GD.N0106.N0428.N0765.N1579 _root_.GD.N0106.N0428.N0765.N1572 _root_.GD.N0106.N0428.N0765.N1578 _root_.GD.N0106.N0428.N0765.N1548


theorem d029820 (f : ℕ → ℕ → ℝ) :
    (∑ k ∈ Finset.range (281 * 161), f (k / 161) (k % 161)) =
      ∑ i ∈ Finset.range 281, ∑ j ∈ Finset.range 161, f i j := by
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun k _ => (k / 161, k % 161))
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  · intro a ha b hb hab
    have h₁ := congrArg Prod.fst hab
    have h₂ := congrArg Prod.snd hab
    dsimp at h₁ h₂
    omega
  · rintro ⟨i, j⟩ hij
    simp only [Finset.mem_product, Finset.mem_range] at hij
    refine ⟨i * 161 + j, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · apply Prod.ext <;> dsimp <;> omega
  · intro k hk
    rfl


theorem d029821 :
    _root_.GD.N0106.N0428.N0765.N1578.d029817 = (1 / 16 : ℝ) ^ 2 *
      ∑ k ∈ Finset.range _root_.GD.N0106.N0428.N0765.N1579.d007475, _root_.GD.N0106.N0428.N0765.N1572.d023813 k := by
  unfold _root_.GD.N0106.N0428.N0765.N1578.d029817
  simp_rw [← Finset.mul_sum]
  rw [← _root_.GD.N0106.N0428.N0765.N1571.d029820]
  unfold _root_.GD.N0106.N0428.N0765.N1579.d007475
  apply congrArg (fun s : ℝ => (1 / 16 : ℝ) ^ 2 * s)
  apply Finset.sum_congr rfl
  intro k hk
  unfold _root_.GD.N0106.N0428.N0765.N1572.d023813 _root_.GD.N0106.N0428.N0765.N1579.d007476 _root_.GD.N0106.N0428.N0765.N1578.d029789 _root_.GD.N0106.N0428.N0765.N1578.d029790
  push_cast
  rfl


theorem d029822 (location : ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1627.d021120 location _root_.GD.N0106.N0428.N0765.N1572.d023746 - _root_.GD.N0106.N0428.N0765.N1578.d029817| ≤
      _root_.GD.N0106.N0428.N0765.N1578.d029795 + _root_.GD.N0106.N0428.N0765.N1577.d029584 := by
  have h := _root_.GD.N0106.N0428.N0765.N1518.d029728 location
    _root_.GD.N0106.N0428.N0765.N1572.d023747 (by norm_num : (0 : ℝ) < 1 / 16)
    (by norm_num : (0 : ℝ) < 7 / 25)
    (by norm_num : (0 : ℝ) < 7 / 50)
    (by have := Real.pi_gt_three; linarith : (21 : ℝ) / 2 * (7 / 25) < Real.pi)
    (by have := Real.pi_gt_three; linarith :
      (21 : ℝ) / 2 * (7 / 50 + 7 / 50) < Real.pi)
    (-14) (-5) 281 161
  rw [_root_.GD.N0106.N0428.N0765.N1578.d029818, _root_.GD.N0106.N0428.N0765.N1578.d029815] at h
  change |_root_.GD.N0106.N0428.N0765.N1627.d021120 location _root_.GD.N0106.N0428.N0765.N1572.d023746 - _root_.GD.N0106.N0428.N0765.N1578.d029817| ≤
    _root_.GD.N0106.N0428.N0765.N1577.d029597 + _root_.GD.N0106.N0428.N0765.N1578.d029795 at h
  rw [← _root_.GD.N0106.N0428.N0765.N1577.d029598] at h
  simpa only [add_comm] using h


theorem d029823 (location : ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1627.d021120 location _root_.GD.N0106.N0428.N0765.N1572.d023746 - _root_.GD.N0106.N0428.N0765.N1578.d029817| ≤
      (419 : ℝ) / 100000000000 := by
  apply (_root_.GD.N0106.N0428.N0765.N1571.d029822 location).trans
  have ht := _root_.GD.N0106.N0428.N0765.N1578.d029810.2
  have hp := _root_.GD.N0106.N0428.N0765.N1577.d029587.2
  change _root_.GD.N0106.N0428.N0765.N1578.d029795 ≤ (_root_.GD.N0106.N0428.N0765.N1582.d007423.hi : ℝ) / (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ) at ht
  change _root_.GD.N0106.N0428.N0765.N1577.d029584 ≤
    (_root_.GD.N0106.N0428.N0765.N1582.d007424.hi : ℝ) / (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ) at hp
  apply (add_le_add ht hp).trans
  norm_num [_root_.GD.N0106.N0428.N0765.N1582.d007423, _root_.GD.N0106.N0428.N0765.N1582.d007424,
    _root_.GD.N0106.N0428.N0765.N1579.d007456, _root_.GD.N0106.N0428.N0765.N1582.d007417, _root_.GD.N0106.N0428.N0765.N1582.d007416]



theorem d029824 (location : ℝ) {I : _root_.GD.N0106.N0428.N0765.N1579.d007457}
    (hI : I.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 _root_.GD.N0106.N0428.N0765.N1578.d029817) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007482 I).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1627.d021120 location _root_.GD.N0106.N0428.N0765.N1572.d023746) := by
  exact _root_.GD.N0106.N0428.N0765.N1572.d023822 hI _root_.GD.N0106.N0428.N0765.N1578.d029810
    _root_.GD.N0106.N0428.N0765.N1577.d029587 (_root_.GD.N0106.N0428.N0765.N1571.d029822 location)



theorem d029825 (location : ℝ) {cache : _root_.GD.N0106.N0428.N0765.N1579.d007463}
    (hc : _root_.GD.N0106.N0428.N0765.N1581.d023715 cache = true)
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007480 cache 0 _root_.GD.N0106.N0428.N0765.N1579.d007475).valid = true)
    (hf : (_root_.GD.N0106.N0428.N0765.N1579.d007481 (_root_.GD.N0106.N0428.N0765.N1579.d007480 cache 0 _root_.GD.N0106.N0428.N0765.N1579.d007475).sum).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007482 (_root_.GD.N0106.N0428.N0765.N1579.d007481 (_root_.GD.N0106.N0428.N0765.N1579.d007480 cache 0 _root_.GD.N0106.N0428.N0765.N1579.d007475).sum)).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456
      (_root_.GD.N0106.N0428.N0765.N1627.d021120 location _root_.GD.N0106.N0428.N0765.N1572.d023746) := by
  apply _root_.GD.N0106.N0428.N0765.N1571.d029824 location
  rw [_root_.GD.N0106.N0428.N0765.N1571.d029821]
  simpa only [zero_add] using _root_.GD.N0106.N0428.N0765.N1572.d023821 hc 0 _root_.GD.N0106.N0428.N0765.N1579.d007475 hv hf


theorem d029826 (location : ℝ)
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007480 _root_.GD.N0106.N0428.N0765.N1575.d007495 0 _root_.GD.N0106.N0428.N0765.N1579.d007475).valid = true)
    (hf : (_root_.GD.N0106.N0428.N0765.N1579.d007481 (_root_.GD.N0106.N0428.N0765.N1579.d007480 _root_.GD.N0106.N0428.N0765.N1575.d007495 0 _root_.GD.N0106.N0428.N0765.N1579.d007475).sum).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007482 (_root_.GD.N0106.N0428.N0765.N1579.d007481 (_root_.GD.N0106.N0428.N0765.N1579.d007480 _root_.GD.N0106.N0428.N0765.N1575.d007495 0 _root_.GD.N0106.N0428.N0765.N1579.d007475).sum)).d007727
      _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1627.d021120 location _root_.GD.N0106.N0428.N0765.N1572.d023746) :=
  _root_.GD.N0106.N0428.N0765.N1571.d029825 location _root_.GD.N0106.N0428.N0765.N1574.d023744 hv hf


theorem d029827 :
    (_root_.GD.N0106.N0428.N0765.N1579.d007482 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007425)).interval =
      _root_.GD.N0106.N0428.N0765.N1582.d007426 := by
  decide +kernel


theorem d029828 (location : ℝ)
    (hfinite : _root_.GD.N0106.N0428.N0765.N1582.d007425.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456 _root_.GD.N0106.N0428.N0765.N1578.d029817) :
    _root_.GD.N0106.N0428.N0765.N1582.d007426.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1627.d021120 location _root_.GD.N0106.N0428.N0765.N1572.d023746) := by
  have h := _root_.GD.N0106.N0428.N0765.N1571.d029824 location (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007728 hfinite)
  change (_root_.GD.N0106.N0428.N0765.N1579.d007482 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007425)).interval.d006928
    _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1627.d021120 location _root_.GD.N0106.N0428.N0765.N1572.d023746) at h
  rwa [_root_.GD.N0106.N0428.N0765.N1571.d029827] at h


theorem d029829 :
    |_root_.GD.N0106.N0428.N0765.N1515.d029731 (Real.log _root_.GD.N0106.N0428.N0765.N1572.d023746) -
      _root_.GD.N0106.N0428.N0765.N1578.d029817 / _root_.GD.N0106.N0428.N0765.N1515.d029729 _root_.GD.N0106.N0428.N0765.N1572.d023746| ≤
      (_root_.GD.N0106.N0428.N0765.N1578.d029795 + _root_.GD.N0106.N0428.N0765.N1577.d029584) /
        _root_.GD.N0106.N0428.N0765.N1515.d029729 _root_.GD.N0106.N0428.N0765.N1572.d023746 := by
  have hp := _root_.GD.N0106.N0428.N0765.N1515.d029741 _root_.GD.N0106.N0428.N0765.N1572.d023747
  have hj := _root_.GD.N0106.N0428.N0765.N1515.d029756 0 (Real.log _root_.GD.N0106.N0428.N0765.N1572.d023746)
  rw [Real.exp_log _root_.GD.N0106.N0428.N0765.N1572.d023747] at hj
  rw [← hj, _root_.GD.N0106.N0428.N0765.N1515.d029730, ← sub_div, abs_div,
    abs_of_pos hp]
  exact div_le_div_of_nonneg_right (_root_.GD.N0106.N0428.N0765.N1571.d029822 0) hp.le

end GD.N0106.N0428.N0765.N1571

#print axioms _root_.GD.N0106.N0428.N0765.N1571.d029822
#print axioms _root_.GD.N0106.N0428.N0765.N1571.d029825
#print axioms _root_.GD.N0106.N0428.N0765.N1571.d029829
