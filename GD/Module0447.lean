import GD.Module0001
import GD.Module0446

























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open _root_.GD.N0232.N0720.N1164
open _root_.GD.N0106.N0428.N0765.N1545

namespace GD.N0106.N0428.N0765.N1541


def d006878 (r : ℕ) : _root_.GD.N0232.N0720.N1164.d006809 :=
  _root_.GD.N0106.N0428.N0765.N1545.d006851.d006817 ((r : ℚ) / 28)

theorem d006879 (r : ℕ) :
    (_root_.GD.N0106.N0428.N0765.N1541.d006878 r).d006810 ((r : ℝ) * Real.pi / 28) := by
  have h := _root_.GD.N0232.N0720.N1164.d006809.d006824 ((r : ℚ) / 28) _root_.GD.N0106.N0428.N0765.N1545.d006852
  have e : (((r : ℚ) / 28 : ℚ) : ℝ) * Real.pi =
      (r : ℝ) * Real.pi / 28 := by
    push_cast
    ring
  rw [e] at h
  exact h



private theorem d006880 : ∀ r : Fin 28,
    0 ≤ (_root_.GD.N0106.N0428.N0765.N1541.d006878 r.val).lo ∧
    (_root_.GD.N0106.N0428.N0765.N1541.d006878 r.val).hi ≤ _root_.GD.N0106.N0428.N0765.N1545.d006851.lo ∧
    |(_root_.GD.N0106.N0428.N0765.N1541.d006878 r.val).lo / 2 ^ 2| ≤ 1 ∧
    |(_root_.GD.N0106.N0428.N0765.N1541.d006878 r.val).hi / 2 ^ 2| ≤ 1 := by
  decide +kernel



def d006881 (r : Fin 29) : _root_.GD.N0232.N0720.N1164.d006809 :=
  if r.val = 0 then _root_.GD.N0106.N0428.N0765.N1545.d006828 1
  else if r.val = 14 then _root_.GD.N0106.N0428.N0765.N1545.d006828 0
  else if r.val = 28 then _root_.GD.N0106.N0428.N0765.N1545.d006828 (-1)
  else _root_.GD.N0106.N0428.N0765.N1545.d006868 (_root_.GD.N0106.N0428.N0765.N1541.d006878 r.val) 2 24

theorem d006882 (r : Fin 29) :
    (_root_.GD.N0106.N0428.N0765.N1541.d006881 r).d006810 ((Real.cos ((r.val : ℝ) * Real.pi / 28))) := by
  by_cases h0 : r.val = 0
  · simp only [_root_.GD.N0106.N0428.N0765.N1541.d006881, if_pos h0]
    simpa [h0] using (_root_.GD.N0106.N0428.N0765.N1545.d006829 (1 : ℚ))
  by_cases h14 : r.val = 14
  · simp only [_root_.GD.N0106.N0428.N0765.N1541.d006881, if_neg h0, if_pos h14]
    have he : (r.val : ℝ) * Real.pi / 28 = Real.pi / 2 := by
      rw [h14]
      norm_num only [Nat.cast_ofNat] <;> ring
    rw [he, Real.cos_pi_div_two]
    simpa using (_root_.GD.N0106.N0428.N0765.N1545.d006829 (0 : ℚ))
  by_cases h28 : r.val = 28
  · simp only [_root_.GD.N0106.N0428.N0765.N1541.d006881, if_neg h0, if_neg h14, if_pos h28]
    have he : (r.val : ℝ) * Real.pi / 28 = Real.pi := by
      rw [h28]
      norm_num only [Nat.cast_ofNat] <;> ring
    rw [he, Real.cos_pi]
    simpa using (_root_.GD.N0106.N0428.N0765.N1545.d006829 (-1 : ℚ))
  · simp only [_root_.GD.N0106.N0428.N0765.N1541.d006881, if_neg h0, if_neg h14, if_neg h28]
    have hr : r.val < 28 := by omega
    have hc := _root_.GD.N0106.N0428.N0765.N1541.d006880 ⟨r.val, hr⟩
    exact _root_.GD.N0106.N0428.N0765.N1545.d006869 (_root_.GD.N0106.N0428.N0765.N1541.d006879 r.val)
      hc.1 (_root_.GD.N0106.N0428.N0765.N1545.d006853 hc.2.1) hc.2.2.1 hc.2.2.2 (by norm_num)


def d006883 (m k : Fin 14) : Fin 29 :=
  let p := m.val * (2 * k.val + 1)
  ⟨min (p % 56) (56 - p % 56), by
    have hp : p % 56 < 56 := Nat.mod_lt p (by norm_num)
    by_cases h : p % 56 ≤ 28
    · have hm := (min_le_left (p % 56) (56 - p % 56)).trans h
      omega
    · have hr : 56 - p % 56 ≤ 28 := by omega
      have hm := (min_le_right (p % 56) (56 - p % 56)).trans hr
      omega⟩


noncomputable def d006884 (m k : Fin 14) : ℝ :=
  Real.cos ((m.val : ℝ) * (2 * (k.val : ℝ) + 1) * Real.pi / 28)


def d006885 (m k : Fin 14) : _root_.GD.N0232.N0720.N1164.d006809 :=
  _root_.GD.N0106.N0428.N0765.N1541.d006881 (_root_.GD.N0106.N0428.N0765.N1541.d006883 m k)

theorem d006886 (m k : Fin 14) :
    _root_.GD.N0106.N0428.N0765.N1541.d006884 m k = Real.cos (((_root_.GD.N0106.N0428.N0765.N1541.d006883 m k).val : ℝ) * Real.pi / 28) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1541.d006884, _root_.GD.N0106.N0428.N0765.N1541.d006883, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
    _root_.GD.N0106.N0428.N0765.N1540.d000001 (m.val * (2 * k.val + 1))


theorem d006887 (m k : Fin 14) :
    (_root_.GD.N0106.N0428.N0765.N1541.d006885 m k).d006810 (_root_.GD.N0106.N0428.N0765.N1541.d006884 m k) := by
  rw [_root_.GD.N0106.N0428.N0765.N1541.d006886]
  exact _root_.GD.N0106.N0428.N0765.N1541.d006882 (_root_.GD.N0106.N0428.N0765.N1541.d006883 m k)



theorem d006888 (m k : Fin 14) (J : _root_.GD.N0232.N0720.N1164.d006809)
    (hlo : J.lo ≤ (_root_.GD.N0106.N0428.N0765.N1541.d006885 m k).lo)
    (hhi : (_root_.GD.N0106.N0428.N0765.N1541.d006885 m k).hi ≤ J.hi) :
    J.d006810 (_root_.GD.N0106.N0428.N0765.N1541.d006884 m k) :=
  _root_.GD.N0106.N0428.N0765.N1545.d006830 (_root_.GD.N0106.N0428.N0765.N1541.d006887 m k) hlo hhi

end GD.N0106.N0428.N0765.N1541

#print axioms _root_.GD.N0106.N0428.N0765.N1541.d006879
#print axioms _root_.GD.N0106.N0428.N0765.N1541.d006882
#print axioms _root_.GD.N0106.N0428.N0765.N1541.d006886
#print axioms _root_.GD.N0106.N0428.N0765.N1541.d006887
#print axioms _root_.GD.N0106.N0428.N0765.N1541.d006888
