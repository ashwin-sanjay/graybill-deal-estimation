import GD.Module0446










set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open _root_.GD.N0232.N0720.N1164
open _root_.GD.N0106.N0428.N0765.N1545

namespace GD.N0106.N0428.N0765.N1621

def d007628 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨(43702630 : ℚ), (43702631 : ℚ)⟩
def d007629 : _root_.GD.N0232.N0720.N1164.d006809 := _root_.GD.N0106.N0428.N0765.N1545.d006835 2 _root_.GD.N0106.N0428.N0765.N1621.d007628
def d007630 : _root_.GD.N0232.N0720.N1164.d006809 := (_root_.GD.N0106.N0428.N0765.N1621.d007629.d006813 _root_.GD.N0232.N0720.N1164.d006809.d006811).d006815
def d007631 : _root_.GD.N0232.N0720.N1164.d006809 := (_root_.GD.N0106.N0428.N0765.N1621.d007628.d006813 _root_.GD.N0232.N0720.N1164.d006809.d006811).d006815
def d007632 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨(11087551587 / 10000000000 : ℚ), (2771887897 / 2500000000 : ℚ)⟩


theorem d007633 : _root_.GD.N0106.N0428.N0765.N1621.d007628.d006810 (Real.exp ((28 / 5 : ℝ) * Real.pi)) := by
  have h := _root_.GD.N0106.N0428.N0765.N1545.d006849 (k := 5) (n := 12)
    (_root_.GD.N0232.N0720.N1164.d006809.d006824 (28 / 5 : ℚ) _root_.GD.N0106.N0428.N0765.N1545.d006852)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by norm_num)
  have hr : (_root_.GD.N0106.N0428.N0765.N1545.d006848 (_root_.GD.N0106.N0428.N0765.N1545.d006851.d006817 (28 / 5 : ℚ)) 5 12).d006810
      (Real.exp ((28 / 5 : ℝ) * Real.pi)) := by
    convert h using 1 <;> norm_num
  exact _root_.GD.N0106.N0428.N0765.N1545.d006830 hr (by decide +kernel) (by decide +kernel)

theorem d007634 : _root_.GD.N0106.N0428.N0765.N1621.d007629.d006810 (Real.exp ((56 / 5 : ℝ) * Real.pi)) := by
  have h := _root_.GD.N0106.N0428.N0765.N1545.d006836 2 (by decide +kernel : 0 ≤ _root_.GD.N0106.N0428.N0765.N1621.d007628.lo) _root_.GD.N0106.N0428.N0765.N1621.d007633
  have e : Real.exp ((28 / 5 : ℝ) * Real.pi) ^ 2 =
      Real.exp ((56 / 5 : ℝ) * Real.pi) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [e] at h
  exact h

theorem d007635 : _root_.GD.N0106.N0428.N0765.N1621.d007630.d006810
    (1 / (Real.exp ((56 / 5 : ℝ) * Real.pi) - 1)) :=
  _root_.GD.N0232.N0720.N1164.d006809.d006822 (by decide +kernel)
    (_root_.GD.N0232.N0720.N1164.d006809.d006820 _root_.GD.N0106.N0428.N0765.N1621.d007634 _root_.GD.N0232.N0720.N1164.d006809.d006818)

theorem d007636 : _root_.GD.N0106.N0428.N0765.N1621.d007631.d006810
    (1 / (Real.exp ((28 / 5 : ℝ) * Real.pi) - 1)) :=
  _root_.GD.N0232.N0720.N1164.d006809.d006822 (by decide +kernel)
    (_root_.GD.N0232.N0720.N1164.d006809.d006820 _root_.GD.N0106.N0428.N0765.N1621.d007633 _root_.GD.N0232.N0720.N1164.d006809.d006818)

theorem d007637 : _root_.GD.N0106.N0428.N0765.N1621.d007632.d006810
    ((1 / Real.cos (7 / 50 : ℝ)) ^ ((21 : ℝ) / 2)) := by
  have hc : (_root_.GD.N0106.N0428.N0765.N1545.d006866 (7 / 50 : ℚ) 0 12).d006810 (Real.cos (7 / 50 : ℝ)) :=
    by convert (_root_.GD.N0106.N0428.N0765.N1545.d006867 (x := (7 / 50 : ℚ)) (j := 0) (n := 12)
      (by decide +kernel) (by norm_num)) using 1 <;> norm_num
  exact _root_.GD.N0106.N0428.N0765.N1545.d006876 21 hc (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)


theorem d007638 :
    2 * (1 / Real.cos (7 / 50 : ℝ)) ^ ((21 : ℝ) / 2) /
      (Real.exp (2 * Real.pi * (7 / 50) / (1 / 40)) - 1)
      < (117 / 100000000000000000 : ℝ) := by
  have h := _root_.GD.N0106.N0428.N0765.N1545.d006877 _root_.GD.N0106.N0428.N0765.N1621.d007637 _root_.GD.N0106.N0428.N0765.N1621.d007634
    (by decide +kernel) (by decide +kernel)
  have hb : 2 * ((1 / Real.cos (7 / 50 : ℝ)) ^ ((21 : ℝ) / 2) *
      (1 / (Real.exp ((56 / 5 : ℝ) * Real.pi) - 1))) ≤
      ((1162 / 1000000000000000000 : ℚ) : ℝ) :=
    (_root_.GD.N0106.N0428.N0765.N1545.d006830 (J := ⟨0, 1162 / 1000000000000000000⟩) h
      (by decide +kernel) (by decide +kernel)).2
  have e : 2 * Real.pi * (7 / 50 : ℝ) / (1 / 40) = (56 / 5 : ℝ) * Real.pi := by ring
  rw [e]
  calc
    _ = 2 * ((1 / Real.cos (7 / 50 : ℝ)) ^ ((21 : ℝ) / 2) *
      (1 / (Real.exp ((56 / 5 : ℝ) * Real.pi) - 1))) := by ring
    _ ≤ _ := hb
    _ < _ := by norm_num


noncomputable def d007639 (M : ℝ) : ℝ :=
  (2 * M + 2 * M) / (Real.exp (2 * Real.pi * (7 / 50) / (1 / 40)) - 1) +
  4 * M / (Real.exp (2 * Real.pi * (7 / 100) / (1 / 40)) - 1) ^ 2

def d007640 (M : ℚ) : _root_.GD.N0232.N0720.N1164.d006809 :=
  (_root_.GD.N0106.N0428.N0765.N1621.d007630.d006817 (4 * M)).d006812 ((_root_.GD.N0106.N0428.N0765.N1545.d006835 2 _root_.GD.N0106.N0428.N0765.N1621.d007631).d006817 (4 * M))

theorem d007641 (M : ℚ) :
    (_root_.GD.N0106.N0428.N0765.N1621.d007640 M).d006810 (_root_.GD.N0106.N0428.N0765.N1621.d007639 (M : ℝ)) := by
  have ha := _root_.GD.N0232.N0720.N1164.d006809.d006824 (4 * M) _root_.GD.N0106.N0428.N0765.N1621.d007635
  have hm := _root_.GD.N0232.N0720.N1164.d006809.d006824 (4 * M)
    (_root_.GD.N0106.N0428.N0765.N1545.d006836 2 (by decide +kernel : 0 ≤ _root_.GD.N0106.N0428.N0765.N1621.d007631.lo)
      _root_.GD.N0106.N0428.N0765.N1621.d007636)
  have hs := _root_.GD.N0232.N0720.N1164.d006809.d006819 ha hm
  have ea : 2 * Real.pi * (7 / 50 : ℝ) / (1 / 40) = (56 / 5 : ℝ) * Real.pi := by ring
  have em : 2 * Real.pi * (7 / 100 : ℝ) / (1 / 40) = (28 / 5 : ℝ) * Real.pi := by ring
  convert hs using 1
  · rfl
  · unfold _root_.GD.N0106.N0428.N0765.N1621.d007639
    rw [ea, em]
    push_cast
    simp only [div_pow, one_pow]
    ring

theorem d007642 :
    _root_.GD.N0106.N0428.N0765.N1621.d007639 12 < (503 / 10000000000000000 : ℝ) := by
  have h := _root_.GD.N0106.N0428.N0765.N1621.d007641 12
  have hb := (_root_.GD.N0106.N0428.N0765.N1545.d006830 (J := ⟨0, 5027 / 100000000000000000⟩) h
    (by decide +kernel) (by decide +kernel)).2
  exact hb.trans_lt (by norm_num)

theorem d007643 :
    _root_.GD.N0106.N0428.N0765.N1621.d007639 300000 < (126 / 100000000000 : ℝ) := by
  have h := _root_.GD.N0106.N0428.N0765.N1621.d007641 300000
  have hb := (_root_.GD.N0106.N0428.N0765.N1545.d006830 (J := ⟨0, 1257 / 1000000000000⟩) h
    (by decide +kernel) (by decide +kernel)).2
  exact hb.trans_lt (by norm_num)

end GD.N0106.N0428.N0765.N1621

#print axioms _root_.GD.N0106.N0428.N0765.N1621.d007633
#print axioms _root_.GD.N0106.N0428.N0765.N1621.d007634
#print axioms _root_.GD.N0106.N0428.N0765.N1621.d007637
#print axioms _root_.GD.N0106.N0428.N0765.N1621.d007638
#print axioms _root_.GD.N0106.N0428.N0765.N1621.d007641
#print axioms _root_.GD.N0106.N0428.N0765.N1621.d007642
#print axioms _root_.GD.N0106.N0428.N0765.N1621.d007643
