import GD.Module0479
import GD.Module0513
import GD.Module1296




set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open _root_.GD.N0232.N0720.N1164

namespace GD.N0106.N0428.N0765.N1573
open _root_.GD.N0106.N0428.N0765.N1548 _root_.GD.N0106.N0428.N0765.N1545 _root_.GD.N0106.N0428.N0765.N1582

theorem d022632 : (0 : ℤ) < _root_.GD.N0106.N0428.N0765.N1582.d007417 := by decide +kernel

theorem d022633 : _root_.GD.N0106.N0428.N0765.N1582.d007421.d006928 _root_.GD.N0106.N0428.N0765.N1582.d007417 (Real.exp (1 / 16)) := by
  have h := _root_.GD.N0106.N0428.N0765.N1545.d006845 (y := 1 / 16) (n := 24) (by norm_num) (by decide)
  have hc := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006932 _root_.GD.N0106.N0428.N0765.N1573.d022632 h
    (J := _root_.GD.N0106.N0428.N0765.N1582.d007421) (by decide +kernel)
  simpa using hc

def d022634 : _root_.GD.N0106.N0428.N0765.N1548.d006926 :=
  ⟨2847269000965159388862228488058035763263159335662124597736,
   2847269000965159388862228488100232967615142733300501494672⟩

def d022635 : _root_.GD.N0106.N0428.N0765.N1548.d006926 :=
  ⟨25277328797406239448420745661625926058433309976531668684887312,
   25277328797406239448420745665559394370677796656527043235767922⟩

def d022636 : _root_.GD.N0106.N0428.N0765.N1548.d006926 :=
  ⟨6371931249439381671368279717694682265268693697932683718624586387314392,
   6371931249439381671929018294495438773333728208817858029303698364215979⟩

theorem d022637 : _root_.GD.N0106.N0428.N0765.N1573.d022634.d006928 _root_.GD.N0106.N0428.N0765.N1582.d007417 (Real.cos (11 / 10)) := by
  have h := _root_.GD.N0106.N0428.N0765.N1545.d006867 (x := 11 / 10) (j := 1) (n := 24)
    (by norm_num) (by decide)
  have hc := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006932 _root_.GD.N0106.N0428.N0765.N1573.d022632 h
    (J := _root_.GD.N0106.N0428.N0765.N1573.d022634) (by decide +kernel)
  simpa using hc

theorem d022638 : _root_.GD.N0106.N0428.N0765.N1573.d022635.d006928 _root_.GD.N0106.N0428.N0765.N1582.d007417 ((Real.cos (11 / 10)) ^ (-21 / 2 : ℝ)) := by
  have hc := _root_.GD.N0106.N0428.N0765.N1573.d022637
  have hcp : 0 < _root_.GD.N0106.N0428.N0765.N1573.d022634.lo := by decide +kernel
  have hi := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006966 _root_.GD.N0106.N0428.N0765.N1573.d022632 hcp hc
  have hp := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006967 _root_.GD.N0106.N0428.N0765.N1573.d022632
    (I := _root_.GD.N0106.N0428.N0765.N1573.d022634.d006945 _root_.GD.N0106.N0428.N0765.N1582.d007417) (by decide +kernel) hi 21
  have hk := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006968 _root_.GD.N0106.N0428.N0765.N1573.d022632 hp
    (J := _root_.GD.N0106.N0428.N0765.N1573.d022635) (by decide +kernel)
  have hc0 : (0 : ℝ) ≤ Real.cos (11 / 10) :=
    _root_.GD.N0106.N0428.N0765.N1548.d006926.d006956 _root_.GD.N0106.N0428.N0765.N1573.d022632 hcp.le hc
  have heq : Real.sqrt ((1 / Real.cos (11 / 10)) ^ 21) =
      (Real.cos (11 / 10)) ^ (-21 / 2 : ℝ) := by
    rw [← _root_.GD.N0106.N0428.N0765.N1545.d006875 (by positivity) 21, one_div,
      Real.inv_rpow hc0, ← Real.rpow_neg hc0]
    norm_num
  simpa only [heq] using hk

def d022639 : _root_.GD.N0232.N0720.N1164.d006809 := _root_.GD.N0106.N0428.N0765.N1545.d006851.d006817 (44 / 5)

theorem d022640 :
    _root_.GD.N0106.N0428.N0765.N1573.d022639.d006810 ((44 : ℝ) / 5 * Real.pi) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1573.d022639, Rat.cast_div, Rat.cast_ofNat] using
    _root_.GD.N0232.N0720.N1164.d006809.d006824 (44 / 5) _root_.GD.N0106.N0428.N0765.N1545.d006852

theorem d022641 :
    _root_.GD.N0106.N0428.N0765.N1573.d022636.d006928 _root_.GD.N0106.N0428.N0765.N1582.d007417 (Real.exp ((44 : ℝ) / 5 * Real.pi)) := by
  have h := _root_.GD.N0106.N0428.N0765.N1545.d006849 (k := 5) (n := 24) _root_.GD.N0106.N0428.N0765.N1573.d022640
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide)
  exact _root_.GD.N0106.N0428.N0765.N1548.d006926.d006932 _root_.GD.N0106.N0428.N0765.N1573.d022632 h (by decide +kernel)

theorem d022642 : _root_.GD.N0106.N0428.N0765.N1582.d007422.d006928 _root_.GD.N0106.N0428.N0765.N1582.d007417
    (_root_.GD.N0106.N0428.N0765.N1562.d021061 (11 / 10) (1 / 4)) := by
  have htwo := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006964 _root_.GD.N0106.N0428.N0765.N1573.d022632 (show (0 : ℤ) < 1 by decide) 2
  have hnum := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006965 _root_.GD.N0106.N0428.N0765.N1573.d022632
    (I := _root_.GD.N0106.N0428.N0765.N1573.d022635) (J := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006939 _root_.GD.N0106.N0428.N0765.N1582.d007417 2 1)
    (by decide +kernel) (by decide +kernel) _root_.GD.N0106.N0428.N0765.N1573.d022638 htwo
  have hsub := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006953 _root_.GD.N0106.N0428.N0765.N1573.d022641 (_root_.GD.N0106.N0428.N0765.N1548.d006926.d006949 _root_.GD.N0106.N0428.N0765.N1573.d022632)
  have hinv := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006966 _root_.GD.N0106.N0428.N0765.N1573.d022632 (by decide +kernel) hsub
  have heps := _root_.GD.N0106.N0428.N0765.N1548.d006926.d006965 _root_.GD.N0106.N0428.N0765.N1573.d022632
    (by decide +kernel) (by decide +kernel) hnum hinv
  have hexec : (_root_.GD.N0106.N0428.N0765.N1573.d022635.d006944 _root_.GD.N0106.N0428.N0765.N1582.d007417 (_root_.GD.N0106.N0428.N0765.N1548.d006926.d006939 _root_.GD.N0106.N0428.N0765.N1582.d007417 2 1)).d006944 _root_.GD.N0106.N0428.N0765.N1582.d007417
      ((_root_.GD.N0106.N0428.N0765.N1573.d022636.d006938 (_root_.GD.N0106.N0428.N0765.N1548.d006926.d006935 _root_.GD.N0106.N0428.N0765.N1582.d007417)).d006945 _root_.GD.N0106.N0428.N0765.N1582.d007417) = _root_.GD.N0106.N0428.N0765.N1582.d007422 := by
    decide +kernel
  rw [hexec] at heps
  convert heps using 1
  unfold _root_.GD.N0106.N0428.N0765.N1562.d021061
  rw [show 2 * Real.pi * (11 / 10) / (1 / 4) = (44 : ℝ) / 5 * Real.pi by ring]
  norm_num <;> ring

end GD.N0106.N0428.N0765.N1573
