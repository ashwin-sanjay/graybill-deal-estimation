import GD.Module0446







set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open _root_.GD.N0232.N0720.N1164
open _root_.GD.N0106.N0428.N0765.N1545

namespace GD.N0106.N0428.N0765.N1557


def d006919 : _root_.GD.N0232.N0720.N1164.d006809 := _root_.GD.N0106.N0428.N0765.N1545.d006846 (1 / 16) 0 24

theorem d006920 : _root_.GD.N0106.N0428.N0765.N1557.d006919.d006810 (Real.exp ((1 / 16 : ℚ) : ℝ)) := by
  unfold _root_.GD.N0106.N0428.N0765.N1557.d006919
  exact _root_.GD.N0106.N0428.N0765.N1545.d006847 (by norm_num) (by decide +kernel) (by norm_num)

theorem d006921 : 0 < _root_.GD.N0106.N0428.N0765.N1557.d006919.lo := by
  decide +kernel


def d006922 (n : ℕ) : _root_.GD.N0232.N0720.N1164.d006809 := _root_.GD.N0106.N0428.N0765.N1545.d006835 n _root_.GD.N0106.N0428.N0765.N1557.d006919

theorem d006923 (n : ℕ) :
    (_root_.GD.N0106.N0428.N0765.N1557.d006922 n).d006810 (Real.exp ((n : ℝ) / 16)) := by
  have h := _root_.GD.N0106.N0428.N0765.N1545.d006836 n _root_.GD.N0106.N0428.N0765.N1557.d006921.le _root_.GD.N0106.N0428.N0765.N1557.d006920
  have harg : ((n : ℝ) / 16) = (n : ℝ) * (((1 / 16 : ℚ) : ℝ)) := by
    norm_num <;> ring
  rw [harg, Real.exp_nat_mul]
  exact h


def d006924 (n : ℕ) : _root_.GD.N0232.N0720.N1164.d006809 := (_root_.GD.N0106.N0428.N0765.N1557.d006922 n).d006815

theorem d006925 (n : ℕ) :
    (_root_.GD.N0106.N0428.N0765.N1557.d006924 n).d006810 (Real.exp (-(n : ℝ) / 16)) := by
  have hpos : 0 < (_root_.GD.N0106.N0428.N0765.N1557.d006922 n).lo := by
    change 0 < _root_.GD.N0106.N0428.N0765.N1557.d006919.lo ^ n
    exact pow_pos _root_.GD.N0106.N0428.N0765.N1557.d006921 n
  have h := _root_.GD.N0232.N0720.N1164.d006809.d006822 hpos (_root_.GD.N0106.N0428.N0765.N1557.d006923 n)
  simpa only [_root_.GD.N0106.N0428.N0765.N1557.d006924, Real.exp_neg, one_div, neg_div] using h

end GD.N0106.N0428.N0765.N1557

#print axioms _root_.GD.N0106.N0428.N0765.N1557.d006923
#print axioms _root_.GD.N0106.N0428.N0765.N1557.d006925
