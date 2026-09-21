import GD.Module1263

set_option autoImplicit false
set_option warningAsError true









open scoped BigOperators

namespace GD.N0210.N0458

open _root_.GD.N0213.N0477

theorem d020494 {k d : ℕ} (sizes : Fin k → ℕ)
    (hdim : (∑ i, sizes i) = d + 2) :
    _root_.GD.N0213.N0477.d020391 d = (((∑ i, sizes i) + 1 : ℕ) : ℝ) / 2 := by
  unfold _root_.GD.N0213.N0477.d020391
  rw [hdim]
  push_cast
  ring

theorem d020495 (d : ℕ) :
    _root_.GD.N0213.N0477.d020391 d = (((d + 2) + 1 : ℕ) : ℝ) / 2 := by
  unfold _root_.GD.N0213.N0477.d020391
  push_cast
  ring

end GD.N0210.N0458

#print axioms _root_.GD.N0210.N0458.d020494
#print axioms _root_.GD.N0210.N0458.d020495
