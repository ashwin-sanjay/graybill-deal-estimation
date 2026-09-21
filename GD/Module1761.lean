import GD.Module0360



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1688
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1539 ProbabilityTheory

theorem d029139 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x ≤ (beta a b)⁻¹ * Real.exp (a * x) := by
  have hB := beta_pos ha hb
  have hp : (1 : ℝ) ≤ (1 + Real.exp x) ^ (a + b) :=
    Real.one_le_rpow (by linarith [Real.exp_pos x]) (by linarith)
  have hd : beta a b ≤ beta a b * (1 + Real.exp x) ^ (a + b) := by
    nlinarith
  calc _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x ≤ Real.exp (a*x) / beta a b :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hB hd
    _ = _ := by ring

theorem d029140 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x ≤ (beta a b)⁻¹ * Real.exp (-b * x) := by
  have hB := beta_pos ha hb
  have hp := Real.rpow_le_rpow (Real.exp_pos x).le
    (show Real.exp x ≤ 1 + Real.exp x by linarith) (show 0 ≤ a+b by linarith)
  rw [← Real.exp_mul] at hp
  have hd := mul_le_mul_of_nonneg_left hp hB.le
  calc _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x ≤ Real.exp (a*x) / (beta a b * Real.exp (x*(a+b))) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (mul_pos hB (Real.exp_pos _)) hd
    _ = (beta a b)⁻¹ * (Real.exp (a*x) / Real.exp (x*(a+b))) := by ring
    _ = _ := by rw [← Real.exp_sub]; congr 2; ring


theorem d029141 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (j x : ℝ) :
    Real.exp (j*x) * _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x ≤
      (beta a b)⁻¹ * Real.exp ((a+j)*x) := by
  calc _ ≤ Real.exp (j*x) * ((beta a b)⁻¹ * Real.exp (a*x)) :=
      mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1688.d029139 ha hb x) (Real.exp_pos _).le
    _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

theorem d029142 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (j x : ℝ) :
    Real.exp (j*x) * _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x ≤
      (beta a b)⁻¹ * Real.exp (-(b-j)*x) := by
  calc _ ≤ Real.exp (j*x) * ((beta a b)⁻¹ * Real.exp (-b*x)) :=
      mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1688.d029140 ha hb x) (Real.exp_pos _).le
    _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

end
end GD.N0106.N0428.N0765.N1688
#print axioms _root_.GD.N0106.N0428.N0765.N1688.d029141
#print axioms _root_.GD.N0106.N0428.N0765.N1688.d029142
