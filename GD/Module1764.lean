import GD.Module1421
import GD.Module1422
import GD.Module1761




set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1587
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1539 ProbabilityTheory _root_.GD.N0106.N0428.N0765.N1688
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1675 _root_.GD.N0106.N0428.N0765.N1537 _root_.GD.N0106.N0428.N0765.N1521

def d029254 (a b x : ℝ) : ℝ := if x ≤ 0 then Real.exp (a*x) else Real.exp (-b*x)

theorem d029255 (a b x : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1587.d029254 a b x := by
  unfold _root_.GD.N0106.N0428.N0765.N1587.d029254; split <;> exact Real.exp_pos _

theorem d029256 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1539.d005373 a b x ≤ (beta a b)⁻¹ * _root_.GD.N0106.N0428.N0765.N1587.d029254 a b x := by
  unfold _root_.GD.N0106.N0428.N0765.N1587.d029254
  split
  · exact _root_.GD.N0106.N0428.N0765.N1688.d029139 ha hb x
  · exact _root_.GD.N0106.N0428.N0765.N1688.d029140 ha hb x



theorem d029257 {j : ℝ} (hj : j ∈ Icc (0 : ℝ) 2) (x : ℝ) :
    Real.exp (j*x) * _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 x ≤
      (beta 5 5)⁻¹ * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 x := by
  unfold _root_.GD.N0106.N0428.N0765.N1587.d029254
  split_ifs with hx
  · exact (_root_.GD.N0106.N0428.N0765.N1688.d029141 (by norm_num) (by norm_num) j x).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hj.1]))
        (inv_nonneg.mpr (beta_pos (by norm_num) (by norm_num)).le))
  · exact (_root_.GD.N0106.N0428.N0765.N1688.d029142 (by norm_num) (by norm_num) j x).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hj.2, le_of_lt (lt_of_not_ge hx)]))
        (inv_nonneg.mpr (beta_pos (by norm_num) (by norm_num)).le))

theorem d029258 {g c : ℝ} (hg : 0 ≤ g) (hc : 0 ≤ c) (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 x * ((g * Real.exp x + 1)^2 + (c * Real.exp x + 1)^2) ≤
      ((g+1)^2+(c+1)^2) * ((beta 5 5)⁻¹ * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 x) := by
  have h0 := _root_.GD.N0106.N0428.N0765.N1587.d029257 (j := 0) (by norm_num) x
  have h1 := _root_.GD.N0106.N0428.N0765.N1587.d029257 (j := 1) (by norm_num) x
  have h2 := _root_.GD.N0106.N0428.N0765.N1587.d029257 (j := 2) (by norm_num) x
  simp only [zero_mul, Real.exp_zero, one_mul] at h0 h1
  have hx2 : Real.exp (2*x) = (Real.exp x)^2 := by
    rw [show 2*x = x+x by ring, Real.exp_add, pow_two]
  rw [hx2] at h2
  have h2' := mul_le_mul_of_nonneg_left h2 (add_nonneg (sq_nonneg g) (sq_nonneg c))
  have h1' := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2*(g+c) by positivity)
  have h0' := mul_le_mul_of_nonneg_left h0 (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith only [h2', h1', h0']


def d029259 (α β : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1537.d021528 α β * ((_root_.GD.N0106.N0428.N0765.N1537.d021529 β + 1)^2 + (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β + 1)^2) *
    (beta ((3 : ℝ)/2) 10)⁻¹ * (beta 5 5)⁻¹

theorem d029260 {α β : ℝ}
    (hw : ((21 : ℝ)/2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) : 0 < _root_.GD.N0106.N0428.N0765.N1587.d029259 α β := by
  have hD := _root_.GD.N0106.N0428.N0765.N1537.d021537 hw
  have hg := _root_.GD.N0106.N0428.N0765.N1537.d021538 (_root_.GD.N0106.N0428.N0765.N1537.d021535 hw).2
  have hc := _root_.GD.N0106.N0428.N0765.N1675.d021512 hw
  have hA := beta_pos (by norm_num : (0 : ℝ) < 3/2) (by norm_num : (0 : ℝ) < 10)
  have hB := beta_pos (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 5)
  unfold _root_.GD.N0106.N0428.N0765.N1587.d029259
  positivity

theorem d029261 {α β : ℝ}
    (hw : ((21 : ℝ)/2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (x y : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1537.d021533 α β (x,y) ≤
      _root_.GD.N0106.N0428.N0765.N1587.d029259 α β * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 x * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y := by
  have ha := _root_.GD.N0106.N0428.N0765.N1587.d029256 (by norm_num : (0 : ℝ) < 3/2)
    (by norm_num : (0 : ℝ) < 10) x
  have hb := _root_.GD.N0106.N0428.N0765.N1587.d029258 (_root_.GD.N0106.N0428.N0765.N1537.d021538 (_root_.GD.N0106.N0428.N0765.N1537.d021535 hw).2).le
    (_root_.GD.N0106.N0428.N0765.N1675.d021512 hw).le y
  have hQ : 0 ≤ _root_.GD.N0106.N0428.N0765.N1539.d005373 5 5 y *
      ((_root_.GD.N0106.N0428.N0765.N1537.d021529 β * Real.exp y + 1)^2 + (_root_.GD.N0106.N0428.N0765.N1675.d021511 α β * Real.exp y + 1)^2) :=
    mul_nonneg (_root_.GD.N0106.N0428.N0765.N1539.d005375 (by norm_num) (by norm_num) y).le
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hA : 0 ≤ (beta ((3 : ℝ)/2) 10)⁻¹ * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 x := by
    exact mul_nonneg (inv_nonneg.mpr (beta_pos (by norm_num) (by norm_num)).le)
      (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _).le
  have h := mul_le_mul_of_nonneg_left (mul_le_mul ha hb hQ hA) (_root_.GD.N0106.N0428.N0765.N1537.d021537 hw).le
  simpa only [_root_.GD.N0106.N0428.N0765.N1537.d021533, _root_.GD.N0106.N0428.N0765.N1521.d020868, _root_.GD.N0106.N0428.N0765.N1587.d029259, Prod.fst, Prod.snd,
    mul_assoc, mul_left_comm, mul_comm] using h


theorem d029262 {e α β : ℝ} (he : 0 ≤ e)
    (hw : ((21 : ℝ)/2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (x y : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e α β (x,y)‖ ≤
      _root_.GD.N0106.N0428.N0765.N1587.d029259 α β * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 x * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y :=
  (_root_.GD.N0106.N0428.N0765.N1537.d021542 he hw (x,y)).trans (_root_.GD.N0106.N0428.N0765.N1587.d029261 hw x y)

end
end GD.N0106.N0428.N0765.N1587
#print axioms _root_.GD.N0106.N0428.N0765.N1587.d029262
#print axioms _root_.GD.N0106.N0428.N0765.N1587.d029257
