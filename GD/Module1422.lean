import GD.Module1421



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1586
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1592 _root_.GD.N0106.N0428.N0765.N1599 _root_.GD.N0106.N0428.N0765.N1585

def d022739 (e : ℝ) (w : ℂ) : ℂ := Complex.exp w / (1 + (e : ℂ) * Complex.exp w)
def d022740 (e : ℝ) (z w : ℂ) : ℂ :=
  _root_.GD.N0106.N0428.N0765.N1585.d005529 ((3 : ℝ) / 2) 10 z * _root_.GD.N0106.N0428.N0765.N1585.d005529 5 5 w *
    ((_root_.GD.N0106.N0428.N0765.N1586.d022739 e w - ((1 + e)⁻¹ : ℝ))^2 - (_root_.GD.N0106.N0428.N0765.N1599.d022733 e z w - ((1 + e)⁻¹ : ℝ))^2)

theorem d022741 {z w : ℂ}
    (h : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 z.im w.im < Real.pi) :
    |z.im| < Real.pi / 2 ∧ |w.im| < Real.pi / 2 := by
  unfold _root_.GD.N0106.N0428.N0765.N1538.d021192 at h
  constructor <;> nlinarith [abs_nonneg z.im, abs_nonneg w.im, Real.pi_pos]

theorem d022742 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {z : ℂ} (hz : |z.im| < Real.pi / 2) : DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1585.d005529 a b) z := by
  have ho : IsOpen {q : ℂ | |q.im| < Real.pi / 2} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  exact (_root_.GD.N0106.N0428.N0765.N1585.d005539 ha hb).differentiableAt (ho.mem_nhds hz)

theorem d022743 {e : ℝ} (he : 0 ≤ e) {w : ℂ}
    (hw : |w.im| < Real.pi / 2) : DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1586.d022739 e) w := by
  have hc : 0 < Real.cos w.im := Real.cos_pos_of_mem_Ioo (abs_lt.mp hw)
  have hp : 0 < (1 + (e : ℂ) * Complex.exp w).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_re]
    positivity
  have hn : 1 + (e : ℂ) * Complex.exp w ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hp; exact lt_irrefl _ hp
  exact (Complex.differentiable_exp.differentiableAt).div
    (by fun_prop : DifferentiableAt ℂ (fun q => 1 + (e : ℂ) * Complex.exp q) w) hn

theorem d022744 (axis : Bool) {e : ℝ} (he : 0 ≤ e)
    {w z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :
    DifferentiableAt ℂ (fun q => _root_.GD.N0106.N0428.N0765.N1586.d022740 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w q) (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w q)) z := by
  have hs := _root_.GD.N0106.N0428.N0765.N1586.d022741 hz
  have h1 : DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w) z := by
    cases axis <;> unfold _root_.GD.N0106.N0428.N0765.N1592.d022705 <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  have h2 : DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w) z := by
    cases axis <;> unfold _root_.GD.N0106.N0428.N0765.N1592.d022706 <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  have hd1 := (_root_.GD.N0106.N0428.N0765.N1586.d022742 (by norm_num : (0 : ℝ) < 3 / 2)
    (by norm_num : (0 : ℝ) < 10) hs.1).comp z h1
  have hd2 := (_root_.GD.N0106.N0428.N0765.N1586.d022742 (by norm_num : (0 : ℝ) < 5)
    (by norm_num : (0 : ℝ) < 5) hs.2).comp z h2
  have hg := (_root_.GD.N0106.N0428.N0765.N1586.d022743 he hs.2).comp z h2
  have hq := (_root_.GD.N0106.N0428.N0765.N1599.d022736 axis he hz).differentiableAt
  exact (hd1.mul hd2).mul ((hg.sub_const _).pow 2 |>.sub ((hq.sub_const _).pow 2))


theorem d022745 (e a b α β : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1586.d022740 e (_root_.GD.N0106.N0428.N0765.N1537.d021524 a α) (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β) =
      _root_.GD.N0106.N0428.N0765.N1537.d021532 e α β (a,b) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1586.d022740, _root_.GD.N0106.N0428.N0765.N1537.d021532, _root_.GD.N0106.N0428.N0765.N1537.d021527,
    _root_.GD.N0106.N0428.N0765.N1586.d022739, _root_.GD.N0106.N0428.N0765.N1537.d021530, _root_.GD.N0106.N0428.N0765.N1537.d021531,
    _root_.GD.N0106.N0428.N0765.N1599.d022738]

end
end GD.N0106.N0428.N0765.N1586
#print axioms _root_.GD.N0106.N0428.N0765.N1586.d022744
