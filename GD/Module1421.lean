import GD.Module1420
import GD.Module1313
import GD.Module1318




set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1599
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1672 _root_.GD.N0106.N0428.N0765.N1528
open _root_.GD.N0106.N0428.N0765.N1592

def d022731 (e : ℝ) (z w : ℂ) : ℂ := _root_.GD.N0106.N0428.N0765.N1672.d021423 e z.re w.re z.im w.im
def d022732 (e : ℝ) (z w : ℂ) : ℂ := _root_.GD.N0106.N0428.N0765.N1672.d021424 e z.re w.re z.im w.im
def d022733 (e : ℝ) (z w : ℂ) : ℂ := _root_.GD.N0106.N0428.N0765.N1599.d022732 e z w / _root_.GD.N0106.N0428.N0765.N1599.d022731 e z w

theorem d022734 {e : ℝ} (he : 0 ≤ e) {z w : ℂ}
    (hz : ((21 : ℝ) / 2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 z.im w.im < Real.pi) : _root_.GD.N0106.N0428.N0765.N1599.d022731 e z w ≠ 0 := by
  rcases he.eq_or_lt with he | he
  · subst e
    exact _root_.GD.N0106.N0428.N0765.N1528.d021466 z.re w.re z.im w.im hz
  · intro h
    have hn : _root_.GD.N0106.N0428.N0765.N1538.d021243 e z.re w.re z.im w.im ≠ 0 := norm_pos_iff.mp
      ((mul_pos (_root_.GD.N0106.N0428.N0765.N1538.d021232 hz) (_root_.GD.N0106.N0428.N0765.N1538.d021248 he z.re w.re)).trans_le
        (_root_.GD.N0106.N0428.N0765.N1538.d021250 he z.re w.re z.im w.im hz))
    rw [_root_.GD.N0106.N0428.N0765.N1672.d021427 he z.re w.re z.im w.im (_root_.GD.N0106.N0428.N0765.N1538.d021233 hz)] at hn
    exact hn (by rw [show _root_.GD.N0106.N0428.N0765.N1672.d021423 e z.re w.re z.im w.im = 0 from h, mul_zero])

def d022735 (axis : Bool) (e : ℝ) (w z : ℂ) : ℂ :=
  (_root_.GD.N0106.N0428.N0765.N1592.d022713 true axis e w z * _root_.GD.N0106.N0428.N0765.N1599.d022731 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z) (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z) -
    _root_.GD.N0106.N0428.N0765.N1599.d022732 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z) (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z) * _root_.GD.N0106.N0428.N0765.N1592.d022713 false axis e w z) /
      _root_.GD.N0106.N0428.N0765.N1599.d022731 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z) (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z) ^ 2

theorem d022736 (axis : Bool) {e : ℝ} (he : 0 ≤ e)
    {w z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :
    HasDerivAt (fun q => _root_.GD.N0106.N0428.N0765.N1599.d022733 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w q) (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w q))
      (_root_.GD.N0106.N0428.N0765.N1599.d022735 axis e w z) z :=
  (_root_.GD.N0106.N0428.N0765.N1592.d022730 axis he hz).div (_root_.GD.N0106.N0428.N0765.N1592.d022729 axis he hz)
    (_root_.GD.N0106.N0428.N0765.N1599.d022734 he hz)

theorem d022737 (axis : Bool) {e : ℝ} (he : 0 ≤ e) (w : ℂ) :
    DifferentiableOn ℂ (fun z => _root_.GD.N0106.N0428.N0765.N1599.d022733 e (_root_.GD.N0106.N0428.N0765.N1592.d022705 axis w z) (_root_.GD.N0106.N0428.N0765.N1592.d022706 axis w z))
      (_root_.GD.N0106.N0428.N0765.N1592.d022707 axis w) :=
  fun _ hz => (_root_.GD.N0106.N0428.N0765.N1599.d022736 axis he hz).differentiableAt.differentiableWithinAt


theorem d022738 (e a b α β : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1599.d022733 e (_root_.GD.N0106.N0428.N0765.N1537.d021524 a α) (_root_.GD.N0106.N0428.N0765.N1537.d021524 b β) =
      _root_.GD.N0106.N0428.N0765.N1675.d021510 e α β (a,b) := by
  simp [_root_.GD.N0106.N0428.N0765.N1599.d022733, _root_.GD.N0106.N0428.N0765.N1599.d022732, _root_.GD.N0106.N0428.N0765.N1599.d022731, _root_.GD.N0106.N0428.N0765.N1675.d021510]

end
end GD.N0106.N0428.N0765.N1599
#print axioms _root_.GD.N0106.N0428.N0765.N1599.d022736
