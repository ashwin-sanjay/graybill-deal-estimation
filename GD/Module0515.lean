import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace GD.N0106.N0428.N0766
noncomputable section

def d007747 (c d h s t : ℝ) : ℝ := c + d * s + h * t
def d007748 (c d h a r s t : ℝ) : ℝ :=
  (a + s) * (_root_.GD.N0106.N0428.N0766.d007747 c d h s t) ^ (-r)
def d007749 (c d h a r s t : ℝ) : ℝ :=
  (_root_.GD.N0106.N0428.N0766.d007747 c d h s t) ^ (-r) - r * d * (a + s) * (_root_.GD.N0106.N0428.N0766.d007747 c d h s t) ^ (-r - 1)
def d007750 (c d h a r s t : ℝ) : ℝ :=
  -2 * r * d * (_root_.GD.N0106.N0428.N0766.d007747 c d h s t) ^ (-r - 1) +
    r * (r + 1) * d ^ 2 * (a + s) * (_root_.GD.N0106.N0428.N0766.d007747 c d h s t) ^ (-r - 2)
def d007751 (c d h a r s t : ℝ) : ℝ :=
  3 * r * (r + 1) * d ^ 2 * (_root_.GD.N0106.N0428.N0766.d007747 c d h s t) ^ (-r - 2) -
    r * (r + 1) * (r + 2) * d ^ 3 * (a + s) * (_root_.GD.N0106.N0428.N0766.d007747 c d h s t) ^ (-r - 3)
def d007752 (c d h a r s t : ℝ) : ℝ :=
  -r * h * (a + s) * (_root_.GD.N0106.N0428.N0766.d007747 c d h s t) ^ (-r - 1)
def d007753 (c d h a r s t : ℝ) : ℝ :=
  -r * h * (_root_.GD.N0106.N0428.N0766.d007747 c d h s t) ^ (-r - 1) +
    r * (r + 1) * d * h * (a + s) * (_root_.GD.N0106.N0428.N0766.d007747 c d h s t) ^ (-r - 2)

theorem d007754 (c d h s t : ℝ) :
    HasDerivAt (fun v => _root_.GD.N0106.N0428.N0766.d007747 c d h v t) d s := by
  simpa [_root_.GD.N0106.N0428.N0766.d007747] using (((hasDerivAt_id s).const_mul d).const_add c).add_const (h * t)

theorem d007755 (c d h s t : ℝ) :
    HasDerivAt (fun v => _root_.GD.N0106.N0428.N0766.d007747 c d h s v) h t := by
  simpa [_root_.GD.N0106.N0428.N0766.d007747] using ((hasDerivAt_id t).const_mul h).const_add (c + d * s)

theorem d007756 (c d h s t p : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    HasDerivAt (fun v => (_root_.GD.N0106.N0428.N0766.d007747 c d h v t) ^ p)
      (d * p * (_root_.GD.N0106.N0428.N0766.d007747 c d h s t) ^ (p - 1)) s :=
  (_root_.GD.N0106.N0428.N0766.d007754 c d h s t).rpow_const (Or.inl hb)

theorem d007757 (c d h s t p : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    HasDerivAt (fun v => (_root_.GD.N0106.N0428.N0766.d007747 c d h s v) ^ p)
      (h * p * (_root_.GD.N0106.N0428.N0766.d007747 c d h s t) ^ (p - 1)) t :=
  (_root_.GD.N0106.N0428.N0766.d007755 c d h s t).rpow_const (Or.inl hb)

theorem d007758 (c d h a r s t : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    HasDerivAt (fun v => _root_.GD.N0106.N0428.N0766.d007748 c d h a r v t) (_root_.GD.N0106.N0428.N0766.d007749 c d h a r s t) s := by
  have hp := ((hasDerivAt_id s).const_add a).mul (_root_.GD.N0106.N0428.N0766.d007756 c d h s t (-r) hb)
  apply hp.congr_deriv
  simp only [_root_.GD.N0106.N0428.N0766.d007749, id_eq]
  ring

theorem d007759 (c d h a r s t : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    HasDerivAt (fun v => _root_.GD.N0106.N0428.N0766.d007748 c d h a r s v) (_root_.GD.N0106.N0428.N0766.d007752 c d h a r s t) t := by
  have hp := (_root_.GD.N0106.N0428.N0766.d007757 c d h s t (-r) hb).const_mul (a + s)
  apply hp.congr_deriv
  unfold _root_.GD.N0106.N0428.N0766.d007752
  ring

theorem d007760 (c d h a r s t : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    HasDerivAt (fun v => _root_.GD.N0106.N0428.N0766.d007749 c d h a r v t) (_root_.GD.N0106.N0428.N0766.d007750 c d h a r s t) s := by
  have hp := (_root_.GD.N0106.N0428.N0766.d007756 c d h s t (-r) hb).sub
    ((((hasDerivAt_id s).const_add a).const_mul (r * d)).mul
      (_root_.GD.N0106.N0428.N0766.d007756 c d h s t (-r - 1) hb))
  apply hp.congr_deriv
  simp only [_root_.GD.N0106.N0428.N0766.d007750, id_eq, show -r - 1 - 1 = -r - 2 by ring]
  ring

theorem d007761 (c d h a r s t : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    HasDerivAt (fun v => _root_.GD.N0106.N0428.N0766.d007750 c d h a r v t) (_root_.GD.N0106.N0428.N0766.d007751 c d h a r s t) s := by
  have hp := ((_root_.GD.N0106.N0428.N0766.d007756 c d h s t (-r - 1) hb).const_mul (-2 * r * d)).add
    ((((hasDerivAt_id s).const_add a).const_mul (r * (r + 1) * d ^ 2)).mul
      (_root_.GD.N0106.N0428.N0766.d007756 c d h s t (-r - 2) hb))
  apply hp.congr_deriv
  simp only [_root_.GD.N0106.N0428.N0766.d007751, id_eq,
    show -r - 1 - 1 = -r - 2 by ring, show -r - 2 - 1 = -r - 3 by ring]
  ring

theorem d007762 (c d h a r s t : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    HasDerivAt (fun v => _root_.GD.N0106.N0428.N0766.d007752 c d h a r v t) (_root_.GD.N0106.N0428.N0766.d007753 c d h a r s t) s := by
  have hp := (((hasDerivAt_id s).const_add a).const_mul (-r * h)).mul
    (_root_.GD.N0106.N0428.N0766.d007756 c d h s t (-r - 1) hb)
  apply hp.congr_deriv
  simp only [_root_.GD.N0106.N0428.N0766.d007753, id_eq, show -r - 1 - 1 = -r - 2 by ring]
  ring

theorem d007763 (c d h a r s t : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    HasDerivAt (fun v => _root_.GD.N0106.N0428.N0766.d007749 c d h a r s v) (_root_.GD.N0106.N0428.N0766.d007753 c d h a r s t) t := by
  have hp := (_root_.GD.N0106.N0428.N0766.d007757 c d h s t (-r) hb).sub
    ((_root_.GD.N0106.N0428.N0766.d007757 c d h s t (-r - 1) hb).const_mul (r * d * (a + s)))
  apply hp.congr_deriv
  simp only [_root_.GD.N0106.N0428.N0766.d007753, show -r - 1 - 1 = -r - 2 by ring]
  ring

end
end GD.N0106.N0428.N0766

#print axioms _root_.GD.N0106.N0428.N0766.d007758
#print axioms _root_.GD.N0106.N0428.N0766.d007759
#print axioms _root_.GD.N0106.N0428.N0766.d007760
#print axioms _root_.GD.N0106.N0428.N0766.d007761
#print axioms _root_.GD.N0106.N0428.N0766.d007762
#print axioms _root_.GD.N0106.N0428.N0766.d007763
