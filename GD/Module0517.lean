import GD.Module0516





set_option autoImplicit false
set_option warningAsError true

open Filter
open scoped Topology

namespace GD.N0106.N0428.N0766
noncomputable section

theorem d007765 (c d h a r s t : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    deriv (fun v => _root_.GD.N0106.N0428.N0766.d007748 c d h a r v t) s = _root_.GD.N0106.N0428.N0766.d007749 c d h a r s t :=
  (_root_.GD.N0106.N0428.N0766.d007758 c d h a r s t hb).deriv

theorem d007766 (c d h a r s t : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    deriv (fun v => _root_.GD.N0106.N0428.N0766.d007748 c d h a r s v) t = _root_.GD.N0106.N0428.N0766.d007752 c d h a r s t :=
  (_root_.GD.N0106.N0428.N0766.d007759 c d h a r s t hb).deriv

theorem d007767 (c d h a r s t : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    deriv (deriv (fun v => _root_.GD.N0106.N0428.N0766.d007748 c d h a r v t)) s = _root_.GD.N0106.N0428.N0766.d007750 c d h a r s t := by
  have he : deriv (fun v => _root_.GD.N0106.N0428.N0766.d007748 c d h a r v t) =ᶠ[𝓝 s]
      (fun v => _root_.GD.N0106.N0428.N0766.d007749 c d h a r v t) :=
    ((_root_.GD.N0106.N0428.N0766.d007754 c d h s t).continuousAt.eventually_ne hb).mono
      fun v hv => _root_.GD.N0106.N0428.N0766.d007765 c d h a r v t hv
  exact he.deriv_eq.trans (_root_.GD.N0106.N0428.N0766.d007760 c d h a r s t hb).deriv

theorem d007768 (c d h a r s t : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    deriv (deriv (deriv (fun v => _root_.GD.N0106.N0428.N0766.d007748 c d h a r v t))) s =
      _root_.GD.N0106.N0428.N0766.d007751 c d h a r s t := by
  have he : deriv (deriv (fun v => _root_.GD.N0106.N0428.N0766.d007748 c d h a r v t)) =ᶠ[𝓝 s]
      (fun v => _root_.GD.N0106.N0428.N0766.d007750 c d h a r v t) :=
    ((_root_.GD.N0106.N0428.N0766.d007754 c d h s t).continuousAt.eventually_ne hb).mono
      fun v hv => _root_.GD.N0106.N0428.N0766.d007767 c d h a r v t hv
  exact he.deriv_eq.trans (_root_.GD.N0106.N0428.N0766.d007761 c d h a r s t hb).deriv

theorem d007769 (c d h a r s t : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    deriv (fun v => deriv (fun w => _root_.GD.N0106.N0428.N0766.d007748 c d h a r v w) t) s =
      _root_.GD.N0106.N0428.N0766.d007753 c d h a r s t := by
  have he : (fun v => deriv (fun w => _root_.GD.N0106.N0428.N0766.d007748 c d h a r v w) t) =ᶠ[𝓝 s]
      (fun v => _root_.GD.N0106.N0428.N0766.d007752 c d h a r v t) :=
    ((_root_.GD.N0106.N0428.N0766.d007754 c d h s t).continuousAt.eventually_ne hb).mono
      fun v hv => _root_.GD.N0106.N0428.N0766.d007766 c d h a r v t hv
  exact he.deriv_eq.trans (_root_.GD.N0106.N0428.N0766.d007762 c d h a r s t hb).deriv

theorem d007770 (c d h a r s t : ℝ) (hb : _root_.GD.N0106.N0428.N0766.d007747 c d h s t ≠ 0) :
    deriv (fun v => deriv (fun w => _root_.GD.N0106.N0428.N0766.d007748 c d h a r w v) s) t =
      _root_.GD.N0106.N0428.N0766.d007753 c d h a r s t := by
  have he : (fun v => deriv (fun w => _root_.GD.N0106.N0428.N0766.d007748 c d h a r w v) s) =ᶠ[𝓝 t]
      (fun v => _root_.GD.N0106.N0428.N0766.d007749 c d h a r s v) :=
    ((_root_.GD.N0106.N0428.N0766.d007755 c d h s t).continuousAt.eventually_ne hb).mono
      fun v hv => _root_.GD.N0106.N0428.N0766.d007765 c d h a r s v hv
  exact he.deriv_eq.trans (_root_.GD.N0106.N0428.N0766.d007763 c d h a r s t hb).deriv


theorem d007771 (c d h a r : ℝ) (hc : c ≠ 0) :
    _root_.GD.N0106.N0428.N0766.d007748 c d h a r 0 0 = c ^ (-r) * a ∧
    deriv (fun v => _root_.GD.N0106.N0428.N0766.d007748 c d h a r v 0) 0 =
      c ^ (-r) * (1 - r * a * d / c) ∧
    deriv (deriv (fun v => _root_.GD.N0106.N0428.N0766.d007748 c d h a r v 0)) 0 =
      c ^ (-r) * (-2 * r * d / c + r * (r + 1) * a * d ^ 2 / c ^ 2) ∧
    deriv (deriv (deriv (fun v => _root_.GD.N0106.N0428.N0766.d007748 c d h a r v 0))) 0 = c ^ (-r) *
      (3 * r * (r + 1) * d ^ 2 / c ^ 2 -
       r * (r + 1) * (r + 2) * a * d ^ 3 / c ^ 3) ∧
    deriv (fun v => _root_.GD.N0106.N0428.N0766.d007748 c d h a r 0 v) 0 = c ^ (-r) * (-r * a * h / c) ∧
    deriv (fun v => deriv (fun w => _root_.GD.N0106.N0428.N0766.d007748 c d h a r v w) 0) 0 =
      c ^ (-r) * (-r * h / c + r * (r + 1) * a * d * h / c ^ 2) := by
  have hb : _root_.GD.N0106.N0428.N0766.d007747 c d h 0 0 ≠ 0 := by simpa only [_root_.GD.N0106.N0428.N0766.d007747, mul_zero, add_zero] using hc
  rw [_root_.GD.N0106.N0428.N0766.d007765 c d h a r 0 0 hb, _root_.GD.N0106.N0428.N0766.d007767 c d h a r 0 0 hb,
    _root_.GD.N0106.N0428.N0766.d007768 c d h a r 0 0 hb, _root_.GD.N0106.N0428.N0766.d007766 c d h a r 0 0 hb,
    _root_.GD.N0106.N0428.N0766.d007769 c d h a r 0 0 hb]
  exact _root_.GD.N0106.N0428.N0766.d007764 c d h a r hc

end
end GD.N0106.N0428.N0766

#print axioms _root_.GD.N0106.N0428.N0766.d007771
#print axioms _root_.GD.N0106.N0428.N0766.d007770
