import GD.Module1792
import GD.Module1303
import GD.Module0448
import Mathlib.Analysis.Calculus.MeanValue










set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace GD.N0106.N0428.N0765.N1570

open _root_.GD.N0106.N0428.N0765.N1579 _root_.GD.N0106.N0428.N0765.N1572 _root_.GD.N0106.N0428.N0765.N1548

noncomputable def d029830 : ℝ :=
  (1 + Real.cos (Real.pi / 28)) / 14

theorem d029831 :
    |Real.log _root_.GD.N0106.N0428.N0765.N1572.d023746 - _root_.GD.N0106.N0428.N0765.N1570.d029830| ≤ (4735513 : ℝ) / 100000000000000000000000 := by
  simpa [_root_.GD.N0106.N0428.N0765.N1572.d023746, _root_.GD.N0106.N0428.N0765.N1582.d007418, _root_.GD.N0106.N0428.N0765.N1582.d007419,
    _root_.GD.N0106.N0428.N0765.N1570.d029830, _root_.GD.N0106.N0428.N0765.N1545.d006870] using
    _root_.GD.N0106.N0428.N0765.N1544.d006915


theorem d029832 : _root_.GD.N0106.N0428.N0765.N1515.d029731 = _root_.GD.N0106.N0428.N0765.N1523.d021314 := rfl

theorem d029833 : Differentiable ℝ _root_.GD.N0106.N0428.N0765.N1515.d029731 := by
  intro x
  have h := (_root_.GD.N0106.N0428.N0765.N1523.d021315 0
    (_root_.GD.N0106.N0428.N0765.N1535.d021138 x)).differentiableAt
  have hreal := Complex.reCLM.differentiableAt.comp x
    ((h.restrictScalars ℝ).comp x Complex.ofRealCLM.differentiableAt)
  simpa only [iteratedDeriv_zero, _root_.GD.N0106.N0428.N0765.N1515.d029731, Function.comp_def,
    Complex.reCLM_apply, Complex.ofRealCLM_apply] using! hreal


theorem d029834 (x : ℝ) : |deriv _root_.GD.N0106.N0428.N0765.N1515.d029731 x| ≤ 77 := by
  have h := _root_.GD.N0106.N0428.N0765.N1523.d021318 0 1 x
  have heq : (fun y : ℝ => 11 * _root_.GD.N0106.N0428.N0765.N1627.d021120 0 (Real.exp y) /
      (1 + Real.exp y)) = _root_.GD.N0106.N0428.N0765.N1515.d029731 := by
    funext y
    exact (_root_.GD.N0106.N0428.N0765.N1515.d029755 0 y).symm
  rw [heq] at h
  norm_num at h
  exact h


theorem d029835 (x y : ℝ) :
    |_root_.GD.N0106.N0428.N0765.N1515.d029731 x - _root_.GD.N0106.N0428.N0765.N1515.d029731 y| ≤ 77 * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := _root_.GD.N0106.N0428.N0765.N1515.d029731) (s := Set.univ) (C := (77 : ℝ))
    (fun z _ => _root_.GD.N0106.N0428.N0765.N1570.d029833 z)
    (fun z _ => by simpa only [Real.norm_eq_abs] using _root_.GD.N0106.N0428.N0765.N1570.d029834 z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using h

theorem d029836 :
    |_root_.GD.N0106.N0428.N0765.N1515.d029731 _root_.GD.N0106.N0428.N0765.N1570.d029830 -
      _root_.GD.N0106.N0428.N0765.N1515.d029731 (Real.log _root_.GD.N0106.N0428.N0765.N1572.d023746)| ≤
      (77 * 4735513 : ℝ) / 100000000000000000000000 := by
  apply (_root_.GD.N0106.N0428.N0765.N1570.d029835 _root_.GD.N0106.N0428.N0765.N1570.d029830 (Real.log _root_.GD.N0106.N0428.N0765.N1572.d023746)).trans
  have h := mul_le_mul_of_nonneg_left _root_.GD.N0106.N0428.N0765.N1570.d029831 (by norm_num : (0 : ℝ) ≤ 77)
  simpa only [abs_sub_comm, mul_div_assoc] using h

def d029837 (D : _root_.GD.N0106.N0428.N0765.N1579.d007457) : _root_.GD.N0106.N0428.N0765.N1579.d007457 :=
  _root_.GD.N0106.N0428.N0765.N1579.d007436.d007447 _root_.GD.N0106.N0428.N0765.N1579.d007456 D
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007449 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1579.d007460 11 1) (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007442 _root_.GD.N0106.N0428.N0765.N1579.d007459 _root_.GD.N0106.N0428.N0765.N1579.d007458))

theorem d029838 (location : ℝ) {D : _root_.GD.N0106.N0428.N0765.N1579.d007457}
    (hD : D.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1627.d021120 location _root_.GD.N0106.N0428.N0765.N1572.d023746))
    (hv : (_root_.GD.N0106.N0428.N0765.N1570.d029837 D).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1570.d029837 D).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1515.d029731 (Real.log _root_.GD.N0106.N0428.N0765.N1572.d023746)) := by
  have hdiv := (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007737 hv).2
  have hfactor := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007740 hdiv
    (_root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 11) (d := 1) (by decide))
    (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007732 _root_.GD.N0106.N0428.N0765.N1581.d023717 _root_.GD.N0106.N0428.N0765.N1572.d023748)
  have h := _root_.GD.N0106.N0428.N0765.N1579.d007436.d007738 hv hD hfactor
  have hj := _root_.GD.N0106.N0428.N0765.N1515.d029755 location (Real.log _root_.GD.N0106.N0428.N0765.N1572.d023746)
  rw [Real.exp_log _root_.GD.N0106.N0428.N0765.N1572.d023747] at hj
  rw [hj]
  unfold _root_.GD.N0106.N0428.N0765.N1570.d029837
  convert h using 1 <;> ring


theorem d029839 (location : ℝ) {D : _root_.GD.N0106.N0428.N0765.N1579.d007457}
    (hD : D.d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1627.d021120 location _root_.GD.N0106.N0428.N0765.N1572.d023746))
    (hv : (_root_.GD.N0106.N0428.N0765.N1579.d007483 D).valid = true) :
    (_root_.GD.N0106.N0428.N0765.N1579.d007483 D).d007727 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1515.d029731 _root_.GD.N0106.N0428.N0765.N1570.d029830) := by
  have hparts := Bool.and_eq_true_iff.mp hv
  have hs := _root_.GD.N0106.N0428.N0765.N1570.d029838 location hD hparts.1
  have hm := _root_.GD.N0106.N0428.N0765.N1572.d023764 (n := 77 * 4735513) (d := 100000000000000000000000) (by decide)
  have hmove : (77 * 4735513 : ℝ) / 100000000000000000000000 ≤
      ((_root_.GD.N0106.N0428.N0765.N1579.d007460 (77 * 4735513) 100000000000000000000000).interval.hi : ℝ) / (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ) := by
    simpa only [Int.cast_mul, Int.cast_ofNat] using hm.2
  have hab := abs_le.mp _root_.GD.N0106.N0428.N0765.N1570.d029836
  change
    (((_root_.GD.N0106.N0428.N0765.N1570.d029837 D).interval.lo -
      (_root_.GD.N0106.N0428.N0765.N1579.d007460 (77 * 4735513) 100000000000000000000000).interval.hi : ℤ) : ℝ) /
        (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ) ≤ _root_.GD.N0106.N0428.N0765.N1515.d029731 _root_.GD.N0106.N0428.N0765.N1570.d029830 ∧
    _root_.GD.N0106.N0428.N0765.N1515.d029731 _root_.GD.N0106.N0428.N0765.N1570.d029830 ≤
      (((_root_.GD.N0106.N0428.N0765.N1570.d029837 D).interval.hi +
        (_root_.GD.N0106.N0428.N0765.N1579.d007460 (77 * 4735513) 100000000000000000000000).interval.hi : ℤ) : ℝ) /
        (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ)
  push_cast
  rw [sub_div, add_div]
  constructor <;> linarith [hs.1, hs.2, hmove, hab.1, hab.2]


theorem d029840 :
    (_root_.GD.N0106.N0428.N0765.N1579.d007483 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007426)).valid = true ∧
    (_root_.GD.N0106.N0428.N0765.N1579.d007483 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007426)).interval =
      _root_.GD.N0106.N0428.N0765.N1582.d007427 := by
  decide +kernel

theorem d029841
    (hfinite : _root_.GD.N0106.N0428.N0765.N1582.d007425.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456
      _root_.GD.N0106.N0428.N0765.N1578.d029817) :
    _root_.GD.N0106.N0428.N0765.N1582.d007427.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1515.d029731 _root_.GD.N0106.N0428.N0765.N1570.d029830) := by
  have hD := _root_.GD.N0106.N0428.N0765.N1571.d029828 0 hfinite
  have h := _root_.GD.N0106.N0428.N0765.N1570.d029839 0 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007728 hD)
    _root_.GD.N0106.N0428.N0765.N1570.d029840.1
  change (_root_.GD.N0106.N0428.N0765.N1579.d007483 (_root_.GD.N0106.N0428.N0765.N1579.d007436.d007437 _root_.GD.N0106.N0428.N0765.N1582.d007426)).interval.d006928
    _root_.GD.N0106.N0428.N0765.N1579.d007456 (_root_.GD.N0106.N0428.N0765.N1515.d029731 _root_.GD.N0106.N0428.N0765.N1570.d029830) at h
  rwa [_root_.GD.N0106.N0428.N0765.N1570.d029840.2] at h


theorem d029842 {I : _root_.GD.N0106.N0428.N0765.N1548.d006926} {ln ld un ud : ℤ} {x : ℝ}
    (hc : _root_.GD.N0106.N0428.N0765.N1579.d007484 I ln ld un ud = true) (hx : I.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456 x) :
    (ln : ℝ) / (ld : ℝ) ≤ x ∧ x ≤ (un : ℝ) / (ud : ℝ) := by
  have h : 0 < ld ∧ 0 < ud ∧ ln * _root_.GD.N0106.N0428.N0765.N1579.d007456 ≤ I.lo * ld ∧ I.hi * ud ≤ un * _root_.GD.N0106.N0428.N0765.N1579.d007456 :=
    of_decide_eq_true hc
  have hs : (0 : ℝ) < _root_.GD.N0106.N0428.N0765.N1579.d007456 := by exact_mod_cast _root_.GD.N0106.N0428.N0765.N1573.d022632
  have hld : (0 : ℝ) < ld := by exact_mod_cast h.1
  have hud : (0 : ℝ) < ud := by exact_mod_cast h.2.1
  have hlo : (ln : ℝ) * (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ) ≤ (I.lo : ℝ) * (ld : ℝ) := by
    exact_mod_cast h.2.2.1
  have hhi : (I.hi : ℝ) * (ud : ℝ) ≤ (un : ℝ) * (_root_.GD.N0106.N0428.N0765.N1579.d007456 : ℝ) := by
    exact_mod_cast h.2.2.2
  exact ⟨((div_le_div_iff₀ hld hs).mpr hlo).trans hx.1,
    hx.2.trans ((div_le_div_iff₀ hs hud).mpr hhi)⟩

theorem d029843 :
    _root_.GD.N0106.N0428.N0765.N1579.d007485 _root_.GD.N0106.N0428.N0765.N1582.d007426 = true ∧
    _root_.GD.N0106.N0428.N0765.N1579.d007486 _root_.GD.N0106.N0428.N0765.N1582.d007427 = true := by
  decide +kernel


theorem d029844 (location : ℝ)
    (hfinite : _root_.GD.N0106.N0428.N0765.N1582.d007425.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456
      _root_.GD.N0106.N0428.N0765.N1578.d029817) :
    (_root_.GD.N0106.N0428.N0765.N1582.d007428 : ℝ) / (_root_.GD.N0106.N0428.N0765.N1582.d007429 : ℝ) ≤
      _root_.GD.N0106.N0428.N0765.N1627.d021120 location _root_.GD.N0106.N0428.N0765.N1572.d023746 ∧
    _root_.GD.N0106.N0428.N0765.N1627.d021120 location _root_.GD.N0106.N0428.N0765.N1572.d023746 ≤
      (_root_.GD.N0106.N0428.N0765.N1582.d007430 : ℝ) / (_root_.GD.N0106.N0428.N0765.N1582.d007431 : ℝ) :=
  _root_.GD.N0106.N0428.N0765.N1570.d029842 _root_.GD.N0106.N0428.N0765.N1570.d029843.1
    (_root_.GD.N0106.N0428.N0765.N1571.d029828 location hfinite)


theorem d029845
    (hfinite : _root_.GD.N0106.N0428.N0765.N1582.d007425.d006928 _root_.GD.N0106.N0428.N0765.N1579.d007456
      _root_.GD.N0106.N0428.N0765.N1578.d029817) :
    (_root_.GD.N0106.N0428.N0765.N1582.d007432 : ℝ) / (_root_.GD.N0106.N0428.N0765.N1582.d007433 : ℝ) ≤
      _root_.GD.N0106.N0428.N0765.N1515.d029731 _root_.GD.N0106.N0428.N0765.N1570.d029830 ∧
    _root_.GD.N0106.N0428.N0765.N1515.d029731 _root_.GD.N0106.N0428.N0765.N1570.d029830 ≤
      (_root_.GD.N0106.N0428.N0765.N1582.d007434 : ℝ) / (_root_.GD.N0106.N0428.N0765.N1582.d007435 : ℝ) :=
  _root_.GD.N0106.N0428.N0765.N1570.d029842 _root_.GD.N0106.N0428.N0765.N1570.d029843.2 (_root_.GD.N0106.N0428.N0765.N1570.d029841 hfinite)

end GD.N0106.N0428.N0765.N1570

#print axioms _root_.GD.N0106.N0428.N0765.N1570.d029835
#print axioms _root_.GD.N0106.N0428.N0765.N1570.d029839
#print axioms _root_.GD.N0106.N0428.N0765.N1570.d029841
#print axioms _root_.GD.N0106.N0428.N0765.N1570.d029844
#print axioms _root_.GD.N0106.N0428.N0765.N1570.d029845
