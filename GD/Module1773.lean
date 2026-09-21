import GD.Module1765
import GD.Module1766
import GD.Module1772



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
open MeasureTheory Set Filter Topology
open scoped FourierTransform
namespace GD.N0106.N0428.N0765.N1597
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1601 _root_.GD.N0106.N0428.N0765.N1587 _root_.GD.N0106.N0428.N0765.N1602
open _root_.GD.N0106.N0428.N0765.N1595 _root_.GD.N0106.N0428.N0765.N1594 _root_.GD.N0106.N0428.N0765.N1593
open _root_.GD.N0106.N0428.N0765.N1589 _root_.GD.N0106.N0428.N0765.N1586 _root_.GD.N0106.N0428.N0765.N1592
open _root_.GD.N0106.N0428.N0765.N1537 _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1652 _root_.GD.N0106.N0428.N0765.N1550


def d029348 (dA dB : ℝ) : ℝ :=
  max (max (_root_.GD.N0106.N0428.N0765.N1537.d021534 (-dA) (-dB)) (_root_.GD.N0106.N0428.N0765.N1537.d021534 (-dA) dB))
    (max (_root_.GD.N0106.N0428.N0765.N1537.d021534 dA (-dB)) (_root_.GD.N0106.N0428.N0765.N1537.d021534 dA dB))

theorem d029349 (dA dB xi eta : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1537.d021534 (if 0 ≤ xi then -dA else dA) (if 0 ≤ eta then -dB else dB) ≤
      _root_.GD.N0106.N0428.N0765.N1597.d029348 dA dB := by
  unfold _root_.GD.N0106.N0428.N0765.N1597.d029348
  split_ifs
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem d029350 {e dA dB : ℝ} (he : 0 ≤ e) (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ)/2)*(dA+dB) < Real.pi) (xi eta : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0) xi eta‖ ≤ _root_.GD.N0106.N0428.N0765.N1597.d029348 dA dB *
      Real.exp (-2*Real.pi*dA*|xi|) * Real.exp (-2*Real.pi*dB*|eta|) := by
  exact (_root_.GD.N0106.N0428.N0765.N1593.d029347 he hdA hdB hd xi eta).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (_root_.GD.N0106.N0428.N0765.N1597.d029349 dA dB xi eta) (Real.exp_nonneg _))
      (Real.exp_nonneg _))

theorem d029351 {e : ℝ} (he : 0 ≤ e) (x : ℝ) :
    Continuous (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 (x,y)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd : DifferentiableAt ℂ (fun z => _root_.GD.N0106.N0428.N0765.N1586.d022740 e (_root_.GD.N0106.N0428.N0765.N1537.d021524 x 0) z) (_root_.GD.N0106.N0428.N0765.N1537.d021524 y 0) :=
    _root_.GD.N0106.N0428.N0765.N1586.d022744 false he (by
      change ((21 : ℝ)/2)*_root_.GD.N0106.N0428.N0765.N1538.d021192 (_root_.GD.N0106.N0428.N0765.N1537.d021524 x 0).im (_root_.GD.N0106.N0428.N0765.N1537.d021524 y 0).im < Real.pi
      simp [_root_.GD.N0106.N0428.N0765.N1537.d021526, _root_.GD.N0106.N0428.N0765.N1538.d021192, Real.pi_pos])
  have hc := ContinuousAt.comp (f := fun t : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021524 t 0) (x := y)
    hd.continuousAt (by unfold _root_.GD.N0106.N0428.N0765.N1537.d021524; fun_prop)
  simpa only [Function.comp_def, _root_.GD.N0106.N0428.N0765.N1586.d022745] using hc

theorem d029352 {e : ℝ} (he : 0 ≤ e) (eta : ℝ) :
    Continuous (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0) eta) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hp : _root_.GD.N0106.N0428.N0765.N1537.d021524 x 0 ∈ _root_.GD.N0106.N0428.N0765.N1595.d029334 0 := by
    change ((21 : ℝ)/2)*_root_.GD.N0106.N0428.N0765.N1538.d021192 (_root_.GD.N0106.N0428.N0765.N1537.d021524 x 0).im 0 < Real.pi
    simp [_root_.GD.N0106.N0428.N0765.N1537.d021526, _root_.GD.N0106.N0428.N0765.N1538.d021192, Real.pi_pos]
  have hc := ContinuousAt.comp (f := fun t : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021524 t 0) (x := x)
    (_root_.GD.N0106.N0428.N0765.N1595.d029339 (xi := eta) he hp).2.continuousAt (by unfold _root_.GD.N0106.N0428.N0765.N1537.d021524; fun_prop)
  change ContinuousAt (fun t : ℝ => 𝓕 (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 (t,y)) eta) x
  simpa only [Function.comp_def, _root_.GD.N0106.N0428.N0765.N1594.d029340, _root_.GD.N0106.N0428.N0765.N1537.d021525, _root_.GD.N0106.N0428.N0765.N1537.d021526] using hc


theorem d029353 {d : ℝ} (hd : 0 ≤ d)
    (hstrip : ((21 : ℝ)/2)*d < Real.pi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : ℝ, 0 ≤ e → ∀ x eta : ℝ,
      ‖_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0) eta x‖ ≤
        C * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 x * Real.exp (-2*Real.pi*d*|eta|) := by
  have hs : ((21 : ℝ)/2)*(0+d) < Real.pi := by simpa only [zero_add] using hstrip
  obtain ⟨K,hKpos,hK⟩ := _root_.GD.N0106.N0428.N0765.N1602.d029274 (le_refl (0 : ℝ)) hd hs
  refine ⟨K * ∫ y : ℝ, _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y,
    mul_nonneg hKpos.le (integral_nonneg fun y => (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ y).le), ?_⟩
  intro e he x eta
  let β : ℝ := if 0 ≤ eta then -d else d
  have hβ : |β| ≤ d := by simp only [β]; split <;> simp [abs_of_nonneg hd]
  have hp : ((21 : ℝ)/2)*_root_.GD.N0106.N0428.N0765.N1538.d021192 0 β < Real.pi := by unfold _root_.GD.N0106.N0428.N0765.N1538.d021192; simp only [abs_zero]; nlinarith
  have hi := _root_.GD.N0106.N0428.N0765.N1602.d029278 he hp x
  have hint : (∫ y : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 β (x,y)‖) ≤
      (K * ∫ y : ℝ, _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y) * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 x := by
    calc (∫ y : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 β (x,y)‖)
        ≤ ∫ y : ℝ, (K * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 x) * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y := by
          apply integral_mono_ae hi.norm
            ((_root_.GD.N0106.N0428.N0765.N1602.d029276 (by norm_num : (0 : ℝ) < 5) (by norm_num : (0 : ℝ) < 3)).const_mul _)
          exact Filter.Eventually.of_forall (fun y => hK e he 0 β (by simp) hβ x y)
      _ = _ := by rw [integral_const_mul]; ring
  have hf := _root_.GD.N0106.N0428.N0765.N1589.d029322 (α := 0) he (le_refl (0 : ℝ)) hd hs (by simp) x eta
  exact hf.trans ((mul_le_mul_of_nonneg_left hint (Real.exp_nonneg _)).trans_eq (by ring))

theorem d029354 {e d : ℝ} (he : 0 ≤ e) (hd : 0 < d)
    (hstrip : ((21 : ℝ)/2)*d < Real.pi) (x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1601.d029267 (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0 (x,y)) := by
  obtain ⟨C,_,hC⟩ := _root_.GD.N0106.N0428.N0765.N1597.d029353 hd.le hstrip
  refine ⟨_root_.GD.N0106.N0428.N0765.N1597.d029351 he x, 5,3,2*Real.pi*d,
    _root_.GD.N0106.N0428.N0765.N1587.d029259 0 0 * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 x,
    C * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 x, by norm_num, by norm_num, by positivity, ?_, ?_⟩
  · intro y
    exact _root_.GD.N0106.N0428.N0765.N1587.d029262 (α := 0) (β := 0) he (by simp [_root_.GD.N0106.N0428.N0765.N1538.d021192, Real.pi_pos]) x y
  · intro eta
    simpa only [_root_.GD.N0106.N0428.N0765.N1652.d005816, neg_mul] using hC e he x eta

theorem d029355 {e d : ℝ} (he : 0 ≤ e) (hd : 0 < d)
    (hstrip : ((21 : ℝ)/2)*(d+d) < Real.pi) (eta : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1601.d029267 (_root_.GD.N0106.N0428.N0765.N1652.d005816 (_root_.GD.N0106.N0428.N0765.N1537.d021532 e 0 0) eta) := by
  obtain ⟨C,hC⟩ := _root_.GD.N0106.N0428.N0765.N1593.d029345 hd.le hd.le hstrip
  refine ⟨_root_.GD.N0106.N0428.N0765.N1597.d029352 he eta, 3/2,10,2*Real.pi*d,C,
    _root_.GD.N0106.N0428.N0765.N1597.d029348 d d * Real.exp (-2*Real.pi*d*|eta|),
    by norm_num, by norm_num, by positivity, ?_, ?_⟩
  · intro x
    have h := hC e he eta (_root_.GD.N0106.N0428.N0765.N1537.d021524 x 0) (by simp only [_root_.GD.N0106.N0428.N0765.N1537.d021526, abs_zero]; exact hd.le)
    simpa only [_root_.GD.N0106.N0428.N0765.N1594.d029340, _root_.GD.N0106.N0428.N0765.N1537.d021525, _root_.GD.N0106.N0428.N0765.N1537.d021526, _root_.GD.N0106.N0428.N0765.N1652.d005816] using h
  · intro xi
    have ha : -(2*Real.pi*d)*|xi| = -2*Real.pi*d*|xi| := by ring
    rw [ha]
    exact (_root_.GD.N0106.N0428.N0765.N1597.d029350 he hd.le hd.le hstrip xi eta).trans_eq (by ring)

end
end GD.N0106.N0428.N0765.N1597
#print axioms _root_.GD.N0106.N0428.N0765.N1597.d029354
#print axioms _root_.GD.N0106.N0428.N0765.N1597.d029355
