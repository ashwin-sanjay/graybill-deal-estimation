import GD.Module1430
import GD.Module0431
import GD.Module1531

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0031
noncomputable section

open _root_.GD.N0051 _root_.GD.N0042

def d023846 (b r : ℝ) : ℝ :=
  _root_.GD.N0042.d006724 b b * _root_.GD.N0031.d022773 r ^ b

theorem d023847 {b r : ℝ} (hb : 0 < b) (hr : 0 < r) :
    0 < _root_.GD.N0031.d023846 b r :=
  mul_pos (_root_.GD.N0042.d006725 hb hb)
    (Real.rpow_pos_of_pos (_root_.GD.N0031.d022774 hr) _)

theorem d023848 {a : ℝ} (ha : 0 < a) :
    (∫⁻ x : ℝ, ENNReal.ofReal x ∂gammaMeasure a a) = 1 := by
  have hi : Integrable (fun x : ℝ => x) (gammaMeasure a a) := by
    simpa only [Real.rpow_one] using
      _root_.GD.N0051.d022782 ha ha (show 0 < a + 1 by linarith)
  have hn : 0 ≤ᵐ[gammaMeasure a a] (fun x : ℝ => x) :=
    (_root_.GD.N0232.N0719.N0910.d010286 ha ha).mono fun _ hx => hx.le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    _root_.GD.N0232.N0719.N0960.d009682 ha ha,
    div_self ha.ne']
  norm_num



theorem d023849 {p q a b v w y z : ℝ}
    (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hv : 0 < v) (hw : 0 < w) (hrb : (p / q) * b = 1)
    (f : _root_.GD.N0051.d023832 → ℝ) (hf : Measurable f)
    (hfirst : ∀ y z s t : ℝ, 0 < s → 0 < t →
      (f ((y, z), (s, t)) - y) ^ 2 ≤ s + (z - y) ^ 2 *
        (Iic (_root_.GD.N0031.d022775 (p / q) s (z - y))).indicator (fun _ => (1 : ℝ)) t) :
    (∫⁻ u, ENNReal.ofReal ((f ((y, z), (v * u.1, w * u.2)) - y) ^ 2)
      ∂(gammaMeasure a a).prod (gammaMeasure b b)) ≤
      ENNReal.ofReal (v * (1 + _root_.GD.N0031.d023846 b (p / q) * ((z - y) ^ 2 / w) ^ b)) := by
  letI := isProbabilityMeasure_gammaMeasure ha ha
  letI := isProbabilityMeasure_gammaMeasure hb hb
  let L : ℝ := 1 + _root_.GD.N0031.d023846 b (p / q) * ((z - y) ^ 2 / w) ^ b
  have hL : 0 ≤ L := by
    exact add_nonneg (by norm_num)
      (mul_nonneg (_root_.GD.N0031.d023847 hb (div_pos hp hq)).le
        (Real.rpow_nonneg (div_nonneg (sq_nonneg _) hw.le) _))
  have hmeas : Measurable (fun u : ℝ × ℝ =>
      ENNReal.ofReal ((f ((y, z), (v * u.1, w * u.2)) - y) ^ 2)) := by fun_prop
  rw [lintegral_prod _ hmeas.aemeasurable]
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal ((v * x) * L) ∂gammaMeasure a a := by
      apply lintegral_mono_ae
      filter_upwards [_root_.GD.N0232.N0719.N0910.d010286 ha ha] with x hx
      exact _root_.GD.N0031.d022791 (gammaMeasure b b)
        (_root_.GD.N0232.N0719.N0910.d010286 hb hb)
        hp hq (mul_pos hv hx) hw hb (_root_.GD.N0042.d006725 hb hb).le hrb
        (fun u hu => _root_.GD.N0042.d006728 hb hu)
        (fun t => f ((y, z), (v * x, w * t)))
        (fun t ht => hfirst y z (v * x) (w * t) (mul_pos hv hx) (mul_pos hw ht))
    _ = ENNReal.ofReal (v * L) *
        (∫⁻ x : ℝ, ENNReal.ofReal x ∂gammaMeasure a a) := by
      rw [← lintegral_const_mul' (ENNReal.ofReal (v * L))
        (fun x : ℝ => ENNReal.ofReal x) ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul (mul_nonneg hv.le hL)]
      congr 1
      ring
    _ = _ := by rw [_root_.GD.N0031.d023848 ha, mul_one]

end
end GD.N0031

#print axioms _root_.GD.N0031.d023847
#print axioms _root_.GD.N0031.d023848
#print axioms _root_.GD.N0031.d023849
