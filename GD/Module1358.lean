import GD.Module0884

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0045
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1434 _root_.GD.N0232.N0720.N1441

theorem d021921 (m n : ℕ) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1441.d013678 m n t = _root_.GD.N0232.N0720.N1436.d013288.withDensity
      (fun z => ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 m n (t : ℝ) z)) := rfl

theorem d021922 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    ∀ᵐ z ∂_root_.GD.N0232.N0720.N1436.d013288, 0 < _root_.GD.N0232.N0720.N1436.d013273 m n (t : ℝ) z := by
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with z hz
  exact _root_.GD.N0232.N0720.N1436.d013286 hm hn t.property.1 t.property.2 hz


theorem d021923 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    (∫ z, f z ∂_root_.GD.N0232.N0720.N1441.d013678 m n t) =
      ∫ z, _root_.GD.N0232.N0720.N1436.d013273 m n (t : ℝ) z * f z ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  rw [_root_.GD.N0045.d021921, integral_withDensity_eq_integral_toReal_smul
    (_root_.GD.N0232.N0720.N1436.d013279 m n t).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0045.d021922 m n hm hn t] with z hz
  rw [ENNReal.toReal_ofReal hz.le, smul_eq_mul]

theorem d021924 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : ∀ z, |f z| ≤ B) :
    Integrable (fun z => _root_.GD.N0232.N0720.N1436.d013273 m n (t : ℝ) z * f z) _root_.GD.N0232.N0720.N1436.d013288 := by
  have hi := _root_.GD.N0232.N0720.N1434.d013559 hm hn
    t.property.1 t.property.2 f hf hB
  have hi' := (integrable_withDensity_iff_integrable_smul₀'
    (μ := _root_.GD.N0232.N0720.N1436.d013288)
    (f := fun z => ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 m n (t : ℝ) z))
    (_root_.GD.N0232.N0720.N1436.d013279 m n t).ennreal_ofReal.aemeasurable
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hi
  apply hi'.congr
  filter_upwards [_root_.GD.N0045.d021922 m n hm hn t] with z hz
  rw [ENNReal.toReal_ofReal hz.le, smul_eq_mul]

theorem d021925 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    Integrable (_root_.GD.N0232.N0720.N1436.d013273 m n (t : ℝ)) _root_.GD.N0232.N0720.N1436.d013288 := by
  simpa only [mul_one] using _root_.GD.N0045.d021924 m n hm hn t
    (fun _ => 1) measurable_const (B := 1) (by intro z; norm_num)

theorem d021926 {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} {B : ℝ}
    (hB : ∀ z, |g z| ≤ B) (a : ℝ) (z : _root_.GD.N0232.N0720.N1436.d013217) :
    |(g z - a) ^ 2| ≤ (B + |a|) ^ 2 := by
  have ha : |g z - a| ≤ B + |a| := (abs_sub (g z) a).trans (add_le_add (hB z) le_rfl)
  have hb : 0 ≤ B + |a| := (abs_nonneg _).trans ha
  have hh := (sq_le_sq₀ (abs_nonneg (g z - a)) hb).mpr ha
  simpa only [sq_abs, abs_of_nonneg (sq_nonneg (g z - a))] using hh

theorem d021927 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B) (a : ℝ) :
    Integrable (fun z => (g z - a) ^ 2) (_root_.GD.N0232.N0720.N1441.d013678 m n t) :=
  _root_.GD.N0232.N0720.N1434.d013559 hm hn t.property.1 t.property.2
    (fun z => (g z - a) ^ 2) (by fun_prop) (_root_.GD.N0045.d021926 hB a)

theorem d021928 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B) (a : ℝ) :
    Integrable (fun z => _root_.GD.N0232.N0720.N1436.d013273 m n (t : ℝ) z * (g z - a) ^ 2)
      _root_.GD.N0232.N0720.N1436.d013288 :=
  _root_.GD.N0045.d021924 m n hm hn t (fun z => (g z - a) ^ 2)
    (by fun_prop) (_root_.GD.N0045.d021926 hB a)

end
end GD.N0045

#print axioms _root_.GD.N0045.d021921
#print axioms _root_.GD.N0045.d021922
#print axioms _root_.GD.N0045.d021923
#print axioms _root_.GD.N0045.d021924
#print axioms _root_.GD.N0045.d021927
#print axioms _root_.GD.N0045.d021928
