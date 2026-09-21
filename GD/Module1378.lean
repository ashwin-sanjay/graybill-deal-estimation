import GD.Module1376
import GD.Module0459








set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set

namespace GD.N0180
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1434
open _root_.GD.N0045 _root_.GD.N0062
open _root_.GD.N0178



theorem d022167 (t : _root_.GD.N0232.N0720.N1441.d013676)
    {u s : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hs : 0 < s) :
    _root_.GD.N0178.d007131 t u s = _root_.GD.N0232.N0720.N1436.d013273 3 3 t (u, s) / ((t : ℝ) * (1 - t)) := by
  rw [_root_.GD.N0062.d022145 t.property hu hs]
  have hD : _root_.GD.N0178.d007129 t u s = s + _root_.GD.N0062.d022142 t u := by
    unfold _root_.GD.N0178.d007129 _root_.GD.N0062.d022142
    ring
  rw [_root_.GD.N0178.d007131, hD, _root_.GD.N0178.d007130, div_div]
  congr 1
  ring

theorem d022168 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    (fun p : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0178.d007131 t p.1 p.2) =ᵐ[_root_.GD.N0232.N0720.N1436.d013288]
      (fun p => _root_.GD.N0232.N0720.N1436.d013273 3 3 t p / ((t : ℝ) * (1 - t))) := by
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
  exact _root_.GD.N0180.d022167 t hp.1 hp.2

theorem d022169 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    Integrable (fun p : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0178.d007131 t p.1 p.2)
      _root_.GD.N0232.N0720.N1436.d013288 := by
  exact ((_root_.GD.N0045.d021925 3 3 (by norm_num) (by norm_num) t).div_const
    ((t : ℝ) * (1 - t))).congr (_root_.GD.N0180.d022168 t).symm


theorem d022170 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    (∫ p : _root_.GD.N0232.N0720.N1436.d013217, _root_.GD.N0178.d007131 t p.1 p.2 ∂_root_.GD.N0232.N0720.N1436.d013288) =
      1 / ((t : ℝ) * (1 - t)) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1441.d013678 3 3 t) :=
    _root_.GD.N0232.N0720.N1434.d013564 (by norm_num) (by norm_num)
      t.property.1 t.property.2
  have hpdf : (∫ p, _root_.GD.N0232.N0720.N1436.d013273 3 3 t p ∂_root_.GD.N0232.N0720.N1436.d013288) = 1 := by
    simpa using (_root_.GD.N0045.d021923 3 3 (by norm_num) (by norm_num) t
      (fun _ => (1 : ℝ))).symm
  rw [integral_congr_ae (_root_.GD.N0180.d022168 t), integral_div, hpdf]

theorem d022171 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : ∀ p, |f p| ≤ B) :
    Integrable (fun p => _root_.GD.N0178.d007131 t p.1 p.2 * f p) _root_.GD.N0232.N0720.N1436.d013288 := by
  have hi := (_root_.GD.N0045.d021924 3 3 (by norm_num) (by norm_num)
    t f hf hB).div_const ((t : ℝ) * (1 - t))
  apply hi.congr
  filter_upwards [_root_.GD.N0180.d022168 t] with p hp
  rw [hp]
  ring


theorem d022172 (t : _root_.GD.N0232.N0720.N1441.d013676) (f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    (∫ p, _root_.GD.N0178.d007131 t p.1 p.2 * f p ∂_root_.GD.N0232.N0720.N1436.d013288) =
      (∫ p, f p ∂_root_.GD.N0232.N0720.N1441.d013678 3 3 t) / ((t : ℝ) * (1 - t)) := by
  rw [_root_.GD.N0045.d021923 3 3 (by norm_num) (by norm_num) t f, ← integral_div]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0180.d022168 t] with p hp
  rw [hp]
  ring

def d022173 (t : _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) : ℝ :=
  ∫ p, _root_.GD.N0178.d007131 t p.1 p.2 * (g p - t) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013288

theorem d022174 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ p, |g p| ≤ B) :
    Integrable (fun p => _root_.GD.N0178.d007131 t p.1 p.2 * (g p - t) ^ 2)
      _root_.GD.N0232.N0720.N1436.d013288 :=
  _root_.GD.N0180.d022171 t _ (by fun_prop) (_root_.GD.N0045.d021926 hB t)


theorem d022175 (t t₀ : _root_.GD.N0232.N0720.N1441.d013676) {q d : ℝ}
    (hq : 0 ≤ q) (hqt : q * (t₀ : ℝ) ≤ t) (htt₀ : (t : ℝ) ≤ t₀)
    (ht₀d : (t₀ : ℝ) ≤ d) (hd : d < 1)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    _root_.GD.N0178.d007132 q d * _root_.GD.N0180.d022173 t g -
      2 * _root_.GD.N0178.d007132 q d * ((t₀ : ℝ) - t) / ((t : ℝ) * (1 - t)) ≤ _root_.GD.N0180.d022173 t₀ g := by
  have hB : ∀ p, |g p| ≤ 1 := fun p => by rw [abs_of_nonneg (hg0 p)]; exact hg1 p
  have hi := _root_.GD.N0180.d022174 t g hg hB
  have hi₀ := _root_.GD.N0180.d022174 t₀ g hg hB
  have hik := _root_.GD.N0180.d022169 t
  have h := integral_mono_ae
    ((hi.const_mul (_root_.GD.N0178.d007132 q d)).sub
      (hik.const_mul (2 * _root_.GD.N0178.d007132 q d * ((t₀ : ℝ) - t)))) hi₀
    (by
      filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
      have hpoint := _root_.GD.N0178.d007143 hq t.property.1 hqt htt₀ ht₀d hd
        hp.1.1.le hp.1.2.le hp.2 (hg1 p)
      simpa only [Pi.sub_apply, mul_assoc] using hpoint)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hi.const_mul _) (hik.const_mul _), integral_const_mul,
    integral_const_mul, _root_.GD.N0180.d022170] at h
  simpa only [_root_.GD.N0180.d022173, mul_one_div] using h


theorem d022176 (t t₀ : _root_.GD.N0232.N0720.N1441.d013676) {q d : ℝ}
    (hq : 0 < q) (hqt : q * (t₀ : ℝ) ≤ t) (htt₀ : (t : ℝ) ≤ t₀)
    (ht₀d : (t₀ : ℝ) ≤ d) (hd : d < 1)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    _root_.GD.N0178.d007132 q d * _root_.GD.N0180.d022173 t g -
      2 * _root_.GD.N0178.d007132 q d * (q⁻¹ - 1) / (1 - d) ≤ _root_.GD.N0180.d022173 t₀ g := by
  have herr := _root_.GD.N0178.d007144 hq t.property.1 hqt htt₀ ht₀d hd
  have hc : 0 ≤ 2 * _root_.GD.N0178.d007132 q d := by
    unfold _root_.GD.N0178.d007132
    exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (_root_.GD.N0178.d007133 (by linarith)))
  have hmul := mul_le_mul_of_nonneg_left herr hc
  have hbin := _root_.GD.N0180.d022175 t t₀ hq.le hqt htt₀ ht₀d hd g hg hg0 hg1
  rw [← mul_div_assoc, ← mul_div_assoc] at hmul
  linarith

end
end GD.N0180

#print axioms _root_.GD.N0180.d022167
#print axioms _root_.GD.N0180.d022169
#print axioms _root_.GD.N0180.d022170
#print axioms _root_.GD.N0180.d022171
#print axioms _root_.GD.N0180.d022172
#print axioms _root_.GD.N0180.d022174
#print axioms _root_.GD.N0180.d022175
#print axioms _root_.GD.N0180.d022176
