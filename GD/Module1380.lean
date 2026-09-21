import GD.Module1379












set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0182
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0178 _root_.GD.N0180
open _root_.GD.N0163


def d022216 (t : _root_.GD.N0232.N0720.N1441.d013676) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨1 - (t : ℝ), by constructor <;> linarith [t.property.1, t.property.2]⟩


theorem d022217 (t u s : ℝ) :
    _root_.GD.N0178.d007131 (1 - t) u s = _root_.GD.N0178.d007131 t (1 - u) s := by
  have hd : _root_.GD.N0178.d007129 (1 - t) u s = _root_.GD.N0178.d007129 t (1 - u) s := by
    unfold _root_.GD.N0178.d007129
    simp only [sub_sub_cancel]
    ring
  unfold _root_.GD.N0178.d007131
  rw [hd]
  simp only [sub_sub_cancel]
  congr 1
  ring


theorem d022218 {q t t₀ d u s v : ℝ}
    (hq : 0 ≤ q) (ht : 0 < t) (hqt : q * t₀ ≤ t)
    (htt₀ : t ≤ t₀) (ht₀d : t₀ ≤ d) (hd : d < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hs : 0 < s) (hv : 0 ≤ v) :
    _root_.GD.N0178.d007132 q d * _root_.GD.N0178.d007131 (1 - t) u s * (v - (1 - t)) ^ 2 -
        2 * _root_.GD.N0178.d007132 q d * (t₀ - t) * _root_.GD.N0178.d007131 (1 - t) u s ≤
      _root_.GD.N0178.d007131 (1 - t₀) u s * (v - (1 - t₀)) ^ 2 := by
  have h := _root_.GD.N0178.d007143 hq ht hqt htt₀ ht₀d hd
    (show 0 ≤ 1 - u by linarith) (show 1 - u ≤ 1 by linarith) hs
    (show 1 - v ≤ 1 by linarith)
  rw [← _root_.GD.N0182.d022217 t u s, ← _root_.GD.N0182.d022217 t₀ u s] at h
  have hs0 : (1 - v - t) ^ 2 = (v - (1 - t)) ^ 2 := by ring
  have hs1 : (1 - v - t₀) ^ 2 = (v - (1 - t₀)) ^ 2 := by ring
  simpa only [hs0, hs1] using h


theorem d022219 (t t₀ : _root_.GD.N0232.N0720.N1441.d013676) {q d : ℝ}
    (hq : 0 ≤ q) (hqt : q * (t₀ : ℝ) ≤ t) (htt₀ : (t : ℝ) ≤ t₀)
    (ht₀d : (t₀ : ℝ) ≤ d) (hd : d < 1)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    _root_.GD.N0178.d007132 q d * _root_.GD.N0180.d022173 (_root_.GD.N0182.d022216 t) g -
      2 * _root_.GD.N0178.d007132 q d * ((t₀ : ℝ) - t) / ((t : ℝ) * (1 - t)) ≤
      _root_.GD.N0180.d022173 (_root_.GD.N0182.d022216 t₀) g := by
  have hB : ∀ p, |g p| ≤ 1 := fun p => by
    rw [abs_of_nonneg (hg0 p)]
    exact hg1 p
  have hi := _root_.GD.N0180.d022174 (_root_.GD.N0182.d022216 t) g hg hB
  have hi₀ := _root_.GD.N0180.d022174 (_root_.GD.N0182.d022216 t₀) g hg hB
  have hik := _root_.GD.N0180.d022169 (_root_.GD.N0182.d022216 t)
  have h := integral_mono_ae
    ((hi.const_mul (_root_.GD.N0178.d007132 q d)).sub
      (hik.const_mul (2 * _root_.GD.N0178.d007132 q d * ((t₀ : ℝ) - t)))) hi₀
    (by
      filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with p hp
      have hpoint := _root_.GD.N0182.d022218 hq t.property.1 hqt
        htt₀ ht₀d hd hp.1.1.le hp.1.2.le hp.2 (hg0 p)
      simpa only [Pi.sub_apply, _root_.GD.N0182.d022216, mul_assoc] using hpoint)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (hi.const_mul _) (hik.const_mul _), integral_const_mul,
    integral_const_mul, _root_.GD.N0180.d022170] at h
  have hden : (_root_.GD.N0182.d022216 t : ℝ) * (1 - (_root_.GD.N0182.d022216 t : ℝ)) =
      (t : ℝ) * (1 - t) := by
    change (1 - (t : ℝ)) * (1 - (1 - t)) = _
    ring
  simpa only [_root_.GD.N0180.d022173, hden, mul_one_div] using h


theorem d022220 (t t₀ : _root_.GD.N0232.N0720.N1441.d013676) {q d : ℝ}
    (hq : 0 < q) (hqt : q * (t₀ : ℝ) ≤ t) (htt₀ : (t : ℝ) ≤ t₀)
    (ht₀d : (t₀ : ℝ) ≤ d) (hd : d < 1)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    _root_.GD.N0178.d007132 q d * _root_.GD.N0180.d022173 (_root_.GD.N0182.d022216 t) g -
      2 * _root_.GD.N0178.d007132 q d * (q⁻¹ - 1) / (1 - d) ≤ _root_.GD.N0180.d022173 (_root_.GD.N0182.d022216 t₀) g := by
  have herr := _root_.GD.N0178.d007144 hq t.property.1 hqt htt₀ ht₀d hd
  have hc : 0 ≤ 2 * _root_.GD.N0178.d007132 q d := by
    unfold _root_.GD.N0178.d007132
    exact mul_nonneg (by norm_num)
      (mul_nonneg (sq_nonneg _) (_root_.GD.N0178.d007133 (by linarith)))
  have hmul := mul_le_mul_of_nonneg_left herr hc
  have hbin := _root_.GD.N0182.d022219 t t₀ hq.le hqt htt₀ ht₀d hd g hg hg0 hg1
  rw [← mul_div_assoc, ← mul_div_assoc] at hmul
  linarith


def d022221 (t : _root_.GD.N0232.N0720.N1441.d013676) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) : ℝ :=
  _root_.GD.N0180.d022173 t g + _root_.GD.N0180.d022173 (_root_.GD.N0182.d022216 t) g


theorem d022222 (t t₀ : _root_.GD.N0232.N0720.N1441.d013676) {q d : ℝ}
    (hq : 0 < q) (hqt : q * (t₀ : ℝ) ≤ t) (htt₀ : (t : ℝ) ≤ t₀)
    (ht₀d : (t₀ : ℝ) ≤ d) (hd : d < 1)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) :
    _root_.GD.N0178.d007132 q d * _root_.GD.N0182.d022221 t g -
      2 * (2 * _root_.GD.N0178.d007132 q d * (q⁻¹ - 1) / (1 - d)) ≤ _root_.GD.N0182.d022221 t₀ g := by
  have hf := _root_.GD.N0180.d022176 t t₀ hq hqt htt₀ ht₀d hd g hg hg0 hg1
  have hr := _root_.GD.N0182.d022220 t t₀ hq hqt htt₀ ht₀d hd g hg hg0 hg1
  unfold _root_.GD.N0182.d022221
  linarith


theorem d022223 (t t₀ : _root_.GD.N0232.N0720.N1441.d013676) {q d : ℝ}
    (hq : 0 < q) (hqt : q * (t₀ : ℝ) ≤ t) (htt₀ : (t : ℝ) ≤ t₀)
    (ht₀d : (t₀ : ℝ) ≤ d) (hd : d < 1)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ p, g p ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0178.d007132 q d * _root_.GD.N0182.d022221 t (_root_.GD.N0163.d022211 g) -
      2 * (2 * _root_.GD.N0178.d007132 q d * (q⁻¹ - 1) / (1 - d)) ≤
      _root_.GD.N0182.d022221 t₀ (_root_.GD.N0163.d022211 g) :=
  _root_.GD.N0182.d022222 t t₀ hq hqt htt₀ ht₀d hd (_root_.GD.N0163.d022211 g)
    (_root_.GD.N0163.d022213 g hg)
    (fun p => (_root_.GD.N0163.d022214 g h01 p).1)
    (fun p => (_root_.GD.N0163.d022214 g h01 p).2)

end
end GD.N0182

#print axioms _root_.GD.N0182.d022217
#print axioms _root_.GD.N0182.d022218
#print axioms _root_.GD.N0182.d022219
#print axioms _root_.GD.N0182.d022220
#print axioms _root_.GD.N0182.d022222
#print axioms _root_.GD.N0182.d022223
