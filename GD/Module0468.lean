import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0052
noncomputable section

def d007220 (a b c : ℝ) : ℝ := max (min a b) (min (max a b) c)

theorem d007221 (a b c : ℝ) : _root_.GD.N0052.d007220 a b c = _root_.GD.N0052.d007220 b a c := by
  simp only [_root_.GD.N0052.d007220, min_comm a b, max_comm a b]

theorem d007222 (a b c : ℝ) : _root_.GD.N0052.d007220 a b c = _root_.GD.N0052.d007220 a c b := by
  unfold _root_.GD.N0052.d007220
  rcases le_total a b with hab | hba <;>
    rcases le_total a c with hac | hca <;>
    rcases le_total b c with hbc | hcb <;>
    simp_all <;> linarith


theorem d007223 (a b c μ : ℝ) :
    (_root_.GD.N0052.d007220 a b c - μ) ^ 2 ≤ (a - μ) ^ 2 + (b - μ) ^ 2 := by
  have hlo : min a b ≤ _root_.GD.N0052.d007220 a b c := le_max_left _ _
  have hhi : _root_.GD.N0052.d007220 a b c ≤ max a b :=
    max_le (min_le_left a b |>.trans (le_max_left a b)) (min_le_left _ _)
  let M := max |a - μ| |b - μ|
  have hA : |a - μ| ≤ M := le_max_left _ _
  have hB : |b - μ| ≤ M := le_max_right _ _
  have hM : 0 ≤ M := (abs_nonneg _).trans hA
  have hl : μ - M ≤ min a b := le_min
    (by have := (abs_le.mp hA).1; linarith)
    (by have := (abs_le.mp hB).1; linarith)
  have hu : max a b ≤ μ + M := max_le
    (by have := (abs_le.mp hA).2; linarith)
    (by have := (abs_le.mp hB).2; linarith)
  have ha : |_root_.GD.N0052.d007220 a b c - μ| ≤ M := abs_le.mpr ⟨by linarith, by linarith⟩
  have hs : |_root_.GD.N0052.d007220 a b c - μ| ^ 2 ≤ M ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hM).mpr ha
  rw [sq_abs] at hs
  rcases le_total |a - μ| |b - μ| with h | h
  · simpa only [M, max_eq_right h, sq_abs] using
      hs.trans (by simp only [M, max_eq_right h, sq_abs]; nlinarith [sq_nonneg (a - μ)])
  · simpa only [M, max_eq_left h, sq_abs] using
      hs.trans (by simp only [M, max_eq_left h, sq_abs]; nlinarith [sq_nonneg (b - μ)])

theorem d007224 (a b c μ : ℝ) :
    (_root_.GD.N0052.d007220 a b c - μ) ^ 2 ≤ (a - μ) ^ 2 + (c - μ) ^ 2 := by
  rw [_root_.GD.N0052.d007222]
  exact _root_.GD.N0052.d007223 a c b μ

theorem d007225 (a b c μ : ℝ) :
    (_root_.GD.N0052.d007220 a b c - μ) ^ 2 ≤ (b - μ) ^ 2 + (c - μ) ^ 2 := by
  rw [_root_.GD.N0052.d007221, _root_.GD.N0052.d007222]
  exact _root_.GD.N0052.d007223 b c a μ

variable {Ω : Type*} [MeasurableSpace Ω]

def d007226 (f g h : Ω → ℝ) : Ω → ℝ := fun z => _root_.GD.N0052.d007220 (f z) (g z) (h z)

theorem d007227 {f g h : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable (_root_.GD.N0052.d007226 f g h) := by
  unfold _root_.GD.N0052.d007226 _root_.GD.N0052.d007220
  exact (hf.min hg).max ((hf.max hg).min hh)

def d007228 (P : Measure Ω) (μ : ℝ) (f : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((f z - μ) ^ 2) ∂P


theorem d007229 (P : Measure Ω) (μ : ℝ)
    (f g h : Ω → ℝ) (hf : Measurable f) (_hg : Measurable g) :
    _root_.GD.N0052.d007228 P μ (_root_.GD.N0052.d007226 f g h) ≤ _root_.GD.N0052.d007228 P μ f + _root_.GD.N0052.d007228 P μ g := by
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal ((f z - μ) ^ 2 + (g z - μ) ^ 2) ∂P :=
      lintegral_mono fun z => ENNReal.ofReal_le_ofReal (_root_.GD.N0052.d007223 _ _ _ _)
    _ = _root_.GD.N0052.d007228 P μ f + _root_.GD.N0052.d007228 P μ g := by
      simp only [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      exact lintegral_add_left (by fun_prop) _

theorem d007230 (P : Measure Ω) (μ : ℝ)
    (f g h : Ω → ℝ) (hf : Measurable f) (hh : Measurable h) :
    _root_.GD.N0052.d007228 P μ (_root_.GD.N0052.d007226 f g h) ≤ _root_.GD.N0052.d007228 P μ f + _root_.GD.N0052.d007228 P μ h := by
  have hm : _root_.GD.N0052.d007226 f g h = _root_.GD.N0052.d007226 f h g := by
    funext z
    exact _root_.GD.N0052.d007222 _ _ _
  rw [hm]
  exact _root_.GD.N0052.d007229 P μ f h g hf hh

theorem d007231 (P : Measure Ω) (μ : ℝ)
    (f g h : Ω → ℝ) (hg : Measurable g) (hh : Measurable h) :
    _root_.GD.N0052.d007228 P μ (_root_.GD.N0052.d007226 f g h) ≤ _root_.GD.N0052.d007228 P μ g + _root_.GD.N0052.d007228 P μ h := by
  have hm : _root_.GD.N0052.d007226 f g h = _root_.GD.N0052.d007226 g h f := by
    funext z
    rw [_root_.GD.N0052.d007226, _root_.GD.N0052.d007226, _root_.GD.N0052.d007221, _root_.GD.N0052.d007222]
  rw [hm]
  exact _root_.GD.N0052.d007229 P μ g h f hg hh

end
end GD.N0052

#print axioms _root_.GD.N0052.d007223
#print axioms _root_.GD.N0052.d007224
#print axioms _root_.GD.N0052.d007225
#print axioms _root_.GD.N0052.d007227
#print axioms _root_.GD.N0052.d007229
#print axioms _root_.GD.N0052.d007230
#print axioms _root_.GD.N0052.d007231
