import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory

namespace GD.N0018.N0254

noncomputable section

def d007702 (f g h : ℝ) : ℝ := f / 2 + 2 * g / 13 + 9 * h / 26

def d007703 (f g h : ℝ) : ℝ := 4 * (g - f) ^ 2 + 9 * (h - f) ^ 2

theorem d007704 (f g h μ : ℝ) :
    (_root_.GD.N0018.N0254.d007702 f g h - μ) ^ 2 + _root_.GD.N0018.N0254.d007703 f g h / 52 +
        9 * (g - h) ^ 2 / 169 =
      (f - μ) ^ 2 / 2 + 2 * (g - μ) ^ 2 / 13 + 9 * (h - μ) ^ 2 / 26 := by
  unfold _root_.GD.N0018.N0254.d007702 _root_.GD.N0018.N0254.d007703
  ring

theorem d007705 (f g h : ℝ) : 0 ≤ _root_.GD.N0018.N0254.d007703 f g h := by
  unfold _root_.GD.N0018.N0254.d007703
  positivity

theorem d007706 (f g h : ℝ) :
    _root_.GD.N0018.N0254.d007703 f g h = 0 ↔ g = f ∧ h = f := by
  constructor
  · intro he
    have h₁ := sq_nonneg (g - f)
    have h₂ := sq_nonneg (h - f)
    have hg : (g - f) ^ 2 = 0 := by dsimp [_root_.GD.N0018.N0254.d007703] at he; nlinarith
    have hh : (h - f) ^ 2 = 0 := by dsimp [_root_.GD.N0018.N0254.d007703] at he; nlinarith
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hg), sub_eq_zero.mp (sq_eq_zero_iff.mp hh)⟩
  · rintro ⟨rfl, rfl⟩
    simp [_root_.GD.N0018.N0254.d007703]

theorem d007707 (f g h μ b : ℝ)
    (hf : (f - μ) ^ 2 ≤ b) (hg : (g - μ) ^ 2 ≤ b)
    (hh : (h - μ) ^ 2 ≤ b) :
    (_root_.GD.N0018.N0254.d007702 f g h - μ) ^ 2 + _root_.GD.N0018.N0254.d007703 f g h / 52 +
      9 * (g - h) ^ 2 / 169 ≤ b := by
  rw [_root_.GD.N0018.N0254.d007704]
  linarith

theorem d007708 (c : ℝ)
    (hc : ∀ f g h μ b : ℝ,
      (f - μ) ^ 2 ≤ b → (g - μ) ^ 2 ≤ b → (h - μ) ^ 2 ≤ b →
      ∃ x : ℝ, (x - μ) ^ 2 + c * _root_.GD.N0018.N0254.d007703 f g h ≤ b) :
    c ≤ 1 / 52 := by
  obtain ⟨x, hx⟩ := hc 0 1 1 (1 / 2) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num [_root_.GD.N0018.N0254.d007703] at hx
  nlinarith [sq_nonneg (x - 1 / 2)]

theorem d007709 :
    IsGreatest {c : ℝ | ∀ f g h μ b : ℝ,
      (f - μ) ^ 2 ≤ b → (g - μ) ^ 2 ≤ b → (h - μ) ^ 2 ≤ b →
      ∃ x : ℝ, (x - μ) ^ 2 + c * _root_.GD.N0018.N0254.d007703 f g h ≤ b} (1 / 52) := by
  refine ⟨?_, fun c hc => _root_.GD.N0018.N0254.d007708 c hc⟩
  intro f g h μ b hf hg hh
  refine ⟨_root_.GD.N0018.N0254.d007702 f g h, ?_⟩
  have hb := _root_.GD.N0018.N0254.d007707 f g h μ b hf hg hh
  nlinarith [sq_nonneg (g - h)]

theorem d007710 (f g h μ c d : ℝ) (hc : c + d ≠ 0) :
    (f / 2 + (c * g + d * h) / (2 * (c + d)) - μ) ^ 2 +
        (c * (g - f) ^ 2 + d * (h - f) ^ 2) / (4 * (c + d)) +
        c * d * (g - h) ^ 2 / (4 * (c + d) ^ 2) =
      (f - μ) ^ 2 / 2 + c * (g - μ) ^ 2 / (2 * (c + d)) +
        d * (h - μ) ^ 2 / (2 * (c + d)) := by
  field_simp
  ring

variable {Ω : Type*} [MeasurableSpace Ω]

def d007711 (ν : Measure Ω) (μ : ℝ) (f : Ω → ℝ) : ℝ :=
  ∫ z, (f z - μ) ^ 2 ∂ν

def d007712 (ν : Measure Ω) (f g h : Ω → ℝ) : ℝ :=
  ∫ z, _root_.GD.N0018.N0254.d007703 (f z) (g z) (h z) ∂ν

theorem d007713
    (ν : Measure Ω) (f g h : Ω → ℝ) (μ : ℝ)
    (hf : Integrable (fun z => (f z - μ) ^ 2) ν)
    (hg : Integrable (fun z => (g z - μ) ^ 2) ν)
    (hh : Integrable (fun z => (h z - μ) ^ 2) ν)
    (hb : Integrable (fun z => (_root_.GD.N0018.N0254.d007702 (f z) (g z) (h z) - μ) ^ 2) ν)
    (he : Integrable (fun z => _root_.GD.N0018.N0254.d007703 (f z) (g z) (h z)) ν)
    (hd : Integrable (fun z => (g z - h z) ^ 2) ν) :
    _root_.GD.N0018.N0254.d007711 ν μ (fun z => _root_.GD.N0018.N0254.d007702 (f z) (g z) (h z)) +
        _root_.GD.N0018.N0254.d007712 ν f g h / 52 +
        9 * _root_.GD.N0018.N0254.d007711 ν 0 (fun z => g z - h z) / 169 =
      _root_.GD.N0018.N0254.d007711 ν μ f / 2 + 2 * _root_.GD.N0018.N0254.d007711 ν μ g / 13 +
        9 * _root_.GD.N0018.N0254.d007711 ν μ h / 26 := by
  have hid := congrArg (fun F : Ω → ℝ => ∫ z, F z ∂ν)
    (funext fun z => _root_.GD.N0018.N0254.d007704 (f z) (g z) (h z) μ)
  have hbe : Integrable (fun z =>
      (_root_.GD.N0018.N0254.d007702 (f z) (g z) (h z) - μ) ^ 2 + _root_.GD.N0018.N0254.d007703 (f z) (g z) (h z) / 52) ν :=
    hb.add (he.div_const 52)
  have hfg : Integrable (fun z =>
      (f z - μ) ^ 2 / 2 + 2 * (g z - μ) ^ 2 / 13) ν :=
    (hf.div_const 2).add ((hg.const_mul 2).div_const 13)
  rw [integral_add hbe ((hd.const_mul 9).div_const 169),
    integral_add hb (he.div_const 52),
    integral_add hfg ((hh.const_mul 9).div_const 26),
    integral_add (hf.div_const 2) ((hg.const_mul 2).div_const 13)] at hid
  simp only [integral_div, integral_const_mul] at hid
  simpa only [_root_.GD.N0018.N0254.d007711, _root_.GD.N0018.N0254.d007712, sub_zero] using hid

theorem d007714
    (ν : Measure Ω) (f g h : Ω → ℝ) (μ b : ℝ)
    (hidentity :
      _root_.GD.N0018.N0254.d007711 ν μ (fun z => _root_.GD.N0018.N0254.d007702 (f z) (g z) (h z)) +
          _root_.GD.N0018.N0254.d007712 ν f g h / 52 +
          9 * _root_.GD.N0018.N0254.d007711 ν 0 (fun z => g z - h z) / 169 =
        _root_.GD.N0018.N0254.d007711 ν μ f / 2 + 2 * _root_.GD.N0018.N0254.d007711 ν μ g / 13 +
          9 * _root_.GD.N0018.N0254.d007711 ν μ h / 26)
    (hf : _root_.GD.N0018.N0254.d007711 ν μ f ≤ b) (hg : _root_.GD.N0018.N0254.d007711 ν μ g ≤ b)
    (hh : _root_.GD.N0018.N0254.d007711 ν μ h ≤ b) :
    _root_.GD.N0018.N0254.d007711 ν μ (fun z => _root_.GD.N0018.N0254.d007702 (f z) (g z) (h z)) +
      _root_.GD.N0018.N0254.d007712 ν f g h / 52 ≤ b := by
  have hd : 0 ≤ _root_.GD.N0018.N0254.d007711 ν 0 (fun z => g z - h z) :=
    integral_nonneg (fun _ => sq_nonneg _)
  linarith

end

end GD.N0018.N0254

#print axioms _root_.GD.N0018.N0254.d007704
#print axioms _root_.GD.N0018.N0254.d007710
#print axioms _root_.GD.N0018.N0254.d007708
#print axioms _root_.GD.N0018.N0254.d007709
#print axioms _root_.GD.N0018.N0254.d007713
#print axioms _root_.GD.N0018.N0254.d007714
