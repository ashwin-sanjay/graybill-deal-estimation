import Mathlib






set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0138.N0430
noncomputable section

abbrev d007904 (n : ℕ) := Fin n → ℝ

def d007905 (n : ℕ) : Measure (_root_.GD.N0138.N0430.d007904 n) :=
  Measure.pi (fun _ => gaussianReal 0 1)

def d007906 (n : ℕ) (mu sigma : ℝ) (x : _root_.GD.N0138.N0430.d007904 n) : _root_.GD.N0138.N0430.d007904 n :=
  fun j => mu + sigma * x j

def d007907 (n : ℕ) (mu sigma : ℝ) : Measure (_root_.GD.N0138.N0430.d007904 n) :=
  (_root_.GD.N0138.N0430.d007905 n).map (_root_.GD.N0138.N0430.d007906 n mu sigma)

def d007908 (k : ℕ) (sizes : Fin k → ℕ) (mu : ℝ) (sigma : Fin k → ℝ) :
    Measure (∀ i, _root_.GD.N0138.N0430.d007904 (sizes i)) :=
  Measure.pi (fun i => _root_.GD.N0138.N0430.d007907 (sizes i) mu (sigma i))

def d007909 (m n : ℕ) (mu sigma tau : ℝ) : Measure (_root_.GD.N0138.N0430.d007904 m × _root_.GD.N0138.N0430.d007904 n) :=
  ((_root_.GD.N0138.N0430.d007905 m).prod (_root_.GD.N0138.N0430.d007905 n)).map
    (fun x => (_root_.GD.N0138.N0430.d007906 m mu sigma x.1, _root_.GD.N0138.N0430.d007906 n mu tau x.2))

def d007910 (n : ℕ) (x : _root_.GD.N0138.N0430.d007904 n) : ℝ := (∑ j, x j) / (n : ℝ)

def d007911 (n : ℕ) (x : _root_.GD.N0138.N0430.d007904 n) : ℝ :=
  (∑ j, (x j - _root_.GD.N0138.N0430.d007910 n x) ^ 2) / ((n - 1 : ℕ) : ℝ)

def d007912 (n : ℕ) (x : _root_.GD.N0138.N0430.d007904 n) : ℝ :=
  if 0 < _root_.GD.N0138.N0430.d007911 n x / (n : ℝ) then (_root_.GD.N0138.N0430.d007911 n x / (n : ℝ))⁻¹ else 0

def d007913 (k : ℕ) (sizes : Fin k → ℕ) (x : ∀ i, _root_.GD.N0138.N0430.d007904 (sizes i)) : ℝ :=
  let total := ∑ i, _root_.GD.N0138.N0430.d007912 (sizes i) (x i)
  ∑ i, (if total = 0 then (k : ℝ)⁻¹
        else _root_.GD.N0138.N0430.d007912 (sizes i) (x i) / total) * _root_.GD.N0138.N0430.d007910 (sizes i) (x i)

def d007914 (m n : ℕ) (x : _root_.GD.N0138.N0430.d007904 m × _root_.GD.N0138.N0430.d007904 n) : ℝ :=
  let vx := _root_.GD.N0138.N0430.d007911 m x.1 / (m : ℝ)
  let vy := _root_.GD.N0138.N0430.d007911 n x.2 / (n : ℝ)
  let weight := if 0 < vx + vy then vy / (vx + vy) else (1 : ℝ) / 2
  _root_.GD.N0138.N0430.d007910 n x.2 + weight * (_root_.GD.N0138.N0430.d007910 m x.1 - _root_.GD.N0138.N0430.d007910 n x.2)

def d007915 {X : Type*} [MeasurableSpace X] (law : Measure X)
    (mu : ℝ) (d : X → ℝ) : ℝ := ∫ x, (d x - mu) ^ 2 ∂law

def d007916 {X : Type*} [MeasurableSpace X] (law : Measure X)
    (mu : ℝ) (d : X → ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal ((d x - mu) ^ 2) ∂law


def d007917 : Prop :=
  ∀ (k : ℕ), 0 < k → ∀ (mu : ℝ) (sigma : Fin k → ℝ),
    (∀ i, 0 < sigma i) →
    _root_.GD.N0138.N0430.d007915 (_root_.GD.N0138.N0430.d007908 k (fun _ => 2) mu sigma) mu (_root_.GD.N0138.N0430.d007913 k (fun _ => 2)) =
      ((∑ i, sigma i) / (∑ i, (sigma i)⁻¹) +
        (k : ℝ) / (∑ i, (sigma i)⁻¹) ^ 2) / 4


def d007918 : Prop :=
  ∀ (m n : ℕ), 2 ≤ m → 2 ≤ n →
    ∃ d : _root_.GD.N0138.N0430.d007904 m × _root_.GD.N0138.N0430.d007904 n → ℝ, Measurable d ∧
      ∀ (mu sigma tau : ℝ), 0 < sigma → 0 < tau →
        Integrable (fun x => (d x - mu) ^ 2) (_root_.GD.N0138.N0430.d007909 m n mu sigma tau) ∧
        _root_.GD.N0138.N0430.d007915 (_root_.GD.N0138.N0430.d007909 m n mu sigma tau) mu d <
          _root_.GD.N0138.N0430.d007915 (_root_.GD.N0138.N0430.d007909 m n mu sigma tau) mu (_root_.GD.N0138.N0430.d007914 m n)

def d007919 (x : _root_.GD.N0138.N0430.d007904 3 × _root_.GD.N0138.N0430.d007904 3) : ℝ :=
  let vx := _root_.GD.N0138.N0430.d007911 3 x.1
  let vy := _root_.GD.N0138.N0430.d007911 3 x.2
  if vx ^ 2 + vy ^ 2 = 0 then (_root_.GD.N0138.N0430.d007910 3 x.1 + _root_.GD.N0138.N0430.d007910 3 x.2) / 2
  else (vy ^ 2 * _root_.GD.N0138.N0430.d007910 3 x.1 + vx ^ 2 * _root_.GD.N0138.N0430.d007910 3 x.2) / (vx ^ 2 + vy ^ 2)

abbrev d007920 := {s : ℝ // 0 < s}

def d007921 (d : _root_.GD.N0138.N0430.d007904 3 × _root_.GD.N0138.N0430.d007904 3 → ℝ)
    (mu : ℝ) (sigma tau : _root_.GD.N0138.N0430.d007920) : ℝ≥0∞ :=
  _root_.GD.N0138.N0430.d007916 (_root_.GD.N0138.N0430.d007909 3 3 mu sigma tau) mu d /
    ENNReal.ofReal (1 / (3 / (sigma : ℝ) ^ 2 + 3 / (tau : ℝ) ^ 2))

def d007922 (d : _root_.GD.N0138.N0430.d007904 3 × _root_.GD.N0138.N0430.d007904 3 → ℝ) : ℝ≥0∞ :=
  ⨆ (mu : ℝ) (sigma : _root_.GD.N0138.N0430.d007920) (tau : _root_.GD.N0138.N0430.d007920), _root_.GD.N0138.N0430.d007921 d mu sigma tau


def d007923 : Prop :=
  (∀ d : _root_.GD.N0138.N0430.d007904 3 × _root_.GD.N0138.N0430.d007904 3 → ℝ, Measurable d →
    ENNReal.ofReal (1 + Real.pi / 4) ≤ _root_.GD.N0138.N0430.d007922 d) ∧
  Measurable _root_.GD.N0138.N0430.d007919 ∧
  _root_.GD.N0138.N0430.d007922 _root_.GD.N0138.N0430.d007919 = ENNReal.ofReal (1 + Real.pi / 4) ∧
  ∀ (mu : ℝ) (sigma tau : _root_.GD.N0138.N0430.d007920),
    _root_.GD.N0138.N0430.d007921 _root_.GD.N0138.N0430.d007919 mu sigma tau < ENNReal.ofReal (1 + Real.pi / 4)


theorem d007924 : Nonempty _root_.GD.N0138.N0430.d007920 := ⟨⟨1, zero_lt_one⟩⟩

theorem d007925 (n : ℕ) (mu sigma : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0138.N0430.d007907 n mu sigma) := by
  have : IsProbabilityMeasure (_root_.GD.N0138.N0430.d007905 n) := by unfold _root_.GD.N0138.N0430.d007905; infer_instance
  have hm : Measurable (_root_.GD.N0138.N0430.d007906 n mu sigma) := by unfold _root_.GD.N0138.N0430.d007906; fun_prop
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

theorem d007926 (k : ℕ) (sizes : Fin k → ℕ)
    (mu : ℝ) (sigma : Fin k → ℝ) : IsProbabilityMeasure (_root_.GD.N0138.N0430.d007908 k sizes mu sigma) := by
  have (i : Fin k) : IsProbabilityMeasure (_root_.GD.N0138.N0430.d007907 (sizes i) mu (sigma i)) :=
    _root_.GD.N0138.N0430.d007925 _ _ _
  unfold _root_.GD.N0138.N0430.d007908
  infer_instance

theorem d007927 (m n : ℕ) (mu sigma tau : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0138.N0430.d007909 m n mu sigma tau) := by
  have (r : ℕ) : IsProbabilityMeasure (_root_.GD.N0138.N0430.d007905 r) := by unfold _root_.GD.N0138.N0430.d007905; infer_instance
  have hm : Measurable (fun x : _root_.GD.N0138.N0430.d007904 m × _root_.GD.N0138.N0430.d007904 n =>
      (_root_.GD.N0138.N0430.d007906 m mu sigma x.1, _root_.GD.N0138.N0430.d007906 n mu tau x.2)) := by
    unfold _root_.GD.N0138.N0430.d007906
    fun_prop
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

end
end GD.N0138.N0430
