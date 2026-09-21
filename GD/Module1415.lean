import GD.Module1414

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GD.N0076.N0312

noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859

variable {X : Type*} [MeasurableSpace X]

theorem d022683 (μ : Measure X) [IsProbabilityMeasure μ] (c r : ℝ) :
    _root_.GD.N0076.N0312.d022661 μ c (fun _ => r) = ENNReal.ofReal ((r - c) ^ 2) := by
  simp [_root_.GD.N0076.N0312.d022661]




theorem d022684
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ) :
    μ = ν ↔ ∀ (d e : X → ℝ), Measurable d → Measurable e →
      _root_.GD.N0076.N0312.d022661 μ c d ≤ _root_.GD.N0076.N0312.d022661 μ c e → _root_.GD.N0076.N0312.d022661 ν c d ≤ _root_.GD.N0076.N0312.d022661 ν c e := by
  constructor
  · rintro rfl d e _ _ h
    exact h
  · intro h
    apply Measure.ext
    intro s hs
    let d : X → ℝ := fun x => c + s.indicator (fun _ => (1 : ℝ)) x
    let r : ℝ := c + Real.sqrt (μ s).toReal
    have hd : Measurable d := measurable_const.add (measurable_const.indicator hs)
    have hrμ : _root_.GD.N0076.N0312.d022661 μ c (fun _ => r) = μ s := by
      rw [_root_.GD.N0076.N0312.d022683]
      simp only [r, add_sub_cancel_left, Real.sq_sqrt ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top μ s)]
    have hrν : _root_.GD.N0076.N0312.d022661 ν c (fun _ => r) = μ s := by
      rw [_root_.GD.N0076.N0312.d022683]
      simp only [r, add_sub_cancel_left, Real.sq_sqrt ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top μ s)]
    have hdμ : _root_.GD.N0076.N0312.d022661 μ c d = μ s := _root_.GD.N0076.N0312.d022663 μ c s hs
    have hdν : _root_.GD.N0076.N0312.d022661 ν c d = ν s := _root_.GD.N0076.N0312.d022663 ν c s hs
    have h₁ := h d (fun _ => r) hd measurable_const (by rw [hdμ, hrμ])
    have h₂ := h (fun _ => r) d measurable_const hd (by rw [hrμ, hdμ])
    rw [hdν, hrν] at h₁ h₂
    exact le_antisymm h₂ h₁


variable {Y : Type*} [MeasurableSpace Y]

theorem d022685 (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : X → Y) (hT : Measurable T) (c : ℝ) :
    μ.map T = ν ↔ ∀ (d e : Y → ℝ), Measurable d → Measurable e →
      _root_.GD.N0076.N0312.d022661 μ c (d ∘ T) ≤ _root_.GD.N0076.N0312.d022661 μ c (e ∘ T) →
        _root_.GD.N0076.N0312.d022661 ν c d ≤ _root_.GD.N0076.N0312.d022661 ν c e := by
  letI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  constructor
  · intro h d e hd he hde
    apply (_root_.GD.N0076.N0312.d022684 (μ.map T) ν c).mp h d e hd he
    simpa only [_root_.GD.N0076.N0312.d022662 μ T hT c d hd, _root_.GD.N0076.N0312.d022662 μ T hT c e he] using hde
  · intro h
    apply (_root_.GD.N0076.N0312.d022684 (μ.map T) ν c).mpr
    intro d e hd he hde
    apply h d e hd he
    simpa only [_root_.GD.N0076.N0312.d022662 μ T hT c d hd, _root_.GD.N0076.N0312.d022662 μ T hT c e he] using hde

theorem d022686 (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ : ProbabilityTheory.Kernel X Y) [ProbabilityTheory.IsMarkovKernel κ] (c : ℝ) :
    κ ∘ₘ μ = ν ↔ ∀ (d e : Y → ℝ), Measurable d → Measurable e →
      (∫⁻ x, _root_.GD.N0076.N0312.d022661 (κ x) c d ∂μ) ≤ (∫⁻ x, _root_.GD.N0076.N0312.d022661 (κ x) c e ∂μ) →
        _root_.GD.N0076.N0312.d022661 ν c d ≤ _root_.GD.N0076.N0312.d022661 ν c e := by
  have h (d : Y → ℝ) (hd : Measurable d) :
      _root_.GD.N0076.N0312.d022661 (κ ∘ₘ μ) c d = ∫⁻ x, _root_.GD.N0076.N0312.d022661 (κ x) c d ∂μ :=
    Measure.lintegral_bind κ.aemeasurable (by fun_prop)
  constructor
  · intro hκ d e hd he hde
    apply (_root_.GD.N0076.N0312.d022684 (κ ∘ₘ μ) ν c).mp hκ d e hd he
    simpa only [h d hd, h e he] using hde
  · intro hκ
    apply (_root_.GD.N0076.N0312.d022684 (κ ∘ₘ μ) ν c).mpr
    intro d e hd he hde
    apply hκ d e hd he
    simpa only [h d hd, h e he] using hde

theorem d022687 {k l : ℕ} {n : Fin k → ℕ} {m : Fin l → ℕ}
    (g : Fin l → Fin k) (j : ∀ i, Fin (m i) → Fin (n (g i)))
    (x : _root_.GD.N0232.N0719.d009173 k n) (b a : ℝ) :
    _root_.GD.N0076.N0312.d022672 g j (_root_.GD.N0232.N0719.N0900.d009095 k n b a x) =
      _root_.GD.N0232.N0719.N0900.d009095 l m b a (_root_.GD.N0076.N0312.d022672 g j x) := rfl

theorem d022688 {k l : ℕ} {n : Fin k → ℕ} {m : Fin l → ℕ}
    (g : Fin l → Fin k) (j : ∀ i, Fin (m i) → Fin (n (g i)))
    (d : _root_.GD.N0232.N0719.d009173 l m → ℝ)
    (hd : ∀ (x : _root_.GD.N0232.N0719.d009173 l m) (b a : ℝ), 0 < a →
      d (_root_.GD.N0232.N0719.N0900.d009095 l m b a x) = b + a * d x) :
    ∀ (x : _root_.GD.N0232.N0719.d009173 k n) (b a : ℝ), 0 < a →
      (d ∘ _root_.GD.N0076.N0312.d022672 g j) (_root_.GD.N0232.N0719.N0900.d009095 k n b a x) =
        b + a * (d ∘ _root_.GD.N0076.N0312.d022672 g j) x := by
  intro x b a ha
  exact hd (_root_.GD.N0076.N0312.d022672 g j x) b a ha

def d022689 : _root_.GD.N0232.N0719.d009173 2 (fun _ => 3) :=
  fun _ => ![-1, 1, 0]

def d022690 : _root_.GD.N0232.N0719.d009173 2 (fun _ => 3) :=
  ![![-1, 1, 3], ![-1, 1, 0]]

def d022691 : _root_.GD.N0232.N0719.d009173 2 (fun _ => 3) →
    _root_.GD.N0232.N0719.d009173 2 (fun _ => 2) :=
  _root_.GD.N0076.N0312.d022672 id (fun _ => Fin.castLE (by decide))

theorem d022692 :
    _root_.GD.N0076.N0312.d022691 _root_.GD.N0076.N0312.d022689 = _root_.GD.N0076.N0312.d022691 _root_.GD.N0076.N0312.d022690 := by
  funext i a
  fin_cases i <;> fin_cases a <;> rfl

theorem d022693 :
    _root_.GD.N0076.N0310.d014216 2 (fun _ => 3) _root_.GD.N0076.N0312.d022689 = 0 := by
  norm_num [_root_.GD.N0076.N0310.d014216, _root_.GD.N0076.N0310.d014206,
    _root_.GD.N0076.N0310.d014205, Fin.sum_univ_succ, _root_.GD.N0076.N0312.d022689]

theorem d022694 :
    _root_.GD.N0076.N0310.d014216 2 (fun _ => 3) _root_.GD.N0076.N0312.d022690 = 1 / 5 := by
  norm_num [_root_.GD.N0076.N0310.d014216, _root_.GD.N0076.N0310.d014206,
    _root_.GD.N0076.N0310.d014205, Fin.sum_univ_succ, _root_.GD.N0076.N0312.d022690]




theorem d022695 :
    ¬ ∃ d : _root_.GD.N0232.N0719.d009173 2 (fun _ => 2) → ℝ,
      _root_.GD.N0076.N0310.d014216 2 (fun _ => 3) = d ∘ _root_.GD.N0076.N0312.d022691 := by
  apply _root_.GD.N0076.N0312.d022668 _root_.GD.N0076.N0312.d022691 _ _root_.GD.N0076.N0312.d022689 _root_.GD.N0076.N0312.d022690
    _root_.GD.N0076.N0312.d022692
  rw [_root_.GD.N0076.N0312.d022693, _root_.GD.N0076.N0312.d022694]
  norm_num


theorem d022696 :
    ∀ i : Fin 2,
      0 < _root_.GD.N0107.d009085 (_root_.GD.N0076.N0312.d022689 i) ∧
      0 < _root_.GD.N0107.d009085 (_root_.GD.N0076.N0312.d022690 i) := by
  intro i
  fin_cases i <;>
    norm_num [_root_.GD.N0076.N0310.d014206,
      _root_.GD.N0076.N0310.d014205, Fin.sum_univ_succ,
      _root_.GD.N0076.N0312.d022689, _root_.GD.N0076.N0312.d022690]



theorem d022697 :
    ¬ ∃ d : _root_.GD.N0232.N0719.d009173 2 (fun _ => 2) → ℝ,
      _root_.GD.N0232.N0719.N0859.d010815 2 (fun _ => 3) = d ∘ _root_.GD.N0076.N0312.d022691 := by
  apply _root_.GD.N0076.N0312.d022668 _root_.GD.N0076.N0312.d022691 _ _root_.GD.N0076.N0312.d022689 _root_.GD.N0076.N0312.d022690
    _root_.GD.N0076.N0312.d022692
  have h₀ := _root_.GD.N0076.N0310.d014219 2 (fun _ => 3)
    (by decide) (fun _ => by decide) _root_.GD.N0076.N0312.d022689
    (fun i => (_root_.GD.N0076.N0312.d022696 i).1)
  have h₁ := _root_.GD.N0076.N0310.d014219 2 (fun _ => 3)
    (by decide) (fun _ => by decide) _root_.GD.N0076.N0312.d022690
    (fun i => (_root_.GD.N0076.N0312.d022696 i).2)
  rw [← h₀, ← h₁, _root_.GD.N0076.N0312.d022693, _root_.GD.N0076.N0312.d022694]
  norm_num

end
end GD.N0076.N0312

#print axioms _root_.GD.N0076.N0312.d022687
#print axioms _root_.GD.N0076.N0312.d022688
#print axioms _root_.GD.N0076.N0312.d022692
#print axioms _root_.GD.N0076.N0312.d022693
#print axioms _root_.GD.N0076.N0312.d022694
#print axioms _root_.GD.N0076.N0312.d022695

#print axioms _root_.GD.N0076.N0312.d022683
#print axioms _root_.GD.N0076.N0312.d022684

#print axioms _root_.GD.N0076.N0312.d022685
#print axioms _root_.GD.N0076.N0312.d022686

#print axioms _root_.GD.N0076.N0312.d022696
#print axioms _root_.GD.N0076.N0312.d022697
