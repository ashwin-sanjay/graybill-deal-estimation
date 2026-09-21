import GD.Module1415
import GD.Module0357
import GD.Module0553

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GD.N0079

noncomputable section

open _root_.GD.N0076.N0312
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859

theorem d022954 {X Θ Λ : Type*} [MeasurableSpace X]
    (μ : Λ → Measure X) (c : Λ → ℝ) (ρ : Θ → Λ) (hρ : Function.Surjective ρ)
    (b : X → ℝ) :
    _root_.GD.N0079.N0318.d005274 (μ ∘ ρ) (c ∘ ρ) b ↔
      _root_.GD.N0079.N0318.d005274 μ c b := by
  constructor
  · intro h e he hdom η
    obtain ⟨θ, rfl⟩ := hρ η
    exact h e he (fun θ => hdom (ρ θ)) θ
  · intro h e he hdom θ
    apply h e he _ (ρ θ)
    intro η
    obtain ⟨ξ, rfl⟩ := hρ η
    exact hdom ξ

theorem d022955 {k l : ℕ}
    {n : Fin k → ℕ} {m : Fin l → ℕ}
    (g : Fin l → Fin k) (hg : Function.Injective g)
    (j : ∀ i, Fin (m i) → Fin (n (g i))) (hj : ∀ i, Function.Injective (j i))
    (b : _root_.GD.N0232.N0719.d009173 l m → ℝ) (hb : Measurable b) :
    _root_.GD.N0079.N0318.d005274 (_root_.GD.N0232.N0719.N0859.d010812 k n) _root_.GD.N0232.N0719.N0859.d010809.location (b ∘ _root_.GD.N0076.N0312.d022672 g j) ↔
      _root_.GD.N0079.N0318.d005274 (_root_.GD.N0232.N0719.N0859.d010812 l m) _root_.GD.N0232.N0719.N0859.d010809.location b ∧
        _root_.GD.N0079.N0318.d005276 (_root_.GD.N0232.N0719.N0859.d010812 k n) _root_.GD.N0232.N0719.N0859.d010809.location
          (_root_.GD.N0076.N0312.d022672 g j) b := by
  have h := _root_.GD.N0079.N0318.d005280 (_root_.GD.N0232.N0719.N0859.d010812 k n)
    (_root_.GD.N0232.N0719.N0859.d010812 l m ∘ _root_.GD.N0076.N0312.d022673 g) _root_.GD.N0232.N0719.N0859.d010809.location (_root_.GD.N0076.N0312.d022672 g j)
    (_root_.GD.N0076.N0312.d022674 g j) (_root_.GD.N0076.N0312.d022676 g hg j hj) b hb
  exact h.trans (and_congr
    (_root_.GD.N0079.d022954 (_root_.GD.N0232.N0719.N0859.d010812 l m) _root_.GD.N0232.N0719.N0859.d010809.location (_root_.GD.N0076.N0312.d022673 g)
      (_root_.GD.N0076.N0312.d022678 g hg) b) Iff.rfl)

structure d022956 : Prop where
  statistic_law_criterion : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (T : X → Y), Measurable T → ∀ c : ℝ,
      μ.map T = ν ↔ ∀ d : Y → ℝ, Measurable d →
        _root_.GD.N0076.N0312.d022661 μ c (d ∘ T) = _root_.GD.N0076.N0312.d022661 ν c d
  kernel_law_criterion : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (κ : Kernel X Y) (c : ℝ),
      κ ∘ₘ μ = ν ↔ ∀ d : Y → ℝ, Measurable d →
        (∫⁻ x, _root_.GD.N0076.N0312.d022661 (κ x) c d ∂μ) = _root_.GD.N0076.N0312.d022661 ν c d
  order_criterion : ∀ (X : Type) [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : ℝ),
      μ = ν ↔ ∀ d e : X → ℝ, Measurable d → Measurable e →
        _root_.GD.N0076.N0312.d022661 μ c d ≤ _root_.GD.N0076.N0312.d022661 μ c e → _root_.GD.N0076.N0312.d022661 ν c d ≤ _root_.GD.N0076.N0312.d022661 ν c e
  observation_permission : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y]
    (T : X → Y) (d : X → ℝ),
      Measurable[(inferInstance : MeasurableSpace Y).comap T] d ↔
        ∃ e : Y → ℝ, Measurable e ∧ d = e ∘ T
  terminal_criterion : ∀ (X Y Θ : Type) [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Θ → Measure X) (ν : Θ → Measure Y) (c : Θ → ℝ)
    (T : X → Y), Measurable T → (∀ θ, (μ θ).map T = ν θ) →
    ∀ b : Y → ℝ, Measurable b →
      (_root_.GD.N0079.N0318.d005274 μ c (b ∘ T) ↔
        _root_.GD.N0079.N0318.d005274 ν c b ∧
          _root_.GD.N0079.N0318.d005276 μ c T b)
  gaussian_deletion : ∀ (k l : ℕ) (n : Fin k → ℕ) (m : Fin l → ℕ)
    (g : Fin l → Fin k), Function.Injective g →
    ∀ j : ∀ i, Fin (m i) → Fin (n (g i)), (∀ i, Function.Injective (j i)) →
    ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      (_root_.GD.N0232.N0719.N0859.d010812 k n θ).map (_root_.GD.N0076.N0312.d022672 g j) = _root_.GD.N0232.N0719.N0859.d010812 l m (_root_.GD.N0076.N0312.d022673 g θ)
  deletion_risk_order : ∀ (k l : ℕ) (n : Fin k → ℕ) (m : Fin l → ℕ)
    (g : Fin l → Fin k), Function.Injective g →
    ∀ j : ∀ i, Fin (m i) → Fin (n (g i)), (∀ i, Function.Injective (j i)) →
    ∀ d e : _root_.GD.N0232.N0719.d009173 l m → ℝ, Measurable d → Measurable e →
      ((∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k n θ (d ∘ _root_.GD.N0076.N0312.d022672 g j) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k n θ (e ∘ _root_.GD.N0076.N0312.d022672 g j)) ↔
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 l m θ d ≤ _root_.GD.N0232.N0719.N0859.d010840 l m θ e))
  deletion_terminality : ∀ (k l : ℕ) (n : Fin k → ℕ) (m : Fin l → ℕ)
    (g : Fin l → Fin k), Function.Injective g →
    ∀ j : ∀ i, Fin (m i) → Fin (n (g i)), (∀ i, Function.Injective (j i)) →
    ∀ b : _root_.GD.N0232.N0719.d009173 l m → ℝ, Measurable b →
      (_root_.GD.N0079.N0318.d005274 (_root_.GD.N0232.N0719.N0859.d010812 k n) _root_.GD.N0232.N0719.N0859.d010809.location (b ∘ _root_.GD.N0076.N0312.d022672 g j) ↔
        _root_.GD.N0079.N0318.d005274 (_root_.GD.N0232.N0719.N0859.d010812 l m) _root_.GD.N0232.N0719.N0859.d010809.location b ∧
          _root_.GD.N0079.N0318.d005276 (_root_.GD.N0232.N0719.N0859.d010812 k n) _root_.GD.N0232.N0719.N0859.d010809.location
            (_root_.GD.N0076.N0312.d022672 g j) b)
  baseline_criterion : ∀ (X Y : Type) (T : X → Y) (bX : X → ℝ) (bY : Y → ℝ),
    bY ∘ T = bX ↔ ∀ x, bY (T x) = bX x
  baseline_deletion_obstruction :
    ¬ ∃ d : _root_.GD.N0232.N0719.d009173 2 (fun _ => 2) → ℝ,
      _root_.GD.N0076.N0310.d014216 2 (fun _ => 3) = d ∘ _root_.GD.N0076.N0312.d022691
  stable_baseline_deletion_obstruction :
    ¬ ∃ d : _root_.GD.N0232.N0719.d009173 2 (fun _ => 2) → ℝ,
      _root_.GD.N0232.N0719.N0859.d010815 2 (fun _ => 3) = d ∘ _root_.GD.N0076.N0312.d022691

theorem d022957 : _root_.GD.N0079.d022956 where
  statistic_law_criterion _ _ _ _ μ ν T hT c := _root_.GD.N0076.N0312.d022664 μ ν T hT c
  kernel_law_criterion _ _ _ _ μ ν κ c := _root_.GD.N0076.N0312.d022666 μ ν κ c
  order_criterion _ _ μ ν _ _ c := _root_.GD.N0076.N0312.d022684 μ ν c
  observation_permission _ _ _ _ T d := _root_.GD.N0076.N0312.d022667 T d
  terminal_criterion _ _ _ _ _ μ ν c T hT hmap b hb :=
    _root_.GD.N0079.N0318.d005280 μ ν c T hT hmap b hb
  gaussian_deletion _ _ _ _ g hg j hj θ := _root_.GD.N0076.N0312.d022676 g hg j hj θ
  deletion_risk_order _ _ _ _ g hg j hj d e hd he := _root_.GD.N0076.N0312.d022679 g hg j hj d e hd he
  deletion_terminality _ _ _ _ g hg j hj b hb := _root_.GD.N0079.d022955 g hg j hj b hb
  baseline_criterion _ _ T bX bY := _root_.GD.N0076.N0312.d022669 T bX bY
  baseline_deletion_obstruction := _root_.GD.N0076.N0312.d022695
  stable_baseline_deletion_obstruction := _root_.GD.N0076.N0312.d022697

end
end GD.N0079

#print axioms _root_.GD.N0079.d022957
#print axioms _root_.GD.N0079.d022954
#print axioms _root_.GD.N0079.d022955
