import GD.Module0004
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.NormNum

















set_option autoImplicit false
set_option warningAsError true

namespace GD.N0230.N0681

open _root_.GD.N0230.N0556 MeasureTheory

noncomputable section

variable {Θ Ξ Rule : Type*}


def d000472 (risk : Θ → Rule → ℝ) (scale : Θ → ℝ) : Θ → Rule → ℝ :=
  fun θ d => scale θ * risk θ d


def d000473 (risk : Θ → Rule → ℝ) (inclusion : Ξ → Θ) : Ξ → Rule → ℝ :=
  fun ξ d => risk (inclusion ξ) d


theorem d000474
    (risk : Θ → Rule → ℝ) (scale : Θ → ℝ)
    (hscale : ∀ θ, 0 < scale θ) (e d : Rule) :
    _root_.GD.N0230.N0556.d000028 (_root_.GD.N0230.N0681.d000472 risk scale) e d ↔
      _root_.GD.N0230.N0556.d000028 risk e d := by
  constructor
  · intro h θ
    exact (mul_le_mul_iff_right₀ (hscale θ)).mp (h θ)
  · intro h θ
    exact (mul_le_mul_iff_right₀ (hscale θ)).mpr (h θ)


theorem d000475
    (risk : Θ → Rule → ℝ) (scale : Θ → ℝ)
    (hscale : ∀ θ, 0 < scale θ) (θ : Θ) (e d : Rule) :
    _root_.GD.N0230.N0681.d000472 risk scale θ e < _root_.GD.N0230.N0681.d000472 risk scale θ d ↔
      risk θ e < risk θ d :=
  mul_lt_mul_iff_right₀ (hscale θ)


theorem d000476
    (risk : Θ → Rule → ℝ) (scale : Θ → ℝ)
    (hscale : ∀ θ, 0 < scale θ) (e d : Rule) :
    _root_.GD.N0230.N0556.d000029 (_root_.GD.N0230.N0681.d000472 risk scale) e d ↔
      _root_.GD.N0230.N0556.d000029 risk e d := by
  constructor
  · rintro ⟨hweak, θ, hstrict⟩
    exact ⟨(_root_.GD.N0230.N0681.d000474 risk scale hscale e d).mp hweak,
      θ, (_root_.GD.N0230.N0681.d000475 risk scale hscale θ e d).mp hstrict⟩
  · rintro ⟨hweak, θ, hstrict⟩
    exact ⟨(_root_.GD.N0230.N0681.d000474 risk scale hscale e d).mpr hweak,
      θ, (_root_.GD.N0230.N0681.d000475 risk scale hscale θ e d).mpr hstrict⟩


theorem d000477
    (risk : Θ → Rule → ℝ) (scale : Θ → ℝ)
    (hscale : ∀ θ, 0 < scale θ) (d : Rule) :
    _root_.GD.N0230.N0556.d000031 (_root_.GD.N0230.N0681.d000472 risk scale) d ↔ _root_.GD.N0230.N0556.d000031 risk d := by
  simp only [_root_.GD.N0230.N0556.d000031, _root_.GD.N0230.N0681.d000476 risk scale hscale]


theorem d000478
    (risk : Θ → Rule → ℝ) (inclusion : Ξ → Θ) {e d : Rule}
    (hweak : _root_.GD.N0230.N0556.d000028 risk e d) :
    _root_.GD.N0230.N0556.d000028 (_root_.GD.N0230.N0681.d000473 risk inclusion) e d := by
  intro ξ
  exact hweak (inclusion ξ)


theorem d000479
    (risk : Θ → Rule → ℝ) (inclusion : Ξ → Θ) {e d : Rule}
    (hweak : _root_.GD.N0230.N0556.d000028 risk e d) :
    _root_.GD.N0230.N0556.d000029 (_root_.GD.N0230.N0681.d000473 risk inclusion) e d ↔
      ∃ ξ, risk (inclusion ξ) e < risk (inclusion ξ) d := by
  constructor
  · exact fun h => h.2
  · intro hstrict
    exact ⟨_root_.GD.N0230.N0681.d000478 risk inclusion hweak, hstrict⟩


theorem d000480
    (risk : Θ → Rule → ℝ) (submodel : Set Θ) {e d : Rule}
    (hweak : _root_.GD.N0230.N0556.d000028 risk e d) :
    _root_.GD.N0230.N0556.d000029 (_root_.GD.N0230.N0681.d000473 risk (Subtype.val : submodel → Θ)) e d ↔
      ∃ θ ∈ submodel, risk θ e < risk θ d := by
  rw [_root_.GD.N0230.N0681.d000479 risk Subtype.val hweak]
  constructor
  · rintro ⟨⟨θ, hθ⟩, hstrict⟩
    exact ⟨θ, hθ, hstrict⟩
  · rintro ⟨θ, hθ, hstrict⟩
    exact ⟨⟨θ, hθ⟩, hstrict⟩




def d000481 (target action : Bool → ℝ) (θ d : Bool) : ℝ :=
  ∫ _ : Unit, (action d - target θ) ^ 2 ∂Measure.dirac ()

theorem d000482 (target action : Bool → ℝ) (θ d : Bool) :
    _root_.GD.N0230.N0681.d000481 target action θ d = (action d - target θ) ^ 2 := by
  simp [_root_.GD.N0230.N0681.d000481]


theorem d000483 : IsProbabilityMeasure (Measure.dirac ()) :=
  inferInstance


def d000484 (risk : Bool → Bool → ℝ) (d : Bool) : ℝ :=
  max (risk false d) (risk true d)

theorem d000485 (risk : Bool → Bool → ℝ) (d : Bool) (bound : ℝ) :
    _root_.GD.N0230.N0681.d000484 risk d ≤ bound ↔ ∀ θ, risk θ d ≤ bound := by
  constructor
  · intro h θ
    cases θ
    · exact (le_max_left _ _).trans h
    · exact (le_max_right _ _).trans h
  · intro h
    exact max_le (h false) (h true)


def d000486 (risk : Bool → Bool → ℝ) (d : Bool) : Prop :=
  ∀ e, _root_.GD.N0230.N0681.d000484 risk d ≤ _root_.GD.N0230.N0681.d000484 risk e


def d000487 : Bool → Bool → ℝ :=
  _root_.GD.N0230.N0681.d000481 (fun θ => if θ then 2 else 0) (fun d => if d then 1 else 0)


def d000488 (θ : Bool) : ℝ := if θ then 1 else 9

theorem d000489 (θ : Bool) : 0 < _root_.GD.N0230.N0681.d000488 θ := by
  cases θ <;> norm_num [_root_.GD.N0230.N0681.d000488]


theorem d000490 :
    _root_.GD.N0230.N0681.d000484 _root_.GD.N0230.N0681.d000487 true < _root_.GD.N0230.N0681.d000484 _root_.GD.N0230.N0681.d000487 false ∧
      _root_.GD.N0230.N0681.d000484 (_root_.GD.N0230.N0681.d000472 _root_.GD.N0230.N0681.d000487 _root_.GD.N0230.N0681.d000488) false <
        _root_.GD.N0230.N0681.d000484 (_root_.GD.N0230.N0681.d000472 _root_.GD.N0230.N0681.d000487 _root_.GD.N0230.N0681.d000488) true := by
  norm_num [_root_.GD.N0230.N0681.d000484, _root_.GD.N0230.N0681.d000487, _root_.GD.N0230.N0681.d000482, _root_.GD.N0230.N0681.d000472, _root_.GD.N0230.N0681.d000488]


theorem d000491 :
    (_root_.GD.N0230.N0681.d000486 _root_.GD.N0230.N0681.d000487 true ∧ ¬ _root_.GD.N0230.N0681.d000486 _root_.GD.N0230.N0681.d000487 false) ∧
      (_root_.GD.N0230.N0681.d000486 (_root_.GD.N0230.N0681.d000472 _root_.GD.N0230.N0681.d000487 _root_.GD.N0230.N0681.d000488) false ∧
        ¬ _root_.GD.N0230.N0681.d000486 (_root_.GD.N0230.N0681.d000472 _root_.GD.N0230.N0681.d000487 _root_.GD.N0230.N0681.d000488) true) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro d
    cases d <;> norm_num [_root_.GD.N0230.N0681.d000484, _root_.GD.N0230.N0681.d000487, _root_.GD.N0230.N0681.d000482]
  · intro h
    exact (not_le_of_gt _root_.GD.N0230.N0681.d000490.1) (h true)
  · intro d
    cases d <;>
      norm_num [_root_.GD.N0230.N0681.d000484, _root_.GD.N0230.N0681.d000487, _root_.GD.N0230.N0681.d000482, _root_.GD.N0230.N0681.d000472, _root_.GD.N0230.N0681.d000488]
  · intro h
    exact (not_le_of_gt _root_.GD.N0230.N0681.d000490.2) (h false)


theorem d000492 : _root_.GD.N0230.N0556.d000031 _root_.GD.N0230.N0681.d000487 false := by
  rintro ⟨e, hweak, θ, hstrict⟩
  cases e
  · exact (lt_irrefl _) hstrict
  · have h := hweak false
    norm_num [_root_.GD.N0230.N0681.d000487, _root_.GD.N0230.N0681.d000482] at h


theorem d000493 :
    _root_.GD.N0230.N0556.d000029 (_root_.GD.N0230.N0681.d000473 _root_.GD.N0230.N0681.d000487 (fun _ : Unit => true)) true false := by
  constructor
  · intro ξ
    norm_num [_root_.GD.N0230.N0681.d000473, _root_.GD.N0230.N0681.d000487, _root_.GD.N0230.N0681.d000482]
  · exact ⟨(), by norm_num [_root_.GD.N0230.N0681.d000473, _root_.GD.N0230.N0681.d000487, _root_.GD.N0230.N0681.d000482]⟩


theorem d000494 :
    _root_.GD.N0230.N0556.d000031 _root_.GD.N0230.N0681.d000487 false ∧
      ¬ _root_.GD.N0230.N0556.d000031 (_root_.GD.N0230.N0681.d000473 _root_.GD.N0230.N0681.d000487 (fun _ : Unit => true)) false := by
  exact ⟨_root_.GD.N0230.N0681.d000492, fun h => h ⟨true, _root_.GD.N0230.N0681.d000493⟩⟩


def d000495 : Bool → Bool → ℝ :=
  _root_.GD.N0230.N0681.d000481 (fun θ => if θ then 1 else 0) (fun d => if d then 2 else 0)


theorem d000496 :
    _root_.GD.N0230.N0556.d000029 _root_.GD.N0230.N0681.d000495 false true := by
  constructor
  · intro θ
    cases θ <;> norm_num [_root_.GD.N0230.N0681.d000495, _root_.GD.N0230.N0681.d000482]
  · exact ⟨false, by norm_num [_root_.GD.N0230.N0681.d000495, _root_.GD.N0230.N0681.d000482]⟩


theorem d000497 :
    _root_.GD.N0230.N0556.d000031 (_root_.GD.N0230.N0681.d000473 _root_.GD.N0230.N0681.d000495 (fun _ : Unit => true)) true := by
  rintro ⟨e, _, ξ, hstrict⟩
  cases e <;> norm_num [_root_.GD.N0230.N0681.d000473, _root_.GD.N0230.N0681.d000495, _root_.GD.N0230.N0681.d000482] at hstrict


theorem d000498 :
    _root_.GD.N0230.N0556.d000031 (_root_.GD.N0230.N0681.d000473 _root_.GD.N0230.N0681.d000495 (fun _ : Unit => true)) true ∧
      ¬ _root_.GD.N0230.N0556.d000031 _root_.GD.N0230.N0681.d000495 true := by
  exact ⟨_root_.GD.N0230.N0681.d000497,
    fun h => h ⟨false, _root_.GD.N0230.N0681.d000496⟩⟩


theorem d000499 :
    _root_.GD.N0230.N0556.d000029 _root_.GD.N0230.N0681.d000495 false true ∧
      _root_.GD.N0230.N0556.d000028 (_root_.GD.N0230.N0681.d000473 _root_.GD.N0230.N0681.d000495 (fun _ : Unit => true)) false true ∧
      ¬ _root_.GD.N0230.N0556.d000029 (_root_.GD.N0230.N0681.d000473 _root_.GD.N0230.N0681.d000495 (fun _ : Unit => true)) false true := by
  refine ⟨_root_.GD.N0230.N0681.d000496,
    _root_.GD.N0230.N0681.d000478 _ _ _root_.GD.N0230.N0681.d000496.1, ?_⟩
  exact fun h => _root_.GD.N0230.N0681.d000497 ⟨false, h⟩

end

end GD.N0230.N0681

#print axioms _root_.GD.N0230.N0681.d000474
#print axioms _root_.GD.N0230.N0681.d000476
#print axioms _root_.GD.N0230.N0681.d000477
#print axioms _root_.GD.N0230.N0681.d000478
#print axioms _root_.GD.N0230.N0681.d000479
#print axioms _root_.GD.N0230.N0681.d000480
#print axioms _root_.GD.N0230.N0681.d000482
#print axioms _root_.GD.N0230.N0681.d000483
#print axioms _root_.GD.N0230.N0681.d000491
#print axioms _root_.GD.N0230.N0681.d000494
#print axioms _root_.GD.N0230.N0681.d000498
#print axioms _root_.GD.N0230.N0681.d000499
