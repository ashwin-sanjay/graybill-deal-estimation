import GD.Module0344
import GD.Module1844

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0024.N0274

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1220
open _root_.GD.N0046.N0305
open _root_.GD.N0034.N0289

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d030341 (θ : _root_.GD.N0232.N0720.N1080.d014168) : ℝ := (_root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).toReal

theorem d030342 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    ENNReal.ofReal (_root_.GD.N0024.N0274.d030341 m n hm hn θ) = _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  apply ENNReal.ofReal_toReal
  rw [_root_.GD.N0232.N0720.N1080.d014184]
  exact ENNReal.ofReal_ne_top

theorem d030343 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0034.N0289.d030220 m n hm hn θ = min (_root_.GD.N0024.N0274.d030341 m n hm hn θ) (v * _root_.GD.N0232.N0720.N1257.d015508 m n θ) := by
  have hβ : 0 ≤ _root_.GD.N0024.N0274.d030341 m n hm hn θ := ENNReal.toReal_nonneg
  have hτ : 0 ≤ v * _root_.GD.N0232.N0720.N1257.d015508 m n θ := mul_nonneg hv (_root_.GD.N0232.N0720.N1257.d015509 m n θ)
  unfold _root_.GD.N0034.N0289.d030220
  rw [hvalue, ← ENNReal.ofReal_mul hv, ← _root_.GD.N0024.N0274.d030342 m n hm hn θ,
    ← ENNReal.ofReal_min, ENNReal.toReal_ofReal (le_min hτ hβ), min_comm]

def d030344 (a : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) : ℝ :=
  a _root_.GD.N0232.N0720.N1080.d014169 + ∑ θ ∈ F, w θ * a θ

def d030345 (v : ℝ) (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) : ℝ :=
  _root_.GD.N0024.N0274.d030344 (fun θ => max (v * _root_.GD.N0232.N0720.N1257.d015508 m n θ - _root_.GD.N0024.N0274.d030341 m n hm hn θ) 0) F w

def d030346 (v : ℝ) (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) : ℝ :=
  v * _root_.GD.N0232.N0720.N1220.d017307 m n F w - _root_.GD.N0232.N0720.N1220.d017301 m n F w

theorem d030347 (v : ℝ) (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ) : 0 ≤ _root_.GD.N0024.N0274.d030345 m n hm hn v F w := by
  exact add_nonneg (le_max_right _ _) (Finset.sum_nonneg fun θ hθ =>
    mul_nonneg (hw θ hθ) (le_max_right _ _))

include hm hn in
theorem d030348 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ) :
    0 ≤ _root_.GD.N0024.N0274.d030346 m n v F w := by
  exact sub_nonneg.mpr ((_root_.GD.N0232.N0720.N1220.d017309 m n hm hn v hv).mp
    (le_of_eq hvalue) F w hw)

theorem d030349 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) :
    _root_.GD.N0232.N0720.N1220.d017301 m n F w - _root_.GD.N0024.N0274.d030344 (_root_.GD.N0034.N0289.d030220 m n hm hn) F w =
      _root_.GD.N0024.N0274.d030345 m n hm hn v F w - _root_.GD.N0024.N0274.d030346 m n v F w := by
  simp only [_root_.GD.N0024.N0274.d030344, _root_.GD.N0024.N0274.d030343 m n hm hn v hv hvalue,
    _root_.GD.N0024.N0265.d005121, mul_sub, Finset.sum_sub_distrib,
    _root_.GD.N0024.N0274.d030345, _root_.GD.N0024.N0274.d030346, _root_.GD.N0232.N0720.N1220.d017307, mul_add, Finset.mul_sum, mul_left_comm v]
  ring

theorem d030350 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v) :
    (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty ↔
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0024.N0274.d030345 m n hm hn v F w ≤ _root_.GD.N0024.N0274.d030346 m n v F w := by
  rw [_root_.GD.N0034.N0289.d030225]
  constructor
  · intro h F w hw
    have hb := h F w hw
    have hi := _root_.GD.N0024.N0274.d030349 m n hm hn v hv hvalue F w
    change _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤ _root_.GD.N0024.N0274.d030344 (_root_.GD.N0034.N0289.d030220 m n hm hn) F w at hb
    linarith
  · intro h F w hw
    have hb := h F w hw
    have hi := _root_.GD.N0024.N0274.d030349 m n hm hn v hv hvalue F w
    change _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤ _root_.GD.N0024.N0274.d030344 (_root_.GD.N0034.N0289.d030220 m n hm hn) F w
    linarith

theorem d030351 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v) :
    (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty ↔
      ∃ ε : ℝ, 0 < ε ∧
        ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
          _root_.GD.N0024.N0274.d030345 m n hm hn v F w + ε ≤ _root_.GD.N0024.N0274.d030346 m n v F w := by
  rw [_root_.GD.N0034.N0289.d030225,
    _root_.GD.N0034.N0288.d030333]
  constructor
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, fun F w hw => ?_⟩
    have hb := h F w hw
    have hi := _root_.GD.N0024.N0274.d030349 m n hm hn v hv hvalue F w
    change _root_.GD.N0232.N0720.N1220.d017301 m n F w + ε ≤ _root_.GD.N0024.N0274.d030344 (_root_.GD.N0034.N0289.d030220 m n hm hn) F w at hb
    linarith
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, fun F w hw => ?_⟩
    have hb := h F w hw
    have hi := _root_.GD.N0024.N0274.d030349 m n hm hn v hv hvalue F w
    change _root_.GD.N0232.N0720.N1220.d017301 m n F w + ε ≤ _root_.GD.N0024.N0274.d030344 (_root_.GD.N0034.N0289.d030220 m n hm hn) F w
    linarith

theorem d030352 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) ∧
        _root_.GD.N0024.N0274.d030346 m n v F w < _root_.GD.N0024.N0274.d030345 m n hm hn v F w + ε) :
    _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  intro hK
  obtain ⟨ε, hε, hbound⟩ :=
    (_root_.GD.N0024.N0274.d030351 m n hm hn v hv hvalue).mp hK
  obtain ⟨F, w, hw, hlt⟩ := hsmall ε hε
  exact (not_le.mpr hlt) (hbound F w hw)

theorem d030353 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v)
    (hK : (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ) :
    _root_.GD.N0024.N0274.d030345 m n hm hn v F w / _root_.GD.N0232.N0720.N1220.d017307 m n F w ≤
      v - _root_.GD.N0232.N0720.N1220.d017301 m n F w / _root_.GD.N0232.N0720.N1220.d017307 m n F w := by
  have h := (_root_.GD.N0024.N0274.d030350 m n hm hn v hv hvalue).mp hK F w hw
  have ht := _root_.GD.N0232.N0720.N1220.d017308 m n hm F w hw
  have hd := div_le_div_of_nonneg_right h ht.le
  unfold _root_.GD.N0024.N0274.d030346 at hd
  rwa [sub_div, mul_div_cancel_right₀ _ ht.ne'] at hd

theorem d030354 (v δ : ℝ) (hv : 0 ≤ v) (_hδ : 0 < δ)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v)
    (hK : (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty)
    (F A : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ) (hAF : A ⊆ F)
    (hactive : ∀ θ ∈ A,
      _root_.GD.N0024.N0274.d030341 m n hm hn θ ≤ (v - δ) * _root_.GD.N0232.N0720.N1257.d015508 m n θ) :
    δ * (∑ θ ∈ A, w θ * _root_.GD.N0232.N0720.N1257.d015508 m n θ) ≤ _root_.GD.N0024.N0274.d030346 m n v F w := by
  have hpoint : ∀ θ ∈ A, δ * _root_.GD.N0232.N0720.N1257.d015508 m n θ ≤
      max (v * _root_.GD.N0232.N0720.N1257.d015508 m n θ - _root_.GD.N0024.N0274.d030341 m n hm hn θ) 0 := by
    intro θ hθ
    have hb := hactive θ hθ
    have hm := le_max_left (v * _root_.GD.N0232.N0720.N1257.d015508 m n θ - _root_.GD.N0024.N0274.d030341 m n hm hn θ) 0
    nlinarith
  have hsum : δ * (∑ θ ∈ A, w θ * _root_.GD.N0232.N0720.N1257.d015508 m n θ) ≤
      ∑ θ ∈ F, w θ * max (v * _root_.GD.N0232.N0720.N1257.d015508 m n θ - _root_.GD.N0024.N0274.d030341 m n hm hn θ) 0 := by
    calc
      _ = ∑ θ ∈ A, w θ * (δ * _root_.GD.N0232.N0720.N1257.d015508 m n θ) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro θ _
        ring
      _ ≤ ∑ θ ∈ A, w θ * max (v * _root_.GD.N0232.N0720.N1257.d015508 m n θ - _root_.GD.N0024.N0274.d030341 m n hm hn θ) 0 :=
        Finset.sum_le_sum fun θ hθ =>
          mul_le_mul_of_nonneg_left (hpoint θ hθ) (hw θ (hAF hθ))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hAF
        (fun θ hθ _ => mul_nonneg (hw θ hθ) (le_max_right _ _))
  have hdebt := (_root_.GD.N0024.N0274.d030350 m n hm hn v hv hvalue).mp hK F w hw
  have hanchor : 0 ≤ max (v * _root_.GD.N0232.N0720.N1257.d015508 m n _root_.GD.N0232.N0720.N1080.d014169 -
      _root_.GD.N0024.N0274.d030341 m n hm hn _root_.GD.N0232.N0720.N1080.d014169) 0 := le_max_right _ _
  unfold _root_.GD.N0024.N0274.d030345 _root_.GD.N0024.N0274.d030344 at hdebt
  linarith

end
end GD.N0024.N0274

#print axioms _root_.GD.N0024.N0274.d030343
#print axioms _root_.GD.N0024.N0274.d030349
#print axioms _root_.GD.N0024.N0274.d030350
#print axioms _root_.GD.N0024.N0274.d030351
#print axioms _root_.GD.N0024.N0274.d030352
#print axioms _root_.GD.N0024.N0274.d030353
#print axioms _root_.GD.N0024.N0274.d030354
