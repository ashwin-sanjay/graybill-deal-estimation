import GD.Module1471
import GD.Module1465
import GD.Module0538
import GD.Module0464

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace GD.N0213.N0517
noncomputable section
open _root_.GD.N0213.N0523 _root_.GD.N0213.N0522 _root_.GD.N0213.N0495

variable {k : ℕ}

def d023248 (a : Fin k → ℝ) : Prop :=
  ((k : ℝ) - 1 < ∑ i, a i) ∧ ∀ i, ((k : ℝ) - 1) * a i < ∑ j, a j

theorem d023249 [NeZero k] {a : ℝ} (ha : 1 < a) :
    _root_.GD.N0213.N0517.d023248 (fun _ : Fin k => a) := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (NeZero.pos k)
  simp only [_root_.GD.N0213.N0517.d023248, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  constructor
  · nlinarith
  · intro i
    nlinarith

theorem d023250 [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hreg : _root_.GD.N0213.N0517.d023248 a) :
    _root_.GD.N0213.N0523.d023154 a < 1 ∧ (∀ i, 0 < _root_.GD.N0213.N0523.d023155 a i) ∧ ∑ i, _root_.GD.N0213.N0523.d023155 a i = 1 := by
  have h := (_root_.GD.N0213.N0523.d023157 a ha).mpr hreg
  exact ⟨h.1, h.2, _root_.GD.N0213.N0523.d023156 a
    (Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty).ne'⟩

theorem d023251 [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hreg : _root_.GD.N0213.N0517.d023248 a) {L : ℝ} (hL : 0 < L) :
    _root_.GD.N0213.N0522.d008037 (_root_.GD.N0213.N0523.d023155 a) L univ ≠ ⊤ := by
  have h := _root_.GD.N0213.N0517.d023250 a ha hreg
  exact _root_.GD.N0213.N0522.d008039 (_root_.GD.N0213.N0523.d023155 a) h.2.1 h.2.2 hL

theorem d023252 [NeZero k] (a : Fin k → ℝ) (L : ℝ) :
    _root_.GD.N0213.N0522.d008037 (_root_.GD.N0213.N0523.d023155 a) L univ ≠ 0 := by
  rw [ne_eq, _root_.GD.N0213.N0522.d008038]
  exact (lt_of_lt_of_le (_root_.GD.N0213.N0522.d008029 (_root_.GD.N0213.N0523.d023155 a) (NeZero.pos k))
    (measure_mono (subset_univ _))).ne'

theorem d023253 (a : Fin k → ℝ) (s : Set (Fin k → ℝ))
    (hs : MeasurableSet s) :
    Tendsto (fun n : ℕ => _root_.GD.N0213.N0522.d008037 (_root_.GD.N0213.N0523.d023155 a) ((n : ℝ) + 1) s)
      atTop (𝓝 (_root_.GD.N0213.N0522.d008020 (_root_.GD.N0213.N0523.d023155 a) s)) := by
  simp only [_root_.GD.N0213.N0522.d008037, withDensity_apply _ hs]
  exact _root_.GD.N0213.N0489.d007196 (_root_.GD.N0213.N0522.d008020 (_root_.GD.N0213.N0523.d023155 a))
    (fun β => ∑ i, β i) (by fun_prop) s

theorem d023254 [NeZero k] (a : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hreg : _root_.GD.N0213.N0517.d023248 a) :
    Tendsto (fun n : ℕ => ∫ β, (∑ i, β i) *
      _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ i, β i) ^ 2 ∂_root_.GD.N0213.N0522.d008020 (_root_.GD.N0213.N0523.d023155 a)) atTop (𝓝 0) := by
  have h := _root_.GD.N0213.N0517.d023250 a ha hreg
  exact _root_.GD.N0213.N0522.d008041 (_root_.GD.N0213.N0523.d023155 a) h.2.1 h.2.2

theorem d023255 {a ρ t L b : ℝ}
    (ha : 0 < a) (hρ : ρ < 1) (ht : 0 < t) (hL : 0 < L) (hb : 0 ≤ b) :
    (∫ β, β⁻¹ * _root_.GD.N0213.N0495.d007174 L (β + b) ^ 2 ∂gammaMeasure (_root_.GD.N0213.N0523.d023144 a ρ) (a * t)) =
      (t / (1 - ρ)) * (∫ β, _root_.GD.N0213.N0495.d007174 L (β + b) ^ 2
        ∂gammaMeasure (_root_.GD.N0213.N0523.d023144 a ρ) (a * t)) -
      (2 / (a * (1 - ρ))) * (∫ β, _root_.GD.N0213.N0495.d007174 L (β + b) * _root_.GD.N0213.N0495.d007175 L (β + b)
        ∂gammaMeasure (_root_.GD.N0213.N0523.d023144 a ρ) (a * t)) := by
  have h := _root_.GD.N0213.N0520.d023082
    (mul_pos ha (sub_pos.mpr hρ)) (mul_pos ha ht) hL hb
  have hc : a * t / (a * (1 - ρ)) = t / (1 - ρ) := by
    field_simp
  rw [hc] at h
  exact h

end
end GD.N0213.N0517

#print axioms _root_.GD.N0213.N0517.d023249
#print axioms _root_.GD.N0213.N0517.d023250
#print axioms _root_.GD.N0213.N0517.d023251
#print axioms _root_.GD.N0213.N0517.d023252
#print axioms _root_.GD.N0213.N0517.d023253
#print axioms _root_.GD.N0213.N0517.d023254
#print axioms _root_.GD.N0213.N0517.d023255
