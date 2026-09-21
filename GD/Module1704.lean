import GD.Module1696







set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0413
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0072 _root_.GD.N0021 _root_.GD.N0101.N0357
open _root_.GD.N0101.N0411

variable {k : ℕ}

def d028605 (w : (Fin k → ℝ) → Fin k → ℝ) :
    (Fin k → ℝ) → Fin k → ℝ := by
  classical
  exact fun t => if t ∈ _root_.GD.N0101.N0357.d023158 then w t else _root_.GD.N0021.d023313 t

theorem d028606 (w : (Fin k → ℝ) → Fin k → ℝ)
    (hw : Measurable w) : Measurable (_root_.GD.N0101.N0413.d028605 w) := by
  classical
  exact hw.ite _root_.GD.N0101.N0357.d023159 _root_.GD.N0021.d023314

theorem d028607 (hk : 0 < k)
    (w : (Fin k → ℝ) → Fin k → ℝ)
    (hunit : ∀ t ∈ _root_.GD.N0101.N0357.d023158, ∑ i, w t i = 1) :
    ∀ t, ∑ i, _root_.GD.N0101.N0413.d028605 w t i = 1 := by
  intro t
  by_cases ht : t ∈ _root_.GD.N0101.N0357.d023158
  · simpa only [_root_.GD.N0101.N0413.d028605, if_pos ht] using hunit t ht
  · simpa only [_root_.GD.N0101.N0413.d028605, if_neg ht] using _root_.GD.N0101.N0411.d028560 hk t



theorem d028608 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0101.N0413.d028605 w =ᵐ[_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale] w := by
  filter_upwards [_root_.GD.N0232.N0719.N0910.d010288 hn θ.scale_pos] with t ht
  exact if_pos ht

theorem d028609
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0072.d023291 sizes (_root_.GD.N0101.N0413.d028605 w) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
      _root_.GD.N0072.d023291 sizes w := by
  have hmap : _root_.GD.N0101.N0413.d028605 w =ᵐ[(_root_.GD.N0232.N0719.N0859.d010812 k sizes θ).map
      (_root_.GD.N0232.N0719.N0900.d009103 k sizes)] w := by
    rw [_root_.GD.N0072.d023301 sizes hn θ]
    exact _root_.GD.N0101.N0413.d028608 sizes hn w θ
  have hraw := ae_of_ae_map
    (measurable_pi_iff.mpr
      (_root_.GD.N0232.N0719.N0900.d009114 k sizes)).aemeasurable hmap
  filter_upwards [hraw] with z hz
  simp only [_root_.GD.N0072.d023291, hz]


theorem d028610 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes (_root_.GD.N0101.N0413.d028605 w)) =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) :=
  _root_.GD.N0232.N0719.N0896.d011094 k sizes θ
    (_root_.GD.N0101.N0413.d028609 sizes hn w θ)

theorem d028611 (hk : 0 < k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t ∈ _root_.GD.N0101.N0357.d023158, ∑ i, w t i = 1) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) =
      ∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621
        (fun i => θ.scale i ^ 2 / (sizes i : ℝ)) (w t))
        ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale := by
  rw [← _root_.GD.N0101.N0413.d028610 sizes hn w θ,
    _root_.GD.N0072.d023297 sizes hn (_root_.GD.N0101.N0413.d028605 w)
      (_root_.GD.N0101.N0413.d028606 w hw) (_root_.GD.N0101.N0413.d028607 hk w hunit)]
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0101.N0413.d028608 sizes hn w θ] with t ht
  rw [ht]



theorem d028612 (hk : 0 < k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hadm : ¬ ∃ w : (Fin k → ℝ) → Fin k → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d) :
    ¬ ∃ w : (Fin k → ℝ) → Fin k → ℝ,
      Measurable w ∧ (∀ t ∈ _root_.GD.N0101.N0357.d023158, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d := by
  rintro ⟨w, hw, hunit, hweak, θ, hstrict⟩
  apply hadm
  refine ⟨_root_.GD.N0101.N0413.d028605 w, _root_.GD.N0101.N0413.d028606 w hw,
    _root_.GD.N0101.N0413.d028607 hk w hunit, ?_, θ, ?_⟩
  · intro η
    simpa only [_root_.GD.N0101.N0413.d028610 sizes hn w η] using hweak η
  · simpa only [_root_.GD.N0101.N0413.d028610 sizes hn w θ] using hstrict



theorem d028613 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 3 ≤ sizes i)
    (ρ : ℝ) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i)
    (hsum : ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1) :
    ¬ ∃ w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ,
      Measurable w ∧ (∀ t ∈ _root_.GD.N0101.N0357.d023158, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes) :=
  _root_.GD.N0101.N0413.d028612 (Nat.succ_pos _) sizes
    (fun i => by have := hn i; omega) _
    (_root_.GD.N0101.N0411.d028565 sizes hn ρ hρ hα hsum)

end
end GD.N0101.N0413

#print axioms _root_.GD.N0101.N0413.d028606
#print axioms _root_.GD.N0101.N0413.d028607
#print axioms _root_.GD.N0101.N0413.d028608
#print axioms _root_.GD.N0101.N0413.d028609
#print axioms _root_.GD.N0101.N0413.d028610
#print axioms _root_.GD.N0101.N0413.d028611
#print axioms _root_.GD.N0101.N0413.d028612
#print axioms _root_.GD.N0101.N0413.d028613
