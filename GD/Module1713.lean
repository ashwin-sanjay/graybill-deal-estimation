import GD.Module1698
import GD.Module1501

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0224.N0534
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0072 _root_.GD.N0021
open _root_.GD.N0225.N0538
open _root_.GD.N0101.N0411
open _root_.GD.N0213.N0485
open _root_.GD.N0213.N0486

variable {k : ℕ}

theorem d028677 (sizes : Fin k → ℕ) (hk : 0 < k)
    (hn : ∀ i, 2 ≤ sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ∧
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≠ ⊤ := by
  have hg := _root_.GD.N0101.N0411.d028560 hk
  have hfinite := _root_.GD.N0225.N0538.d023463 sizes hn _root_.GD.N0021.d023313 _root_.GD.N0021.d023314
    hg (_root_.GD.N0101.N0411.d028561 hk)
  rw [_root_.GD.N0021.d023315]
  refine ⟨?_, hfinite.2 θ⟩
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale) :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hn _
  rw [_root_.GD.N0072.d023297 sizes hn _root_.GD.N0021.d023313 _root_.GD.N0021.d023314 hg]
  have hmeas : Measurable (fun t : Fin k → ℝ => ENNReal.ofReal
      (_root_.GD.N0072.d007621 (fun i => θ.scale i ^ 2 / (sizes i : ℝ)) (_root_.GD.N0021.d023313 t))) :=
    ((_root_.GD.N0072.d007626 (fun i : Fin k => θ.scale i ^ 2 / (sizes i : ℝ))).comp
      _root_.GD.N0021.d023314).ennreal_ofReal
  rw [lintegral_pos_iff_support hmeas]
  have he (t : Fin k → ℝ) :
      0 < _root_.GD.N0072.d007621 (fun i => θ.scale i ^ 2 / (sizes i : ℝ)) (_root_.GD.N0021.d023313 t) := by
    have hnz : ∃ i, _root_.GD.N0021.d023313 t i ≠ 0 := by
      by_contra h
      push Not at h
      have hu := hg t
      simp only [h, Finset.sum_const_zero] at hu
      norm_num at hu
    obtain ⟨i, hi⟩ := hnz
    unfold _root_.GD.N0072.d007621
    apply Finset.sum_pos'
    · intro j _
      positivity
    · exact ⟨i, Finset.mem_univ _, mul_pos (sq_pos_of_ne_zero hi)
        (div_pos (sq_pos_of_pos (θ.scale_pos i)) (Nat.cast_pos.mpr (by have := hn i; omega)))⟩
  have hs : Function.support (fun t => ENNReal.ofReal
      (_root_.GD.N0072.d007621 (fun i => θ.scale i ^ 2 / (sizes i : ℝ)) (_root_.GD.N0021.d023313 t))) = univ := by
    ext t
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (he t)).ne'
  rw [hs]
  simp

theorem d028678
    (sizes : Fin k → ℕ) (hk : 0 < k) (hn : ∀ i, 2 ≤ sizes i)
    (hadm : _root_.GD.N0213.N0485.d028566 sizes)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) (c : ℝ≥0∞)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      c * _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes)) :
    1 ≤ c := by
  by_contra hc
  have hc1 : c < 1 := lt_of_not_ge hc
  have hweak (θ) : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) := by
    have hh := mul_le_mul_left hc1.le
      (_root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes))
    simpa only [one_mul] using (hcap θ).trans hh
  have hb := _root_.GD.N0224.N0534.d028677 sizes hk hn (_root_.GD.N0232.N0719.N0859.d010810 k)
  have hstrict := (hcap (_root_.GD.N0232.N0719.N0859.d010810 k)).trans_lt
    (by simpa only [one_mul] using ENNReal.mul_lt_mul_left hb.1.ne' hb.2 hc1)
  exact hadm ⟨w, hw, hunit, hweak, _root_.GD.N0232.N0719.N0859.d010810 k, hstrict⟩

theorem d028679
    (sizes : Fin k → ℕ) (hk : 0 < k) (hn : ∀ i, 2 ≤ sizes i)
    (hadm : _root_.GD.N0213.N0485.d028566 sizes) (c : ℝ≥0∞) :
    (∃ w : (Fin k → ℝ) → Fin k → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        c * _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes)) ↔ 1 ≤ c := by
  constructor
  · rintro ⟨w, hw, hu, hc⟩
    exact _root_.GD.N0224.N0534.d028678 sizes hk hn hadm w hw hu c hc
  · intro hc
    refine ⟨_root_.GD.N0021.d023313, _root_.GD.N0021.d023314, _root_.GD.N0101.N0411.d028560 hk, ?_⟩
    intro θ
    rw [← _root_.GD.N0021.d023315]
    simpa only [one_mul] using mul_le_mul_left hc
      (_root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes))

theorem d028680 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hcone : _root_.GD.N0213.N0486.d028577 sizes) (c : ℝ≥0∞) :
    (∃ w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        c * _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) sizes)) ↔ 1 ≤ c :=
  _root_.GD.N0224.N0534.d028679 sizes (Nat.succ_pos _) hn
    (_root_.GD.N0213.N0486.d028581 sizes hn hcone) c

end
end GD.N0224.N0534

#print axioms _root_.GD.N0224.N0534.d028677
#print axioms _root_.GD.N0224.N0534.d028678
#print axioms _root_.GD.N0224.N0534.d028679
#print axioms _root_.GD.N0224.N0534.d028680
