import GD.Module1750

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped ENNReal

namespace GD.N0003.N0240

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0842 _root_.GD.N0232.N0719.N0946
open _root_.GD.N0097 _root_.GD.N0226
open _root_.GD.N0232.N0719.N0970 _root_.GD.N0232.N0719.N0962

noncomputable section

variable {k : ℕ} (sizes : Fin k → ℕ)

theorem d029022 (s t : ℝ)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :
    _root_.GD.N0226.d028194 sizes s (_root_.GD.N0097.d028164 sizes t f) =
      _root_.GD.N0097.d028164 sizes (Real.exp s * t) (_root_.GD.N0226.d028194 sizes s f) := by
  unfold _root_.GD.N0226.d028194 _root_.GD.N0097.d028164
  rw [_root_.GD.N0232.N0719.N0842.d010916 k sizes 0 (Real.exp s) t 1 (Real.exp_ne_zero s) one_ne_zero,
    _root_.GD.N0232.N0719.N0842.d010916 k sizes (Real.exp s * t) 1 0 (Real.exp s)
      one_ne_zero (Real.exp_ne_zero s)]
  simp only [zero_add, mul_one, one_mul, mul_zero, add_zero]


theorem d029023
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    {s t : ℝ} (hs : s ∈ _root_.GD.N0226.d028198 sizes f)
    (ht : t ∈ _root_.GD.N0097.d028168 sizes f) :
    Real.exp s * t ∈ _root_.GD.N0097.d028168 sizes f := by
  change _root_.GD.N0097.d028164 sizes (Real.exp s * t) f =ᵐ[_] f
  have h := _root_.GD.N0226.d028197 sizes s ht
  rw [_root_.GD.N0003.N0240.d029022] at h
  exact (_root_.GD.N0097.d028167 sizes (Real.exp s * t) hs).symm.trans (h.trans hs)



theorem d029024
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hs : ∀ s : ℝ, s ∈ _root_.GD.N0226.d028198 sizes f)
    {t : ℝ} (ht : t ∈ _root_.GD.N0097.d028168 sizes f) (hne : t ≠ 0) :
    ∀ a : ℝ, a ∈ _root_.GD.N0097.d028168 sizes f := by
  obtain ⟨p, hp, hpf⟩ : ∃ p : ℝ, 0 < p ∧ p ∈ _root_.GD.N0097.d028168 sizes f := by
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact ⟨-t, neg_pos.mpr hneg, (_root_.GD.N0097.d028168 sizes f).neg_mem ht⟩
    · exact ⟨t, hpos, ht⟩
  have hpositive (a : ℝ) (ha : 0 < a) : a ∈ _root_.GD.N0097.d028168 sizes f := by
    have h := _root_.GD.N0003.N0240.d029023 sizes f (hs (Real.log (a / p))) hpf
    rwa [Real.exp_log (div_pos ha hp), div_mul_cancel₀ _ (ne_of_gt hp)] at h
  intro a
  rcases lt_trichotomy a 0 with hneg | rfl | hpos
  · simpa only [neg_neg] using
      (_root_.GD.N0097.d028168 sizes f).neg_mem (hpositive (-a) (neg_pos.mpr hneg))
  · exact (_root_.GD.N0097.d028168 sizes f).zero_mem
  · exact hpositive a hpos

local instance d029025 : IsProbabilityMeasure
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010813 _root_.GD.N0232.N0719.d009182
  infer_instance



theorem d029026
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : Measurable f) (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f)
    (hstrict : _root_.GD.N0232.N0719.N0970.d012310 k sizes f)
    (hscale : ∀ s : ℝ, s ∈ _root_.GD.N0226.d028198 sizes f) :
    _root_.GD.N0097.d028168 sizes f = ⊥ := by
  apply le_antisymm
  · intro t htf
    change t = 0
    by_contra hne
    have hall := _root_.GD.N0003.N0240.d029024 sizes f hscale htf hne
    have hcov (a : _root_.GD.N0232.N0719.N0946.d009229) :
        (fun z => f (a • z)) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
          fun z => a • f z := by
      have hshift := (_root_.GD.N0097.d028175 sizes f a.shift).mp (hall a.shift)
      have hpull := (_root_.GD.N0232.N0719.N0896.d011119
        k sizes 0 (Real.exp a.logScale) (Real.exp_pos a.logScale)).ae_eq hshift
      have hsc := _root_.GD.N0226.d029008 sizes f (hscale a.logScale)
      filter_upwards [hpull, hsc] with z hz hs
      change f (fun i j => a.shift + Real.exp a.logScale * z i j) =
        a.shift + Real.exp a.logScale * f z
      have he : _root_.GD.N0232.N0719.N0900.d009095 k sizes 0 (Real.exp a.logScale) z =
          (fun i j => Real.exp a.logScale * z i j) := by
        ext i j
        exact zero_add _
      change f (fun i j => a.shift +
        _root_.GD.N0232.N0719.N0900.d009095 k sizes 0 (Real.exp a.logScale) z i j) =
        a.shift + f (_root_.GD.N0232.N0719.N0900.d009095 k sizes 0 (Real.exp a.logScale) z) at hz
      rw [he] at hz
      exact hz.trans (congrArg (a.shift + ·) hs)
    obtain ⟨g, hg, hgf, hge⟩ :=
      _root_.GD.N0232.N0719.N0946.d009261
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (by omega) (fun i => by have := hn i; omega) f hf hcov
    have hgfθ (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : g =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f :=
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hgf
    have hrisk (θ : _root_.GD.N0232.N0719.N0859.d010809 k) := _root_.GD.N0232.N0719.N0896.d011094 k sizes θ (hgfθ θ)
    apply _root_.GD.N0212.N0466.d028993 hk sizes hn
    refine ⟨g, hg, hge, ?_, ?_⟩
    · intro θ
      rw [hrisk θ]
      exact hstrict θ
    · intro e he hdom θ
      exact (ht e he (fun θ => by simpa only [hrisk θ] using hdom θ) θ).trans
        (hgfθ θ).symm
  · exact bot_le

end
end GD.N0003.N0240

#print axioms _root_.GD.N0003.N0240.d029022
#print axioms _root_.GD.N0003.N0240.d029023
#print axioms _root_.GD.N0003.N0240.d029024
#print axioms _root_.GD.N0003.N0240.d029026
