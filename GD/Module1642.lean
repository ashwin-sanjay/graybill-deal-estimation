import GD.Module1637
import GD.Module1641
import GD.Module1371
import GD.Module0759

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0024.N0272

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N1012 _root_.GD.N0232.N0719.N1010
open _root_.GD.N0232.N0719.N0842 _root_.GD.N0232.N0719.N0946
open _root_.GD.N0074

theorem d028027
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 0 < k) (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (hd : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, MemLp d 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ))
    (hcov : ∀ (b a : ℝ), 0 < a → ∀ x,
      d (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a x) = b + a * d x) :
    ∃ q : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ,
      Measurable q ∧
      (∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ s, q (g • s) = g • q s) ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (q ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d := by
  let p := _root_.GD.N0074.d027958 k sizes d hd
  let q := _root_.GD.N0074.d023620 k sizes hsizes p
  have hpfix (b a : ℝ) (ha : 0 < a) : _root_.GD.N0074.d027955 k sizes b a ha p = p := by
    apply _root_.GD.N0079.N0320.d028021
    funext x
    have h := hcov b a ha (_root_.GD.N0232.N0719.N0842.d010907 k sizes b a x)
    rw [_root_.GD.N0232.N0719.N0842.d010910 k sizes b a ha.ne'] at h
    exact h.symm
  have hqfix (b a : ℝ) (ha : 0 < a) : _root_.GD.N0074.d027955 k sizes b a ha q.val = q.val := by
    dsimp only [q]
    rw [← _root_.GD.N0074.d027964 k sizes hsizes a ha b p, hpfix]
  have hqfixed (b a : ℝ) (ha : 0 < a) :
      _root_.GD.N0232.N0719.N0842.d010911 k sizes b a (q.val.val : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
        =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] q.val.val := by
    have h := _root_.GD.N0074.d027956 k sizes b a ha q.val (_root_.GD.N0232.N0719.N0859.d010810 k)
    rw [hqfix] at h
    exact h.symm
  have hqcov (g : _root_.GD.N0232.N0719.N0946.d009229) :
      (fun x => q.val.val (g • x)) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
        fun x => g • q.val.val x := by
    have h := (_root_.GD.N0232.N0719.N0896.d011119 k sizes
      g.shift g.d009239 g.d009240).ae_eq_comp
      (hqfixed g.shift g.d009239 g.d009240)
    filter_upwards [h] with x hx
    simp only [Function.comp_apply, _root_.GD.N0232.N0719.N0842.d010911,
      _root_.GD.N0232.N0719.N0842.d010909 k sizes g.shift g.d009239
        g.d009241] at hx
    exact hx.symm
  have hqs : AEStronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes]
      (q.val.val : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    (_root_.GD.N0074.d023615 k sizes q.val).mp q.property
  obtain ⟨value, hvalue, hfactor⟩ := hqs.stronglyMeasurable_mk.exists_eq_measurable_comp
  have hrep : (q.val.val : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
      =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
        value ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes := by
    exact hqs.ae_eq_mk.trans (Filter.Eventually.of_forall (congrFun hfactor))
  have hcovSummary : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun x : _root_.GD.N0232.N0719.N0900.d009094 k sizes =>
        value (g • _root_.GD.N0232.N0719.N0900.d009104 k sizes x))
        =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      fun x => g • value (_root_.GD.N0232.N0719.N0900.d009104 k sizes x) := by
    intro g
    have hrepG := (_root_.GD.N0232.N0719.N0896.d011119 k sizes
      g.shift g.d009239 g.d009240).ae_eq_comp hrep
    filter_upwards [hrepG, hqcov g, hrep] with x hG hC hR
    simp only [Function.comp_apply] at hG hR
    change q.val.val (g • x) = value (_root_.GD.N0232.N0719.N0900.d009104 k sizes (g • x)) at hG
    rw [_root_.GD.N0232.N0719.N1010.d011418 (fun i => by have := hsizes i; omega)] at hG
    exact hG.symm.trans (hC.trans (congrArg (g • ·) hR))
  obtain ⟨repaired, hr, hrae, hrcov⟩ :=
    _root_.GD.N0232.N0719.N1010.d011423 hk value hvalue.measurable hcovSummary
  refine ⟨repaired, hr, hrcov, fun θ => ?_⟩
  have hrepθ : (q.val.val : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
      value ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes :=
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_eq hrep
  have hdecθ : _root_.GD.N0232.N0719.N0896.d011088 k sizes q.val.val =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ]
      (q.val.val : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) :=
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_eq
      (_root_.GD.N0232.N0719.N0896.d011090 k sizes q.val.val)
  have hraw : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (repaired ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes θ q.val.val := by
    rw [_root_.GD.N0232.N0719.N0896.d011094 k sizes θ
      ((hrae θ).trans (hrepθ.symm.trans hdecθ.symm)), _root_.GD.N0232.N0719.N0896.d011093]
  rw [hraw]
  exact (_root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes θ p.val).trans_eq
    (_root_.GD.N0232.N0719.N0859.d010841 k sizes θ d (_root_.GD.N0074.d027954 k sizes d hd)).symm

end
end GD.N0024.N0272

#print axioms _root_.GD.N0024.N0272.d028027
