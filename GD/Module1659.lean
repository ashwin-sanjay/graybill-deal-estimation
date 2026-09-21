import GD.Module1658
import Mathlib.MeasureTheory.Function.Floor

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped ENNReal

namespace GD.N0097

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0970 _root_.GD.N0232.N0719.N0962

noncomputable section

variable {k : ℕ} (sizes : Fin k → ℕ)


theorem d028188 (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : Measurable f) (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes f) :
    f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := by
  refine ⟨hf, fun θ => ne_top_of_le_ne_top ?_ (hs θ).le⟩
  rw [_root_.GD.N0232.N0719.N0859.d010842 k sizes hk hn, _root_.GD.N0232.N0719.N0859.d010823 k sizes hk hn]
  exact ENNReal.ofReal_ne_top




theorem d028189
    (hk : 0 < k) (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (h1 : _root_.GD.N0097.d028174 sizes f 1) (h2 : _root_.GD.N0097.d028174 sizes f (Real.sqrt 2)) :
    ∃ g : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable g ∧ _root_.GD.N0097.d028173 sizes g ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, g =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f := by
  let p := _root_.GD.N0232.N0719.N0970.d012312 k sizes f hf
  have hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p := by
    intro θ
    rw [_root_.GD.N0232.N0719.N0970.d012313]
    exact hf.2 θ
  have hdf : _root_.GD.N0232.N0719.N0896.d011088 k sizes p =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] f := by
    apply (_root_.GD.N0232.N0719.N0896.d011090 k sizes p).trans
    exact (_root_.GD.N0232.N0719.N0896.d011095 k sizes f hf.1
      (hf.2 (_root_.GD.N0232.N0719.N0859.d010810 k))).coeFn_toLp
  have toDecision (t : ℝ) (ht : _root_.GD.N0097.d028174 sizes f t) :
      _root_.GD.N0097.d028164 sizes t (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010813 k sizes] _root_.GD.N0232.N0719.N0896.d011088 k sizes p :=
    (_root_.GD.N0097.d028167 sizes t hdf).trans
      (((_root_.GD.N0097.d028175 sizes f t).mpr ht).trans hdf.symm)
  have hall := _root_.GD.N0097.d028172 sizes p hp
    (toDecision 1 h1) (toDecision (Real.sqrt 2) h2)
  apply _root_.GD.N0097.d028187 sizes hk hn f hf.1
  intro t
  apply (_root_.GD.N0097.d028175 sizes f t).mp
  exact (_root_.GD.N0097.d028167 sizes t hdf.symm).trans ((hall t).trans hdf)




theorem d028190
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    (∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable f ∧ _root_.GD.N0097.d028173 sizes f ∧
      _root_.GD.N0232.N0719.N0970.d012309 k sizes f ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes f) ↔
    (∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable f ∧ _root_.GD.N0232.N0719.N0970.d012309 k sizes f ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes f ∧
      _root_.GD.N0097.d028174 sizes f 1 ∧ _root_.GD.N0097.d028174 sizes f (Real.sqrt 2)) := by
  constructor
  · rintro ⟨f, hf, he, ht, hs⟩
    exact ⟨f, hf, ht, hs, ae_of_all _ (he 1), ae_of_all _ (he (Real.sqrt 2))⟩
  · rintro ⟨f, hf, ht, hs, h1, h2⟩
    obtain ⟨g, hg, hge, hgf⟩ := _root_.GD.N0097.d028189 sizes
      (by omega) (fun i => by have := hn i; omega) f
      (_root_.GD.N0097.d028188 sizes hk hn f hf hs) h1 h2
    have hrisk (θ : _root_.GD.N0232.N0719.N0859.d010809 k) := _root_.GD.N0232.N0719.N0896.d011094 k sizes θ (hgf θ)
    refine ⟨g, hg, hge, ?_, ?_⟩
    · intro e he hdom θ
      exact (ht e he (fun θ => by simpa only [hrisk θ] using hdom θ) θ).trans
        (hgf θ).symm
    · intro θ
      rw [hrisk θ]
      exact hs θ




theorem d028191
    (hk : 0 < k) (hn : ∀ i, 0 < sizes i) :
    ∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable f ∧
      (∀ z, f (fun i j => 1 + z i j) = 1 + f z) ∧
      ¬ _root_.GD.N0097.d028173 sizes f := by
  let i : Fin k := ⟨0, hk⟩
  let j : Fin (sizes i) := ⟨0, hn i⟩
  let f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ :=
    fun z => (⌊z i j⌋ : ℤ)
  refine ⟨f, ?_, ?_, ?_⟩
  · unfold f
    fun_prop
  · intro z
    change (⌊1 + z i j⌋ : ℝ) = 1 + (⌊z i j⌋ : ℝ)
    exact_mod_cast Int.floor_intCast_add (1 : ℤ) (z i j)
  · intro h
    have hh := h (1 / 2) (fun _ _ => 0)
    have hhalf : ⌊(1 / 2 : ℝ)⌋ = (0 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num, by norm_num⟩
    norm_num [f, hhalf] at hh

end
end GD.N0097

#print axioms _root_.GD.N0097.d028189
#print axioms _root_.GD.N0097.d028190
#print axioms _root_.GD.N0097.d028191
