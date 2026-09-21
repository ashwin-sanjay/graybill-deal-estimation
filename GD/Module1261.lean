import GD.Module1255
import GD.Module1260
import GD.Module0867

set_option autoImplicit false
set_option warningAsError true











open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace GD.N0232.N0719.N0979

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0719.N0987 _root_.GD.N0232.N0719.N0982
open _root_.GD.N0232.N0719.N1006 _root_.GD.N0232.N0719.N0862

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]

omit [Fintype I] in
theorem d020355 (i : I) (x : _root_.GD.N0232.N0720.N1352.d002739) :
    _root_.GD.N0232.N0719.N0987.d020296 i x = _root_.GD.N0232.N0719.N0982.d020335 i x := by
  ext j <;> simp [_root_.GD.N0232.N0719.N0987.d020296, _root_.GD.N0232.N0719.N0987.d020293]



theorem d020356
    (D : ℕ) (mu : Measure Ω) [IsProbabilityMeasure mu]
    (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131) (ht : ∀ i, Measurable (t i))
    (hsum : ∀ᵐ z ∂mu, ∑ i, (t i z : ℝ) = 1)
    (m : _root_.GD.N0232.N0719.N0982.d020351 (D + 1) (_root_.GD.N0232.N0719.N0987.d020298 ((D : ℝ) / 2) mu t)) (i : I) (center : ℝ) :
    ∀ᶠ epsilon in 𝓝 (0 : ℝ),
      _root_.GD.N0232.N0720.N1290.d004143 ((D : ℝ) / 2) (_root_.GD.N0232.N0720.N1290.d004147 center epsilon)
        (_root_.GD.N0232.N0719.N1006.d013356 mu t i) = 0 := by
  letI := _root_.GD.N0232.N0719.N1006.d013357 mu t ht i
  apply _root_.GD.N0232.N0719.N0982.d020354 D m i (_root_.GD.N0232.N0719.N1006.d013356 mu t i)
  intro x hx
  rw [← _root_.GD.N0232.N0719.N0979.d020355]
  exact _root_.GD.N0232.N0719.N0987.d020301 D mu t ht hsum i hx



theorem d020357
    (hI : 3 ≤ Fintype.card I) (D : ℕ) (hD : 3 ≤ D)
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131) (ht : ∀ i, Measurable (t i))
    (hsum : ∀ᵐ z ∂mu, ∑ i, (t i z : ℝ) = 1)
    (hceiling : ∀ i, ∀ c : ℝ, c < 1 →
      ¬ (∀ᵐ z : _root_.GD.N0232.N0720.N1290.d004131 ∂_root_.GD.N0232.N0719.N1006.d013356 mu t i, (z : ℝ) ≤ c)) :
    ¬ Nonempty (_root_.GD.N0232.N0719.N0982.d020351 (D + 1) (_root_.GD.N0232.N0719.N0987.d020298 ((D : ℝ) / 2) mu t)) := by
  rintro ⟨m⟩
  have hq : (3 / 2 : ℝ) ≤ (D : ℝ) / 2 := by
    have hDR : (3 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  exact _root_.GD.N0232.N0719.N1006.d013360 hI ((D : ℝ) / 2) hq mu t ht hsum
    (fun i => _root_.GD.N0232.N0719.N0979.d020356 D mu t ht hsum m i _) hceiling




theorem d020358
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (D : ℕ) (hD : 3 ≤ D)
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (t : Fin k → Ω → _root_.GD.N0232.N0720.N1290.d004131) (ht : ∀ i, Measurable (t i))
    (K : _root_.GD.N0232.N0719.d009173 k sizes → Ω → ℝ)
    (hK : _root_.GD.N0232.N0719.N0862.d013365 sizes mu t K)
    (hsum : ∀ᵐ z ∂mu, ∑ i, (t i z : ℝ) = 1)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    (hf : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) →
      MemLp f 2 (_root_.GD.N0232.N0719.d009176 k sizes 0 s))
    (hcap : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) →
      (∫ x, f x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s) ≤
        ∫ x, _root_.GD.N0232.N0719.N0900.d009111 k sizes x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s)
    (hrep : ∀ᵐ x ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
      f x = ∑ i, _root_.GD.N0232.N0719.N0862.d013361 mu t (K x) i * _root_.GD.N0232.N0719.N0900.d009102 k sizes x i) :
    ¬ Nonempty (_root_.GD.N0232.N0719.N0982.d020351 (D + 1) (_root_.GD.N0232.N0719.N0987.d020298 ((D : ℝ) / 2) mu t)) := by
  exact _root_.GD.N0232.N0719.N0979.d020357 (by simpa using hk) D hD mu t ht hsum
    (_root_.GD.N0232.N0719.N0862.d013367 sizes hn mu t ht K hK hsum f hfm hf hcap hrep)

end
end GD.N0232.N0719.N0979

#print axioms _root_.GD.N0232.N0719.N0979.d020356
#print axioms _root_.GD.N0232.N0719.N0979.d020357
#print axioms _root_.GD.N0232.N0719.N0979.d020358
