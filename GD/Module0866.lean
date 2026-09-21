import GD.Module0865














open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace GD.N0232.N0719.N1006

open _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1344
open _root_.GD.N0232.N0720.N1340
open _root_.GD.N0232.N0720.N1414 (d004212)

noncomputable section


theorem d013355
    (q : ℝ) (hq : 3 / 2 ≤ q) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hF : ∀ᶠ epsilon in 𝓝 (0 : ℝ),
      _root_.GD.N0232.N0720.N1290.d004143 q (_root_.GD.N0232.N0720.N1290.d004147 (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) epsilon) mu = 0)
    (hceiling : ∀ c : ℝ, c < 1 → ¬ (∀ᵐ t : _root_.GD.N0232.N0720.N1290.d004131 ∂mu, (t : ℝ) ≤ c)) :
    1 / 2 ≤ _root_.GD.N0232.N0720.N1414.d004212 0 1 mu := by
  have hclass := _root_.GD.N0232.N0720.N1344.d013344 q hq mu hF
  have hend := _root_.GD.N0232.N0720.N1340.d013353 q hq hclass
  have hmem := _root_.GD.N0232.N0720.N1340.d013354 q hq
    (show 0 ≤ _root_.GD.N0232.N0720.N1344.d013342 q hq 0 1 mu from Real.sqrt_nonneg _) hclass
  have hu : 1 ≤ _root_.GD.N0232.N0720.N1414.d004212 0 1 mu + _root_.GD.N0232.N0720.N1344.d013342 q hq 0 1 mu := by
    by_contra! hlt
    exact hceiling _ hlt (hmem.mono fun _ ht => ht.2)
  linarith [hend.1]

variable {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]

def d013356 (mu : Measure Ω) (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131) (i : I) : Measure _root_.GD.N0232.N0720.N1290.d004131 :=
  Measure.map (t i) mu

omit [Fintype I] in
theorem d013357 (mu : Measure Ω) [IsProbabilityMeasure mu]
    (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131) (ht : ∀ i, Measurable (t i)) (i : I) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N1006.d013356 mu t i) :=
  Measure.isProbabilityMeasure_map (ht i).aemeasurable

omit [Fintype I] in
theorem d013358 (mu : Measure Ω) [IsProbabilityMeasure mu]
    (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131) (ht : ∀ i, Measurable (t i)) (i : I) :
    Integrable (fun x => (t i x : ℝ)) mu := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_subtype_coe.comp (ht i)).aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    change ‖(t i x : ℝ)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (t i x).2.1]
    exact (t i x).2.2


theorem d013359 (mu : Measure Ω) [IsProbabilityMeasure mu]
    (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131) (ht : ∀ i, Measurable (t i))
    (hsum : ∀ᵐ x ∂mu, ∑ i, (t i x : ℝ) = 1) :
    ∑ i, _root_.GD.N0232.N0720.N1414.d004212 0 1 (_root_.GD.N0232.N0719.N1006.d013356 mu t i) = 1 := by
  have hm (i : I) : _root_.GD.N0232.N0720.N1414.d004212 0 1 (_root_.GD.N0232.N0719.N1006.d013356 mu t i) =
      ∫ x, (t i x : ℝ) ∂mu := by
    unfold _root_.GD.N0232.N0720.N1414.d004212 _root_.GD.N0232.N0719.N1006.d013356
    exact integral_map (ht i).aemeasurable continuous_subtype_val.aestronglyMeasurable
  simp_rw [hm]
  rw [← integral_finsetSum _ (fun i _ => _root_.GD.N0232.N0719.N1006.d013358 mu t ht i)]
  rw [integral_congr_ae hsum]
  simp



theorem d013360
    (hI : 3 ≤ Fintype.card I) (q : ℝ) (hq : 3 / 2 ≤ q)
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131) (ht : ∀ i, Measurable (t i))
    (hsum : ∀ᵐ x ∂mu, ∑ i, (t i x : ℝ) = 1)
    (hF : ∀ i, ∀ᶠ epsilon in 𝓝 (0 : ℝ),
      _root_.GD.N0232.N0720.N1290.d004143 q
        (_root_.GD.N0232.N0720.N1290.d004147 (_root_.GD.N0232.N0720.N1414.d004212 0 1 (_root_.GD.N0232.N0719.N1006.d013356 mu t i)) epsilon)
          (_root_.GD.N0232.N0719.N1006.d013356 mu t i) = 0)
    (hceiling : ∀ i, ∀ c : ℝ, c < 1 →
      ¬ (∀ᵐ z : _root_.GD.N0232.N0720.N1290.d004131 ∂_root_.GD.N0232.N0719.N1006.d013356 mu t i, (z : ℝ) ≤ c)) : False := by
  have hhalf (i : I) : 1 / 2 ≤ _root_.GD.N0232.N0720.N1414.d004212 0 1 (_root_.GD.N0232.N0719.N1006.d013356 mu t i) := by
    letI := _root_.GD.N0232.N0719.N1006.d013357 mu t ht i
    exact _root_.GD.N0232.N0719.N1006.d013355 q hq _ (hF i) (hceiling i)
  have htotal := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hhalf i)
  rw [_root_.GD.N0232.N0719.N1006.d013359 mu t ht hsum] at htotal
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htotal
  have hcard : (3 : ℝ) ≤ Fintype.card I := by exact_mod_cast hI
  nlinarith

end
end GD.N0232.N0719.N1006

#print axioms _root_.GD.N0232.N0719.N1006.d013355
#print axioms _root_.GD.N0232.N0719.N1006.d013359
#print axioms _root_.GD.N0232.N0719.N1006.d013360
