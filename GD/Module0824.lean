import GD.Module0762
import GD.Module0822






















open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1500

noncomputable section

open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0933
open _root_.GD.N0232.N0719.N0910
open _root_.GD.N0232.N0719.N0930
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1497

private abbrev d012578 : Fin 2 → ℝ := ![1, 1]

private theorem d012579 :
    ∀ i, 2 ≤ _root_.GD.N0232.N0720.N1467.d012537 2 2 i := by
  intro i
  fin_cases i <;> norm_num [_root_.GD.N0232.N0720.N1467.d012537]





private theorem d012580 :
    _root_.GD.N0232.N0719.N0933.d009300 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) 0 _root_.GD.N0232.N0720.N1500.d012578
        {y | y 0 - y 1 = 0} = 0 := by
  let mu : Fin 2 → Measure ℝ := fun i ↦
    _root_.GD.N0232.N0719.N0933.d009288 (_root_.GD.N0232.N0720.N1467.d012537 2 2 i) 0 (_root_.GD.N0232.N0720.N1500.d012578 i)
  letI (i : Fin 2) : IsProbabilityMeasure (mu i) := by
    dsimp [mu]
    infer_instance
  letI : NoAtoms (mu 0) := by
    dsimp [mu, _root_.GD.N0232.N0720.N1500.d012578]
    rw [_root_.GD.N0232.N0719.N0933.d009297 (by norm_num : 0 < (2 : ℕ))]
    apply noAtoms_gaussianReal
    intro hv
    have hvcoe := congrArg (fun q : ℝ≥0 ↦ (q : ℝ)) hv
    norm_num at hvcoe
  let tail : ℝ → ℝ := fun y ↦
    -((((1 + 1 : ℕ) : ℝ)⁻¹) * y)
  let graphSet : Set (ℝ × ℝ) :=
    {z | (((1 + 1 : ℕ) : ℝ)⁻¹ * z.1 + tail z.2 = 0)}
  let contrastSet : Set (Fin 2 → ℝ) := {y | y 0 - y 1 = 0}
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 ↦ ℝ)
  have htail : Measurable tail := by
    dsimp [tail]
    fun_prop
  have hgraphMeas : MeasurableSet graphSet := by
    dsimp [graphSet]
    change MeasurableSet
      ((fun z : ℝ × ℝ ↦
        (((1 + 1 : ℕ) : ℝ)⁻¹ * z.1 + tail z.2)) ⁻¹' ({0} : Set ℝ))
    exact ((measurable_const.mul measurable_fst).add
      (htail.comp measurable_snd)) (measurableSet_singleton (0 : ℝ))
  have hpreimage : e ⁻¹' graphSet = contrastSet := by
    ext y
    change
      (2 : ℝ)⁻¹ * y 0 + -((2 : ℝ)⁻¹ * y 1) = 0 ↔
        y 0 - y 1 = 0
    constructor <;> intro h <;> norm_num at h ⊢ <;> linarith
  have hpreserving : MeasurePreserving e (Measure.pi mu)
      ((mu 0).prod (mu 1)) :=
    measurePreserving_piFinTwo mu
  have hgraph : (mu 0).prod (mu 1) graphSet = 0 := by
    simpa [graphSet] using
      (_root_.GD.N0232.N0719.N0930.d011505
        1 (mu 0) (mu 1) tail htail)
  change Measure.pi mu contrastSet = 0
  calc
    Measure.pi mu contrastSet =
        Measure.pi mu (e ⁻¹' graphSet) := by rw [hpreimage]
    _ = (Measure.pi mu).map e graphSet := by
      exact (Measure.map_apply e.measurable hgraphMeas).symm
    _ = (mu 0).prod (mu 1) graphSet := by rw [hpreserving.map_eq]
    _ = 0 := hgraph





private theorem d012581 :
    ∀ᵐ omega ∂_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) 0
        _root_.GD.N0232.N0720.N1500.d012578,
      (_root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) omega).mean 0 -
          (_root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) omega).mean 1 ≠ 0 := by
  let meanLaw := _root_.GD.N0232.N0719.N0933.d009300 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) 0 _root_.GD.N0232.N0720.N1500.d012578
  let varianceLaw :=
    _root_.GD.N0232.N0719.N0933.d009301 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) _root_.GD.N0232.N0720.N1500.d012578
  let P := _root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) 0 _root_.GD.N0232.N0720.N1500.d012578
  have hmean : ∀ᵐ y ∂meanLaw, y 0 - y 1 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using _root_.GD.N0232.N0720.N1500.d012580
  letI : IsProbabilityMeasure varianceLaw :=
    _root_.GD.N0232.N0719.N0910.d010289
      (_root_.GD.N0232.N0720.N1467.d012537 2 2) _root_.GD.N0232.N0720.N1500.d012579 _root_.GD.N0232.N0720.N1500.d012578
  have hpair : ∀ᵐ z ∂meanLaw.prod varianceLaw,
      z.1 0 - z.1 1 ≠ 0 :=
    (Measure.quasiMeasurePreserving_fst
      (μ := meanLaw) (ν := varianceLaw)).ae hmean
  have hstat : P.map
        (_root_.GD.N0232.N0719.N0933.d009304 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2)) =
      meanLaw.prod varianceLaw := by
    simpa [P, meanLaw, varianceLaw] using
      (_root_.GD.N0232.N0719.N0933.d009309
        2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) _root_.GD.N0232.N0720.N1500.d012579 0 _root_.GD.N0232.N0720.N1500.d012578)
  have hpreserving : MeasurePreserving
      (_root_.GD.N0232.N0719.N0933.d009304 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2)) P
        (meanLaw.prod varianceLaw) :=
    ⟨_root_.GD.N0232.N0719.N0933.d009308 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2), hstat⟩
  have hraw := hpreserving.quasiMeasurePreserving.ae hpair
  filter_upwards [hraw] with omega homega
  change
    (_root_.GD.N0232.N0719.N0933.d009304 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) omega).1 0 -
        (_root_.GD.N0232.N0719.N0933.d009304 2 (_root_.GD.N0232.N0720.N1467.d012537 2 2) omega).1 1 ≠ 0
  exact homega



theorem d012582 :
    ∀ᵐ x ∂_root_.GD.N0107.d009030 2 2 0 1 1,
      (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).mean 0 -
          (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).mean 1 ≠ 0 := by
  have hpull :=
    (_root_.GD.N0232.N0720.N1497.d012552 2 2 0 1 1).quasiMeasurePreserving.ae
      _root_.GD.N0232.N0720.N1500.d012581
  simpa [_root_.GD.N0232.N0720.N1500.d012578, _root_.GD.N0232.N0720.N1467.d012542] using hpull

end

end N1500
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1500.d012582
