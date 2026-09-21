import GD.Module0441
import GD.Module1735

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace GD.N0153.N0442

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0973
open _root_.GD.N0003.N0239
open _root_.GD.N0004.N0242
open _root_.GD.N0153.N0441

variable (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
variable [MeasurableSpace (_root_.GD.N0232.N0719.N0859.d010809 k)] [OpensMeasurableSpace (_root_.GD.N0232.N0719.N0859.d010809 k)]




theorem d028843
    {d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hcap : ∀ θ, (_root_.GD.N0003.N0239.d028829 k sizes hk hn θ d).toReal <
      (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn).toReal)
    (μ : ℕ → Measure (_root_.GD.N0232.N0719.N0859.d010809 k)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure (_root_.GD.N0232.N0719.N0859.d010809 k)) [IsProbabilityMeasure ν]
    {ε : ℝ} (hε : 0 < ε)
    (hlim : Tendsto (fun n => ∫ θ, (_root_.GD.N0003.N0239.d028829 k sizes hk hn θ d).toReal ∂μ n)
      atTop (𝓝 (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn).toReal)) :
    ∃ B : Set (_root_.GD.N0232.N0719.N0859.d010809 k), MeasurableSet B ∧ ν.real B < ε ∧
      Tendsto (fun n => (μ n).real B) atTop (𝓝 1) :=
  _root_.GD.N0153.N0441.d006788 μ ν
    (_root_.GD.N0004.N0242.d028838 k sizes hk hn hd) (fun _ => ENNReal.toReal_nonneg)
    hcap hε hlim



theorem d028844
    {d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hv : (⨆ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ d) = _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn) :
    ∃ θ : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k,
      Tendsto (fun n => ∫ η, (_root_.GD.N0003.N0239.d028829 k sizes hk hn η d).toReal
        ∂Measure.dirac (θ n)) atTop (𝓝 (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn).toReal) := by
  have hlub : IsLUB (range (fun θ => _root_.GD.N0003.N0239.d028829 k sizes hk hn θ d))
      (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn) := by
    rw [← hv]
    exact isLUB_iSup
  obtain ⟨u, _, _, hu, hmem⟩ := hlub.exists_seq_monotone_tendsto
    (show (range (fun θ => _root_.GD.N0003.N0239.d028829 k sizes hk hn θ d)).Nonempty from
      ⟨_, _root_.GD.N0232.N0719.N0859.d010810 k, rfl⟩)
  choose θ hθ using hmem
  refine ⟨θ, ?_⟩
  have hlim := (ENNReal.tendsto_toReal (_root_.GD.N0232.N0719.N0973.d012379 k sizes hk hn)).comp hu
  have hmeas := (_root_.GD.N0004.N0242.d028838 k sizes hk hn hd).stronglyMeasurable
  simpa only [integral_dirac' _ _ hmeas, hθ, Function.comp_def] using hlim





theorem d028845 :
    ∃ d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes, _root_.GD.N0232.N0719.N0970.d012309 k sizes d ∧
      _root_.GD.N0232.N0719.N0970.d012310 k sizes d ∧
      (⨆ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ d) = _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn ∧
      ∀ (μ : ℕ → Measure (_root_.GD.N0232.N0719.N0859.d010809 k)), (∀ n, IsProbabilityMeasure (μ n)) →
        Tendsto (fun n => ∫ θ, (_root_.GD.N0003.N0239.d028829 k sizes hk hn θ d).toReal ∂μ n)
          atTop (𝓝 (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn).toReal) →
        ∀ (ν : Measure (_root_.GD.N0232.N0719.N0859.d010809 k)), IsProbabilityMeasure ν →
          ∀ ε : ℝ, 0 < ε → ∃ B : Set (_root_.GD.N0232.N0719.N0859.d010809 k),
            MeasurableSet B ∧ ν.real B < ε ∧
              Tendsto (fun n => (μ n).real B) atTop (𝓝 1) := by
  obtain ⟨d, hd, ht, hs, hv, hcap, _⟩ :=
    _root_.GD.N0004.N0242.d028839 k sizes hk hn
  refine ⟨d, hd, ht, hs, hv, ?_⟩
  intro μ hμ hlim ν hν ε hε
  letI := hμ
  letI := hν
  exact _root_.GD.N0153.N0442.d028843 k sizes hk hn hd hcap μ ν hε hlim

end GD.N0153.N0442

#print axioms _root_.GD.N0153.N0442.d028843
#print axioms _root_.GD.N0153.N0442.d028844
#print axioms _root_.GD.N0153.N0442.d028845
