import GD.Module1875
import GD.Module0441

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace GD.N0231

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1066
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0611
open _root_.GD.N0046.N0303
open _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1226
open _root_.GD.N0076.N0313
open _root_.GD.N0214.N0531
open _root_.GD.N0153.N0441 _root_.GD.N0004.N0241

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
variable [MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168] [OpensMeasurableSpace _root_.GD.N0232.N0720.N1080.d014168]

theorem d030667
    (p : _root_.GD.N0076.N0313.d030564 m n)
    (hcap : ∀ θ, (_root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal <
      (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal)
    (μ : ℕ → Measure _root_.GD.N0232.N0720.N1080.d014168) [∀ j, IsProbabilityMeasure (μ j)]
    (ν : Measure _root_.GD.N0232.N0720.N1080.d014168) [IsProbabilityMeasure ν]
    (hlim : Tendsto
      (fun j => ∫ θ, (_root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal ∂μ j)
      atTop (𝓝 (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal)) :
    (∀ ε : ℝ, 0 < ε → ∃ B : Set _root_.GD.N0232.N0720.N1080.d014168, MeasurableSet B ∧ ν.real B < ε ∧
      Tendsto (fun j => (μ j).real B) atTop (𝓝 1)) ∧
    (¬ ∀ B : Set _root_.GD.N0232.N0720.N1080.d014168, MeasurableSet B →
      Tendsto (fun j => (μ j).real B) atTop (𝓝 (ν.real B))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ B : Set _root_.GD.N0232.N0720.N1080.d014168, MeasurableSet B ∧
      ∀ᶠ j in atTop, 1 - ε < |(μ j).real B - ν.real B|) := by
  have hmeas := _root_.GD.N0214.N0531.d030664 m n hm hn p
  have hnonneg (θ : _root_.GD.N0232.N0720.N1080.d014168) :
      0 ≤ (_root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal :=
    ENNReal.toReal_nonneg
  exact ⟨fun _ hε => _root_.GD.N0153.N0441.d006788
      μ ν hmeas hnonneg hcap hε hlim,
    _root_.GD.N0153.N0441.d006789 μ ν hmeas hnonneg hcap hlim,
    fun _ hε => _root_.GD.N0153.N0441.d006790 μ ν hmeas hnonneg hcap hε hlim⟩

theorem d030668
    (p : _root_.GD.N0076.N0313.d030564 m n)
    (hv : _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) (_root_.GD.N0232.N0720.N1214.d014265 m n p) =
      _root_.GD.N0076.N0313.d030569 m n hm hn) :
    ∃ θ : ℕ → _root_.GD.N0232.N0720.N1080.d014168,
      Tendsto (fun j => ∫ η, (_root_.GD.N0076.N0313.d030568 m n hm hn η (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal
        ∂Measure.dirac (θ j)) atTop (𝓝 (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal) := by
  have hlub : IsLUB (range (fun θ => _root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)))
      (_root_.GD.N0076.N0313.d030569 m n hm hn) := by
    rw [← hv]
    exact isLUB_iSup
  obtain ⟨u, _, _, hu, hmem⟩ := hlub.exists_seq_monotone_tendsto
    (show (range (fun θ => _root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p))).Nonempty from
      ⟨_, _root_.GD.N0232.N0720.N1080.d014169, rfl⟩)
  choose θ hθ using hmem
  refine ⟨θ, ?_⟩
  have hlim := (ENNReal.tendsto_toReal (_root_.GD.N0076.N0313.d030574 m n hm hn)).comp hu
  have hmeas := (_root_.GD.N0214.N0531.d030664 m n hm hn p).stronglyMeasurable
  simpa only [integral_dirac' _ _ hmeas, hθ, Function.comp_def] using hlim

theorem d030669 :
    ∃ p : _root_.GD.N0076.N0313.d030564 m n,
      _root_.GD.N0232.N0720.N1214.d014265 m n p ∈ _root_.GD.N0232.N0720.N1256.d015551 m n ∧
      _root_.GD.N0076.N0313.d030591 m n (_root_.GD.N0232.N0720.N1214.d014265 m n p) ∧
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1214.d014265 m n p) <
        _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) (_root_.GD.N0232.N0720.N1214.d014265 m n p) = _root_.GD.N0076.N0313.d030569 m n hm hn ∧
      (∀ θ, (_root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal <
        (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal) ∧
      (∀ ν : Measure _root_.GD.N0232.N0720.N1080.d014168, IsProbabilityMeasure ν →
        (∫ θ, (_root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal ∂ν) <
          (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal) ∧
      (∃ θ : ℕ → _root_.GD.N0232.N0720.N1080.d014168,
        Tendsto (fun j => ∫ η, (_root_.GD.N0076.N0313.d030568 m n hm hn η (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal
          ∂Measure.dirac (θ j)) atTop (𝓝 (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal)) ∧
      ∀ μ : ℕ → Measure _root_.GD.N0232.N0720.N1080.d014168, (∀ j, IsProbabilityMeasure (μ j)) →
        Tendsto
          (fun j => ∫ θ, (_root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal ∂μ j)
          atTop (𝓝 (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal) →
        ∀ ν : Measure _root_.GD.N0232.N0720.N1080.d014168, IsProbabilityMeasure ν →
          (∀ ε : ℝ, 0 < ε → ∃ B : Set _root_.GD.N0232.N0720.N1080.d014168, MeasurableSet B ∧ ν.real B < ε ∧
            Tendsto (fun j => (μ j).real B) atTop (𝓝 1)) ∧
          (¬ ∀ B : Set _root_.GD.N0232.N0720.N1080.d014168, MeasurableSet B →
            Tendsto (fun j => (μ j).real B) atTop (𝓝 (ν.real B))) ∧
          (∀ ε : ℝ, 0 < ε → ∃ B : Set _root_.GD.N0232.N0720.N1080.d014168, MeasurableSet B ∧
            ∀ᶠ j in atTop, 1 - ε < |(μ j).real B - ν.real B|) := by
  obtain ⟨p, hp, ht, hs, hv, hcap⟩ :=
    _root_.GD.N0214.N0531.d030663 m n hm hn
  have hcap' (θ : _root_.GD.N0232.N0720.N1080.d014168) :
      (_root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal <
        (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal :=
    (ENNReal.toReal_lt_toReal (ne_top_of_lt (hcap θ)) (_root_.GD.N0076.N0313.d030574 m n hm hn)).mpr (hcap θ)
  refine ⟨p, hp, ht, hs, hv, hcap', ?_,
    _root_.GD.N0231.d030668 m n hm hn p hv, ?_⟩
  · intro ν hν
    letI := hν
    exact _root_.GD.N0004.N0241.d005269 ν (_root_.GD.N0214.N0531.d030664 m n hm hn p)
      (fun _ => ENNReal.toReal_nonneg) hcap'
  · intro μ hμ hlim ν hν
    letI := hμ
    letI := hν
    exact _root_.GD.N0231.d030667 m n hm hn p hcap' μ ν hlim

end GD.N0231

#print axioms _root_.GD.N0231.d030667
#print axioms _root_.GD.N0231.d030668
#print axioms _root_.GD.N0231.d030669
