import GD.Module0356
import GD.Module1734
import GD.Module0749

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace GD.N0004.N0242

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0973
open _root_.GD.N0003.N0239
open _root_.GD.N0004.N0241

variable (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
variable [MeasurableSpace (_root_.GD.N0232.N0719.N0859.d010809 k)] [OpensMeasurableSpace (_root_.GD.N0232.N0719.N0859.d010809 k)]

theorem d028837 {d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) :
    Measurable (fun θ : _root_.GD.N0232.N0719.N0859.d010809 k => _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d) := by
  have h := (_root_.GD.N0232.N0719.N0865.d011222 k sizes
    (_root_.GD.N0232.N0719.N0970.d012312 k sizes d hd)).measurable
  simpa only [_root_.GD.N0232.N0719.N0970.d012313] using h

theorem d028838 {d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) :
    Measurable (fun θ => (_root_.GD.N0003.N0239.d028829 k sizes hk hn θ d).toReal) := by
  have hbase : Measurable (fun θ : _root_.GD.N0232.N0719.N0859.d010809 k =>
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0972.d012340 k sizes θ)) := by
    have h := (_root_.GD.N0232.N0719.N0865.d011222 k sizes
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hn)).measurable
    convert h using 1
    ext θ
    exact (_root_.GD.N0232.N0719.N0972.d012341 k sizes hk hn θ).symm.trans
      (_root_.GD.N0232.N0719.N0859.d010842 k sizes hk hn θ)
  exact ((_root_.GD.N0004.N0242.d028837 k sizes hd).div hbase).ennreal_toReal

theorem d028839 :
    ∃ d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes, _root_.GD.N0232.N0719.N0970.d012309 k sizes d ∧
      _root_.GD.N0232.N0719.N0970.d012310 k sizes d ∧
      (⨆ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ d) = _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn ∧
      (∀ θ, (_root_.GD.N0003.N0239.d028829 k sizes hk hn θ d).toReal <
        (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn).toReal) ∧
      ∀ (μ : Measure (_root_.GD.N0232.N0719.N0859.d010809 k)), IsProbabilityMeasure μ →
        (∫ θ, (_root_.GD.N0003.N0239.d028829 k sizes hk hn θ d).toReal ∂μ) <
          (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn).toReal := by
  obtain ⟨d, hd, ht, hs, hv, hp⟩ :=
    _root_.GD.N0003.N0239.d028830 k sizes hk hn
  have hp' (θ) : (_root_.GD.N0003.N0239.d028829 k sizes hk hn θ d).toReal <
      (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn).toReal :=
    (ENNReal.toReal_lt_toReal
      (ne_top_of_le_ne_top (_root_.GD.N0232.N0719.N0973.d012379 k sizes hk hn) (hp θ).le)
      (_root_.GD.N0232.N0719.N0973.d012379 k sizes hk hn)).mpr (hp θ)
  refine ⟨d, hd, ht, hs, hv, hp', ?_⟩
  intro μ hμ
  letI := hμ
  exact _root_.GD.N0004.N0241.d005269 μ (_root_.GD.N0004.N0242.d028838 k sizes hk hn hd)
    (fun _ => ENNReal.toReal_nonneg) hp'

theorem d028840 :
    ¬ ∃ (μ : Measure (_root_.GD.N0232.N0719.N0859.d010809 k)), IsProbabilityMeasure μ ∧
      ∀ d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
        (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn).toReal ≤
          ∫ θ, (_root_.GD.N0003.N0239.d028829 k sizes hk hn θ d).toReal ∂μ := by
  rintro ⟨μ, hμ, hmin⟩
  obtain ⟨d, hd, _, _, _, _, hp⟩ :=
    _root_.GD.N0004.N0242.d028839 k sizes hk hn
  exact (not_lt_of_ge (hmin d hd)) (hp μ hμ)

theorem d028841 :
    ¬ ∃ (μ : Measure (_root_.GD.N0232.N0719.N0859.d010809 k)), IsProbabilityMeasure μ ∧
      ∀ d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
        _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn ≤
          ∫⁻ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ d ∂μ := by
  rintro ⟨μ, hμ, hmin⟩
  letI := hμ
  obtain ⟨d, hd, _, _, _, hcap, hp⟩ :=
    _root_.GD.N0004.N0242.d028839 k sizes hk hn
  have hi := _root_.GD.N0004.N0241.d005268 μ (_root_.GD.N0004.N0242.d028838 k sizes hk hn hd)
    (fun _ => ENNReal.toReal_nonneg) (fun θ => (hcap θ).le)
  have hf (θ) : _root_.GD.N0003.N0239.d028829 k sizes hk hn θ d ≠ ⊤ :=
    ENNReal.div_ne_top (hd.2 θ)
      (ne_of_gt (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0719.N0972.d012342 k sizes hk hn θ)))
  have heq : (∫⁻ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ d ∂μ) =
      ENNReal.ofReal (∫ θ, (_root_.GD.N0003.N0239.d028829 k sizes hk hn θ d).toReal ∂μ) := by
    calc
      _ = ∫⁻ θ, ENNReal.ofReal (_root_.GD.N0003.N0239.d028829 k sizes hk hn θ d).toReal ∂μ :=
        lintegral_congr_ae (Eventually.of_forall fun θ => (ENNReal.ofReal_toReal (hf θ)).symm)
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm
  have hpos : 0 < (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn).toReal :=
    ENNReal.toReal_pos (_root_.GD.N0003.N0239.d028831 k sizes hk hn).ne'
      (_root_.GD.N0232.N0719.N0973.d012379 k sizes hk hn)
  have hlt : (∫⁻ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ d ∂μ) < _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn := by
    rw [heq, ← ENNReal.ofReal_toReal (_root_.GD.N0232.N0719.N0973.d012379 k sizes hk hn)]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (hp μ hμ)
  exact (not_lt_of_ge (hmin d hd)) hlt

theorem d028842
    {d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ} (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hcap : ∀ θ, _root_.GD.N0003.N0239.d028829 k sizes hk hn θ d ≤ _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn)
    (μ : ℕ → Measure (_root_.GD.N0232.N0719.N0859.d010809 k)) [∀ n, IsProbabilityMeasure (μ n)]
    {ε : ℝ} (hε : 0 < ε)
    (hlim : Tendsto (fun n => ∫ θ, (_root_.GD.N0003.N0239.d028829 k sizes hk hn θ d).toReal ∂μ n)
      atTop (𝓝 (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn).toReal)) :
    Tendsto (fun n => (μ n).real {θ | ε ≤
      (_root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn).toReal -
        (_root_.GD.N0003.N0239.d028829 k sizes hk hn θ d).toReal}) atTop (𝓝 0) := by
  exact _root_.GD.N0004.N0241.d005271 μ (_root_.GD.N0004.N0242.d028838 k sizes hk hn hd)
    (fun _ => ENNReal.toReal_nonneg)
    (fun θ => ENNReal.toReal_mono (_root_.GD.N0232.N0719.N0973.d012379 k sizes hk hn) (hcap θ))
    hε hlim

end GD.N0004.N0242

#print axioms _root_.GD.N0004.N0242.d028837
#print axioms _root_.GD.N0004.N0242.d028838
#print axioms _root_.GD.N0004.N0242.d028839
#print axioms _root_.GD.N0004.N0242.d028840
#print axioms _root_.GD.N0004.N0242.d028841
#print axioms _root_.GD.N0004.N0242.d028842
