import GD.Module1002






















open Filter MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1175

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0230.N0589
open _root_.GD.N0232.N0720.N1173






theorem d015999
    {X I : Type*} [MeasurableSpace X]
    {l : Filter I} [l.IsCountablyGenerated]
    (mu : Measure X) (f : I → X → ℝ) (envelope : X → ℝ)
    (hfmeas : ∀ᶠ i in l, AEStronglyMeasurable (f i) mu)
    (hdom : ∀ᶠ i in l, ∀ᵐ x ∂mu, ‖f i x‖ ≤ envelope x)
    (henvelope : Integrable envelope mu)
    (hpoint : ∀ᵐ x ∂mu,
      Tendsto (fun i ↦ f i x) l (nhds 0)) :
    Tendsto (fun i ↦ ∫ x, f i x ∂mu) l (nhds 0) := by
  simpa using tendsto_integral_filter_of_dominated_convergence
    envelope hfmeas hdom henvelope hpoint



theorem d016000
    {I : Type*} {l : Filter I}
    {current evidence : I → ℝ} {evidenceLimit : ℝ}
    (hcurrent : Tendsto current l (nhds 0))
    (hevidence : Tendsto evidence l (nhds evidenceLimit))
    (hevidenceLimit : evidenceLimit ≠ 0) :
    Tendsto (fun i ↦ current i ^ 2 / evidence i) l (nhds 0) := by
  have hdivision := (hcurrent.pow 2).div hevidence hevidenceLimit
  have hfun : ((fun i ↦ current i ^ 2) / evidence) =
      (fun i ↦ current i ^ 2 / evidence i) := by
    rfl
  rw [hfun] at hdivision
  simpa using hdivision




def d016001
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936) : ℝ :=
  _root_.GD.N0232.N0720.N1173.d015945 rho weight x ^ 2 /
    _root_.GD.N0232.N0720.N1173.d015940 rho weight x






theorem d016002
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hfull : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hfullMoment : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hfullEvidence : _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ≠ 0) :
    _root_.GD.N0232.N0720.N1173.d015945 rho (fun _ ↦ 1) x = 0 := by
  have hcurrent := _root_.GD.N0232.N0720.N1173.d015952
    rho (fun _ ↦ 1) x
      (by simpa [_root_.GD.N0232.N0720.N1173.d015939] using hfull)
      (by simpa [_root_.GD.N0232.N0720.N1173.d015939] using hfullMoment)
  rw [hcurrent]
  unfold _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1173.d015943
  field_simp [hfullEvidence]
  ring








theorem d016003
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : I → _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (envelope : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hmeas : ∀ᶠ i in l, AEStronglyMeasurable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1173.d015938 theta - _root_.GD.N0232.N0720.N1173.d015944 rho x) *
          _root_.GD.N0232.N0720.N1173.d015939 (weight i) theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hdom : ∀ᶠ i in l, ∀ᵐ theta ∂_root_.GD.N0232.N0720.N1173.d015934 rho,
      ‖(_root_.GD.N0232.N0720.N1173.d015938 theta - _root_.GD.N0232.N0720.N1173.d015944 rho x) *
          _root_.GD.N0232.N0720.N1173.d015939 (weight i) theta x‖ ≤ envelope theta)
    (henvelope : Integrable envelope (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hweight : ∀ᵐ theta ∂_root_.GD.N0232.N0720.N1173.d015934 rho,
      Tendsto (fun i ↦ weight i theta) l (nhds 1))
    (hfull : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hfullMoment : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hfullEvidence : _root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x ≠ 0) :
    Tendsto
      (fun i ↦ _root_.GD.N0232.N0720.N1173.d015945 rho (weight i) x)
      l (nhds 0) := by
  have hlimit : Tendsto
      (fun i ↦ _root_.GD.N0232.N0720.N1173.d015945 rho (weight i) x)
      l (nhds (_root_.GD.N0232.N0720.N1173.d015945 rho (fun _ ↦ 1) x)) := by
    unfold _root_.GD.N0232.N0720.N1173.d015945
    apply tendsto_integral_filter_of_dominated_convergence envelope
    · exact hmeas
    · exact hdom
    · exact henvelope
    · filter_upwards [hweight] with theta htheta
      simpa only [_root_.GD.N0232.N0720.N1173.d015939, mul_assoc, mul_one] using
        htheta.const_mul
          ((_root_.GD.N0232.N0720.N1173.d015938 theta - _root_.GD.N0232.N0720.N1173.d015944 rho x) * _root_.GD.N0232.N0720.N1173.d015937 theta x)
  simpa [_root_.GD.N0232.N0720.N1175.d016002
    rho x hfull hfullMoment hfullEvidence] using hlimit




theorem d016004
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : I → _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (envelope : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hmeas : ∀ᶠ i in l, AEStronglyMeasurable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 (weight i) theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hdom : ∀ᶠ i in l, ∀ᵐ theta ∂_root_.GD.N0232.N0720.N1173.d015934 rho,
      ‖_root_.GD.N0232.N0720.N1173.d015939 (weight i) theta x‖ ≤ envelope theta)
    (henvelope : Integrable envelope (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hweight : ∀ᵐ theta ∂_root_.GD.N0232.N0720.N1173.d015934 rho,
      Tendsto (fun i ↦ weight i theta) l (nhds 1)) :
    Tendsto
      (fun i ↦ _root_.GD.N0232.N0720.N1173.d015940 rho (weight i) x)
      l (nhds (_root_.GD.N0232.N0720.N1173.d015940 rho (fun _ ↦ 1) x)) := by
  unfold _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0230.N0589.d000088
  apply tendsto_integral_filter_of_dominated_convergence envelope
  · exact hmeas
  · exact hdom
  · exact henvelope
  · filter_upwards [hweight] with theta htheta
    simpa only [_root_.GD.N0232.N0720.N1173.d015939, mul_one] using
      htheta.const_mul (_root_.GD.N0232.N0720.N1173.d015937 theta x)





structure d016005
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) : Prop where
  fullJoint : Integrable
    (_root_.GD.N0230.N0589.d000071
      (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938 (_root_.GD.N0232.N0720.N1173.d015944 rho)).uncurry
    ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2))
  cutoffJoint : Integrable
    (_root_.GD.N0230.N0589.d000071
      (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
        (_root_.GD.N0232.N0720.N1173.d015943 rho weight)).uncurry
    ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2))
  tax : Integrable
    (_root_.GD.N0230.N0589.d000089
      (_root_.GD.N0232.N0720.N1173.d015934 rho) (_root_.GD.N0232.N0720.N1173.d015939 weight)
        (_root_.GD.N0232.N0720.N1173.d015944 rho) (_root_.GD.N0232.N0720.N1173.d015943 rho weight))
    (_root_.GD.N0232.N0720.N1080.d014172 2 2)
  moments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
    Integrable
        (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
        (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
    Integrable
        (fun theta ↦
          _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
        (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
    Integrable
        (fun theta ↦
          _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
        (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
    _root_.GD.N0232.N0720.N1173.d015940 rho weight x ≠ 0



theorem d016005.d016006
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hdata : _root_.GD.N0232.N0720.N1175.d016005 rho weight) :
    _root_.GD.N0232.N0720.N1173.d015956 rho weight =
      ∫ x, _root_.GD.N0232.N0720.N1175.d016001 rho weight x
        ∂_root_.GD.N0232.N0720.N1080.d014172 2 2 := by
  simpa [_root_.GD.N0232.N0720.N1175.d016001] using
    _root_.GD.N0232.N0720.N1173.d015957
      rho weight hdata.fullJoint hdata.cutoffJoint hdata.tax hdata.moments




theorem d016005.d016007
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hdata : _root_.GD.N0232.N0720.N1175.d016005 rho weight) :
    Integrable (_root_.GD.N0232.N0720.N1175.d016001 rho weight)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  apply hdata.tax.congr
  filter_upwards [hdata.moments] with x hx
  exact _root_.GD.N0232.N0720.N1173.d015955
    rho weight x hx.1 hx.2.1 hx.2.2.2






theorem d016008
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (weight : ℕ → _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hdata : ∀ n, _root_.GD.N0232.N0720.N1175.d016005 rho (weight n))
    (envelope : _root_.GD.N0232.N0720.N1173.d015936 → ℝ)
    (henvelope : Integrable envelope (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hdom : ∀ n, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      ‖_root_.GD.N0232.N0720.N1175.d016001 rho (weight n) x‖ ≤ envelope x)
    (hpoint : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0720.N1175.d016001 rho (weight n) x)
        atTop (nhds 0)) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1173.d015956 rho (weight n))
      atTop (nhds 0) := by
  have hintegral : Tendsto
      (fun n ↦ ∫ x, _root_.GD.N0232.N0720.N1175.d016001 rho (weight n) x
        ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) atTop (nhds 0) := by
    apply _root_.GD.N0232.N0720.N1175.d015999
      (_root_.GD.N0232.N0720.N1080.d014172 2 2)
      (fun n ↦ _root_.GD.N0232.N0720.N1175.d016001 rho (weight n)) envelope
    · exact Filter.Eventually.of_forall fun n ↦
        (hdata n).d016007
          |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall hdom
    · exact henvelope
    · exact hpoint
  simpa only [(hdata _).d016006] using hintegral











theorem d016009
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (weight : ℕ → _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hdata : ∀ n, _root_.GD.N0232.N0720.N1175.d016005 rho (weight n))
    (evidenceLimit envelope : _root_.GD.N0232.N0720.N1173.d015936 → ℝ)
    (hcurrent : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0720.N1173.d015945 rho (weight n) x)
        atTop (nhds 0))
    (hevidence : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Tendsto
        (fun n ↦ _root_.GD.N0232.N0720.N1173.d015940 rho (weight n) x)
        atTop (nhds (evidenceLimit x)))
    (hevidenceLimit : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < evidenceLimit x)
    (henvelope : Integrable envelope (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hdom : ∀ n, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      ‖_root_.GD.N0232.N0720.N1175.d016001 rho (weight n) x‖ ≤ envelope x) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1173.d015956 rho (weight n))
      atTop (nhds 0) := by
  apply _root_.GD.N0232.N0720.N1175.d016008
    rho weight hdata envelope henvelope hdom
  filter_upwards [hcurrent, hevidence, hevidenceLimit] with x hcx hex hpos
  exact _root_.GD.N0232.N0720.N1175.d016000 hcx hex (ne_of_gt hpos)

end

end N1175
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1175.d015999
#print axioms _root_.GD.N0232.N0720.N1175.d016003
#print axioms _root_.GD.N0232.N0720.N1175.d016004
#print axioms _root_.GD.N0232.N0720.N1175.d016005.d016007
#print axioms _root_.GD.N0232.N0720.N1175.d016009
