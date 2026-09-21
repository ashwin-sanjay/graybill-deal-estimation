import GD.Module0610










open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0142

noncomputable section

open _root_.GD.N0124
open _root_.GD.N0116
open _root_.GD.N0120
open _root_.GD.N0141

variable {Ω : Type*} [MeasurableSpace Ω]






def d008829
    (P : Measure Ω) (D L F : Ω → ℝ)
    (α β e Sigma : ℝ) : Prop :=
  ∀ φ : ℝ × ℝ → ℝ,
    (∫ ω, D ω ^ 2 * φ (L ω, F ω) ∂P)
      = Sigma * _root_.GD.N0120.d008809 α β e φ

theorem d008829.d008830
    {P : Measure Ω} {D L F : Ω → ℝ}
    {α β e Sigma : ℝ}
    (hLaw : _root_.GD.N0142.d008829 P D L F α β e Sigma)
    (q : ℝ × ℝ → ℝ) :
    _root_.GD.N0141.d006687 P D L (fun ω => q (L ω, F ω)) e =
      Sigma * _root_.GD.N0120.d008814 α β e q := by
  unfold _root_.GD.N0142.d008829 at hLaw
  unfold _root_.GD.N0141.d006687 _root_.GD.N0120.d008814 _root_.GD.N0120.d008809
  have h := hLaw (fun p => (p.1 - e) * q p)
  convert h using 1
  · apply integral_congr_ae
    filter_upwards [] with ω
    ring
  · rfl

theorem d008829.d008831
    {P : Measure Ω} {D L F : Ω → ℝ}
    {α β e Sigma : ℝ}
    (hLaw : _root_.GD.N0142.d008829 P D L F α β e Sigma)
    (q : ℝ × ℝ → ℝ) :
    _root_.GD.N0141.d006688 P D (fun ω => q (L ω, F ω)) =
      Sigma * _root_.GD.N0120.d008815 α β e q := by
  unfold _root_.GD.N0142.d008829 at hLaw
  unfold _root_.GD.N0141.d006688 _root_.GD.N0120.d008815 _root_.GD.N0120.d008809
  exact hLaw (fun p => q p ^ 2)



theorem d008832 :
    (∫ z : ℝ, z ^ 2
      ∂ProbabilityTheory.gaussianReal 0 1) = 1 := by
  have h :=
    ProbabilityTheory.variance_fun_id_gaussianReal
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  rw [ProbabilityTheory.variance_eq_integral
    measurable_id'.aemeasurable] at h
  simpa using h

theorem d008833 :
    Integrable (fun z : ℝ => z ^ 2)
      (ProbabilityTheory.gaussianReal 0 1) := by
  have h :=
    ProbabilityTheory.memLp_id_gaussianReal
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (2 : ℝ≥0)
  simpa only [id_eq] using h.integrable_sq

theorem d008834 :
    Integrable
      (fun z : ℝ =>
        z ^ 2 * ProbabilityTheory.gaussianPDFReal 0 1 z) := by
  have h := _root_.GD.N0142.d008833
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (by norm_num),
    MeasureTheory.integrable_withDensity_iff
      (by fun_prop :
        Measurable (ProbabilityTheory.gaussianPDF 0 1))
      (ae_of_all _ fun z => by
        simp [ProbabilityTheory.gaussianPDF])] at h
  simpa only [ProbabilityTheory.gaussianPDF,
    ENNReal.toReal_ofReal
      (ProbabilityTheory.gaussianPDFReal_nonneg 0 1 _)] using h

theorem d008835 :
    (∫ w : ℝ in Ioi 0,
      _root_.GD.N0122.d006380 w) = 1 := by
  have h :=
    _root_.GD.N0122.d006386
      (fun _ : ℝ => (1 : ℝ))
      (by simpa only [mul_one] using
        _root_.GD.N0142.d008834)
  simp only [mul_one] at h
  rw [_root_.GD.N0142.d008832] at h
  exact h.symm

theorem d008836 (c : ℝ) :
    Integrable
      (fun z : ℝ =>
        z ^ 2 * ProbabilityTheory.gaussianPDFReal 0 1 z * c) :=
  _root_.GD.N0142.d008834.mul_const c

theorem d008837 (c : ℝ) :
    (∫ z : ℝ, z ^ 2 * c
      ∂ProbabilityTheory.gaussianReal 0 1) = c := by
  rw [MeasureTheory.integral_mul_const, _root_.GD.N0142.d008832,
    one_mul]

theorem d008838 (c : ℝ) :
    (∫ w : ℝ in Ioi 0,
      _root_.GD.N0122.d006380 w * c) = c := by
  rw [MeasureTheory.integral_mul_const,
    _root_.GD.N0142.d008835, one_mul]








theorem d008839
    {P : Measure Ω} [IsProbabilityMeasure P]
    {U D L F : Ω → ℝ}
    {α β e Sigma : ℝ}
    (q : ℝ × ℝ → ℝ)
    {atomic smear densityError energy C M : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (hSigma : 0 < Sigma)
    (hq : Measurable q)
    (hU : MemLp U 2 P)
    (hWeight : MemLp (fun ω => D ω * (L ω - e)) 2 P)
    (hCarrier : MemLp (fun ω => D ω * q (L ω, F ω)) 2 P)
    (hIndep :
      IndepFun U (fun ω => (D ω, (L ω, F ω))) P)
    (hCentered : ∫ ω, U ω ∂P = 0)
    (hLaw : _root_.GD.N0142.d008829 P D L F α β e Sigma)
    (hTraceTarget :
      IntegrableOn
        (fun p : _root_.GD.N0124.d006387 =>
          ((p.1 - e) * q (p.1, p.2.1)) *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        _root_.GD.N0124.d006389 volume)
    (hEnergyTarget :
      IntegrableOn
        (fun p : _root_.GD.N0124.d006387 =>
          q (p.1, p.2.1) ^ 2 *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        _root_.GD.N0124.d006389 volume)
    (hTraceTargetIter :
      (∫ p : _root_.GD.N0124.d006387 in _root_.GD.N0124.d006389,
          ((p.1 - e) * q (p.1, p.2.1)) *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        =
      ∫ l : ℝ in Ioo 0 1,
        ∫ f : ℝ in Ioi 0,
          ∫ H : ℝ in Ioi 0,
            ((l - e) * q (l, f)) *
              (H ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (l, f, H)))
    (hEnergyTargetIter :
      (∫ p : _root_.GD.N0124.d006387 in _root_.GD.N0124.d006389,
          q (p.1, p.2.1) ^ 2 *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        =
      ∫ l : ℝ in Ioo 0 1,
        ∫ f : ℝ in Ioi 0,
          ∫ H : ℝ in Ioi 0,
            q (l, f) ^ 2 *
              (H ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (l, f, H)))
    (hC : 0 < C) (hM : 0 < M)
    (hAtomic : atomic ≤ -(3 * C / 4))
    (hSmear : |smear| ≤ C / 16)
    (hDensity : |densityError| ≤ C / 16)
    (hReducedTrace :
      _root_.GD.N0120.d008816 α β e q = atomic + smear + densityError)
    (hReducedEnergy :
      _root_.GD.N0120.d008817 α β e q = energy)
    (hEnergyCeiling : energy ≤ M) :
    _root_.GD.N0141.d006684 P
        (_root_.GD.N0141.d006686 U D L (fun ω => q (L ω, F ω))
          e ((C / 2) / M))
      < _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006685 U D L e) := by
  let t : ℝ := _root_.GD.N0120.d008814 α β e q
  let a : ℝ := _root_.GD.N0120.d008815 α β e q
  apply
    _root_.GD.N0120.d008828
      (P := P) (U := U) (D := D) (L := L) (F := F)
      (α := α) (β := β) (e := e) (Sigma := Sigma)
      q (fun _ => t) (fun _ => a)
      hα hβ he0 he1 hSigma hq hU hWeight hCarrier hIndep hCentered
  · rw [_root_.GD.N0142.d008837]
    exact hLaw.d008830 q
  · rw [_root_.GD.N0142.d008837]
    exact hLaw.d008831 q
  · exact _root_.GD.N0142.d008838 t
  · exact _root_.GD.N0142.d008838 a
  · exact _root_.GD.N0142.d008836 t
  · exact _root_.GD.N0142.d008836 a
  · exact hTraceTarget
  · exact hEnergyTarget
  · exact hTraceTargetIter
  · exact hEnergyTargetIter
  · exact hC
  · exact hM
  · exact hAtomic
  · exact hSmear
  · exact hDensity
  · exact hReducedTrace
  · exact hReducedEnergy
  · exact hEnergyCeiling

end

end GD.N0142
