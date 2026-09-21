import GD.Module0421
import GD.Module0413
import GD.Module0430
import GD.Module0609



















open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0120

noncomputable section

open _root_.GD.N0124
open _root_.GD.N0116
open _root_.GD.N0141





noncomputable def d008809
    (α β e : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ p : _root_.GD.N0124.d006387 in _root_.GD.N0124.d006388,
    φ ((_root_.GD.N0124.d006391 e p).1, (_root_.GD.N0124.d006391 e p).2.1) * _root_.GD.N0116.d006510 α β p



noncomputable def d008810
    (α β e : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ L : ℝ in Ioo 0 1,
    ∫ F : ℝ in Ioi 0,
      φ (L, F) * _root_.GD.N0116.d006511 α β e (L, F)


noncomputable def d008811
    (α β e : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.1 ^ (β - 1) * (1 - p.1) ^ (α - 1) *
      p.2 ^ ((1 : ℝ) / 2)) *
    (α * e * (1 - p.1) + β * (1 - e) * p.1 +
      p.2 * e * (1 - e) / 2) ^ (-_root_.GD.N0116.d006509 α β)



noncomputable def d008812
    (α β e : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ L : ℝ in Ioo 0 1,
    ∫ F : ℝ in Ioi 0,
      φ (L, F) * _root_.GD.N0120.d008811 α β e (L, F)



noncomputable def d008813 (α β e : ℝ) : ℝ :=
  _root_.GD.N0116.d006507 α β * _root_.GD.N0116.d006508 α β e


noncomputable def d008814
    (α β e : ℝ) (q : ℝ × ℝ → ℝ) : ℝ :=
  _root_.GD.N0120.d008809 α β e (fun p => (p.1 - e) * q p)


noncomputable def d008815
    (α β e : ℝ) (q : ℝ × ℝ → ℝ) : ℝ :=
  _root_.GD.N0120.d008809 α β e (fun p => q p ^ 2)


noncomputable def d008816
    (α β e : ℝ) (q : ℝ × ℝ → ℝ) : ℝ :=
  _root_.GD.N0120.d008812 α β e (fun p => (p.1 - e) * q p)


noncomputable def d008817
    (α β e : ℝ) (q : ℝ × ℝ → ℝ) : ℝ :=
  _root_.GD.N0120.d008812 α β e (fun p => q p ^ 2)





theorem d008818
    (α β e : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0116.d006511 α β e p =
      _root_.GD.N0120.d008813 α β e * _root_.GD.N0120.d008811 α β e p := by
  unfold _root_.GD.N0116.d006511 _root_.GD.N0120.d008813
    _root_.GD.N0120.d008811
  ring



theorem d008819
    (α β e : ℝ) (φ : ℝ × ℝ → ℝ) :
    _root_.GD.N0120.d008810 α β e φ =
      _root_.GD.N0120.d008813 α β e * _root_.GD.N0120.d008812 α β e φ := by
  unfold _root_.GD.N0120.d008810 _root_.GD.N0120.d008812
  simp_rw [_root_.GD.N0120.d008818]
  rw [← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro L _
  change
    (∫ F : ℝ in Ioi 0,
        φ (L, F) *
          (_root_.GD.N0120.d008813 α β e * _root_.GD.N0120.d008811 α β e (L, F)))
      =
    _root_.GD.N0120.d008813 α β e *
      ∫ F : ℝ in Ioi 0,
        φ (L, F) * _root_.GD.N0120.d008811 α β e (L, F)
  rw [← MeasureTheory.integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro F _
  ring


theorem d008820
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    0 < _root_.GD.N0116.d006506 α β := by
  unfold _root_.GD.N0116.d006506
  positivity


theorem d008821
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    0 < _root_.GD.N0116.d006507 α β := by
  unfold _root_.GD.N0116.d006507
  exact mul_pos (_root_.GD.N0120.d008820 hα hβ)
    (Real.Gamma_pos_of_pos (by positivity))


theorem d008822
    {α β e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    0 < _root_.GD.N0116.d006508 α β e := by
  unfold _root_.GD.N0116.d006508
  exact mul_pos (Real.rpow_pos_of_pos he0 _)
    (Real.rpow_pos_of_pos (sub_pos.mpr he1) _)



theorem d008823
    {α β e : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1) :
    0 < _root_.GD.N0120.d008813 α β e :=
  mul_pos (_root_.GD.N0120.d008821 hα hβ) (_root_.GD.N0120.d008822 he0 he1)








theorem d008824
    {α β e : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (φ : ℝ × ℝ → ℝ)
    (hTarget :
      IntegrableOn
        (fun p : _root_.GD.N0124.d006387 =>
          φ (p.1, p.2.1) *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        _root_.GD.N0124.d006389 volume)
    (hTargetIter :
      (∫ p : _root_.GD.N0124.d006387 in _root_.GD.N0124.d006389,
          φ (p.1, p.2.1) *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        =
      ∫ L : ℝ in Ioo 0 1,
        ∫ F : ℝ in Ioi 0,
          ∫ H : ℝ in Ioi 0,
            φ (L, F) * (H ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (L, F, H))) :
    _root_.GD.N0120.d008809 α β e φ =
      _root_.GD.N0120.d008810 α β e φ := by
  let g : _root_.GD.N0124.d006387 → ℝ :=
    fun p =>
      φ ((_root_.GD.N0124.d006391 e p).1, (_root_.GD.N0124.d006391 e p).2.1) *
        _root_.GD.N0116.d006510 α β p
  have hCoV :
      (∫ p : _root_.GD.N0124.d006387 in _root_.GD.N0124.d006388, g p) =
        ∫ p : _root_.GD.N0124.d006387 in _root_.GD.N0124.d006389,
          (p.2.2 ^ 2 / (e * (1 - e))) * g (_root_.GD.N0124.d006392 e p) := by
    simpa only [smul_eq_mul] using
      (_root_.GD.N0123.d006497
        he0 he1 g)
  have hPoint :
      ∀ p ∈ _root_.GD.N0124.d006389,
        (p.2.2 ^ 2 / (e * (1 - e))) * g (_root_.GD.N0124.d006392 e p) =
          φ (p.1, p.2.1) *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p) := by
    intro p hp
    dsimp [g]
    rw [show
      ((_root_.GD.N0124.d006391 e (_root_.GD.N0124.d006392 e p)).1,
          (_root_.GD.N0124.d006391 e (_root_.GD.N0124.d006392 e p)).2.1) = (p.1, p.2.1) by
      rw [_root_.GD.N0124.d006397 he0 he1 hp]]
    ring
  have hTarget' :
      IntegrableOn
        (fun p : _root_.GD.N0124.d006387 =>
          (p.2.2 ^ 2 / (e * (1 - e))) * g (_root_.GD.N0124.d006392 e p))
        _root_.GD.N0124.d006389 volume := by
    exact hTarget.congr
      ((ae_restrict_iff' _root_.GD.N0123.d006492).2
        (Filter.Eventually.of_forall fun p hp => (hPoint p hp).symm))
  unfold _root_.GD.N0120.d008809 _root_.GD.N0120.d008810
  change (∫ p : _root_.GD.N0124.d006387 in _root_.GD.N0124.d006388, g p) = _
  rw [hCoV]
  rw [setIntegral_congr_fun
    _root_.GD.N0123.d006492 hPoint]
  rw [hTargetIter]
  exact _root_.GD.N0116.d006517
    hα hβ he0 he1 φ



theorem d008825
    {α β e : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (q : ℝ × ℝ → ℝ)
    (hTarget :
      IntegrableOn
        (fun p : _root_.GD.N0124.d006387 =>
          ((p.1 - e) * q (p.1, p.2.1)) *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        _root_.GD.N0124.d006389 volume)
    (hTargetIter :
      (∫ p : _root_.GD.N0124.d006387 in _root_.GD.N0124.d006389,
          ((p.1 - e) * q (p.1, p.2.1)) *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        =
      ∫ L : ℝ in Ioo 0 1,
        ∫ F : ℝ in Ioi 0,
          ∫ H : ℝ in Ioi 0,
            ((L - e) * q (L, F)) *
              (H ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (L, F, H))) :
    _root_.GD.N0120.d008814 α β e q =
      _root_.GD.N0120.d008813 α β e * _root_.GD.N0120.d008816 α β e q := by
  rw [_root_.GD.N0120.d008814, _root_.GD.N0120.d008824
    hα hβ he0 he1 _ hTarget hTargetIter]
  exact _root_.GD.N0120.d008819
    α β e _



theorem d008826
    {α β e : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (q : ℝ × ℝ → ℝ)
    (hTarget :
      IntegrableOn
        (fun p : _root_.GD.N0124.d006387 =>
          q (p.1, p.2.1) ^ 2 *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        _root_.GD.N0124.d006389 volume)
    (hTargetIter :
      (∫ p : _root_.GD.N0124.d006387 in _root_.GD.N0124.d006389,
          q (p.1, p.2.1) ^ 2 *
            (p.2.2 ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
        =
      ∫ L : ℝ in Ioo 0 1,
        ∫ F : ℝ in Ioi 0,
          ∫ H : ℝ in Ioi 0,
            q (L, F) ^ 2 *
              (H ^ 2 / (e * (1 - e))) *
              _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (L, F, H))) :
    _root_.GD.N0120.d008815 α β e q =
      _root_.GD.N0120.d008813 α β e * _root_.GD.N0120.d008817 α β e q := by
  rw [_root_.GD.N0120.d008815, _root_.GD.N0120.d008824
    hα hβ he0 he1 _ hTarget hTargetIter]
  exact _root_.GD.N0120.d008819
    α β e _







theorem d008827
    (f : ℝ → ℝ) {sourceValue gaussianValue : ℝ}
    (hf : Integrable
      (fun z : ℝ =>
        z ^ 2 * ProbabilityTheory.gaussianPDFReal 0 1 z * f (z ^ 2)))
    (hGaussian :
      gaussianValue =
        ∫ z : ℝ, z ^ 2 * f (z ^ 2)
          ∂ProbabilityTheory.gaussianReal 0 1)
    (hResidual :
      (∫ w : ℝ in Ioi 0,
          _root_.GD.N0122.d006380 w * f w)
        = sourceValue) :
    gaussianValue = sourceValue := by
  rw [hGaussian,
    _root_.GD.N0122.d006386 f hf,
    hResidual]



variable {Ω : Type*} [MeasurableSpace Ω]











theorem d008828
    {P : Measure Ω} [IsProbabilityMeasure P]
    {U D L F : Ω → ℝ}
    {α β e Sigma : ℝ}
    (q : ℝ × ℝ → ℝ)
    (traceConditional energyConditional : ℝ → ℝ)
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
    (hTraceGaussian :
      _root_.GD.N0141.d006687 P D L (fun ω => q (L ω, F ω)) e =
        Sigma *
          ∫ z : ℝ, z ^ 2 * traceConditional (z ^ 2)
            ∂ProbabilityTheory.gaussianReal 0 1)
    (hEnergyGaussian :
      _root_.GD.N0141.d006688 P D (fun ω => q (L ω, F ω)) =
        Sigma *
          ∫ z : ℝ, z ^ 2 * energyConditional (z ^ 2)
            ∂ProbabilityTheory.gaussianReal 0 1)
    (hTraceResidual :
      (∫ w : ℝ in Ioi 0,
          _root_.GD.N0122.d006380 w *
            traceConditional w)
        = _root_.GD.N0120.d008814 α β e q)
    (hEnergyResidual :
      (∫ w : ℝ in Ioi 0,
          _root_.GD.N0122.d006380 w *
            energyConditional w)
        = _root_.GD.N0120.d008815 α β e q)
    (hTraceBiasIntegrable :
      Integrable
        (fun z : ℝ =>
          z ^ 2 * ProbabilityTheory.gaussianPDFReal 0 1 z *
            traceConditional (z ^ 2)))
    (hEnergyBiasIntegrable :
      Integrable
        (fun z : ℝ =>
          z ^ 2 * ProbabilityTheory.gaussianPDFReal 0 1 z *
            energyConditional (z ^ 2)))
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
  let A : ℝ := Sigma * _root_.GD.N0120.d008813 α β e
  have hA : 0 < A :=
    mul_pos hSigma (_root_.GD.N0120.d008823 hα hβ he0 he1)
  have hTraceSource :
      _root_.GD.N0141.d006687 P D L (fun ω => q (L ω, F ω)) e =
        Sigma * _root_.GD.N0120.d008814 α β e q := by
    rw [hTraceGaussian]
    congr 1
    exact _root_.GD.N0120.d008827
      traceConditional hTraceBiasIntegrable rfl hTraceResidual
  have hEnergySource :
      _root_.GD.N0141.d006688 P D (fun ω => q (L ω, F ω)) =
        Sigma * _root_.GD.N0120.d008815 α β e q := by
    rw [hEnergyGaussian]
    congr 1
    exact _root_.GD.N0120.d008827
      energyConditional hEnergyBiasIntegrable rfl hEnergyResidual
  have hTraceActual :
      _root_.GD.N0141.d006687 P D L (fun ω => q (L ω, F ω)) e =
        A * (atomic + smear + densityError) := by
    rw [hTraceSource,
      _root_.GD.N0120.d008825
        hα hβ he0 he1 q hTraceTarget hTraceTargetIter,
      hReducedTrace]
    dsimp [A]
    ring
  have hEnergyActual :
      _root_.GD.N0141.d006688 P D (fun ω => q (L ω, F ω)) =
        A * energy := by
    rw [hEnergySource,
      _root_.GD.N0120.d008826
        hα hβ he0 he1 q hEnergyTarget hEnergyTargetIter,
      hReducedEnergy]
    dsimp [A]
    ring
  have hqPair :
      Measurable (fun p : ℝ × (ℝ × ℝ) => q p.2) :=
    hq.comp measurable_snd
  have hRiskIdentity :
      _root_.GD.N0141.d006684 P
          (_root_.GD.N0141.d006686 U D L (fun ω => q (L ω, F ω))
            e ((A * C / 2) / (A * M)))
          - _root_.GD.N0141.d006684 P (_root_.GD.N0141.d006685 U D L e) =
        2 * ((A * C / 2) / (A * M)) *
            _root_.GD.N0141.d006687 P D L (fun ω => q (L ω, F ω)) e
          + ((A * C / 2) / (A * M)) ^ 2 *
            _root_.GD.N0141.d006688 P D (fun ω => q (L ω, F ω)) := by
    have hBridge :=
      _root_.GD.N0144.d006723
        (P := P) (U := U) (D := D) (L := L)
        (Sobs := fun ω => (L ω, F ω))
        (q := fun p : ℝ × (ℝ × ℝ) => q p.2)
        (e := e) (ε := (A * C / 2) / (A * M))
        hqPair hU hWeight
        (by
          convert hCarrier using 1
          rfl)
        hIndep hCentered
    have hCorrected :
        _root_.GD.N0141.d006686 U D L (fun ω => q (L ω, F ω))
            e ((A * C / 2) / (A * M)) =
          fun ω =>
            _root_.GD.N0141.d006685 U D L e ω +
              ((A * C / 2) / (A * M)) *
                (D ω * q (L ω, F ω)) := by
      funext ω
      unfold _root_.GD.N0141.d006686
      ring
    rw [hCorrected]
    exact hBridge
  have hScaled :=
    _root_.GD.N0148.d008808
      (P := P) (U := U) (D := D) (L := L)
      (q := fun ω => q (L ω, F ω)) (e := e)
      (atomic := A * atomic) (smear := A * smear)
      (densityError := A * densityError) (energy := A * energy)
      (C := A * C) (M := A * M)
      (mul_pos hA hC) (mul_pos hA hM)
      (by
        have := mul_le_mul_of_nonneg_left hAtomic hA.le
        nlinarith)
      (by
        rw [abs_mul, abs_of_pos hA]
        calc
          A * |smear| ≤ A * (C / 16) :=
            mul_le_mul_of_nonneg_left hSmear hA.le
          _ = A * C / 16 := by ring)
      (by
        rw [abs_mul, abs_of_pos hA]
        calc
          A * |densityError| ≤ A * (C / 16) :=
            mul_le_mul_of_nonneg_left hDensity hA.le
          _ = A * C / 16 := by ring)
      (by rw [hTraceActual]; ring)
      hEnergyActual
      (mul_le_mul_of_nonneg_left hEnergyCeiling hA.le)
      hRiskIdentity
  have hStep :
      (A * C / 2) / (A * M) = (C / 2) / M := by
    field_simp [ne_of_gt hA, ne_of_gt hM]
  simpa [hStep] using hScaled

end

end GD.N0120
