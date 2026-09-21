import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space






























open Function MeasureTheory
open scoped NNReal ENNReal InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0233
namespace N0727

noncomputable section

variable {E Z : Type*} [MeasurableSpace E] [MeasurableSpace Z]





def d003202 (w : E → ℝ≥0) : E → ℝ≥0∞ :=
  fun e ↦ (w e ^ 2 : ℝ≥0)

theorem d003203 {w : E → ℝ≥0} (hw : Measurable w) :
    Measurable (_root_.GD.N0233.N0727.d003202 w) := by
  exact (hw.pow_const 2).coe_nnreal_ennreal

@[simp]
theorem d003204 {w : E → ℝ≥0}
    (hw0 : ∀ e, w e ≠ 0) (e : E) : _root_.GD.N0233.N0727.d003202 w e ≠ 0 := by
  simp [_root_.GD.N0233.N0727.d003202, hw0 e]

@[simp]
theorem d003205 (w : E → ℝ≥0) (e : E) :
    _root_.GD.N0233.N0727.d003202 w e ≠ ∞ := by
  simp [_root_.GD.N0233.N0727.d003202]


theorem d003206 (mu : Measure E) (f : Lp ℝ 2 mu) :
    ‖f‖ ^ 2 = ∫ e, (f e) ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  congr 1
  funext e
  simp [pow_two]





theorem d003207
    (mu : Measure E) {w : E → ℝ≥0} (hw : Measurable w)
    (hw0 : ∀ e, w e ≠ 0)
    (u : Lp ℝ 2 (mu.withDensity (_root_.GD.N0233.N0727.d003202 w))) :
    MemLp (fun e ↦ (w e : ℝ) * u e) 2 mu := by
  have hdmeas : Measurable (_root_.GD.N0233.N0727.d003202 w) := _root_.GD.N0233.N0727.d003203 hw
  have hd0 : ∀ᵐ e ∂mu, _root_.GD.N0233.N0727.d003202 w e ≠ 0 :=
    ae_of_all mu (_root_.GD.N0233.N0727.d003204 hw0)
  have hmu_ac : mu ≪ mu.withDensity (_root_.GD.N0233.N0727.d003202 w) :=
    withDensity_absolutelyContinuous' hdmeas.aemeasurable hd0
  have hu_meas : AEStronglyMeasurable (fun e ↦ u e) mu :=
    (Lp.aestronglyMeasurable u).mono_ac hmu_ac
  have hraw_meas : AEStronglyMeasurable (fun e ↦ (w e : ℝ) * u e) mu :=
    hw.coe_nnreal_real.aestronglyMeasurable.mul hu_meas
  rw [memLp_two_iff_integrable_sq hraw_meas]
  have hu_sq : Integrable (fun e ↦ (u e) ^ 2)
      (mu.withDensity (_root_.GD.N0233.N0727.d003202 w)) := (Lp.memLp u).integrable_sq
  have hweighted : Integrable
      (fun e ↦ ((w e ^ 2 : ℝ≥0) : ℝ) * (u e) ^ 2) mu := by
    have h := (integrable_withDensity_iff_integrable_coe_smul
      (hw.pow_const 2) (μ := mu)).1 hu_sq
    simpa [smul_eq_mul] using h
  exact hweighted.congr (ae_of_all mu fun e ↦ by
    change (((w e : ℝ) ^ 2) * (u e) ^ 2) =
      (((w e : ℝ) * u e) ^ 2)
    ring)



def d003208
    (mu : Measure E) {w : E → ℝ≥0} (hw : Measurable w)
    (hw0 : ∀ e, w e ≠ 0) :
    Lp ℝ 2 (mu.withDensity (_root_.GD.N0233.N0727.d003202 w)) →ₗᵢ[ℝ] Lp ℝ 2 mu where
  toFun u := (_root_.GD.N0233.N0727.d003207 mu hw hw0 u).toLp _
  map_add' := by
    intro u v
    apply Lp.ext
    have hdmeas : Measurable (_root_.GD.N0233.N0727.d003202 w) := _root_.GD.N0233.N0727.d003203 hw
    have hd0 : ∀ᵐ e ∂mu, _root_.GD.N0233.N0727.d003202 w e ≠ 0 :=
      ae_of_all mu (_root_.GD.N0233.N0727.d003204 hw0)
    have hadd_uv : (fun e ↦ (u + v) e) =ᵐ[mu] fun e ↦ u e + v e :=
      (withDensity_ae_eq hdmeas.aemeasurable hd0).1 (Lp.coeFn_add u v)
    filter_upwards
      [(_root_.GD.N0233.N0727.d003207 mu hw hw0 (u + v)).coeFn_toLp,
       (_root_.GD.N0233.N0727.d003207 mu hw hw0 u).coeFn_toLp,
       (_root_.GD.N0233.N0727.d003207 mu hw hw0 v).coeFn_toLp,
       Lp.coeFn_add
         ((_root_.GD.N0233.N0727.d003207 mu hw hw0 u).toLp _)
         ((_root_.GD.N0233.N0727.d003207 mu hw hw0 v).toLp _),
       hadd_uv]
      with e hout hu hv hout_add hadd
    rw [hout, hadd, hout_add, Pi.add_apply, hu, hv]
    ring
  map_smul' := by
    intro c u
    apply Lp.ext
    have hdmeas : Measurable (_root_.GD.N0233.N0727.d003202 w) := _root_.GD.N0233.N0727.d003203 hw
    have hd0 : ∀ᵐ e ∂mu, _root_.GD.N0233.N0727.d003202 w e ≠ 0 :=
      ae_of_all mu (_root_.GD.N0233.N0727.d003204 hw0)
    have hsmul_u : (fun e ↦ (c • u) e) =ᵐ[mu] fun e ↦ c * u e :=
      (withDensity_ae_eq hdmeas.aemeasurable hd0).1 (Lp.coeFn_smul c u)
    filter_upwards
      [(_root_.GD.N0233.N0727.d003207 mu hw hw0 (c • u)).coeFn_toLp,
       (_root_.GD.N0233.N0727.d003207 mu hw hw0 u).coeFn_toLp,
       Lp.coeFn_smul c
         ((_root_.GD.N0233.N0727.d003207 mu hw hw0 u).toLp _),
       hsmul_u]
      with e hout hu hout_smul hsmul
    rw [RingHom.id_apply, hout, hout_smul, Pi.smul_apply, hu, hsmul]
    simp only [smul_eq_mul]
    ring
  norm_map' := by
    intro u
    have hmem := _root_.GD.N0233.N0727.d003207 mu hw hw0 u
    have hsquares :
        ‖hmem.toLp (fun e ↦ (w e : ℝ) * u e)‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [_root_.GD.N0233.N0727.d003206, _root_.GD.N0233.N0727.d003206]
      rw [integral_withDensity_eq_integral_toReal_smul
        (_root_.GD.N0233.N0727.d003203 hw)
        (ae_of_all mu fun e ↦
          (lt_top_iff_ne_top.mpr (_root_.GD.N0233.N0727.d003205 w e)))]
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp] with e he
      rw [he]
      simp only [_root_.GD.N0233.N0727.d003202, ENNReal.coe_pow,
        ENNReal.toReal_pow, ENNReal.coe_toReal,
        smul_eq_mul]
      change (((w e : ℝ) * u e) ^ 2) =
        ((w e : ℝ) ^ 2) * (u e) ^ 2
      ring
    change ‖hmem.toLp (fun e ↦ (w e : ℝ) * u e)‖ = ‖u‖
    nlinarith [norm_nonneg (hmem.toLp (fun e ↦ (w e : ℝ) * u e)),
      norm_nonneg u]

theorem d003209
    (mu : Measure E) {w : E → ℝ≥0} (hw : Measurable w)
    (hw0 : ∀ e, w e ≠ 0)
    (u : Lp ℝ 2 (mu.withDensity (_root_.GD.N0233.N0727.d003202 w))) :
    (fun e ↦ _root_.GD.N0233.N0727.d003208 mu hw hw0 u e) =ᵐ[mu]
      fun e ↦ (w e : ℝ) * u e :=
  (_root_.GD.N0233.N0727.d003207 mu hw hw0 u).coeFn_toLp



section ModularInvolution

variable (mu : Measure E)
variable (R : E ≃ᵐ E)
variable (w : E → ℝ≥0)
variable (hw : Measurable w)
variable (hw0 : ∀ e, w e ≠ 0)
variable (hpush : mu.map R = mu.withDensity (_root_.GD.N0233.N0727.d003202 w))
variable (hRself : R.symm = R)
variable (hwR : ∀ e, (w (R e) : ℝ) * (w e : ℝ) = 1)



def d003210 :
    MeasurePreserving R mu (mu.withDensity (_root_.GD.N0233.N0727.d003202 w)) :=
  ⟨R.measurable, hpush⟩


def d003211 :
    MeasurePreserving R
      (mu.withDensity (_root_.GD.N0233.N0727.d003202 w)) mu := by
  have h := (_root_.GD.N0233.N0727.d003210 mu R w hpush).symm R
  simpa [hRself] using h



def d003212 :
    Lp ℝ 2 mu →ₗᵢ[ℝ] Lp ℝ 2 (mu.withDensity (_root_.GD.N0233.N0727.d003202 w)) :=
  Lp.compMeasurePreservingₗᵢ ℝ R
    (_root_.GD.N0233.N0727.d003211
      mu R w hpush hRself)


def d003213 : Lp ℝ 2 mu →ₗᵢ[ℝ] Lp ℝ 2 mu :=
  (_root_.GD.N0233.N0727.d003208 mu hw hw0).comp
    (_root_.GD.N0233.N0727.d003212 mu R w hpush hRself)

theorem d003214
    (u : Lp ℝ 2 mu) :
    (fun e ↦ _root_.GD.N0233.N0727.d003213
      mu R w hw hw0 hpush hRself u e) =ᵐ[mu]
      fun e ↦ (w e : ℝ) * u (R e) := by
  have houter := _root_.GD.N0233.N0727.d003209
    mu hw hw0
    (_root_.GD.N0233.N0727.d003212
      mu R w hpush hRself u)
  have hinner := Lp.coeFn_compMeasurePreserving u
    (_root_.GD.N0233.N0727.d003211
      mu R w hpush hRself)
  have hd0 : ∀ᵐ e ∂mu, _root_.GD.N0233.N0727.d003202 w e ≠ 0 :=
    ae_of_all mu (_root_.GD.N0233.N0727.d003204 hw0)
  have hinner_mu :
      (fun e ↦ _root_.GD.N0233.N0727.d003212
        mu R w hpush hRself u e) =ᵐ[mu] fun e ↦ u (R e) :=
    (withDensity_ae_eq
      (_root_.GD.N0233.N0727.d003203 hw).aemeasurable hd0).1 hinner
  filter_upwards [houter, hinner_mu] with e houter_e hinner_e
  change
    _root_.GD.N0233.N0727.d003208 mu hw hw0
        (_root_.GD.N0233.N0727.d003212
          mu R w hpush hRself u) e =
      (w e : ℝ) * u (R e)
  rw [houter_e]
  congr 1

include hwR


@[simp]
theorem d003215
    (u : Lp ℝ 2 mu) :
    _root_.GD.N0233.N0727.d003213 mu R w hw hw0 hpush hRself
        (_root_.GD.N0233.N0727.d003213 mu R w hw hw0 hpush hRself u) = u := by
  apply Lp.ext
  have houter := _root_.GD.N0233.N0727.d003214
    mu R w hw hw0 hpush hRself
    (_root_.GD.N0233.N0727.d003213 mu R w hw hw0 hpush hRself u)
  have hinner0 := _root_.GD.N0233.N0727.d003214
    mu R w hw hw0 hpush hRself u
  have hqmp : Measure.QuasiMeasurePreserving R mu mu := by
    refine ⟨R.measurable, ?_⟩
    rw [hpush]
    exact withDensity_absolutelyContinuous _ _
  have hinner := hqmp.ae_eq_comp hinner0
  filter_upwards [houter, hinner] with e houter_e hinner_e
  rw [houter_e]
  simp only [Function.comp_apply] at hinner_e
  rw [hinner_e]
  have hRR : R (R e) = e := by
    have h := R.apply_symm_apply e
    simpa [hRself] using h
  rw [hRR]
  calc
    (w e : ℝ) * ((w (R e) : ℝ) * u e) =
        ((w (R e) : ℝ) * (w e : ℝ)) * u e := by ring
    _ = 1 * u e := by rw [hwR e]
    _ = u e := one_mul _


theorem d003216 :
    (_root_.GD.N0233.N0727.d003213
      mu R w hw hw0 hpush hRself).toContinuousLinearMap.IsSymmetric := by
  intro u v
  let U := _root_.GD.N0233.N0727.d003213 mu R w hw hw0 hpush hRself
  calc
    inner ℝ (U.toContinuousLinearMap u) v =
        inner ℝ (U (U u)) (U v) := by
          exact (U.inner_map_map (U u) v).symm
    _ = inner ℝ u (U.toContinuousLinearMap v) := by
      rw [_root_.GD.N0233.N0727.d003215
        mu R w hw hw0 hpush hRself hwR]
      rfl

end ModularInvolution





section HilbertCompression

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

variable (S : H →ₗᵢ[ℝ] K)
variable (U : K →ₗᵢ[ℝ] K)
variable (hUinv : ∀ x, U (U x) = x)


def d003217 : H →ₗᵢ[ℝ] K := U.comp S


def d003218 : H →L[ℝ] H :=
  S.toContinuousLinearMap.adjoint.comp
    (_root_.GD.N0233.N0727.d003217 S U).toContinuousLinearMap

theorem d003219 (u : H) :
    _root_.GD.N0233.N0727.d003218 S U u =
      S.toContinuousLinearMap.adjoint (U (S u)) := rfl


theorem d003220 :
    ‖_root_.GD.N0233.N0727.d003218 S U‖ ≤ 1 := by
  calc
    ‖_root_.GD.N0233.N0727.d003218 S U‖ ≤
        ‖S.toContinuousLinearMap.adjoint‖ *
          ‖(_root_.GD.N0233.N0727.d003217 S U).toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (by simpa using S.norm_toContinuousLinearMap_le)
      (by simpa using (_root_.GD.N0233.N0727.d003217 S U).norm_toContinuousLinearMap_le)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

include hUinv


theorem d003221 :
    U.toContinuousLinearMap.IsSymmetric := by
  intro x y
  calc
    inner ℝ (U x) y = inner ℝ (U (U x)) (U y) := by
      exact (U.inner_map_map (U x) y).symm
    _ = inner ℝ x (U y) := by rw [hUinv x]


theorem d003222 :
    (_root_.GD.N0233.N0727.d003218 S U).IsSymmetric := by
  intro u v
  calc
    inner ℝ (_root_.GD.N0233.N0727.d003218 S U u) v =
        inner ℝ (U (S u)) (S v) := by
          exact S.toContinuousLinearMap.adjoint_inner_left
            v (U (S u))
    _ = inner ℝ (S u) (U (S v)) :=
      _root_.GD.N0233.N0727.d003221 U hUinv (S u) (S v)
    _ = inner ℝ u (_root_.GD.N0233.N0727.d003218 S U v) := by
      symm
      exact S.toContinuousLinearMap.adjoint_inner_right
        u (U (S v))


theorem d003223 :
    IsSelfAdjoint (_root_.GD.N0233.N0727.d003218 S U) :=
  (_root_.GD.N0233.N0727.d003222 S U hUinv).isSelfAdjoint

omit hUinv


theorem d003224 (u : H) :
    (1 / 2 : ℝ) *
        ‖S u - _root_.GD.N0233.N0727.d003217 S U u‖ ^ 2 =
      ‖u‖ ^ 2 - inner ℝ u (_root_.GD.N0233.N0727.d003218 S U u) := by
  have hS : ‖S u‖ = ‖u‖ := S.norm_map u
  have hT : ‖_root_.GD.N0233.N0727.d003217 S U u‖ = ‖u‖ :=
    (_root_.GD.N0233.N0727.d003217 S U).norm_map u
  have hcross :
      inner ℝ (S u) (_root_.GD.N0233.N0727.d003217 S U u) =
        inner ℝ u (_root_.GD.N0233.N0727.d003218 S U u) := by
    symm
    exact S.toContinuousLinearMap.adjoint_inner_right u (U (S u))
  rw [norm_sub_sq_real, hS, hT, hcross]
  ring


theorem d003225 (u : H) :
    0 ≤ ‖u‖ ^ 2 - inner ℝ u (_root_.GD.N0233.N0727.d003218 S U u) := by
  rw [← _root_.GD.N0233.N0727.d003224 S U u]
  positivity

end HilbertCompression

end

end N0727
end N0233
end GD

#print axioms _root_.GD.N0233.N0727.d003208
#print axioms _root_.GD.N0233.N0727.d003215
#print axioms _root_.GD.N0233.N0727.d003223
#print axioms _root_.GD.N0233.N0727.d003224
