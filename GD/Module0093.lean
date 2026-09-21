import GD.Module0090
import Mathlib.MeasureTheory.Function.L2Space


















open Filter MeasureTheory Set Topology

namespace GD
namespace N0230
namespace N0691

noncomputable section

open _root_.GD.N0230.N0570
open _root_.GD.N0230.N0708

variable {Omega : Type*} [MeasurableSpace Omega]





theorem d001204
    (mu nu : Measure Omega) (f : Omega → ℝ) :
    MemLp f 2 (mu + nu) ↔ MemLp f 2 mu ∧ MemLp f 2 nu := by
  constructor
  · intro h
    exact ⟨h.left_of_add_measure, h.right_of_add_measure⟩
  · rintro ⟨hmu, hnu⟩
    have hmeas : AEStronglyMeasurable f (mu + nu) :=
      hmu.1.add_measure hnu.1
    rw [memLp_two_iff_integrable_sq hmeas]
    exact
      ((memLp_two_iff_integrable_sq hmu.1).1 hmu).add_measure
        ((memLp_two_iff_integrable_sq hnu.1).1 hnu)


noncomputable def d001205
    (mu nu : Measure Omega) :
    Lp ℝ 2 (mu + nu) →ₗ[ℝ] Lp ℝ 2 mu where
  toFun f := ((Lp.memLp f).left_of_add_measure).toLp f
  map_add' f g := by
    apply Lp.ext
    have hsumAc : mu ≪ mu + nu :=
      Measure.absolutelyContinuous_of_le
        (Measure.le_add_right (le_refl mu))
    filter_upwards
      [((Lp.memLp (f + g)).left_of_add_measure).coeFn_toLp,
       hsumAc.ae_le (Lp.coeFn_add f g),
       ((Lp.memLp f).left_of_add_measure).coeFn_toLp,
       ((Lp.memLp g).left_of_add_measure).coeFn_toLp,
       Lp.coeFn_add
         (((Lp.memLp f).left_of_add_measure).toLp f)
         (((Lp.memLp g).left_of_add_measure).toLp g)]
      with omega hfg hadd hf hg hout
    simp only [hfg, hadd, hf, hg, hout, Pi.add_apply]
  map_smul' c f := by
    apply Lp.ext
    have hsumAc : mu ≪ mu + nu :=
      Measure.absolutelyContinuous_of_le
        (Measure.le_add_right (le_refl mu))
    filter_upwards
      [((Lp.memLp (c • f)).left_of_add_measure).coeFn_toLp,
       hsumAc.ae_le (Lp.coeFn_smul c f),
       ((Lp.memLp f).left_of_add_measure).coeFn_toLp,
       Lp.coeFn_smul c (((Lp.memLp f).left_of_add_measure).toLp f)]
      with omega hcf hsmul hf hout
    simp only [RingHom.id_apply, hcf, hsmul, hf, hout, Pi.smul_apply,
      smul_eq_mul]


noncomputable def d001206
    (mu nu : Measure Omega) :
    Lp ℝ 2 (mu + nu) →ₗ[ℝ] Lp ℝ 2 nu where
  toFun f := ((Lp.memLp f).right_of_add_measure).toLp f
  map_add' f g := by
    apply Lp.ext
    have hsumAc : nu ≪ mu + nu :=
      Measure.absolutelyContinuous_of_le
        (Measure.le_add_left (le_refl nu))
    filter_upwards
      [((Lp.memLp (f + g)).right_of_add_measure).coeFn_toLp,
       hsumAc.ae_le (Lp.coeFn_add f g),
       ((Lp.memLp f).right_of_add_measure).coeFn_toLp,
       ((Lp.memLp g).right_of_add_measure).coeFn_toLp,
       Lp.coeFn_add
         (((Lp.memLp f).right_of_add_measure).toLp f)
         (((Lp.memLp g).right_of_add_measure).toLp g)]
      with omega hfg hadd hf hg hout
    simp only [hfg, hadd, hf, hg, hout, Pi.add_apply]
  map_smul' c f := by
    apply Lp.ext
    have hsumAc : nu ≪ mu + nu :=
      Measure.absolutelyContinuous_of_le
        (Measure.le_add_left (le_refl nu))
    filter_upwards
      [((Lp.memLp (c • f)).right_of_add_measure).coeFn_toLp,
       hsumAc.ae_le (Lp.coeFn_smul c f),
       ((Lp.memLp f).right_of_add_measure).coeFn_toLp,
       Lp.coeFn_smul c (((Lp.memLp f).right_of_add_measure).toLp f)]
      with omega hcf hsmul hf hout
    simp only [RingHom.id_apply, hcf, hsmul, hf, hout, Pi.smul_apply,
      smul_eq_mul]


theorem d001207
    (mu nu : Measure Omega) (f : Lp ℝ 2 (mu + nu)) :
    ‖_root_.GD.N0230.N0691.d001205 mu nu f‖ ≤ ‖f‖ := by
  change ‖((Lp.memLp f).left_of_add_measure).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_measure f
      (Measure.le_add_right (le_refl mu)))


theorem d001208
    (mu nu : Measure Omega) (f : Lp ℝ 2 (mu + nu)) :
    ‖_root_.GD.N0230.N0691.d001206 mu nu f‖ ≤ ‖f‖ := by
  change ‖((Lp.memLp f).right_of_add_measure).toLp f‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_measure f
      (Measure.le_add_left (le_refl nu)))


noncomputable def d001209
    (mu nu : Measure Omega) :
    Lp ℝ 2 (mu + nu) →L[ℝ] Lp ℝ 2 mu :=
  LinearMap.mkContinuous (_root_.GD.N0230.N0691.d001205 mu nu) 1
    (by simpa using _root_.GD.N0230.N0691.d001207 mu nu)


noncomputable def d001210
    (mu nu : Measure Omega) :
    Lp ℝ 2 (mu + nu) →L[ℝ] Lp ℝ 2 nu :=
  LinearMap.mkContinuous (_root_.GD.N0230.N0691.d001206 mu nu) 1
    (by simpa using _root_.GD.N0230.N0691.d001208 mu nu)

theorem d001211
    (mu nu : Measure Omega) (f : Lp ℝ 2 (mu + nu)) :
    _root_.GD.N0230.N0691.d001209 mu nu f =ᵐ[mu] f :=
  ((Lp.memLp f).left_of_add_measure).coeFn_toLp

theorem d001212
    (mu nu : Measure Omega) (f : Lp ℝ 2 (mu + nu)) :
    _root_.GD.N0230.N0691.d001210 mu nu f =ᵐ[nu] f :=
  ((Lp.memLp f).right_of_add_measure).coeFn_toLp




theorem d001213
    (mu : Measure Omega) (f : Lp ℝ 2 mu) :
    ‖f‖ ^ 2 = ∫ omega, (f omega) ^ 2 ∂mu := by
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  congr 1
  funext omega
  simp [pow_two]



theorem d001214
    (mu nu : Measure Omega) (f : Lp ℝ 2 (mu + nu)) :
    ‖f‖ ^ 2 =
      ‖_root_.GD.N0230.N0691.d001209 mu nu f‖ ^ 2 + ‖_root_.GD.N0230.N0691.d001210 mu nu f‖ ^ 2 := by
  have hmuMem : MemLp f 2 mu := (Lp.memLp f).left_of_add_measure
  have hnuMem : MemLp f 2 nu := (Lp.memLp f).right_of_add_measure
  have hmuInt : Integrable (fun omega ↦ (f omega) ^ 2) mu :=
    (memLp_two_iff_integrable_sq hmuMem.1).1 hmuMem
  have hnuInt : Integrable (fun omega ↦ (f omega) ^ 2) nu :=
    (memLp_two_iff_integrable_sq hnuMem.1).1 hnuMem
  rw [_root_.GD.N0230.N0691.d001213]
  rw [integral_add_measure hmuInt hnuInt]
  rw [_root_.GD.N0230.N0691.d001213, _root_.GD.N0230.N0691.d001213]
  congr 1
  · apply integral_congr_ae
    filter_upwards [_root_.GD.N0230.N0691.d001211 mu nu f] with omega homega
    rw [homega]
  · apply integral_congr_ae
    filter_upwards [_root_.GD.N0230.N0691.d001212 mu nu f] with omega homega
    rw [homega]



theorem d001215
    (mu nu : Measure Omega) (f : Lp ℝ 2 (mu + nu)) :
    ‖f‖ ≤ 2 *
      ‖((_root_.GD.N0230.N0691.d001209 mu nu).prod (_root_.GD.N0230.N0691.d001210 mu nu)) f‖ := by
  have hsplit := _root_.GD.N0230.N0691.d001214 mu nu f
  have hl : ‖_root_.GD.N0230.N0691.d001209 mu nu f‖ ≤
      ‖((_root_.GD.N0230.N0691.d001209 mu nu).prod (_root_.GD.N0230.N0691.d001210 mu nu)) f‖ := by
    simp only [ContinuousLinearMap.prod_apply, Prod.norm_def]
    exact le_max_left _ _
  have hr : ‖_root_.GD.N0230.N0691.d001210 mu nu f‖ ≤
      ‖((_root_.GD.N0230.N0691.d001209 mu nu).prod (_root_.GD.N0230.N0691.d001210 mu nu)) f‖ := by
    simp only [ContinuousLinearMap.prod_apply, Prod.norm_def]
    exact le_max_right _ _
  have hfnonneg : 0 ≤ ‖f‖ := norm_nonneg _
  have hjnonneg : 0 ≤
      ‖((_root_.GD.N0230.N0691.d001209 mu nu).prod (_root_.GD.N0230.N0691.d001210 mu nu)) f‖ := norm_nonneg _
  have hlsq : ‖_root_.GD.N0230.N0691.d001209 mu nu f‖ ^ 2 ≤
      ‖((_root_.GD.N0230.N0691.d001209 mu nu).prod (_root_.GD.N0230.N0691.d001210 mu nu)) f‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hjnonneg).2 hl
  have hrsq : ‖_root_.GD.N0230.N0691.d001210 mu nu f‖ ^ 2 ≤
      ‖((_root_.GD.N0230.N0691.d001209 mu nu).prod (_root_.GD.N0230.N0691.d001210 mu nu)) f‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hjnonneg).2 hr
  nlinarith



theorem d001216
    (mu nu : Measure Omega) :
    IsClosed (Set.range
      ((_root_.GD.N0230.N0691.d001209 mu nu).prod (_root_.GD.N0230.N0691.d001210 mu nu))) := by
  exact _root_.GD.N0230.N0570.d001195
    (_root_.GD.N0230.N0691.d001209 mu nu) (_root_.GD.N0230.N0691.d001210 mu nu) 2
    (by simpa using _root_.GD.N0230.N0691.d001215 mu nu)


theorem d001217
    (mu nu : Measure Omega)
    {I : Type*} {u : I → Lp ℝ 2 (mu + nu)} {l : Filter I} [NeBot l]
    {x : Lp ℝ 2 mu} {y : Lp ℝ 2 nu}
    (hx : _root_.GD.N0230.N0708.d001170 ℝ (fun i ↦ _root_.GD.N0230.N0691.d001209 mu nu (u i)) l x)
    (hy : _root_.GD.N0230.N0708.d001170 ℝ (fun i ↦ _root_.GD.N0230.N0691.d001210 mu nu (u i)) l y) :
    _root_.GD.N0230.N0708.d001177 (_root_.GD.N0230.N0691.d001209 mu nu) (_root_.GD.N0230.N0691.d001210 mu nu) x y := by
  exact _root_.GD.N0230.N0570.d001196
    (_root_.GD.N0230.N0691.d001209 mu nu) (_root_.GD.N0230.N0691.d001210 mu nu) 2
    (by simpa using _root_.GD.N0230.N0691.d001215 mu nu) hx hy





noncomputable def d001218
    (mu nu : Measure Omega) (f : Omega → ℝ)
    (hmu : MemLp f 2 mu) (hnu : MemLp f 2 nu) :
    Lp ℝ 2 (mu + nu) :=
  (_root_.GD.N0230.N0691.d001204 mu nu f).2 ⟨hmu, hnu⟩ |>.toLp f

theorem d001219
    (mu nu : Measure Omega) (f : Omega → ℝ)
    (hmu : MemLp f 2 mu) (hnu : MemLp f 2 nu) :
    _root_.GD.N0230.N0691.d001209 mu nu (_root_.GD.N0230.N0691.d001218 mu nu f hmu hnu) = hmu.toLp f := by
  apply Lp.ext
  filter_upwards
    [_root_.GD.N0230.N0691.d001211 mu nu (_root_.GD.N0230.N0691.d001218 mu nu f hmu hnu),
     hmu.coeFn_toLp,
     (Measure.absolutelyContinuous_of_le
       (Measure.le_add_right (le_refl mu))).ae_le
        ((_root_.GD.N0230.N0691.d001204 mu nu f).2 ⟨hmu, hnu⟩).coeFn_toLp]
    with omega hleft hend hsum
  have hcommon : _root_.GD.N0230.N0691.d001218 mu nu f hmu hnu omega = f omega := by
    simpa only [_root_.GD.N0230.N0691.d001218] using hsum
  rw [hleft, hcommon, hend]

theorem d001220
    (mu nu : Measure Omega) (f : Omega → ℝ)
    (hmu : MemLp f 2 mu) (hnu : MemLp f 2 nu) :
    _root_.GD.N0230.N0691.d001210 mu nu (_root_.GD.N0230.N0691.d001218 mu nu f hmu hnu) = hnu.toLp f := by
  apply Lp.ext
  filter_upwards
    [_root_.GD.N0230.N0691.d001212 mu nu (_root_.GD.N0230.N0691.d001218 mu nu f hmu hnu),
     hnu.coeFn_toLp,
     (Measure.absolutelyContinuous_of_le
       (Measure.le_add_left (le_refl nu))).ae_le
        ((_root_.GD.N0230.N0691.d001204 mu nu f).2 ⟨hmu, hnu⟩).coeFn_toLp]
    with omega hright hend hsum
  have hcommon : _root_.GD.N0230.N0691.d001218 mu nu f hmu hnu omega = f omega := by
    simpa only [_root_.GD.N0230.N0691.d001218] using hsum
  rw [hright, hcommon, hend]

end

end N0691
end N0230
end GD

#print axioms _root_.GD.N0230.N0691.d001204
#print axioms _root_.GD.N0230.N0691.d001214
#print axioms _root_.GD.N0230.N0691.d001216
#print axioms _root_.GD.N0230.N0691.d001217
#print axioms _root_.GD.N0230.N0691.d001219
#print axioms _root_.GD.N0230.N0691.d001220
