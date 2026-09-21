import GD.Module0612



















open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0108

noncomputable section

open _root_.GD.N0124
open _root_.GD.N0123
open _root_.GD.N0116
open _root_.GD.N0120
open _root_.GD.N0125



theorem d008880
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {p : _root_.GD.N0124.d006387} (hp : p ∈ _root_.GD.N0124.d006388) :
    0 ≤ _root_.GD.N0116.d006510 α β p := by
  unfold _root_.GD.N0116.d006510 _root_.GD.N0116.d006506 _root_.GD.N0123.d006499
  have hGa : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  have hGb : 0 < Real.Gamma β := Real.Gamma_pos_of_pos hβ
  have hG3 : 0 < Real.Gamma ((3 : ℝ) / 2) :=
    Real.Gamma_pos_of_pos (by norm_num)
  have h2 : 0 < (2 : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hx : 0 ≤ p.1 ^ (α - 1) :=
    Real.rpow_nonneg hp.1.le _
  have hy : 0 ≤ p.2.1 ^ (β - 1) :=
    Real.rpow_nonneg hp.2.1.le _
  have hw : 0 ≤ p.2.2 ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg hp.2.2.le _
  positivity


theorem d008881
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsProbabilityMeasure (_root_.GD.N0125.d008848 α β) := by
  rw [← _root_.GD.N0125.d008873 hα hβ]
  unfold _root_.GD.N0125.d008852 _root_.GD.N0125.d008851
  letI : IsProbabilityMeasure (gammaMeasure α α) :=
    isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure (gammaMeasure β β) :=
    isProbabilityMeasure_gammaMeasure hβ hβ
  letI : IsProbabilityMeasure
      (gammaMeasure ((3 : ℝ) / 2) ((1 : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  infer_instance





theorem d008882
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IntegrableOn (_root_.GD.N0116.d006510 α β) _root_.GD.N0124.d006388 volume := by
  letI : IsProbabilityMeasure (_root_.GD.N0125.d008848 α β) :=
    _root_.GD.N0108.d008881 hα hβ
  have hone :
      Integrable (fun _ : _root_.GD.N0124.d006387 => (1 : ℝ)) (_root_.GD.N0125.d008848 α β) :=
    integrable_const 1
  have hdens :
      Integrable
        (fun p : _root_.GD.N0124.d006387 =>
          (ENNReal.ofReal (_root_.GD.N0116.d006510 α β p)).toReal • (1 : ℝ))
        (volume.restrict _root_.GD.N0124.d006388) := by
    apply
      (integrable_withDensity_iff_integrable_smul₀'
        (μ := volume.restrict _root_.GD.N0124.d006388)
        (f := fun p : _root_.GD.N0124.d006387 => ENNReal.ofReal (_root_.GD.N0116.d006510 α β p))
        (by
          unfold _root_.GD.N0116.d006510 _root_.GD.N0116.d006506 _root_.GD.N0123.d006499
          fun_prop)
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp
    simpa [_root_.GD.N0125.d008848] using hone
  apply hdens.congr
  filter_upwards
    [ae_restrict_mem _root_.GD.N0123.d006491] with p hp
  rw [ENNReal.toReal_ofReal (_root_.GD.N0108.d008880 hα hβ hp)]
  simp



theorem d008883
    {α β e C : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ)
    (hC :
      ∀ L ∈ Ioo (0 : ℝ) 1, ∀ F ∈ Ioi (0 : ℝ),
        |φ (L, F)| ≤ C) :
    IntegrableOn
      (fun p : _root_.GD.N0124.d006387 =>
        φ ((_root_.GD.N0124.d006391 e p).1, (_root_.GD.N0124.d006391 e p).2.1) *
          _root_.GD.N0116.d006510 α β p)
      _root_.GD.N0124.d006388 volume := by
  have hdens := _root_.GD.N0108.d008882 hα hβ
  apply hdens.bdd_mul
  · exact
      (hφ.comp
        ((_root_.GD.N0125.d008858 e).fst.prodMk
          ((_root_.GD.N0125.d008858 e).snd.fst))).aestronglyMeasurable
  · filter_upwards
      [ae_restrict_mem _root_.GD.N0123.d006491] with p hp
    have htarget := _root_.GD.N0124.d006394 he0 he1 hp
    simpa only [Real.norm_eq_abs] using
      hC (_root_.GD.N0124.d006391 e p).1 ⟨htarget.1, htarget.2.1⟩
        (_root_.GD.N0124.d006391 e p).2.1 htarget.2.2.1



theorem d008884
    {α β e C : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ)
    (hC :
      ∀ L ∈ Ioo (0 : ℝ) 1, ∀ F ∈ Ioi (0 : ℝ),
        |φ (L, F)| ≤ C) :
    IntegrableOn
      (fun p : _root_.GD.N0124.d006387 =>
        φ (p.1, p.2.1) *
          (p.2.2 ^ 2 / (e * (1 - e))) *
            _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
      _root_.GD.N0124.d006389 volume := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  letI : Measure.IsAddHaarMeasure (volume : Measure _root_.GD.N0124.d006387) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let g : _root_.GD.N0124.d006387 → ℝ :=
    fun p =>
      φ ((_root_.GD.N0124.d006391 e p).1, (_root_.GD.N0124.d006391 e p).2.1) *
        _root_.GD.N0116.d006510 α β p
  have hsource : IntegrableOn g _root_.GD.N0124.d006388 volume :=
    _root_.GD.N0108.d008883 hα hβ he0 he1 φ hφ hC
  have htransport :
      IntegrableOn
        (fun p : _root_.GD.N0124.d006387 =>
          |(_root_.GD.N0124.d006409 e p).det| •
            g (_root_.GD.N0124.d006392 e p))
        _root_.GD.N0124.d006389 volume := by
    have hiff :=
      MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
        (μ := volume)
        _root_.GD.N0123.d006492
        (fun p _ =>
          (_root_.GD.N0124.d006411 e p).hasFDerivWithinAt)
        (_root_.GD.N0123.d006494 he0 he1)
        g
    apply hiff.mp
    rw [_root_.GD.N0123.d006493 he0 he1]
    exact hsource
  apply htransport.congr_fun
  · intro p hp
    dsimp [g]
    rw [_root_.GD.N0123.d006496 he0 he1 hp]
    rw [show
      ((_root_.GD.N0124.d006391 e (_root_.GD.N0124.d006392 e p)).1,
          (_root_.GD.N0124.d006391 e (_root_.GD.N0124.d006392 e p)).2.1) = (p.1, p.2.1) by
      rw [_root_.GD.N0124.d006397 he0 he1 hp]]
    ring
  · exact _root_.GD.N0123.d006492


theorem d008885
    {α β e C : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ)
    (hC : ∀ p, |φ p| ≤ C) :
    IntegrableOn
      (fun p : _root_.GD.N0124.d006387 =>
        φ (p.1, p.2.1) *
          (p.2.2 ^ 2 / (e * (1 - e))) *
            _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
      _root_.GD.N0124.d006389 volume :=
  _root_.GD.N0108.d008884
    hα hβ he0 he1 φ hφ
      (fun L _ F _ => hC (L, F))



theorem d008886
    {α β e Q : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q)
    (hQ : ∀ p, |q p| ≤ Q) :
    IntegrableOn
      (fun p : _root_.GD.N0124.d006387 =>
        ((p.1 - e) * q (p.1, p.2.1)) *
          (p.2.2 ^ 2 / (e * (1 - e))) *
            _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
      _root_.GD.N0124.d006389 volume := by
  apply _root_.GD.N0108.d008884
    hα hβ he0 he1 (fun p => (p.1 - e) * q p)
  · fun_prop
  · intro L hL F hF
    rw [abs_mul]
    have hLe : |L - e| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hL.1, hL.2]
    calc
      |L - e| * |q (L, F)| ≤ 1 * Q :=
        mul_le_mul hLe (hQ (L, F)) (abs_nonneg _) (by positivity)
      _ = Q := one_mul Q



theorem d008887
    {α β e Q : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q)
    (hQ : ∀ p, |q p| ≤ Q) :
    IntegrableOn
      (fun p : _root_.GD.N0124.d006387 =>
        q (p.1, p.2.1) ^ 2 *
          (p.2.2 ^ 2 / (e * (1 - e))) *
            _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p))
      _root_.GD.N0124.d006389 volume := by
  apply _root_.GD.N0108.d008884
    (C := Q ^ 2) hα hβ he0 he1 (fun p => q p ^ 2)
  · fun_prop
  · intro L hL F hF
    rw [abs_sq]
    calc
      q (L, F) ^ 2 = |q (L, F)| ^ 2 := (sq_abs _).symm
      _ ≤ Q ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hQ (L, F)) 2

end

end GD.N0108
