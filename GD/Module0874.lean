import GD.Module0236
import GD.Module0873

set_option warningAsError true















open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD
namespace N0228
namespace N0547
namespace N0796

noncomputable section

open _root_.GD.N0228.N0547.N0795
open _root_.GD.N0228.N0547.N0794
open _root_.GD.N0232.N0720.N1435



abbrev d013490 := ℝ × (ℝ × ℝ)


def d013491 : Set _root_.GD.N0228.N0547.N0796.d013490 :=
  Set.Ioi 0 ×ˢ (Set.Ioi 0 ×ˢ Set.Ioi 0)


def d013492 : Set _root_.GD.N0228.N0547.N0796.d013490 :=
  Set.Ioi 0 ×ˢ (Set.Ioo 0 1 ×ˢ Set.Ioi 0)

theorem d013493 : MeasurableSet _root_.GD.N0228.N0547.N0796.d013491 := by
  exact measurableSet_Ioi.prod (measurableSet_Ioi.prod measurableSet_Ioi)

theorem d013494 : MeasurableSet _root_.GD.N0228.N0547.N0796.d013492 := by
  exact measurableSet_Ioi.prod (measurableSet_Ioo.prod measurableSet_Ioi)


def d013495 : _root_.GD.N0232.N0720.N1435.d013432 ≃ᵐ _root_.GD.N0232.N0720.N1435.d013432 :=
  { toEquiv :=
      { toFun := fun u => ![u 2, u 1, u 0]
        invFun := fun u => ![u 2, u 1, u 0]
        left_inv := by
          intro u
          funext i
          fin_cases i <;> rfl
        right_inv := by
          intro u
          funext i
          fin_cases i <;> rfl }
    measurable_toFun := by
      apply measurable_pi_lambda
      intro i
      fin_cases i
      · change Measurable (fun u : _root_.GD.N0232.N0720.N1435.d013432 => u 2)
        exact measurable_pi_apply 2
      · change Measurable (fun u : _root_.GD.N0232.N0720.N1435.d013432 => u 1)
        exact measurable_pi_apply 1
      · change Measurable (fun u : _root_.GD.N0232.N0720.N1435.d013432 => u 0)
        exact measurable_pi_apply 0
    measurable_invFun := by
      apply measurable_pi_lambda
      intro i
      fin_cases i
      · change Measurable (fun u : _root_.GD.N0232.N0720.N1435.d013432 => u 2)
        exact measurable_pi_apply 2
      · change Measurable (fun u : _root_.GD.N0232.N0720.N1435.d013432 => u 1)
        exact measurable_pi_apply 1
      · change Measurable (fun u : _root_.GD.N0232.N0720.N1435.d013432 => u 0)
        exact measurable_pi_apply 0 }



def d013496 : _root_.GD.N0228.N0547.N0796.d013490 ≃ᵐ _root_.GD.N0232.N0720.N1435.d013432 :=
  _root_.GD.N0232.N0720.N1435.d013457.symm.trans _root_.GD.N0228.N0547.N0796.d013495

@[simp]
theorem d013497 (p : _root_.GD.N0228.N0547.N0796.d013490) :
    _root_.GD.N0228.N0547.N0796.d013496 p 0 = p.2.2 := by
  rfl

@[simp]
theorem d013498 (p : _root_.GD.N0228.N0547.N0796.d013490) :
    _root_.GD.N0228.N0547.N0796.d013496 p 1 = p.2.1 := by
  rfl

@[simp]
theorem d013499 (p : _root_.GD.N0228.N0547.N0796.d013490) :
    _root_.GD.N0228.N0547.N0796.d013496 p 2 = p.1 := by
  rfl



theorem d013500 :
    MeasurePreserving _root_.GD.N0228.N0547.N0796.d013496
      (volume : Measure _root_.GD.N0228.N0547.N0796.d013490) (volume : Measure _root_.GD.N0232.N0720.N1435.d013432) := by
  have hnested : MeasurePreserving _root_.GD.N0232.N0720.N1435.d013457.symm
      (volume : Measure _root_.GD.N0228.N0547.N0796.d013490) (volume : Measure _root_.GD.N0232.N0720.N1435.d013432) := by
    have h := _root_.GD.N0232.N0720.N1435.d013459
      (fun _ : Fin 3 => (volume : Measure ℝ))
    simpa [Measure.volume_eq_prod, volume_pi] using h
  have hreverse : MeasurePreserving _root_.GD.N0228.N0547.N0796.d013495
      (volume : Measure _root_.GD.N0232.N0720.N1435.d013432) (volume : Measure _root_.GD.N0232.N0720.N1435.d013432) := by
    have h := volume_measurePreserving_piCongrLeft
      (fun _ : Fin 3 => ℝ) (Equiv.swap (0 : Fin 3) 2)
    convert h using 1
    funext u i
    fin_cases i <;> rfl
  exact hreverse.comp hnested



theorem d013501 :
    _root_.GD.N0228.N0547.N0796.d013496 '' _root_.GD.N0228.N0547.N0796.d013491 = _root_.GD.N0232.N0720.N1435.d013433 := by
  ext u
  constructor
  · rintro ⟨p, hp, rfl⟩
    intro i
    fin_cases i
    · exact hp.2.2
    · exact hp.2.1
    · exact hp.1
  · intro hu
    let p : _root_.GD.N0228.N0547.N0796.d013490 := (u 2, (u 1, u 0))
    refine ⟨p, ?_, ?_⟩
    · exact ⟨hu 2, hu 1, hu 0⟩
    · funext i
      fin_cases i <;> simp [p]



theorem d013502 :
    _root_.GD.N0228.N0547.N0796.d013496 '' _root_.GD.N0228.N0547.N0796.d013492 = _root_.GD.N0232.N0720.N1435.d013434 := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨hp.2.2, hp.2.1.1, hp.2.1.2, hp.1⟩
  · intro hz
    let p : _root_.GD.N0228.N0547.N0796.d013490 := (z 2, (z 1, z 0))
    refine ⟨p, ?_, ?_⟩
    · exact ⟨hz.2.2.2, ⟨hz.2.1, hz.2.2.1⟩, hz.1⟩
    · funext i
      fin_cases i <;> simp [p]



theorem d013503 (p : _root_.GD.N0228.N0547.N0796.d013490) :
    _root_.GD.N0228.N0547.N0796.d013496 (_root_.GD.N0228.N0547.N0795.d003428 p) =
      _root_.GD.N0232.N0720.N1435.d013435 (_root_.GD.N0228.N0547.N0796.d013496 p) := by
  funext i
  fin_cases i <;>
    simp [_root_.GD.N0228.N0547.N0795.d003428, _root_.GD.N0228.N0547.N0795.d003425, _root_.GD.N0228.N0547.N0795.d003426, _root_.GD.N0228.N0547.N0795.d003427,
      _root_.GD.N0232.N0720.N1435.d013435] <;> ring_nf

@[simp]
theorem d013504 (p : _root_.GD.N0228.N0547.N0796.d013490) :
    _root_.GD.N0228.N0547.N0796.d013496.symm
        (_root_.GD.N0232.N0720.N1435.d013435 (_root_.GD.N0228.N0547.N0796.d013496 p)) =
      _root_.GD.N0228.N0547.N0795.d003428 p := by
  apply _root_.GD.N0228.N0547.N0796.d013496.injective
  rw [_root_.GD.N0228.N0547.N0796.d013496.apply_symm_apply]
  exact (_root_.GD.N0228.N0547.N0796.d013503 p).symm



theorem d013505
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : _root_.GD.N0228.N0547.N0796.d013490 → E) :
    (∫ q in _root_.GD.N0228.N0547.N0796.d013491, G q) =
      ∫ p in _root_.GD.N0228.N0547.N0796.d013492,
        (p.2.2) ^ 2 • G (_root_.GD.N0228.N0547.N0795.d003428 p) := by
  let F : _root_.GD.N0232.N0720.N1435.d013432 → E := fun u => G (_root_.GD.N0228.N0547.N0796.d013496.symm u)
  have hraw :
      (∫ u in _root_.GD.N0232.N0720.N1435.d013433, F u) =
        ∫ q in _root_.GD.N0228.N0547.N0796.d013491, G q := by
    rw [← _root_.GD.N0228.N0547.N0796.d013501]
    have h := _root_.GD.N0228.N0547.N0796.d013500.setIntegral_image_emb
      _root_.GD.N0228.N0547.N0796.d013496.measurableEmbedding F _root_.GD.N0228.N0547.N0796.d013491
    simpa [F] using h
  have hratio :
      (∫ z in _root_.GD.N0232.N0720.N1435.d013434,
          (z 0) ^ 2 • F (_root_.GD.N0232.N0720.N1435.d013435 z)) =
        ∫ p in _root_.GD.N0228.N0547.N0796.d013492,
          (p.2.2) ^ 2 • G (_root_.GD.N0228.N0547.N0795.d003428 p) := by
    rw [← _root_.GD.N0228.N0547.N0796.d013502]
    have h := _root_.GD.N0228.N0547.N0796.d013500.setIntegral_image_emb
      _root_.GD.N0228.N0547.N0796.d013496.measurableEmbedding
      (fun z => (z 0) ^ 2 • F (_root_.GD.N0232.N0720.N1435.d013435 z)) _root_.GD.N0228.N0547.N0796.d013492
    simpa only [F, _root_.GD.N0228.N0547.N0796.d013497,
      _root_.GD.N0228.N0547.N0796.d013504] using h
  rw [← hraw, _root_.GD.N0232.N0720.N1435.d013452 F, hratio]


theorem d013506
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : _root_.GD.N0228.N0547.N0796.d013490 → E) :
    IntegrableOn G _root_.GD.N0228.N0547.N0796.d013491 ↔
      IntegrableOn
        (fun p => (p.2.2) ^ 2 • G (_root_.GD.N0228.N0547.N0795.d003428 p))
        _root_.GD.N0228.N0547.N0796.d013492 := by
  let F : _root_.GD.N0232.N0720.N1435.d013432 → E := fun u => G (_root_.GD.N0228.N0547.N0796.d013496.symm u)
  have hraw :
      IntegrableOn F _root_.GD.N0232.N0720.N1435.d013433 ↔ IntegrableOn G _root_.GD.N0228.N0547.N0796.d013491 := by
    rw [← _root_.GD.N0228.N0547.N0796.d013501]
    have h := _root_.GD.N0228.N0547.N0796.d013500.integrableOn_image
      _root_.GD.N0228.N0547.N0796.d013496.measurableEmbedding
      (f := F) (s := _root_.GD.N0228.N0547.N0796.d013491)
    have hcomp : F ∘ _root_.GD.N0228.N0547.N0796.d013496 = G := by
      funext p
      simp [F]
    rw [hcomp] at h
    exact h
  have hchart :
      IntegrableOn F _root_.GD.N0232.N0720.N1435.d013433 ↔
        IntegrableOn (fun z => (z 0) ^ 2 • F (_root_.GD.N0232.N0720.N1435.d013435 z))
          _root_.GD.N0232.N0720.N1435.d013434 := by
    rw [← _root_.GD.N0232.N0720.N1435.d013445]
    have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
      (μ := (volume : Measure _root_.GD.N0232.N0720.N1435.d013432))
      _root_.GD.N0232.N0720.N1435.d013440
      (fun z _hz => (_root_.GD.N0232.N0720.N1435.d013449 z).hasFDerivWithinAt)
      _root_.GD.N0232.N0720.N1435.d013446 F
    apply h.trans
    apply integrableOn_congr_fun _ _root_.GD.N0232.N0720.N1435.d013440
    intro z hz
    change |(_root_.GD.N0232.N0720.N1435.d013448 z).det| • F (_root_.GD.N0232.N0720.N1435.d013435 z) =
      (z 0) ^ 2 • F (_root_.GD.N0232.N0720.N1435.d013435 z)
    rw [_root_.GD.N0232.N0720.N1435.d013451 hz]
  have hratio :
      IntegrableOn (fun z => (z 0) ^ 2 • F (_root_.GD.N0232.N0720.N1435.d013435 z))
          _root_.GD.N0232.N0720.N1435.d013434 ↔
        IntegrableOn
          (fun p => (p.2.2) ^ 2 • G (_root_.GD.N0228.N0547.N0795.d003428 p))
          _root_.GD.N0228.N0547.N0796.d013492 := by
    rw [← _root_.GD.N0228.N0547.N0796.d013502]
    let H : _root_.GD.N0232.N0720.N1435.d013432 → E :=
      fun z => (z 0) ^ 2 • F (_root_.GD.N0232.N0720.N1435.d013435 z)
    have h := _root_.GD.N0228.N0547.N0796.d013500.integrableOn_image
      _root_.GD.N0228.N0547.N0796.d013496.measurableEmbedding
      (f := H) (s := _root_.GD.N0228.N0547.N0796.d013492)
    have hcomp : H ∘ _root_.GD.N0228.N0547.N0796.d013496 =
        fun p => (p.2.2) ^ 2 • G (_root_.GD.N0228.N0547.N0795.d003428 p) := by
      funext p
      simp [H, F]
    rw [hcomp] at h
    exact h
  exact hraw.symm.trans (hchart.trans hratio)






def d013507 (α β ρ : ℝ) (q : _root_.GD.N0228.N0547.N0796.d013490) : ℝ :=
  gammaPDFReal (1 / 2) (1 / 2) q.1 *
    (gammaPDFReal α (1 / (2 * ρ)) q.2.1 *
      gammaPDFReal β (1 / (2 * (1 - ρ))) q.2.2)

@[fun_prop]
theorem d013508 (α β ρ : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0796.d013507 α β ρ) := by
  unfold _root_.GD.N0228.N0547.N0796.d013507
  fun_prop

theorem d013509
    {α β ρ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Integrable (_root_.GD.N0228.N0547.N0796.d013507 α β ρ) := by
  have h1ρ : 0 < 1 - ρ := sub_pos.mpr hρ1
  exact
    (_root_.GD.N0232.N0719.N0954.d009352
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2)).mul_prod
      ((_root_.GD.N0232.N0719.N0954.d009352
        hα (by positivity : 0 < (1 / (2 * ρ) : ℝ))).mul_prod
        (_root_.GD.N0232.N0719.N0954.d009352
          hβ (by positivity : 0 < (1 / (2 * (1 - ρ)) : ℝ))))

private theorem d013510
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ x : ℝ, gammaPDFReal a r x) = 1 := by
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  have h :=
    _root_.GD.N0232.N0719.N0954.d009351
      ha hr (fun _ : ℝ => (1 : ℝ))
  simpa using h.symm

private theorem d013511
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ x : ℝ in Set.Ioi 0, gammaPDFReal a r x) = 1 := by
  calc
    (∫ x : ℝ in Set.Ioi 0, gammaPDFReal a r x) =
        ∫ x : ℝ, gammaPDFReal a r x := by
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx hnot
      have hxlt : x < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hx
      simp [gammaPDFReal, not_le.mpr hxlt]
    _ = 1 := _root_.GD.N0228.N0547.N0796.d013510 ha hr


theorem d013512
    {α β ρ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∫ q in _root_.GD.N0228.N0547.N0796.d013491, _root_.GD.N0228.N0547.N0796.d013507 α β ρ q) = 1 := by
  have h1ρ : 0 < 1 - ρ := sub_pos.mpr hρ1
  change
    (∫ q in Set.Ioi (0 : ℝ) ×ˢ
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)),
        gammaPDFReal (1 / 2) (1 / 2) q.1 *
          (gammaPDFReal α (1 / (2 * ρ)) q.2.1 *
            gammaPDFReal β (1 / (2 * (1 - ρ))) q.2.2)
        ∂((volume : Measure ℝ).prod
          ((volume : Measure ℝ).prod (volume : Measure ℝ)))) = 1
  rw [setIntegral_prod_mul
      (gammaPDFReal (1 / 2) (1 / 2))
      (fun q : ℝ × ℝ =>
        gammaPDFReal α (1 / (2 * ρ)) q.1 *
          gammaPDFReal β (1 / (2 * (1 - ρ))) q.2)
      (Set.Ioi 0) (Set.Ioi 0 ×ˢ Set.Ioi 0),
    setIntegral_prod_mul
      (gammaPDFReal α (1 / (2 * ρ)))
      (gammaPDFReal β (1 / (2 * (1 - ρ))))
      (Set.Ioi 0) (Set.Ioi 0),
    _root_.GD.N0228.N0547.N0796.d013511
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2),
    _root_.GD.N0228.N0547.N0796.d013511 hα (by positivity),
    _root_.GD.N0228.N0547.N0796.d013511 hβ (by positivity)]
  norm_num

private theorem d013513
    {x a : ℝ} (hx : 0 < x) :
    (1 / (2 * x) : ℝ) ^ a =
      (2 : ℝ) ^ (-a) * x ^ (-a) := by
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1)
    (mul_nonneg (by norm_num) hx.le)]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le]
  simp only [Real.one_rpow, one_div]
  rw [mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_neg hx.le]




theorem d013514
    {α β ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {q : _root_.GD.N0228.N0547.N0796.d013490} (hT : 0 < q.1) (hU : 0 < q.2.1) (hV : 0 < q.2.2) :
    _root_.GD.N0228.N0547.N0796.d013507 α β ρ q =
      _root_.GD.N0228.N0547.N0795.d003449 α β ρ *
        _root_.GD.N0228.N0547.N0795.d003444 α β q.1 q.2.1 q.2.2 *
        Real.exp (-(_root_.GD.N0228.N0547.N0795.d003437 ρ q.1 q.2.1 q.2.2 / 2)) := by
  have h1ρ : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hpowU : (1 / (2 * ρ) : ℝ) ^ α =
      (2 : ℝ) ^ (-α) * ρ ^ (-α) :=
    _root_.GD.N0228.N0547.N0796.d013513 hρ0
  have hpowV : (1 / (2 * (1 - ρ)) : ℝ) ^ β =
      (2 : ℝ) ^ (-β) * (1 - ρ) ^ (-β) :=
    _root_.GD.N0228.N0547.N0796.d013513 h1ρ
  have hpowHalf : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) =
      (2 : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (-(1 : ℝ) / 2) = -(2 : ℝ)⁻¹ by norm_num]
    exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _).symm
  have hpowTwo :
      (2 : ℝ) ^ (-(1 : ℝ) / 2) * 2 ^ (-α) * 2 ^ (-β) =
        2 ^ (-_root_.GD.N0228.N0547.N0795.d003442 α β) := by
    simp only [_root_.GD.N0228.N0547.N0795.d003442]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring_nf
  simp only [_root_.GD.N0228.N0547.N0796.d013507, gammaPDFReal, if_pos hT.le,
    if_pos hU.le, if_pos hV.le]
  rw [hpowHalf, hpowU, hpowV]
  simp only [_root_.GD.N0228.N0547.N0795.d003449, _root_.GD.N0228.N0547.N0795.d003444, _root_.GD.N0228.N0547.N0795.d003437]
  have hexp :
      Real.exp (-(1 / 2 * q.1)) *
          Real.exp (-(1 / (2 * ρ) * q.2.1)) *
          Real.exp (-(1 / (2 * (1 - ρ)) * q.2.2)) =
        Real.exp (-((q.1 + q.2.1 / ρ + q.2.2 / (1 - ρ)) / 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp [hρ0.ne', h1ρ.ne']
    ring_nf
  rw [show (1 / 2 : ℝ) - 1 = -(1 : ℝ) / 2 by ring_nf]
  simp only [div_eq_mul_inv]
  calc
    _ = (2 ^ (-(1 : ℝ) / 2) * 2 ^ (-α) * 2 ^ (-β)) *
          ((Real.Gamma ((1 : ℝ) / 2))⁻¹ * (Real.Gamma α)⁻¹ *
            (Real.Gamma β)⁻¹ * ρ ^ (-α) * (1 - ρ) ^ (-β) *
            (q.1 ^ (-(1 : ℝ) / 2) * q.2.1 ^ (α - 1) *
              q.2.2 ^ (β - 1))) *
          (Real.exp (-(1 / 2 * q.1)) *
            Real.exp (-(1 / (2 * ρ) * q.2.1)) *
            Real.exp (-(1 / (2 * (1 - ρ)) * q.2.2))) := by ring_nf
    _ = _ := by
      rw [hpowTwo, hexp]
      ring_nf


def d013515 (α β ρ : ℝ) (p : _root_.GD.N0228.N0547.N0796.d013490) : ℝ :=
  _root_.GD.N0228.N0547.N0795.d003449 α β ρ * _root_.GD.N0228.N0547.N0795.d003443 α β p.1 p.2.1 *
    _root_.GD.N0228.N0547.N0795.d003447 (_root_.GD.N0228.N0547.N0795.d003442 α β) (_root_.GD.N0228.N0547.N0794.d003409 ρ p.1 p.2.1) p.2.2



theorem d013516
    {α β ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {p : _root_.GD.N0228.N0547.N0796.d013490} (hp : p ∈ _root_.GD.N0228.N0547.N0796.d013492) :
    _root_.GD.N0228.N0547.N0796.d013507 α β ρ (_root_.GD.N0228.N0547.N0795.d003428 p) * p.2.2 ^ 2 =
      _root_.GD.N0228.N0547.N0796.d013515 α β ρ p := by
  have ht : 0 < p.1 := hp.1
  have hξ0 : 0 < p.2.1 := hp.2.1.1
  have hξ1 : p.2.1 < 1 := hp.2.1.2
  have hR : 0 < p.2.2 := hp.2.2
  rw [_root_.GD.N0228.N0547.N0796.d013514 hρ0 hρ1
    (mul_pos ht hR) (mul_pos hξ0 hR)
    (mul_pos (sub_pos.mpr hξ1) hR)]
  simp only [_root_.GD.N0228.N0547.N0795.d003428]
  calc
    _ = _root_.GD.N0228.N0547.N0795.d003449 α β ρ *
          (_root_.GD.N0228.N0547.N0795.d003444 α β (_root_.GD.N0228.N0547.N0795.d003425 p.1 p.2.2)
            (_root_.GD.N0228.N0547.N0795.d003426 p.2.1 p.2.2) (_root_.GD.N0228.N0547.N0795.d003427 p.2.1 p.2.2) *
            p.2.2 ^ 2) *
          Real.exp (-(_root_.GD.N0228.N0547.N0795.d003437 ρ (_root_.GD.N0228.N0547.N0795.d003425 p.1 p.2.2)
            (_root_.GD.N0228.N0547.N0795.d003426 p.2.1 p.2.2) (_root_.GD.N0228.N0547.N0795.d003427 p.2.1 p.2.2) / 2)) := by
      ring_nf
    _ = _ := by
      rw [_root_.GD.N0228.N0547.N0795.d003445
        ht hξ0 hξ1 hR]
      rw [_root_.GD.N0228.N0547.N0795.d003446]
      simp only [_root_.GD.N0228.N0547.N0796.d013515, _root_.GD.N0228.N0547.N0795.d003447]
      ring_nf

theorem d013517
    {α β ρ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    IntegrableOn (_root_.GD.N0228.N0547.N0796.d013515 α β ρ) _root_.GD.N0228.N0547.N0796.d013492 := by
  have hraw : IntegrableOn (_root_.GD.N0228.N0547.N0796.d013507 α β ρ) _root_.GD.N0228.N0547.N0796.d013491 :=
    (_root_.GD.N0228.N0547.N0796.d013509 hα hβ hρ0 hρ1).integrableOn
  have htrans :=
    (_root_.GD.N0228.N0547.N0796.d013506
      (_root_.GD.N0228.N0547.N0796.d013507 α β ρ)).mp hraw
  apply htrans.congr_fun _ _root_.GD.N0228.N0547.N0796.d013494
  intro p hp
  simp only [smul_eq_mul]
  rw [mul_comm]
  exact _root_.GD.N0228.N0547.N0796.d013516 hρ0 hρ1 hp



theorem d013518
    {α β ρ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∫ p in _root_.GD.N0228.N0547.N0796.d013492, _root_.GD.N0228.N0547.N0796.d013515 α β ρ p) = 1 := by
  calc
    (∫ p in _root_.GD.N0228.N0547.N0796.d013492, _root_.GD.N0228.N0547.N0796.d013515 α β ρ p) =
        ∫ p in _root_.GD.N0228.N0547.N0796.d013492, p.2.2 ^ 2 •
          _root_.GD.N0228.N0547.N0796.d013507 α β ρ (_root_.GD.N0228.N0547.N0795.d003428 p) := by
      apply setIntegral_congr_fun _root_.GD.N0228.N0547.N0796.d013494
      intro p hp
      simp only [smul_eq_mul]
      rw [mul_comm]
      exact (_root_.GD.N0228.N0547.N0796.d013516
        hρ0 hρ1 hp).symm
    _ = ∫ q in _root_.GD.N0228.N0547.N0796.d013491, _root_.GD.N0228.N0547.N0796.d013507 α β ρ q :=
      (_root_.GD.N0228.N0547.N0796.d013505
        (_root_.GD.N0228.N0547.N0796.d013507 α β ρ)).symm
    _ = 1 := _root_.GD.N0228.N0547.N0796.d013512 hα hβ hρ0 hρ1


end

end N0796
end N0547
end N0228
end GD

#print axioms _root_.GD.N0228.N0547.N0796.d013505
#print axioms _root_.GD.N0228.N0547.N0796.d013506
#print axioms _root_.GD.N0228.N0547.N0796.d013512
#print axioms _root_.GD.N0228.N0547.N0796.d013514
#print axioms _root_.GD.N0228.N0547.N0796.d013516
#print axioms _root_.GD.N0228.N0547.N0796.d013517
#print axioms _root_.GD.N0228.N0547.N0796.d013518
