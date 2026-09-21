import GD.Module0874

set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD.N0228.N0547.N0796

noncomputable section

open _root_.GD.N0228.N0547.N0795
open _root_.GD.N0228.N0547.N0794
open _root_.GD.N0232.N0720.N1435
open _root_.GD.N0232.N0720.N1436


theorem d013519
    {α β ρ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    IntegrableOn (fun x : _root_.GD.N0232.N0720.N1436.d013217 =>
      _root_.GD.N0228.N0547.N0795.d003450 α β ρ x.2 x.1) _root_.GD.N0232.N0720.N1436.d013218 := by
  let H : _root_.GD.N0232.N0720.N1435.d013432 → ℝ := fun z =>
    _root_.GD.N0228.N0547.N0796.d013515 α β ρ (_root_.GD.N0228.N0547.N0796.d013496.symm z)
  have hcomp : H ∘ _root_.GD.N0228.N0547.N0796.d013496 =
      _root_.GD.N0228.N0547.N0796.d013515 α β ρ := by
    funext p
    simp [H]
  have hHint : IntegrableOn H _root_.GD.N0232.N0720.N1435.d013434 := by
    rw [← _root_.GD.N0228.N0547.N0796.d013502]
    have h := _root_.GD.N0228.N0547.N0796.d013500.integrableOn_image
      _root_.GD.N0228.N0547.N0796.d013496.measurableEmbedding
      (f := H) (s := _root_.GD.N0228.N0547.N0796.d013492)
    rw [hcomp] at h
    exact h.mpr (_root_.GD.N0228.N0547.N0796.d013517 hα hβ hρ0 hρ1)
  let K : _root_.GD.N0232.N0720.N1436.d013217 × ℝ → ℝ :=
    fun p => H (_root_.GD.N0232.N0720.N1435.d013476 p.1 p.2)
  have hK : IntegrableOn K (_root_.GD.N0232.N0720.N1436.d013218 ×ˢ Ioi 0) := by
    rw [← _root_.GD.N0232.N0720.N1435.d013481]
    have h := _root_.GD.N0232.N0720.N1435.d013480.integrableOn_image
      _root_.GD.N0232.N0720.N1435.d013473.measurableEmbedding
      (f := K) (s := _root_.GD.N0232.N0720.N1435.d013434)
    have hcompK : K ∘ _root_.GD.N0232.N0720.N1435.d013473 = H := by
      funext z
      simp [K, _root_.GD.N0232.N0720.N1435.d013476]
    rw [hcompK] at h
    exact h.mpr hHint
  have hKprod : Integrable K
      ((volume.restrict _root_.GD.N0232.N0720.N1436.d013218).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict]
    simpa only [IntegrableOn, Measure.volume_eq_prod] using hK
  have hmarg : Integrable
      (fun x : _root_.GD.N0232.N0720.N1436.d013217 =>
        ∫ R : ℝ in Ioi 0, K (x, R))
      (volume.restrict _root_.GD.N0232.N0720.N1436.d013218) :=
    hKprod.integral_prod_left
  have hmargOn : IntegrableOn
      (fun x : _root_.GD.N0232.N0720.N1436.d013217 =>
        ∫ R : ℝ in Ioi 0, K (x, R)) _root_.GD.N0232.N0720.N1436.d013218 := hmarg
  apply hmargOn.congr_fun _ _root_.GD.N0232.N0720.N1436.d013219
  intro x hx
  have hjoin (R : ℝ) :
      _root_.GD.N0228.N0547.N0796.d013496.symm (_root_.GD.N0232.N0720.N1435.d013476 x R) = (x.2, (x.1, R)) := by
    rfl
  simp only [K, H, hjoin, _root_.GD.N0228.N0547.N0796.d013515]
  exact _root_.GD.N0228.N0547.N0795.d003452 hα hβ hρ0 hρ1
    hx.2 hx.1.1 hx.1.2



theorem d013520
    {α β ρ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
      _root_.GD.N0228.N0547.N0795.d003450 α β ρ x.2 x.1) = 1 := by
  let H : _root_.GD.N0232.N0720.N1435.d013432 → ℝ := fun z =>
    _root_.GD.N0228.N0547.N0796.d013515 α β ρ (_root_.GD.N0228.N0547.N0796.d013496.symm z)
  have hcomp : H ∘ _root_.GD.N0228.N0547.N0796.d013496 =
      _root_.GD.N0228.N0547.N0796.d013515 α β ρ := by
    funext p
    simp [H]
  have hHint : IntegrableOn H _root_.GD.N0232.N0720.N1435.d013434 := by
    rw [← _root_.GD.N0228.N0547.N0796.d013502]
    have h := _root_.GD.N0228.N0547.N0796.d013500.integrableOn_image
      _root_.GD.N0228.N0547.N0796.d013496.measurableEmbedding
      (f := H) (s := _root_.GD.N0228.N0547.N0796.d013492)
    rw [hcomp] at h
    exact h.mpr (_root_.GD.N0228.N0547.N0796.d013517 hα hβ hρ0 hρ1)
  have htransport :
      (∫ z in _root_.GD.N0232.N0720.N1435.d013434, H z) =
        ∫ p in _root_.GD.N0228.N0547.N0796.d013492, _root_.GD.N0228.N0547.N0796.d013515 α β ρ p := by
    rw [← _root_.GD.N0228.N0547.N0796.d013502]
    have h := _root_.GD.N0228.N0547.N0796.d013500.setIntegral_image_emb
      _root_.GD.N0228.N0547.N0796.d013496.measurableEmbedding H _root_.GD.N0228.N0547.N0796.d013492
    simpa [H] using h
  have hjoin (x : _root_.GD.N0232.N0720.N1436.d013217) (R : ℝ) :
      _root_.GD.N0228.N0547.N0796.d013496.symm (_root_.GD.N0232.N0720.N1435.d013476 x R) = (x.2, (x.1, R)) := by
    rfl
  calc
    (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
      _root_.GD.N0228.N0547.N0795.d003450 α β ρ x.2 x.1) =
        ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
          ∫ R in Ioi 0, H (_root_.GD.N0232.N0720.N1435.d013476 x R) := by
      apply setIntegral_congr_fun _root_.GD.N0232.N0720.N1436.d013219
      intro x hx
      simp only [H, hjoin, _root_.GD.N0228.N0547.N0796.d013515]
      exact (_root_.GD.N0228.N0547.N0795.d003452 hα hβ hρ0 hρ1
        hx.2 hx.1.1 hx.1.2).symm
    _ = ∫ z in _root_.GD.N0232.N0720.N1435.d013434, H z :=
      (_root_.GD.N0232.N0720.N1435.d013482 H hHint).symm
    _ = ∫ p in _root_.GD.N0228.N0547.N0796.d013492,
        _root_.GD.N0228.N0547.N0796.d013515 α β ρ p := htransport
    _ = 1 := _root_.GD.N0228.N0547.N0796.d013518 hα hβ hρ0 hρ1


theorem d013521
    {α β ρ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∫ ξ : ℝ in Ioo 0 1, ∫ t : ℝ in Ioi 0,
      _root_.GD.N0228.N0547.N0795.d003450 α β ρ t ξ) = 1 := by
  have hInt := _root_.GD.N0228.N0547.N0796.d013519
    hα hβ hρ0 hρ1
  have hOne := _root_.GD.N0228.N0547.N0796.d013520
    hα hβ hρ0 hρ1
  have hOne' :
      (∫ z : ℝ × ℝ in Ioo 0 1 ×ˢ Ioi 0,
        _root_.GD.N0228.N0547.N0795.d003450 α β ρ z.2 z.1 ∂((volume : Measure ℝ).prod volume)) = 1 := by
    simpa only [_root_.GD.N0232.N0720.N1436.d013218, Measure.volume_eq_prod] using hOne
  have hsplit := setIntegral_prod
    (fun x : ℝ × ℝ => _root_.GD.N0228.N0547.N0795.d003450 α β ρ x.2 x.1) hInt
  rw [hOne'] at hsplit
  simpa only using hsplit.symm


theorem d013522
    {α β ρ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (∫ t : ℝ in Ioi 0, ∫ ξ : ℝ in Ioo 0 1,
      _root_.GD.N0228.N0547.N0795.d003450 α β ρ t ξ) = 1 := by
  have hInt := _root_.GD.N0228.N0547.N0796.d013519
    hα hβ hρ0 hρ1
  have hOne := _root_.GD.N0228.N0547.N0796.d013520
    hα hβ hρ0 hρ1
  let f : ℝ × ℝ → ℝ := fun x => _root_.GD.N0228.N0547.N0795.d003450 α β ρ x.2 x.1
  have hInt' : IntegrableOn f (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ))
      ((volume : Measure ℝ).prod volume) := by
    simpa only [f, _root_.GD.N0232.N0720.N1436.d013218, Measure.volume_eq_prod] using hInt
  have hswapInt : IntegrableOn (f ∘ Prod.swap)
      (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [Measure.prod_swap] using hInt'.swap
  have hswapIntegral := setIntegral_prod_swap
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (Ioo (0 : ℝ) 1) (Ioi (0 : ℝ)) f
  have hOne' :
      (∫ z : ℝ × ℝ in Ioo 0 1 ×ˢ Ioi 0, f z
        ∂((volume : Measure ℝ).prod volume)) = 1 := by
    simpa only [f, _root_.GD.N0232.N0720.N1436.d013218, Measure.volume_eq_prod] using hOne
  rw [hOne'] at hswapIntegral
  have hswapIntegral' :
      (∫ z : ℝ × ℝ in Ioi 0 ×ˢ Ioo 0 1,
        (f ∘ Prod.swap) z ∂((volume : Measure ℝ).prod volume)) = 1 := by
    simpa only [Function.comp_apply] using hswapIntegral
  have hsplit := setIntegral_prod (f ∘ Prod.swap) hswapInt
  rw [hswapIntegral'] at hsplit
  simpa only [f, Function.comp_apply, Prod.swap_prod_mk] using hsplit.symm

end

end GD.N0228.N0547.N0796

#print axioms _root_.GD.N0228.N0547.N0796.d013519
#print axioms _root_.GD.N0228.N0547.N0796.d013520
#print axioms _root_.GD.N0228.N0547.N0796.d013521
#print axioms _root_.GD.N0228.N0547.N0796.d013522
