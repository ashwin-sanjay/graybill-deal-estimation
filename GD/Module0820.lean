import GD.Module0819
import GD.Module0310










open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal

namespace GD.N0232.N0720.N1389

open _root_.GD.N0232.N0720.N1393 _root_.GD.N0232.N0720.N1372
open _root_.GD.N0232.N0720.N1388 _root_.GD.N0107 _root_.GD.N0137

noncomputable section

abbrev d012507 := (ℝ × ℝ) × (ℝ × ℝ)


def d012508 : _root_.GD.N0232.N0720.N1389.d012507 ≃ᵐ _root_.GD.N0232.N0720.N1393.d004492 :=
  ((MeasurableEquiv.finTwoArrow.symm.prodCongr MeasurableEquiv.finTwoArrow.symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 ↦ ℝ)).symm).trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin 4 ↦ ℝ) finSumFinEquiv).trans
      (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)))

@[simp]
theorem d012509 (x : _root_.GD.N0232.N0720.N1393.d004492) :
    _root_.GD.N0232.N0720.N1389.d012508.symm x = ((x 0, x 1), (x 2, x 3)) := by
  rfl

theorem d012510 : MeasurePreserving _root_.GD.N0232.N0720.N1389.d012508 volume volume := by
  have hpair : MeasurePreserving
      (MeasurableEquiv.finTwoArrow.symm : (ℝ × ℝ) ≃ᵐ (Fin 2 → ℝ))
      volume volume := (volume_preserving_finTwoArrow ℝ).symm _
  have h := (PiLp.volume_preserving_toLp (Fin 4)).comp
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin 4 ↦ ℝ) finSumFinEquiv).comp
      ((volume_measurePreserving_sumPiEquivProdPi_symm
        (fun _ : Fin 2 ⊕ Fin 2 ↦ ℝ)).comp
        (hpair.prod hpair)))
  simpa only [_root_.GD.N0232.N0720.N1389.d012508, MeasurableEquiv.coe_trans, Function.comp_assoc] using! h

private theorem d012511 {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ : Measure α) (ν : Measure β) (he : MeasurePreserving e μ ν)
    (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = ν.withDensity (fun y ↦ f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs]
  simpa only [Function.comp_apply, e.symm_apply_apply] using
    he.setLIntegral_comp_preimage hs (hf.comp e.symm.measurable)

def d012512 (q : _root_.GD.N0232.N0720.N1372.d004518) : ℝ≥0 := ⟨q.2.1, q.2.2.1.le⟩

def d012513 (q : _root_.GD.N0232.N0720.N1372.d004518) : ℝ≥0 :=
  ⟨1 - q.2.1, (sub_pos.mpr q.2.2.2).le⟩

theorem d012514 (q : _root_.GD.N0232.N0720.N1372.d004518) : _root_.GD.N0232.N0720.N1389.d012512 q ≠ 0 := by
  exact ne_of_gt (show 0 < _root_.GD.N0232.N0720.N1389.d012512 q from q.2.2.1)

theorem d012515 (q : _root_.GD.N0232.N0720.N1372.d004518) : _root_.GD.N0232.N0720.N1389.d012513 q ≠ 0 := by
  exact ne_of_gt (show 0 < _root_.GD.N0232.N0720.N1389.d012513 q from sub_pos.mpr q.2.2.2)

def d012516 (q : _root_.GD.N0232.N0720.N1372.d004518) : Measure _root_.GD.N0232.N0720.N1389.d012507 :=
  ((gaussianReal q.1 (_root_.GD.N0232.N0720.N1389.d012512 q)).prod
    (gaussianReal 0 (_root_.GD.N0232.N0720.N1389.d012512 q))).prod
  ((gaussianReal q.1 (_root_.GD.N0232.N0720.N1389.d012513 q)).prod
    (gaussianReal 0 (_root_.GD.N0232.N0720.N1389.d012513 q)))

def d012517 (q : _root_.GD.N0232.N0720.N1372.d004518) (p : _root_.GD.N0232.N0720.N1389.d012507) : ℝ≥0∞ :=
  (gaussianPDF q.1 (_root_.GD.N0232.N0720.N1389.d012512 q) p.1.1 *
    gaussianPDF 0 (_root_.GD.N0232.N0720.N1389.d012512 q) p.1.2) *
  (gaussianPDF q.1 (_root_.GD.N0232.N0720.N1389.d012513 q) p.2.1 *
    gaussianPDF 0 (_root_.GD.N0232.N0720.N1389.d012513 q) p.2.2)

@[fun_prop]
theorem d012518 (q : _root_.GD.N0232.N0720.N1372.d004518) : Measurable (_root_.GD.N0232.N0720.N1389.d012517 q) := by
  unfold _root_.GD.N0232.N0720.N1389.d012517
  fun_prop

theorem d012519 (q : _root_.GD.N0232.N0720.N1372.d004518) :
    _root_.GD.N0232.N0720.N1389.d012516 q = volume.withDensity (_root_.GD.N0232.N0720.N1389.d012517 q) := by
  unfold _root_.GD.N0232.N0720.N1389.d012516
  rw [gaussianReal_of_var_ne_zero _ (_root_.GD.N0232.N0720.N1389.d012514 q),
    gaussianReal_of_var_ne_zero _ (_root_.GD.N0232.N0720.N1389.d012514 q),
    gaussianReal_of_var_ne_zero _ (_root_.GD.N0232.N0720.N1389.d012515 q),
    gaussianReal_of_var_ne_zero _ (_root_.GD.N0232.N0720.N1389.d012515 q)]
  rw [prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
    prod_withDensity (by fun_prop) (by fun_prop)]
  rfl

theorem d012520 (m : ℝ) (v : ℝ≥0) (x r : ℝ) :
    gaussianPDFReal m v x * gaussianPDFReal 0 v r =
      (2 * Real.pi * v)⁻¹ * Real.exp (-((x - m) ^ 2 + r ^ 2) / (2 * v)) := by
  unfold gaussianPDFReal
  rw [sub_zero, mul_mul_mul_comm, ← mul_inv, ← sq,
    Real.sq_sqrt (by positivity), ← Real.exp_add]
  congr 2 <;> ring

theorem d012521 (q : _root_.GD.N0232.N0720.N1372.d004518) (x : _root_.GD.N0232.N0720.N1393.d004492) :
    _root_.GD.N0232.N0720.N1389.d012517 q (_root_.GD.N0232.N0720.N1389.d012508.symm x) = ENNReal.ofReal (_root_.GD.N0232.N0720.N1372.d004523 q x) := by
  rw [_root_.GD.N0232.N0720.N1389.d012509]
  unfold _root_.GD.N0232.N0720.N1389.d012517 gaussianPDF
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_mul (mul_nonneg (gaussianPDFReal_nonneg _ _ _)
      (gaussianPDFReal_nonneg _ _ _)),
    _root_.GD.N0232.N0720.N1389.d012520, _root_.GD.N0232.N0720.N1389.d012520]
  apply congrArg ENNReal.ofReal
  change ((2 * Real.pi * q.2.1)⁻¹ *
      Real.exp (-((x 0 - q.1) ^ 2 + x 1 ^ 2) / (2 * q.2.1))) *
      ((2 * Real.pi * (1 - q.2.1))⁻¹ *
        Real.exp (-((x 2 - q.1) ^ 2 + x 3 ^ 2) / (2 * (1 - q.2.1)))) =
    (4 * Real.pi ^ 2 * (q.2.1 * (1 - q.2.1)))⁻¹ *
      Real.exp (-((x 0 - q.1) ^ 2 + x 1 ^ 2) / (2 * q.2.1) -
        ((x 2 - q.1) ^ 2 + x 3 ^ 2) / (2 * (1 - q.2.1)))
  rw [mul_mul_mul_comm, ← mul_inv, ← Real.exp_add]
  congr 2
  · ring
  · simp only [neg_div, sub_eq_add_neg]



theorem d012522 (q : _root_.GD.N0232.N0720.N1372.d004518) :
    (_root_.GD.N0232.N0720.N1389.d012516 q).map _root_.GD.N0232.N0720.N1389.d012508 =
      volume.withDensity (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1372.d004523 q x)) := by
  rw [_root_.GD.N0232.N0720.N1389.d012519,
    _root_.GD.N0232.N0720.N1389.d012511 _root_.GD.N0232.N0720.N1389.d012508 volume volume _root_.GD.N0232.N0720.N1389.d012510
      (_root_.GD.N0232.N0720.N1389.d012517 q) (_root_.GD.N0232.N0720.N1389.d012518 q)]
  congr 1
  funext x
  exact _root_.GD.N0232.N0720.N1389.d012521 q x


def d012523 (q : _root_.GD.N0232.N0720.N1372.d004518) : ℝ := Real.sqrt (2 * q.2.1)

def d012524 (q : _root_.GD.N0232.N0720.N1372.d004518) : ℝ := Real.sqrt (2 * (1 - q.2.1))

theorem d012525 (q : _root_.GD.N0232.N0720.N1372.d004518) : 0 < _root_.GD.N0232.N0720.N1389.d012523 q := by
  exact Real.sqrt_pos.2 (mul_pos (by norm_num) q.2.2.1)

theorem d012526 (q : _root_.GD.N0232.N0720.N1372.d004518) : 0 < _root_.GD.N0232.N0720.N1389.d012524 q := by
  exact Real.sqrt_pos.2 (mul_pos (by norm_num) (sub_pos.mpr q.2.2.2))

theorem d012527 (q : _root_.GD.N0232.N0720.N1372.d004518) :
    _root_.GD.N0232.N0720.N1388.d012496 (_root_.GD.N0232.N0720.N1389.d012523 q) = _root_.GD.N0232.N0720.N1389.d012512 q := by
  apply Subtype.ext
  change (Real.sqrt (2 * q.2.1)) ^ 2 / 2 = q.2.1
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) q.2.2.1.le)]
  ring

theorem d012528 (q : _root_.GD.N0232.N0720.N1372.d004518) :
    _root_.GD.N0232.N0720.N1388.d012496 (_root_.GD.N0232.N0720.N1389.d012524 q) = _root_.GD.N0232.N0720.N1389.d012513 q := by
  apply Subtype.ext
  change (Real.sqrt (2 * (1 - q.2.1))) ^ 2 / 2 = 1 - q.2.1
  rw [Real.sq_sqrt (mul_nonneg (by norm_num) (sub_pos.mpr q.2.2.2).le)]
  ring

def d012529 (x : _root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2) :
    _root_.GD.N0232.N0720.N1393.d004492 :=
  _root_.GD.N0232.N0720.N1389.d012508 (_root_.GD.N0232.N0720.N1388.d012494 x.1, _root_.GD.N0232.N0720.N1388.d012494 x.2)

@[fun_prop]
theorem d012530 : Measurable _root_.GD.N0232.N0720.N1389.d012529 := by
  exact _root_.GD.N0232.N0720.N1389.d012508.measurable.comp (by fun_prop)



theorem d012531 (q : _root_.GD.N0232.N0720.N1372.d004518) :
    (_root_.GD.N0107.d009030 2 2 q.1 (_root_.GD.N0232.N0720.N1389.d012523 q) (_root_.GD.N0232.N0720.N1389.d012524 q)).map _root_.GD.N0232.N0720.N1389.d012529 =
      volume.withDensity (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1372.d004523 q x)) := by
  change (_root_.GD.N0107.d009030 2 2 q.1 (_root_.GD.N0232.N0720.N1389.d012523 q) (_root_.GD.N0232.N0720.N1389.d012524 q)).map
    (_root_.GD.N0232.N0720.N1389.d012508 ∘ Prod.map _root_.GD.N0232.N0720.N1388.d012494 _root_.GD.N0232.N0720.N1388.d012494) = _
  rw [← Measure.map_map _root_.GD.N0232.N0720.N1389.d012508.measurable (by fun_prop),
    _root_.GD.N0232.N0720.N1388.d012505]
  simp only [_root_.GD.N0232.N0720.N1388.d012497, _root_.GD.N0232.N0720.N1389.d012527,
    _root_.GD.N0232.N0720.N1389.d012528]
  exact _root_.GD.N0232.N0720.N1389.d012522 q

theorem d012532 (q : _root_.GD.N0232.N0720.N1372.d004518) (x : _root_.GD.N0232.N0720.N1393.d004492) :
    0 ≤ _root_.GD.N0232.N0720.N1372.d004523 q x := by
  have hv := _root_.GD.N0232.N0720.N1372.d004524 q
  unfold _root_.GD.N0232.N0720.N1372.d004523
  positivity

@[fun_prop]
theorem d012533 (q : _root_.GD.N0232.N0720.N1372.d004518) : Measurable (_root_.GD.N0232.N0720.N1372.d004523 q) := by
  unfold _root_.GD.N0232.N0720.N1372.d004523
  fun_prop


def d012534 (h : _root_.GD.N0232.N0720.N1393.d004495) (x : _root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2) : ℝ :=
  _root_.GD.N0232.N0720.N1393.d004496 h (_root_.GD.N0232.N0720.N1389.d012529 x)

@[fun_prop]
theorem d012535 (h : _root_.GD.N0232.N0720.N1393.d004495) : Measurable (_root_.GD.N0232.N0720.N1389.d012534 h) :=
  (_root_.GD.N0232.N0720.N1388.d012493 h).comp _root_.GD.N0232.N0720.N1389.d012530



theorem d012536 (q : _root_.GD.N0232.N0720.N1372.d004518) (h : _root_.GD.N0232.N0720.N1393.d004495) :
    (∫⁻ x, ENNReal.ofReal ((_root_.GD.N0232.N0720.N1389.d012534 h x - q.1) ^ 2)
      ∂_root_.GD.N0107.d009030 2 2 q.1 (_root_.GD.N0232.N0720.N1389.d012523 q) (_root_.GD.N0232.N0720.N1389.d012524 q)) =
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1372.d004546 q h) := by
  have hm : Measurable (fun x : _root_.GD.N0232.N0720.N1393.d004492 ↦
      ENNReal.ofReal ((_root_.GD.N0232.N0720.N1393.d004496 h x - q.1) ^ 2)) :=
    ((_root_.GD.N0232.N0720.N1388.d012493 h).sub measurable_const).pow_const 2 |>.ennreal_ofReal
  calc
    _ = ∫⁻ x, ENNReal.ofReal ((_root_.GD.N0232.N0720.N1393.d004496 h x - q.1) ^ 2)
        ∂(_root_.GD.N0107.d009030 2 2 q.1 (_root_.GD.N0232.N0720.N1389.d012523 q) (_root_.GD.N0232.N0720.N1389.d012524 q)).map
          _root_.GD.N0232.N0720.N1389.d012529 := (lintegral_map hm _root_.GD.N0232.N0720.N1389.d012530).symm
    _ = ∫⁻ x, ENNReal.ofReal ((_root_.GD.N0232.N0720.N1393.d004496 h x - q.1) ^ 2)
        ∂volume.withDensity (fun x ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1372.d004523 q x)) := by
      rw [_root_.GD.N0232.N0720.N1389.d012531]
    _ = ∫⁻ x, ENNReal.ofReal (_root_.GD.N0232.N0720.N1372.d004523 q x) *
        ENNReal.ofReal ((_root_.GD.N0232.N0720.N1393.d004496 h x - q.1) ^ 2) :=
      lintegral_withDensity_eq_lintegral_mul volume
        (_root_.GD.N0232.N0720.N1389.d012533 q).ennreal_ofReal hm
    _ = ENNReal.ofReal (_root_.GD.N0232.N0720.N1372.d004546 q h) := by
      rw [_root_.GD.N0232.N0720.N1372.d004546, ofReal_integral_eq_lintegral_ofReal (_root_.GD.N0232.N0720.N1372.d004545 q h)
        (ae_of_all _ (fun x ↦ mul_nonneg (sq_nonneg _) (_root_.GD.N0232.N0720.N1389.d012532 q x)))]
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul (_root_.GD.N0232.N0720.N1389.d012532 q x), mul_comm]

end

end GD.N0232.N0720.N1389

#print axioms _root_.GD.N0232.N0720.N1389.d012510
#print axioms _root_.GD.N0232.N0720.N1389.d012531
#print axioms _root_.GD.N0232.N0720.N1389.d012536
