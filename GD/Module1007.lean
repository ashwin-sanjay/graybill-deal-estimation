import GD.Module1001
import Mathlib.MeasureTheory.Integral.Lebesgue.Map



























open Function MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1178

noncomputable section

open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1172
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229



attribute [local instance] Measure.Subtype.measureSpace







private theorem d016010
    {alpha beta : Type*} [MeasurableSpace alpha] [MeasurableSpace beta]
    (e : alpha ≃ᵐ beta) (mu : Measure alpha) (w : alpha → ℝ≥0∞) :
    (mu.withDensity w).map e =
      (mu.map e).withDensity (w ∘ e.symm) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  change (∫⁻ x, w x ∂mu.restrict (e ⁻¹' s)) =
    ∫⁻ y, (w ∘ e.symm) y ∂(mu.map e).restrict s
  rw [e.restrict_map]
  rw [MeasureTheory.lintegral_map_equiv]
  simp only [Function.comp_apply, e.symm_apply_apply]




def d016011 (g : _root_.GD.N0232.N0719.N0946.d009229) : ℝ ≃ᵐ ℝ where
  toFun x := g.shift + g.d009239 * x
  invFun y := g.d009239⁻¹ * (y - g.shift)
  left_inv x := by
    field_simp [g.d009240.ne']
    ring
  right_inv y := by
    field_simp [g.d009240.ne']
    ring
  measurable_toFun := measurable_const.add (measurable_const.mul measurable_id)
  measurable_invFun := measurable_const.mul (measurable_id.sub measurable_const)

@[simp] theorem d016012
    (g : _root_.GD.N0232.N0719.N0946.d009229) (x : ℝ) :
    _root_.GD.N0232.N0720.N1178.d016011 g x =
      g.shift + g.d009239 * x := rfl


def d016013
    (g : _root_.GD.N0232.N0719.N0946.d009229) : Set.Ioi (0 : ℝ) ≃ᵐ Set.Ioi (0 : ℝ) where
  toFun q :=
    ⟨g.d009239 ^ 2 * (q : ℝ),
      mul_pos (sq_pos_of_pos g.d009240) q.property⟩
  invFun q :=
    ⟨(g.d009239 ^ 2)⁻¹ * (q : ℝ),
      mul_pos (inv_pos.mpr (sq_pos_of_pos g.d009240)) q.property⟩
  left_inv q := by
    apply Subtype.ext
    field_simp [g.d009240.ne']
  right_inv q := by
    apply Subtype.ext
    field_simp [g.d009240.ne']
  measurable_toFun := by
    exact (measurable_const.mul measurable_subtype_coe).subtype_mk
  measurable_invFun := by
    exact (measurable_const.mul measurable_subtype_coe).subtype_mk

@[simp] theorem d016014
    (g : _root_.GD.N0232.N0719.N0946.d009229) (q : Set.Ioi (0 : ℝ)) :
    ((_root_.GD.N0232.N0720.N1178.d016013 g q : Set.Ioi (0 : ℝ)) : ℝ) =
      g.d009239 ^ 2 * (q : ℝ) := rfl


def d016015 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1172.d015905 ≃ᵐ _root_.GD.N0232.N0720.N1172.d015905 :=
  (_root_.GD.N0232.N0720.N1178.d016011 g).prodCongr
    ((_root_.GD.N0232.N0720.N1178.d016013 g).prodCongr
      (MeasurableEquiv.refl (Set.Ioo (0 : ℝ) 1)))

@[simp] theorem d016016
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1172.d015905) :
    _root_.GD.N0232.N0720.N1178.d016015 g theta = _root_.GD.N0232.N0720.N1172.d015906 g theta := rfl

@[fun_prop] theorem d016017 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    Measurable (_root_.GD.N0232.N0720.N1172.d015906 g) := by
  have hfun : _root_.GD.N0232.N0720.N1172.d015906 g = _root_.GD.N0232.N0720.N1178.d016015 g := by
    funext theta
    exact (_root_.GD.N0232.N0720.N1178.d016016 g theta).symm
  rw [hfun]
  exact (_root_.GD.N0232.N0720.N1178.d016015 g).measurable



theorem d016018
    (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1172.d015905) :
    (_root_.GD.N0232.N0720.N1178.d016015 g).symm theta =
      _root_.GD.N0232.N0720.N1172.d015906 g⁻¹ theta := by
  apply (_root_.GD.N0232.N0720.N1178.d016015 g).injective
  simp



theorem d016019
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    (volume : Measure ℝ).map (_root_.GD.N0232.N0720.N1178.d016011 g) =
      ENNReal.ofReal g.d009239⁻¹ • volume := by
  let scale : ℝ → ℝ := fun x => g.d009239 * x
  let translate : ℝ → ℝ := fun x => g.shift + x
  calc
    (volume : Measure ℝ).map (_root_.GD.N0232.N0720.N1178.d016011 g) =
        ((volume : Measure ℝ).map scale).map translate := by
      rw [Measure.map_map]
      · rfl
      · exact measurable_const.add measurable_id
      · exact measurable_const.mul measurable_id
    _ = (ENNReal.ofReal |g.d009239⁻¹| • (volume : Measure ℝ)).map
          translate := by
      rw [Real.map_volume_mul_left g.d009240.ne']
    _ = ENNReal.ofReal |g.d009239⁻¹| •
          (volume : Measure ℝ).map translate := by
      rw [Measure.map_smul]
    _ = ENNReal.ofReal |g.d009239⁻¹| • volume := by
      congr 1
      simpa only [translate] using
        (Measure.IsAddLeftInvariant.map_add_left_eq_self
          (μ := (volume : Measure ℝ)) g.shift)
    _ = ENNReal.ofReal g.d009239⁻¹ • volume := by
      rw [abs_of_pos (inv_pos.mpr g.d009240)]

private theorem d016020 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    (fun q : ℝ => g.d009239 ^ 2 * q) ⁻¹' Set.Ioi (0 : ℝ) =
      Set.Ioi (0 : ℝ) := by
  ext q
  simp only [mem_preimage, mem_Ioi]
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos g.d009240))


theorem d016021
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    (volume : Measure (Set.Ioi (0 : ℝ))).map
        (_root_.GD.N0232.N0720.N1178.d016013 g) =
      ENNReal.ofReal (g.d009239 ^ 2)⁻¹ • volume := by
  apply
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi).map_injective
  let realScale : ℝ ≃ᵐ ℝ :=
    (Homeomorph.mulLeft₀ (g.d009239 ^ 2)
      (sq_pos_of_pos g.d009240).ne').toMeasurableEquiv
  calc
    ((volume : Measure (Set.Ioi (0 : ℝ))).map
          (_root_.GD.N0232.N0720.N1178.d016013 g)).map
        ((↑) : Set.Ioi (0 : ℝ) → ℝ) =
        ((volume : Measure (Set.Ioi (0 : ℝ))).map
          ((↑) : Set.Ioi (0 : ℝ) → ℝ)).map realScale := by
      rw [Measure.map_map measurable_subtype_coe
          (_root_.GD.N0232.N0720.N1178.d016013 g).measurable,
        Measure.map_map realScale.measurable measurable_subtype_coe]
      rfl
    _ = (volume.restrict (Set.Ioi (0 : ℝ))).map realScale := by
      rw [MeasurableSet.map_coe_volume measurableSet_Ioi]
    _ = ((volume : Measure ℝ).map realScale).restrict
          (Set.Ioi (0 : ℝ)) := by
      rw [realScale.restrict_map]
      change
        (volume.restrict (Set.Ioi (0 : ℝ))).map realScale =
          (volume.restrict
            ((fun q : ℝ => g.d009239 ^ 2 * q) ⁻¹'
              Set.Ioi (0 : ℝ))).map realScale
      rw [_root_.GD.N0232.N0720.N1178.d016020]
    _ = (ENNReal.ofReal |(g.d009239 ^ 2)⁻¹| •
          (volume : Measure ℝ)).restrict (Set.Ioi (0 : ℝ)) := by
      change
        ((volume : Measure ℝ).map
          (fun q : ℝ => g.d009239 ^ 2 * q)).restrict
            (Set.Ioi (0 : ℝ)) = _
      rw [Real.map_volume_mul_left
        (sq_pos_of_pos g.d009240).ne']
    _ = ENNReal.ofReal (g.d009239 ^ 2)⁻¹ •
          volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [Measure.restrict_smul,
        abs_of_pos (inv_pos.mpr (sq_pos_of_pos g.d009240))]
    _ = (((ENNReal.ofReal (g.d009239 ^ 2)⁻¹) •
          (volume : Measure (Set.Ioi (0 : ℝ)))).map
            ((↑) : Set.Ioi (0 : ℝ) → ℝ)) := by
      rw [Measure.map_smul,
        MeasurableSet.map_coe_volume measurableSet_Ioi]



private theorem d016022
    (g : _root_.GD.N0232.N0719.N0946.d009229) (q : Set.Ioi (0 : ℝ)) :
    _root_.GD.N0232.N0720.N1486.d015857 ((_root_.GD.N0232.N0720.N1178.d016013 g).symm q) =
      g.d009239 ^ 5 * _root_.GD.N0232.N0720.N1486.d015857 q := by
  have ha : 0 < g.d009239 := g.d009240
  have hc : 0 < g.d009239 ^ 2 := sq_pos_of_pos ha
  have hq : 0 < (q : ℝ) := q.property
  unfold _root_.GD.N0232.N0720.N1486.d015857
  change
    ((g.d009239 ^ 2)⁻¹ * (q : ℝ)) ^ (-(5 / 2 : ℝ)) =
      g.d009239 ^ 5 * (q : ℝ) ^ (-(5 / 2 : ℝ))
  rw [Real.mul_rpow (inv_nonneg.mpr hc.le) hq.le,
    Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
  have hpow2 : g.d009239 ^ 2 = g.d009239 ^ (2 : ℝ) :=
    (Real.rpow_two g.d009239).symm
  rw [hpow2, ← Real.rpow_mul ha.le]
  have hexponent : (2 : ℝ) * -(-(5 / 2 : ℝ)) = 5 := by ring
  calc
    g.d009239 ^ ((2 : ℝ) * -(-(5 / 2 : ℝ))) *
          (q : ℝ) ^ (-(5 / 2 : ℝ)) =
        g.d009239 ^ (5 : ℝ) *
          (q : ℝ) ^ (-(5 / 2 : ℝ)) := by
      rw [hexponent]
    _ = g.d009239 ^ (5 : ℕ) *
          (q : ℝ) ^ (-(5 / 2 : ℝ)) := by
      exact congrArg
        (fun t : ℝ ↦ t * (q : ℝ) ^ (-(5 / 2 : ℝ)))
        (Real.rpow_natCast g.d009239 5)

private theorem d016023
    (g : _root_.GD.N0232.N0719.N0946.d009229) (q : Set.Ioi (0 : ℝ)) :
    _root_.GD.N0232.N0720.N1486.d015860
        ((_root_.GD.N0232.N0720.N1178.d016013 g).symm q) =
      ENNReal.ofReal (g.d009239 ^ 5) *
        _root_.GD.N0232.N0720.N1486.d015860 q := by
  unfold _root_.GD.N0232.N0720.N1486.d015860
  rw [_root_.GD.N0232.N0720.N1178.d016022]
  exact ENNReal.ofReal_mul (pow_nonneg g.d009240.le 5)

private theorem d016024 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    ENNReal.ofReal (g.d009239 ^ 2)⁻¹ *
        ENNReal.ofReal (g.d009239 ^ 5) =
      ENNReal.ofReal (g.d009239 ^ 3) := by
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr
    (sq_pos_of_pos g.d009240).le)]
  congr 1
  field_simp [g.d009240.ne']




theorem d016025
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1486.d015866.map (_root_.GD.N0232.N0720.N1178.d016013 g) =
      ENNReal.ofReal (g.d009239 ^ 3) • _root_.GD.N0232.N0720.N1486.d015866 := by
  rw [_root_.GD.N0232.N0720.N1486.d015866,
    _root_.GD.N0232.N0720.N1178.d016010
      (_root_.GD.N0232.N0720.N1178.d016013 g) volume
      _root_.GD.N0232.N0720.N1486.d015860,
    _root_.GD.N0232.N0720.N1178.d016021]
  have hdensity :
      _root_.GD.N0232.N0720.N1486.d015860 ∘
          (_root_.GD.N0232.N0720.N1178.d016013 g).symm =
        ENNReal.ofReal (g.d009239 ^ 5) •
          _root_.GD.N0232.N0720.N1486.d015860 := by
    funext q
    rw [Function.comp_apply, Pi.smul_apply, smul_eq_mul,
      _root_.GD.N0232.N0720.N1178.d016023]
  rw [hdensity, withDensity_smul_measure,
    withDensity_smul _ _root_.GD.N0232.N0720.N1486.d015863,
    smul_smul, _root_.GD.N0232.N0720.N1178.d016024]






theorem d016026
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    (_root_.GD.N0232.N0720.N1486.d015870 rho).map (_root_.GD.N0232.N0720.N1172.d015906 g) =
      ENNReal.ofReal (g.d009239 ^ 2) •
        _root_.GD.N0232.N0720.N1486.d015870 rho := by
  unfold _root_.GD.N0232.N0720.N1486.d015870
  have haction : _root_.GD.N0232.N0720.N1172.d015906 g =
      Prod.map (_root_.GD.N0232.N0720.N1178.d016011 g)
        (Prod.map (_root_.GD.N0232.N0720.N1178.d016013 g) id) := by
    funext theta
    rfl
  rw [haction]
  rw [← Measure.map_prod_map volume (_root_.GD.N0232.N0720.N1486.d015866.prod rho)
      (_root_.GD.N0232.N0720.N1178.d016011 g).measurable
      ((_root_.GD.N0232.N0720.N1178.d016013 g).measurable.prodMap measurable_id),
    ← Measure.map_prod_map _root_.GD.N0232.N0720.N1486.d015866 rho
      (_root_.GD.N0232.N0720.N1178.d016013 g).measurable measurable_id,
    _root_.GD.N0232.N0720.N1178.d016019,
    _root_.GD.N0232.N0720.N1178.d016025,
    Measure.map_id,
    Measure.prod_smul_left,
    Measure.prod_smul_left,
    Measure.prod_smul_right,
    smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul
    (inv_nonneg.mpr g.d009240.le)]
  congr 1
  field_simp [g.d009240.ne']

end

end N1178
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1178.d016021
#print axioms _root_.GD.N0232.N0720.N1178.d016025
#print axioms _root_.GD.N0232.N0720.N1178.d016026
