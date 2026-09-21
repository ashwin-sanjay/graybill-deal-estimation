import GD.Module0027
import GD.Module0624
import GD.Module0629
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Group.Prod


































open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0946

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0107
open _root_.GD.N0230



@[ext]
structure d009229 where
  shift : ℝ
  logScale : ℝ

namespace d009229



def d009230 : _root_.GD.N0232.N0719.N0946.d009229 ≃ ℝ × ℝ where
  toFun g := (g.logScale, g.shift)
  invFun z := ⟨z.2, z.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance d009231 : MeasurableSpace _root_.GD.N0232.N0719.N0946.d009229 :=
  MeasurableSpace.comap _root_.GD.N0232.N0719.N0946.d009229.d009230 inferInstance



def d009232 : _root_.GD.N0232.N0719.N0946.d009229 ≃ᵐ ℝ × ℝ where
  toEquiv := _root_.GD.N0232.N0719.N0946.d009229.d009230
  measurable_toFun := by
    rw [measurable_iff_comap_le]
    exact le_rfl
  measurable_invFun := by
    rw [measurable_iff_comap_le]
    rw [_root_.GD.N0232.N0719.N0946.d009229.d009231, MeasurableSpace.comap_comp]
    change
      MeasurableSpace.comap id
          (inferInstance : MeasurableSpace (ℝ × ℝ)) ≤
        (inferInstance : MeasurableSpace (ℝ × ℝ))
    rw [MeasurableSpace.comap_id]

instance : Mul _root_.GD.N0232.N0719.N0946.d009229 where
  mul g h :=
    ⟨g.shift + Real.exp g.logScale * h.shift,
      g.logScale + h.logScale⟩

instance : One _root_.GD.N0232.N0719.N0946.d009229 where
  one := ⟨0, 0⟩

instance : Inv _root_.GD.N0232.N0719.N0946.d009229 where
  inv g :=
    ⟨-(Real.exp (-g.logScale) * g.shift), -g.logScale⟩

instance : Group _root_.GD.N0232.N0719.N0946.d009229 :=
  Group.ofLeftAxioms
    (by
      intro g h q
      ext
      · change
          (g.shift + Real.exp g.logScale * h.shift) +
              Real.exp (g.logScale + h.logScale) * q.shift =
            g.shift + Real.exp g.logScale *
              (h.shift + Real.exp h.logScale * q.shift)
        rw [Real.exp_add]
        ring
      · change (g.logScale + h.logScale) + q.logScale =
          g.logScale + (h.logScale + q.logScale)
        ring)
    (by
      intro g
      ext
      · change 0 + Real.exp 0 * g.shift = g.shift
        simp
      · change 0 + g.logScale = g.logScale
        ring)
    (by
      intro g
      ext
      · change
          -(Real.exp (-g.logScale) * g.shift) +
              Real.exp (-g.logScale) * g.shift = 0
        ring
      · change -g.logScale + g.logScale = 0
        ring)

@[simp] theorem d009233 : (1 : _root_.GD.N0232.N0719.N0946.d009229).shift = 0 := rfl
@[simp] theorem d009234 : (1 : _root_.GD.N0232.N0719.N0946.d009229).logScale = 0 := rfl
@[simp] theorem d009235 (g h : _root_.GD.N0232.N0719.N0946.d009229) :
    (g * h).shift = g.shift + Real.exp g.logScale * h.shift := rfl
@[simp] theorem d009236 (g h : _root_.GD.N0232.N0719.N0946.d009229) :
    (g * h).logScale = g.logScale + h.logScale := rfl
@[simp] theorem d009237 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    g⁻¹.shift = -(Real.exp (-g.logScale) * g.shift) := rfl
@[simp] theorem d009238 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    g⁻¹.logScale = -g.logScale := rfl


def d009239 (g : _root_.GD.N0232.N0719.N0946.d009229) : ℝ := Real.exp g.logScale

theorem d009240 (g : _root_.GD.N0232.N0719.N0946.d009229) : 0 < g.d009239 :=
  Real.exp_pos _

@[simp] theorem d009241 (g : _root_.GD.N0232.N0719.N0946.d009229) : g.d009239 ≠ 0 :=
  g.d009240.ne'

@[simp] theorem d009242 : _root_.GD.N0232.N0719.N0946.d009229.d009239 1 = 1 := by simp [_root_.GD.N0232.N0719.N0946.d009229.d009239]

@[simp] theorem d009243 (g h : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0719.N0946.d009229.d009239 (g * h) = _root_.GD.N0232.N0719.N0946.d009229.d009239 g * _root_.GD.N0232.N0719.N0946.d009229.d009239 h := by
  simp [_root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_add]


instance : MulAction _root_.GD.N0232.N0719.N0946.d009229 ℝ where
  smul g y := g.shift + g.d009239 * y
  one_smul y := by
    change 0 + Real.exp 0 * y = y
    simp
  mul_smul g h y := by
    change
      (g.shift + Real.exp g.logScale * h.shift) +
          Real.exp (g.logScale + h.logScale) * y =
        g.shift + Real.exp g.logScale *
          (h.shift + Real.exp h.logScale * y)
    rw [Real.exp_add]
    ring

@[simp] theorem d009244 (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) :
    g • y = g.shift + g.d009239 * y := rfl

theorem d009245 : Measurable _root_.GD.N0232.N0719.N0946.d009229.d009230 :=
  _root_.GD.N0232.N0719.N0946.d009229.d009232.measurable

theorem d009246 : Measurable (fun g : _root_.GD.N0232.N0719.N0946.d009229 ↦ g.shift) := by
  exact measurable_snd.comp _root_.GD.N0232.N0719.N0946.d009229.d009245

theorem d009247 : Measurable (fun g : _root_.GD.N0232.N0719.N0946.d009229 ↦ g.logScale) := by
  exact measurable_fst.comp _root_.GD.N0232.N0719.N0946.d009229.d009245

theorem d009248 : Measurable _root_.GD.N0232.N0719.N0946.d009229.d009239 := by
  exact Real.measurable_exp.comp _root_.GD.N0232.N0719.N0946.d009229.d009247

instance : MeasurableInv _root_.GD.N0232.N0719.N0946.d009229 where
  measurable_inv := by
    have hc : Measurable
        (fun g : _root_.GD.N0232.N0719.N0946.d009229 ↦
          (-g.logScale, -(Real.exp (-g.logScale) * g.shift))) :=
      _root_.GD.N0232.N0719.N0946.d009229.d009247.neg.prodMk
      ((Real.measurable_exp.comp _root_.GD.N0232.N0719.N0946.d009229.d009247.neg).mul
        _root_.GD.N0232.N0719.N0946.d009229.d009246 |>.neg)
    have heq : (Inv.inv : _root_.GD.N0232.N0719.N0946.d009229 → _root_.GD.N0232.N0719.N0946.d009229) =
        _root_.GD.N0232.N0719.N0946.d009229.d009232.symm ∘
          (fun g : _root_.GD.N0232.N0719.N0946.d009229 ↦
            (-g.logScale, -(Real.exp (-g.logScale) * g.shift))) := by
      funext g
      rfl
    rw [heq]
    exact _root_.GD.N0232.N0719.N0946.d009229.d009232.symm.measurable.comp hc

instance : MeasurableMul₂ _root_.GD.N0232.N0719.N0946.d009229 where
  measurable_mul := by
    have hc : Measurable
        (fun z : _root_.GD.N0232.N0719.N0946.d009229 × _root_.GD.N0232.N0719.N0946.d009229 ↦
          (z.1.logScale + z.2.logScale,
            z.1.shift + z.1.d009239 * z.2.shift)) :=
      (((_root_.GD.N0232.N0719.N0946.d009229.d009247.comp measurable_fst).add
          (_root_.GD.N0232.N0719.N0946.d009229.d009247.comp measurable_snd)).prodMk
        ((_root_.GD.N0232.N0719.N0946.d009229.d009246.comp measurable_fst).add
          (((_root_.GD.N0232.N0719.N0946.d009229.d009248.comp measurable_fst).mul
            (_root_.GD.N0232.N0719.N0946.d009229.d009246.comp measurable_snd)))))
    have heq : (fun z : _root_.GD.N0232.N0719.N0946.d009229 × _root_.GD.N0232.N0719.N0946.d009229 ↦ z.1 * z.2) =
        _root_.GD.N0232.N0719.N0946.d009229.d009232.symm ∘
          (fun z : _root_.GD.N0232.N0719.N0946.d009229 × _root_.GD.N0232.N0719.N0946.d009229 ↦
            (z.1.logScale + z.2.logScale,
              z.1.shift + z.1.d009239 * z.2.shift)) := by
      funext z
      rfl
    rw [heq]
    exact _root_.GD.N0232.N0719.N0946.d009229.d009232.symm.measurable.comp hc

instance : MeasurableSMul₂ _root_.GD.N0232.N0719.N0946.d009229 ℝ where
  measurable_smul := by
    exact (_root_.GD.N0232.N0719.N0946.d009229.d009246.comp measurable_fst).add
      ((_root_.GD.N0232.N0719.N0946.d009229.d009248.comp measurable_fst).mul measurable_snd)


def d009249 (h : _root_.GD.N0232.N0719.N0946.d009229) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 + h.logScale, z.2 + Real.exp z.1 * h.shift)

theorem d009250 (h g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0719.N0946.d009229.d009230 (g * h) = _root_.GD.N0232.N0719.N0946.d009229.d009249 h (_root_.GD.N0232.N0719.N0946.d009229.d009230 g) := rfl

theorem d009251 (h : _root_.GD.N0232.N0719.N0946.d009229) :
    Measurable (_root_.GD.N0232.N0719.N0946.d009229.d009249 h) := by
  unfold _root_.GD.N0232.N0719.N0946.d009229.d009249
  fun_prop



theorem d009252 (h : _root_.GD.N0232.N0719.N0946.d009229) :
    MeasurePreserving (_root_.GD.N0232.N0719.N0946.d009229.d009249 h)
      (volume.prod volume) (volume.prod volume) := by
  have hs := MeasurePreserving.skew_product
    (g := fun r b : ℝ ↦ b + Real.exp r * h.shift)
    (measurePreserving_add_right volume h.logScale)
    (by fun_prop)
    (ae_of_all volume fun r ↦
      (measurePreserving_add_right volume (Real.exp r * h.shift)).map_eq)
  change MeasurePreserving
    (fun z : ℝ × ℝ ↦
      (z.1 + h.logScale, z.2 + Real.exp z.1 * h.shift))
    (volume.prod volume) (volume.prod volume)
  exact hs


def d009253 : Measure (ℝ × ℝ) :=
  (ProbabilityTheory.gaussianReal 0 1).prod
    (ProbabilityTheory.gaussianReal 0 1)

instance : IsProbabilityMeasure _root_.GD.N0232.N0719.N0946.d009229.d009253 := by
  unfold _root_.GD.N0232.N0719.N0946.d009229.d009253
  infer_instance



def d009254 : Measure _root_.GD.N0232.N0719.N0946.d009229 :=
  _root_.GD.N0232.N0719.N0946.d009229.d009253.comap _root_.GD.N0232.N0719.N0946.d009229.d009232

instance : IsProbabilityMeasure _root_.GD.N0232.N0719.N0946.d009229.d009254 := by
  unfold _root_.GD.N0232.N0719.N0946.d009229.d009254
  infer_instance



theorem d009255 :
    _root_.GD.N0232.N0719.N0946.d009229.d009253 ≪ volume.prod volume := by
  exact (ProbabilityTheory.gaussianReal_absolutelyContinuous 0
      (v := 1) (by norm_num)).prod
    (ProbabilityTheory.gaussianReal_absolutelyContinuous 0
      (v := 1) (by norm_num))

theorem d009256 :
    volume.prod volume ≪ _root_.GD.N0232.N0719.N0946.d009229.d009253 := by
  exact (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0
      (v := 1) (by norm_num)).prod
    (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0
      (v := 1) (by norm_num))


theorem d009257 (h : _root_.GD.N0232.N0719.N0946.d009229) :
    Measure.QuasiMeasurePreserving (fun g : _root_.GD.N0232.N0719.N0946.d009229 ↦ g * h)
      _root_.GD.N0232.N0719.N0946.d009229.d009254 _root_.GD.N0232.N0719.N0946.d009229.d009254 := by
  let e := _root_.GD.N0232.N0719.N0946.d009229.d009232
  have heForward : Measure.QuasiMeasurePreserving e _root_.GD.N0232.N0719.N0946.d009229.d009254 _root_.GD.N0232.N0719.N0946.d009229.d009253 := by
    refine ⟨e.measurable, ?_⟩
    have hmap : Measure.map e _root_.GD.N0232.N0719.N0946.d009229.d009254 = _root_.GD.N0232.N0719.N0946.d009229.d009253 := by
      dsimp [e]
      rw [_root_.GD.N0232.N0719.N0946.d009229.d009254, ← MeasurableEquiv.map_symm]
      exact MeasurableEquiv.map_map_symm _root_.GD.N0232.N0719.N0946.d009229.d009232
    rw [hmap]
  have heBackward : Measure.QuasiMeasurePreserving e.symm _root_.GD.N0232.N0719.N0946.d009229.d009253 _root_.GD.N0232.N0719.N0946.d009229.d009254 := by
    refine ⟨e.symm.measurable, ?_⟩
    have hmap : Measure.map e.symm _root_.GD.N0232.N0719.N0946.d009229.d009253 = _root_.GD.N0232.N0719.N0946.d009229.d009254 := by
      dsimp [e]
      exact MeasurableEquiv.map_symm _root_.GD.N0232.N0719.N0946.d009229.d009232
    rw [hmap]
  have hcoord : Measure.QuasiMeasurePreserving (_root_.GD.N0232.N0719.N0946.d009229.d009249 h)
      _root_.GD.N0232.N0719.N0946.d009229.d009253 _root_.GD.N0232.N0719.N0946.d009229.d009253 :=
    (_root_.GD.N0232.N0719.N0946.d009229.d009252 h).quasiMeasurePreserving.mono
      _root_.GD.N0232.N0719.N0946.d009229.d009255
      _root_.GD.N0232.N0719.N0946.d009229.d009256
  have hcomp := heBackward.comp (hcoord.comp heForward)
  have hfun :
      (e.symm ∘ _root_.GD.N0232.N0719.N0946.d009229.d009249 h ∘ e) =
        (fun g : _root_.GD.N0232.N0719.N0946.d009229 ↦ g * h) := by
    funext g
    apply e.injective
    exact _root_.GD.N0232.N0719.N0946.d009229.d009250 h g
  rw [← hfun]
  exact hcomp

end d009229



variable {k : ℕ} {sizes : Fin k → ℕ}

@[simp] theorem d009258 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    g • omega = _root_.GD.N0232.N0719.N0900.d009095 k sizes g.shift g.d009239 omega := by
  rfl

instance d009259 :
    MeasurableSMul₂ _root_.GD.N0232.N0719.N0946.d009229 (_root_.GD.N0232.N0719.d009173 k sizes) where
  measurable_smul := by
    change Measurable
      (fun z : _root_.GD.N0232.N0719.N0946.d009229 × _root_.GD.N0232.N0719.d009173 k sizes ↦
        _root_.GD.N0232.N0719.N0900.d009095 k sizes z.1.shift z.1.d009239 z.2)
    unfold _root_.GD.N0232.N0719.N0900.d009095 _root_.GD.N0107.d009018
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact (_root_.GD.N0232.N0719.N0946.d009229.d009246.comp measurable_fst).add
      ((_root_.GD.N0232.N0719.N0946.d009229.d009248.comp measurable_fst).mul
        ((measurable_pi_apply j).comp
          ((measurable_pi_apply i).comp measurable_snd)))



theorem d009260
    (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i) :
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0719.d009173 k sizes) ↦ g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y)
      (_root_.GD.N0232.N0719.N0900.d009111 k sizes) := by
  intro g omega
  exact _root_.GD.N0232.N0719.N0900.d009147 hk hsizes
    g.shift g.d009240 omega









theorem d009261
    (mu : Measure (_root_.GD.N0232.N0719.d009173 k sizes)) [SFinite mu]
    (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (value : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hvalue : Measurable value)
    (hcov : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun omega ↦ value (g • omega)) =ᵐ[mu]
        fun omega ↦ g • value omega) :
    ∃ repaired : _root_.GD.N0232.N0719.d009173 k sizes → ℝ,
      Measurable repaired ∧
      repaired =ᵐ[mu] value ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0719.d009173 k sizes) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) repaired := by
  letI : MeasurableSMul₂ _root_.GD.N0232.N0719.N0946.d009229 (_root_.GD.N0232.N0719.d009173 k sizes) :=
    _root_.GD.N0232.N0719.N0946.d009259 (k := k) (sizes := sizes)
  exact _root_.GD.N0230.N0605.d000343
      (G := _root_.GD.N0232.N0719.N0946.d009229) (X := _root_.GD.N0232.N0719.d009173 k sizes)
      mu _root_.GD.N0232.N0719.N0946.d009229.d009254 value (_root_.GD.N0232.N0719.N0900.d009111 k sizes)
      hvalue (_root_.GD.N0232.N0719.N0900.d009122 k sizes)
      (_root_.GD.N0232.N0719.N0946.d009260 hk hsizes)
      hcov _root_.GD.N0232.N0719.N0946.d009229.d009257








theorem d009262
    (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (value : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hvalue : Measurable value)
    (hcov : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun omega ↦ value (g • omega)) =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes]
        fun omega ↦ g • value omega) :
    ∃ repaired : _root_.GD.N0232.N0719.d009173 k sizes → ℝ,
      Measurable repaired ∧
      (∀ (location : ℝ) (scale : Fin k → ℝ),
        (∀ i, 0 < scale i) →
          repaired =ᵐ[_root_.GD.N0232.N0719.d009176 k sizes location scale] value) ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0719.d009173 k sizes) ↦ g • omega)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) repaired := by
  rcases _root_.GD.N0232.N0719.N0946.d009261
      (mu := _root_.GD.N0232.N0719.d009182 k sizes) hk hsizes value hvalue hcov with
    ⟨repaired, hrepairedMeas, hrepairedRef, hrepairedEquivariant⟩
  refine ⟨repaired, hrepairedMeas, ?_, hrepairedEquivariant⟩
  intro location scale hscale
  exact hrepairedRef.filter_mono
    ((_root_.GD.N0232.N0719.d009183
      k sizes location scale hscale).1.ae_le)

end

end N0946
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0946.d009229.d009252
#print axioms _root_.GD.N0232.N0719.N0946.d009229.d009257
#print axioms _root_.GD.N0232.N0719.N0946.d009261
#print axioms _root_.GD.N0232.N0719.N0946.d009262
