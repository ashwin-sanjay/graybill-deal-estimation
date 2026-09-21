import Mathlib.MeasureTheory.Integral.Prod





















open MeasureTheory

namespace GD
namespace N0230
namespace N0706

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]



theorem d001169
    (μ : Measure Ω) [SFinite μ] (e f g : Ω → ℝ)
    (he : Integrable e μ)
    (hef : Integrable (fun x ↦ e x * f x) μ)
    (heg : Integrable (fun x ↦ e x * g x) μ)
    (hefg : Integrable (fun x ↦ e x * (f x * g x)) μ) :
    (∫ z : Ω × Ω,
        e z.1 * e z.2 *
          (f z.1 - f z.2) * (g z.1 - g z.2) ∂μ.prod μ) =
      2 *
        ((∫ x, e x ∂μ) * (∫ x, e x * (f x * g x) ∂μ) -
          (∫ x, e x * f x ∂μ) * (∫ x, e x * g x ∂μ)) := by
  let ef : Ω → ℝ := fun x ↦ e x * f x
  let eg : Ω → ℝ := fun x ↦ e x * g x
  let efg : Ω → ℝ := fun x ↦ e x * (f x * g x)
  have h11 : Integrable
      (fun z : Ω × Ω ↦ efg z.1 * e z.2) (μ.prod μ) :=
    hefg.mul_prod he
  have h12 : Integrable
      (fun z : Ω × Ω ↦ ef z.1 * eg z.2) (μ.prod μ) :=
    hef.mul_prod heg
  have h21 : Integrable
      (fun z : Ω × Ω ↦ eg z.1 * ef z.2) (μ.prod μ) :=
    heg.mul_prod hef
  have h22 : Integrable
      (fun z : Ω × Ω ↦ e z.1 * efg z.2) (μ.prod μ) :=
    he.mul_prod hefg
  have hexpand :
      (fun z : Ω × Ω ↦
        e z.1 * e z.2 *
          (f z.1 - f z.2) * (g z.1 - g z.2)) =
      (fun z ↦
        efg z.1 * e z.2 - ef z.1 * eg z.2 -
          eg z.1 * ef z.2 + e z.1 * efg z.2) := by
    funext z
    simp only [ef, eg, efg]
    ring
  have hintegralExpand :
      (∫ z : Ω × Ω,
        efg z.1 * e z.2 - ef z.1 * eg z.2 -
          eg z.1 * ef z.2 + e z.1 * efg z.2 ∂μ.prod μ) =
      (∫ z : Ω × Ω, efg z.1 * e z.2 ∂μ.prod μ) -
        (∫ z : Ω × Ω, ef z.1 * eg z.2 ∂μ.prod μ) -
        (∫ z : Ω × Ω, eg z.1 * ef z.2 ∂μ.prod μ) +
        (∫ z : Ω × Ω, e z.1 * efg z.2 ∂μ.prod μ) := by
    have hsub12 :
        (∫ z : Ω × Ω,
          efg z.1 * e z.2 - ef z.1 * eg z.2 ∂μ.prod μ) =
        (∫ z : Ω × Ω, efg z.1 * e z.2 ∂μ.prod μ) -
          ∫ z : Ω × Ω, ef z.1 * eg z.2 ∂μ.prod μ :=
      integral_sub h11 h12
    have hsub123 :
        (∫ z : Ω × Ω,
          (efg z.1 * e z.2 - ef z.1 * eg z.2) -
            eg z.1 * ef z.2 ∂μ.prod μ) =
        (∫ z : Ω × Ω,
          efg z.1 * e z.2 - ef z.1 * eg z.2 ∂μ.prod μ) -
          ∫ z : Ω × Ω, eg z.1 * ef z.2 ∂μ.prod μ :=
      integral_sub (h11.sub h12) h21
    have hadd :
        (∫ z : Ω × Ω,
          (efg z.1 * e z.2 - ef z.1 * eg z.2) -
            eg z.1 * ef z.2 + e z.1 * efg z.2 ∂μ.prod μ) =
        (∫ z : Ω × Ω,
          (efg z.1 * e z.2 - ef z.1 * eg z.2) -
            eg z.1 * ef z.2 ∂μ.prod μ) +
          ∫ z : Ω × Ω, e z.1 * efg z.2 ∂μ.prod μ :=
      integral_add ((h11.sub h12).sub h21) h22
    rw [hadd, hsub123, hsub12]
  rw [hexpand, hintegralExpand]
  rw [integral_prod_mul efg e, integral_prod_mul ef eg,
    integral_prod_mul eg ef, integral_prod_mul e efg]
  simp only [ef, eg, efg]
  ring

end

end N0706
end N0230
end GD

#print axioms _root_.GD.N0230.N0706.d001169
