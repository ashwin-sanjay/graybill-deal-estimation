import GD.Module0677
import Mathlib.MeasureTheory.Constructions.Pi














open MeasureTheory

namespace GD.N0232.N0719.N0922

noncomputable section



theorem d009936 :
    MeasurePreserving _root_.GD.N0232.N0719.N0922.d009920
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
      (Measure.pi fun _ : Fin 2 => (volume : Measure ℝ)) := by
  let shear : ℝ × ℝ → ℝ × ℝ := fun xz => (xz.1, xz.1 + xz.2)
  let swap : ℝ × ℝ → ℝ × ℝ := Prod.swap
  let reflectFirst : ℝ × ℝ → ℝ × ℝ :=
    Prod.map Neg.neg id
  let translateFirst : ℝ × ℝ → ℝ × ℝ :=
    Prod.map (fun x : ℝ => 1 + x) id
  let pairToFin : (ℝ × ℝ) → (Fin 2 → ℝ) :=
    (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ)).symm
  have hshear : MeasurePreserving shear := by
    change MeasurePreserving shear
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
    simpa [shear] using
      (measurePreserving_prod_add (volume : Measure ℝ) (volume : Measure ℝ))
  have hswap : MeasurePreserving swap := by
    change MeasurePreserving swap
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
    simpa [swap] using
      (Measure.measurePreserving_swap :
        MeasurePreserving Prod.swap
          ((volume : Measure ℝ).prod volume)
          ((volume : Measure ℝ).prod volume))
  have hreflect : MeasurePreserving reflectFirst := by
    change MeasurePreserving reflectFirst
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
    simpa [reflectFirst] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
        (MeasurePreserving.id (volume : Measure ℝ))
  have htranslate : MeasurePreserving translateFirst := by
    change MeasurePreserving translateFirst
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
    simpa [translateFirst] using
      (measurePreserving_add_left (volume : Measure ℝ) (1 : ℝ)).prod
        (MeasurePreserving.id (volume : Measure ℝ))
  have hpairToFin : MeasurePreserving pairToFin := by
    simpa [pairToFin] using
      (volume_preserving_finTwoArrow ℝ).symm
        (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ))
  have hcomp :=
    hpairToFin.comp (htranslate.comp (hreflect.comp (hswap.comp hshear)))
  have hcore :
      (translateFirst ∘ reflectFirst ∘ swap ∘ shear) =
        fun xz : ℝ × ℝ => (1 - xz.1 - xz.2, xz.1) := by
    funext xz
    change (1 + -(xz.1 + xz.2), xz.1) =
      (1 - xz.1 - xz.2, xz.1)
    congr 1 <;> ring
  change MeasurePreserving
    (pairToFin ∘ (translateFirst ∘ reflectFirst ∘ swap ∘ shear)) at hcomp
  rw [hcore] at hcomp
  have hchart :
      (pairToFin ∘ fun xz : ℝ × ℝ =>
        (1 - xz.1 - xz.2, xz.1)) = _root_.GD.N0232.N0719.N0922.d009920 := by
    funext xz i
    fin_cases i <;> rfl
  rw [hchart] at hcomp
  exact hcomp

end

end GD.N0232.N0719.N0922
