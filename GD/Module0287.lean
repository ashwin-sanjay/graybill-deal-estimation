import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod








open MeasureTheory

namespace GD.N0235



theorem d004256
    {n : ℕ} {α : Fin n → Type*}
    [∀ i, MeasurableSpace (α i)]
    (μ ν : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (hμν : ∀ i, μ i ≪ ν i) :
    Measure.pi μ ≪ Measure.pi ν := by
  induction n with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ n ih =>
      let i : Fin (n + 1) := 0
      let e := MeasurableEquiv.piFinSuccAbove α i
      have htail :
          Measure.pi (fun j : Fin n => μ (i.succAbove j)) ≪
            Measure.pi (fun j : Fin n => ν (i.succAbove j)) := by
        exact ih
          (fun j : Fin n => μ (i.succAbove j))
          (fun j : Fin n => ν (i.succAbove j))
          (fun j => hμν (i.succAbove j))
      have hprod :
          (μ i).prod (Measure.pi (fun j : Fin n => μ (i.succAbove j))) ≪
            (ν i).prod (Measure.pi (fun j : Fin n => ν (i.succAbove j))) :=
        (hμν i).prod htail
      have hmap := hprod.map e.symm.measurable
      rw [
        (measurePreserving_piFinSuccAbove μ i).symm.map_eq,
        (measurePreserving_piFinSuccAbove ν i).symm.map_eq
      ] at hmap
      exact hmap

end GD.N0235
