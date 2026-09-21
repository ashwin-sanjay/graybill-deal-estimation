import GD.Module0051
import Mathlib.Data.ENNReal.Real





















open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace GD
namespace N0230
namespace N0636

open _root_.GD.N0230.N0688

noncomputable section

universe u

variable {Omega : Type u} [MeasurableSpace Omega]









structure d000655 (mu : Measure Omega) where
  actionLaw : Omega -> _root_.GD.N0230.N0688.d000642
  dispersion_aemeasurable :
    AEMeasurable
      (fun omega => (actionLaw omega).d000644) mu

namespace d000655

variable {mu : Measure Omega}


def d000656 (field : _root_.GD.N0230.N0636.d000655 mu) : ENNReal :=
  ∫⁻ omega,
    ENNReal.ofReal ((field.actionLaw omega).d000644) ∂mu


theorem d000657
    (field : _root_.GD.N0230.N0636.d000655 mu) (omega : Omega) :
    0 <= (field.actionLaw omega).d000644 :=
  variance_nonneg _ _


theorem d000658
    (field : _root_.GD.N0230.N0636.d000655 mu) :
    AEMeasurable
      (fun omega =>
        ENNReal.ofReal ((field.actionLaw omega).d000644)) mu :=
  field.dispersion_aemeasurable.ennreal_ofReal





theorem d000659
    (field : _root_.GD.N0230.N0636.d000655 mu)
    (hzero : field.d000656 = 0) :
    ∀ᵐ omega ∂mu,
      (field.actionLaw omega).d000644 = 0 := by
  have hzero_ofReal :
      (fun omega =>
        ENNReal.ofReal ((field.actionLaw omega).d000644)) =ᵐ[mu]
          fun _ => 0 :=
    (lintegral_eq_zero_iff' field.d000658).1 hzero
  filter_upwards [hzero_ofReal] with omega homega
  have hle : (field.actionLaw omega).d000644 <= 0 :=
    ENNReal.ofReal_eq_zero.mp homega
  exact le_antisymm hle (field.d000657 omega)





theorem d000660
    (field : _root_.GD.N0230.N0636.d000655 mu)
    (hzero : field.d000656 = 0) :
    ∀ᵐ omega ∂mu,
      field.actionLaw omega =
        _root_.GD.N0230.N0688.d000642.d000646
          (field.actionLaw omega).d000643 := by
  filter_upwards
    [field.d000659 hzero]
      with omega homega
  exact
    _root_.GD.N0230.N0688.d000642.d000653
      _ homega





theorem d000661
    (field : _root_.GD.N0230.N0636.d000655 mu)
    (hzero : field.d000656 = 0) :
    ∀ᵐ omega ∂mu,
      (field.actionLaw omega).measure =
        Measure.dirac (field.actionLaw omega).d000643 := by
  filter_upwards
    [field.d000659 hzero]
      with omega homega
  exact
    _root_.GD.N0230.N0688.d000642.d000652
      _ homega





theorem d000662
    (field : _root_.GD.N0230.N0636.d000655 mu) :
    field.d000656 = 0 ↔
      ∀ᵐ omega ∂mu,
        field.actionLaw omega =
          _root_.GD.N0230.N0688.d000642.d000646
            (field.actionLaw omega).d000643 := by
  constructor
  · exact
      field.d000660
  · intro hpure
    apply
      (lintegral_eq_zero_iff'
        field.d000658).2
    filter_upwards [hpure] with omega homega
    rw [homega]
    simp

end d000655

end

end N0636
end N0230
end GD

#print axioms _root_.GD.N0230.N0636.d000655.d000659
#print axioms _root_.GD.N0230.N0636.d000655.d000661
#print axioms _root_.GD.N0230.N0636.d000655.d000662
