import GD.Module0011
import GD.Module0021

















open MeasureTheory
open scoped BigOperators

namespace GD
namespace N0230
namespace N0689

noncomputable section

open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0623

variable {Theta X V E : Type*}
  [MeasurableSpace Theta] [MeasurableSpace X]
  [Fintype V] [Fintype E] [DecidableEq V]



theorem d000663
    (source sink : V → ℝ)
    (hstrict : ∑ v, source v < ∑ v, sink v) :
    ∃ v, source v < sink v := by
  by_contra hnone
  push Not at hnone
  have hsum : ∑ v, sink v ≤ ∑ v, source v := by
    exact Finset.sum_le_sum fun v _hv ↦ hnone v
  exact (not_lt_of_ge hsum) hstrict





theorem d000664
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center boundaryFlux : X → ℝ)
    (src dst : E → V) (flux : E → ℝ)
    (source sink : V → ℝ)
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x)
    (hdeficit : Integrable
      (_root_.GD.N0230.N0589.d000096 likelihood target action center).uncurry
      (prior.prod data))
    (htax : Integrable (_root_.GD.N0230.N0589.d000089 prior likelihood action center) data)
    (hboundary : Integrable boundaryFlux data)
    (hmarginal : ∀ᵐ x ∂data,
      0 < _root_.GD.N0230.N0589.d000088 prior likelihood x)
    (hbalance : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000099 prior likelihood target action center x =
        _root_.GD.N0230.N0589.d000089 prior likelihood action center x + boundaryFlux x)
    (hnonpos : ∀ theta,
      _root_.GD.N0230.N0589.d000098 data likelihood target action center theta ≤ 0)
    (hboundaryNetwork :
      ∫ x, boundaryFlux x ∂data =
        ∑ v, _root_.GD.N0230.N0623.d000204 src dst flux source sink v)
    (hdistinct : ¬ action =ᵐ[data] center) :
    ∑ v, source v < ∑ v, sink v := by
  have hnegative := _root_.GD.N0230.N0589.d000106
    prior data likelihood target action center boundaryFlux
    hlikelihood hdeficit htax hboundary hmarginal hbalance hnonpos hdistinct
  rw [_root_.GD.N0230.N0623.d000207] at hboundaryNetwork
  linarith










theorem d000665
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center boundaryFlux : X → ℝ)
    (src dst : E → V) (flux : E → ℝ)
    (affineEndFlux : ℝ)
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x)
    (hdeficit : Integrable
      (_root_.GD.N0230.N0589.d000096 likelihood target action center).uncurry
      (prior.prod data))
    (htax : Integrable (_root_.GD.N0230.N0589.d000089 prior likelihood action center) data)
    (hboundary : Integrable boundaryFlux data)
    (hmarginal : ∀ᵐ x ∂data,
      0 < _root_.GD.N0230.N0589.d000088 prior likelihood x)
    (hbalance : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000099 prior likelihood target action center x =
        _root_.GD.N0230.N0589.d000089 prior likelihood action center x + boundaryFlux x)
    (hnonpos : ∀ theta,
      _root_.GD.N0230.N0589.d000098 data likelihood target action center theta ≤ 0)
    (hboundarySplit :
      ∫ x, boundaryFlux x ∂data =
        ((∑ v, _root_.GD.N0230.N0623.d000202 dst flux v) -
          (∑ v, _root_.GD.N0230.N0623.d000203 src flux v)) +
          affineEndFlux)
    (hdistinct : ¬ action =ᵐ[data] center) :
    affineEndFlux < 0 := by
  have hnegative := _root_.GD.N0230.N0589.d000106
    prior data likelihood target action center boundaryFlux
    hlikelihood hdeficit htax hboundary hmarginal hbalance hnonpos hdistinct
  have hinternal :
      (∑ v, _root_.GD.N0230.N0623.d000202 dst flux v) -
        (∑ v, _root_.GD.N0230.N0623.d000203 src flux v) = 0 := by
    rw [_root_.GD.N0230.N0623.d000205, _root_.GD.N0230.N0623.d000206]
    ring
  rw [hinternal, zero_add] at hboundarySplit
  simpa [hboundarySplit] using hnegative




theorem d000666
    (prior : Measure Theta) (data : Measure X)
    [SFinite prior] [SFinite data]
    (likelihood : Theta → X → ℝ) (target : Theta → ℝ)
    (action center boundaryFlux : X → ℝ)
    (src dst : E → V) (flux : E → ℝ)
    (source sink : V → ℝ)
    (hlikelihood : ∀ theta x, 0 ≤ likelihood theta x)
    (hdeficit : Integrable
      (_root_.GD.N0230.N0589.d000096 likelihood target action center).uncurry
      (prior.prod data))
    (htax : Integrable (_root_.GD.N0230.N0589.d000089 prior likelihood action center) data)
    (hboundary : Integrable boundaryFlux data)
    (hmarginal : ∀ᵐ x ∂data,
      0 < _root_.GD.N0230.N0589.d000088 prior likelihood x)
    (hbalance : ∀ᵐ x ∂data,
      _root_.GD.N0230.N0589.d000099 prior likelihood target action center x =
        _root_.GD.N0230.N0589.d000089 prior likelihood action center x + boundaryFlux x)
    (hnonpos : ∀ theta,
      _root_.GD.N0230.N0589.d000098 data likelihood target action center theta ≤ 0)
    (hboundaryNetwork :
      ∫ x, boundaryFlux x ∂data =
        ∑ v, _root_.GD.N0230.N0623.d000204 src dst flux source sink v)
    (hclosed : ∑ v, source v = ∑ v, sink v) :
    action =ᵐ[data] center := by
  by_contra hdistinct
  have hstrict := _root_.GD.N0230.N0689.d000664
    prior data likelihood target action center boundaryFlux
    src dst flux source sink hlikelihood hdeficit htax hboundary
    hmarginal hbalance hnonpos hboundaryNetwork hdistinct
  exact (not_lt_of_ge hclosed.ge) hstrict

end

end N0689
end N0230
end GD

#print axioms _root_.GD.N0230.N0689.d000664
#print axioms _root_.GD.N0230.N0689.d000666
#print axioms _root_.GD.N0230.N0689.d000663
#print axioms _root_.GD.N0230.N0689.d000665
