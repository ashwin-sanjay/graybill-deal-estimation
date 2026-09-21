import GD.Module0013
import GD.Module0731
import GD.Module0734














open Filter MeasureTheory

namespace GD
namespace N0232
namespace N0719
namespace N0829

noncomputable section

open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0840
open _root_.GD.N0232.N0719.N0828
open _root_.GD.N0230.N0655
open _root_.GD.N0230.N0594

variable (k : ℕ) (sizes : Fin k → ℕ)




theorem d011030
    (parameter : ℕ → _root_.GD.N0230.N0655.d000349)
    (limitParameter : _root_.GD.N0230.N0655.d000349)
    (hparameter : Tendsto parameter atTop (nhds limitParameter))
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hdMeasurable : Measurable d)
    {p : ENNReal} (hpTop : p ≠ ⊤) (hpZero : p ≠ 0)
    (hdLp : MemLp d p
      ((_root_.GD.N0232.N0719.d009182 k sizes).map
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes
          limitParameter.1 limitParameter.2)))
    (hregular :
      ((_root_.GD.N0232.N0719.d009182 k sizes).map
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes
          limitParameter.1 limitParameter.2)).WeaklyRegular) :
    TendstoInMeasure (_root_.GD.N0232.N0719.d009182 k sizes)
      (fun n ↦ _root_.GD.N0232.N0719.N0842.d010911 k sizes
        (parameter n).1 (parameter n).2 d)
      atTop
      (_root_.GD.N0232.N0719.N0842.d010911 k sizes
        limitParameter.1 limitParameter.2 d) := by
  apply _root_.GD.N0232.N0719.N0840.d011029
    k sizes parameter limitParameter hparameter d hdMeasurable
      hpTop hpZero hdLp hregular
  intro s hs delta hdelta
  exact _root_.GD.N0232.N0719.N0828.d010999
    k sizes parameter limitParameter hparameter s hs delta hdelta










theorem d011031
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hdMeasurable : Measurable d)
    {p : ENNReal} (hpTop : p ≠ ⊤) (hpZero : p ≠ 0)
    (hfixed : ∀ i : _root_.GD.N0230.N0655.d000350,
      _root_.GD.N0232.N0719.N0842.d010911 k sizes (_root_.GD.N0230.N0655.d000351 i).1 (_root_.GD.N0230.N0655.d000351 i).2 d =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes] d)
    (hdLp : ∀ g : _root_.GD.N0230.N0655.d000349,
      MemLp d p
        ((_root_.GD.N0232.N0719.d009182 k sizes).map
          (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 g.2)))
    (hregular : ∀ g : _root_.GD.N0230.N0655.d000349,
      ((_root_.GD.N0232.N0719.d009182 k sizes).map
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.1 g.2)).WeaklyRegular) :
    ∀ g : _root_.GD.N0230.N0655.d000349,
      _root_.GD.N0232.N0719.N0842.d010911 k sizes g.1 g.2 d =ᵐ[_root_.GD.N0232.N0719.d009182 k sizes] d := by
  apply _root_.GD.N0230.N0594.d000115
    (_root_.GD.N0232.N0719.d009182 k sizes) _root_.GD.N0230.N0655.d000351 _root_.GD.N0230.N0655.d000353
      (fun g ↦ _root_.GD.N0232.N0719.N0842.d010911 k sizes g.1 g.2 d) d
      hdMeasurable.aestronglyMeasurable hfixed
  intro sequence g hsequence
  exact _root_.GD.N0232.N0719.N0829.d011030
    k sizes (fun n ↦ _root_.GD.N0230.N0655.d000351 (sequence n)) g hsequence d hdMeasurable
      hpTop hpZero (hdLp g) (hregular g)

end

end N0829
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0829.d011030
#print axioms _root_.GD.N0232.N0719.N0829.d011031
