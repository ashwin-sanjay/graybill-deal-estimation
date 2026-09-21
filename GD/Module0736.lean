import GD.Module0091
import GD.Module0725























open Set MeasureTheory
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0858

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0230.N0633
open _root_.GD.N0230.N0602

variable
  (k : ℕ) (sizes : Fin k → ℕ)
  (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)



noncomputable def d011032 : ℝ :=
  Real.sqrt
    (_root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k))



theorem d011033
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes))
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    ‖d‖ ^ 2 ≤
      _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) := by
  have href := hd (_root_.GD.N0232.N0719.N0859.d010810 k)
  rw [_root_.GD.N0232.N0719.N0859.d010829 k sizes, _root_.GD.N0232.N0719.N0858.d010852] at href
  have hcap : 0 ≤
      _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) :=
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)).le
  have hsq :
      ‖(0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes)) - d‖ ^ 2 ≤
        _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k) :=
    (ENNReal.ofReal_le_ofReal_iff hcap).mp href
  simpa using hsq


theorem d011034
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes))
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    ‖d‖ ≤ _root_.GD.N0232.N0719.N0858.d011032 k sizes hk hsizes := by
  apply (Real.le_sqrt (norm_nonneg d)
    ((_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)).le)).2
  exact _root_.GD.N0232.N0719.N0858.d011033 k sizes hk hsizes d hd




theorem d011035 :
    IsCompact
      (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes)) ''
        _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) := by
  exact _root_.GD.N0230.N0633.d001201
    (_root_.GD.N0232.N0719.N0858.d011032 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0858.d010861 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0858.d011034 k sizes hk hsizes)

end
end N0858
end N0719
end N0232
end GD
