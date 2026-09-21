import GD.Module0738
import GD.Module0769




















open MeasureTheory Set

namespace GD
namespace N0232
namespace N0719
namespace N0806

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0811
open _root_.GD.N0232.N0719.N0812
open _root_.GD.N0232.N0719.N0814
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0718


theorem d011707
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {d : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta d ≤ 1 := by
  have hle := _root_.GD.N0232.N0719.N0812.d011042
    k sizes hk hsizes hd theta
  have hreal := ENNReal.toReal_mono ENNReal.one_ne_top hle
  rw [_root_.GD.N0232.N0719.N0812.d011045
    k sizes hk hsizes theta hd, ENNReal.toReal_one] at hreal
  exact hreal



theorem d011708
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta p q ≤ 1 := by
  have hpOne := _root_.GD.N0232.N0719.N0806.d011707
    k sizes hk hsizes hp theta
  have hqOne := _root_.GD.N0232.N0719.N0806.d011707
    k sizes hk hsizes hq theta
  have hmidNonneg := _root_.GD.N0232.N0719.N0812.d011044
    k sizes hk hsizes theta (_root_.GD.N0230.N0718.d001528 p q)
  have hidentity := _root_.GD.N0232.N0719.N0811.d011040
    k sizes hk hsizes theta hp hq
  linarith



theorem d011709
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    ‖_root_.GD.N0232.N0719.N0814.d011692 k sizes hk hsizes theta p q hp hq‖ ^ 2 ≤
      _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta := by
  have htax := _root_.GD.N0232.N0719.N0806.d011708
    k sizes hk hsizes theta hp hq
  have hcap := _root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta
  unfold _root_.GD.N0232.N0719.N0811.d011037 at htax
  have hnum :
      (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q)).toReal ≤
          _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta :=
    (div_le_one hcap).mp htax
  calc
    ‖_root_.GD.N0232.N0719.N0814.d011692 k sizes hk hsizes theta p q hp hq‖ ^ 2 =
        (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.N0859.d010813 k sizes)
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q)).toReal :=
      _root_.GD.N0232.N0719.N0814.d011700
        k sizes hk hsizes theta p q hp hq
    _ ≤ _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta := hnum

end

end N0806
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0806.d011707
#print axioms _root_.GD.N0232.N0719.N0806.d011708
#print axioms _root_.GD.N0232.N0719.N0806.d011709
