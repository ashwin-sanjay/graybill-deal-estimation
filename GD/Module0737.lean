import GD.Module0147
import GD.Module0730
import GD.Module0736
















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0811

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0718


def d011036
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.N0816.d010975 k sizes) : ℝ :=
  (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta d).toReal /
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta



def d011037
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes) : ℝ :=
  (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q)).toReal /
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta


theorem d011038
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {d : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta d ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (hd theta)
  unfold _root_.GD.N0232.N0719.N0858.d010852
  exact ENNReal.ofReal_ne_top


theorem d011039
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    0 ≤ _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta p q := by
  unfold _root_.GD.N0232.N0719.N0811.d011037
  exact div_nonneg ENNReal.toReal_nonneg
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta).le






theorem d011040
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta
        (_root_.GD.N0230.N0718.d001528 p q) +
        _root_.GD.N0232.N0719.N0811.d011037 k sizes hk hsizes theta p q =
      (_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta p +
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta q) / 2 := by
  have hraw :=
    _root_.GD.N0230.N0670.d001649
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta)
      theta.location p q
      (_root_.GD.N0232.N0719.N0811.d011038 k sizes hk hsizes hp theta)
      (_root_.GD.N0232.N0719.N0811.d011038 k sizes hk hsizes hq theta)
  have hcap : _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta ≠ 0 :=
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta).ne'
  have hraw' :
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0230.N0718.d001528 p q)).toReal +
          (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
            (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q)).toReal =
        ((_root_.GD.N0232.N0719.N0859.d010821 k sizes theta p).toReal +
          (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal) / 2 := by
    exact hraw
  unfold _root_.GD.N0232.N0719.N0811.d011036 _root_.GD.N0232.N0719.N0811.d011037
  calc
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0230.N0718.d001528 p q)).toReal /
          _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta +
        (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
          (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q)).toReal /
          _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta =
        ((_root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0230.N0718.d001528 p q)).toReal +
          (_root_.GD.N0230.N0602.d000117 (μ₀ := _root_.GD.N0232.N0719.d009182 k sizes)
            (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) 0 (_root_.GD.N0230.N0670.d001646 p q)).toReal) /
          _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta := by ring
    _ = (((_root_.GD.N0232.N0719.N0859.d010821 k sizes theta p).toReal +
          (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal) / 2) /
          _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta := by rw [hraw']
    _ = ((_root_.GD.N0232.N0719.N0859.d010821 k sizes theta p).toReal /
          _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta +
        (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal /
          _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta) / 2 := by
      field_simp [hcap]


theorem d011041
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    {d : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    ENNReal.ofReal
        (_root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta d) =
      _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes theta d := by
  have hrisk := _root_.GD.N0232.N0719.N0811.d011038 k sizes hk hsizes hd theta
  have hcapPos := _root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta
  unfold _root_.GD.N0232.N0719.N0811.d011036 _root_.GD.N0232.N0719.N0816.d010977 _root_.GD.N0232.N0719.N0858.d010852
  rw [ENNReal.ofReal_div_of_pos hcapPos]
  rw [ENNReal.ofReal_toReal hrisk]

end

end N0811
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0811.d011038
#print axioms _root_.GD.N0232.N0719.N0811.d011039
#print axioms _root_.GD.N0232.N0719.N0811.d011040
#print axioms _root_.GD.N0232.N0719.N0811.d011041
