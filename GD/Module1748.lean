import GD.Module1747
import GD.Module1553
import GD.Module1455
import GD.Module0964

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped Topology BigOperators

namespace GD.N0212.N0466

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N1022
open _root_.GD.N0232.N0719.N0997
open _root_.GD.N0211.N0459
open _root_.GD.N0232.N0719.N0977
open _root_.GD.N0232.N0720.N1341 (d004415)
open _root_.GD.N0230.N0608
open _root_.GD.N0212.N0462

noncomputable section
variable {k : ℕ}




theorem d028993 (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    ¬ _root_.GD.N0232.N0719.N0896.d011132 k sizes := by
  rintro ⟨s, hs⟩
  letI : NeZero k := ⟨by omega⟩
  have hn0 : ∀ i, 0 < sizes i := fun i => lt_of_lt_of_le (by decide : 0 < 2) (hn i)
  obtain ⟨t, ht, hinterval⟩ := _root_.GD.N0212.N0467.d023018 sizes hn0 hs
  have hN : 2 ≤ ∑ i, sizes i := (hn 0).trans
    (Finset.single_le_sum (fun i _ => Nat.zero_le (sizes i)) (Finset.mem_univ 0))
  let d : ℕ := (∑ i, sizes i) - 2
  have hdim : (∑ i, sizes i) = d + 2 := by dsimp [d]; omega
  have hshape (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
      |t ((_root_.GD.N0211.N0459.d020003 sizes hdim).symm (_root_.GD.N0232.N0719.N0977.d009773 d u))| ≤ 1 := by
    apply _root_.GD.N0212.N0467.d023019 sizes hn0 t hinterval
    intro i j
    rw [_root_.GD.N0211.N0459.d020004]
    exact _root_.GD.N0211.N0459.d019960 u _
  obtain ⟨μ, hμ⟩ := _root_.GD.N0212.N0461.d024006
    sizes hdim hn t ht hshape
  exact _root_.GD.N0212.N0465.d028992 hk sizes hn t μ hμ ht



theorem d028994 (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    ¬ _root_.GD.N0232.N0719.N0896.d011130 k sizes hk hn := by
  intro h
  exact _root_.GD.N0212.N0466.d028993 hk sizes hn
    ((_root_.GD.N0232.N0719.N0896.d011133 k sizes hk hn).mpr h)



theorem d028995 (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hstrict : _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hn)) :
    ∃ g : _root_.GD.N0232.N0719.N0946.d009229,
      0 < _root_.GD.N0232.N0719.N0896.d011114 k sizes s g :=
  _root_.GD.N0232.N0719.N0896.d011138 k sizes hk hn
    (_root_.GD.N0212.N0466.d028993 hk sizes hn) s hstrict



theorem d028996 (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hstrict : _root_.GD.N0230.N0608.d000675
      (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
      (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hn)) :
    0 < _root_.GD.N0232.N0719.N1022.d015189 (k := k) (sizes := sizes) s :=
  (_root_.GD.N0232.N0719.N1022.d015195
    k sizes hk hn).mp (_root_.GD.N0212.N0466.d028993 hk sizes hn) s hstrict

theorem d028997 (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    ¬ ∃ s : _root_.GD.N0232.N0719.N0896.d011106 k sizes,
      _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
        (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hn) ∧
      _root_.GD.N0232.N0719.N1022.d015189 (k := k) (sizes := sizes) s = 0 := by
  rintro ⟨s, hs, hzero⟩
  exact (_root_.GD.N0212.N0466.d028996 hk sizes hn s hs).ne' hzero

end
end GD.N0212.N0466

#print axioms _root_.GD.N0212.N0466.d028993
#print axioms _root_.GD.N0212.N0466.d028994
#print axioms _root_.GD.N0212.N0466.d028995
#print axioms _root_.GD.N0212.N0466.d028996
#print axioms _root_.GD.N0212.N0466.d028997
