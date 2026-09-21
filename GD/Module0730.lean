import GD.Module0062
import GD.Module0097
import GD.Module0728




















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0816

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0712
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0596



abbrev d010975 (k : ℕ) (sizes : Fin k → ℕ) :=
  _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes)


abbrev d010976 (k : ℕ) (sizes : Fin k → ℕ) :=
  WeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)


def d010977
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.N0816.d010975 k sizes) : ENNReal :=
  _root_.GD.N0232.N0719.N0859.d010821 k sizes theta d / _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta



def d010978
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    (d : _root_.GD.N0232.N0719.N0816.d010975 k sizes) : ENNReal :=
  ⨆ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
    _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes theta.1 d



def d010979
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    (d : _root_.GD.N0232.N0719.N0816.d010976 k sizes) : ENNReal :=
  ⨆ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
    _root_.GD.N0230.N0712.d001258 (_root_.GD.N0232.N0719.d009182 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta.1)
        theta.1.location d /
      _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta.1



theorem d010980
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    (d : _root_.GD.N0232.N0719.N0816.d010976 k sizes) :
    _root_.GD.N0232.N0719.N0816.d010979 k sizes hk hsizes active epsilon d =
      _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon
        ((toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes)).symm d) := by
  rfl




theorem d010981
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ) :
    LowerSemicontinuous
      (_root_.GD.N0232.N0719.N0816.d010979
        k sizes hk hsizes active epsilon) := by
  have h :=
    _root_.GD.N0230.N0712.d001262
      (Theta := {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
        _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon})
      (_root_.GD.N0232.N0719.d009182 k sizes)
      (fun theta => _root_.GD.N0232.N0719.N0859.d010812 k sizes theta.1)
      (fun theta => theta.1.location)
      (fun theta => _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta.1)
      (fun theta => _root_.GD.N0232.N0719.N0859.d010814 k sizes theta.1)
      (fun theta => (_root_.GD.N0232.N0719.N0858.d010854 k sizes hk hsizes theta.1).ne')
  change LowerSemicontinuous
    (fun d : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.d009182 k sizes)) =>
      ⨆ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
          _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
        _root_.GD.N0230.N0712.d001258 (_root_.GD.N0232.N0719.d009182 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta.1)
            theta.1.location d /
          _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta.1)
  exact h



abbrev d010982 (k : ℕ) := Finset (Fin k) × ℕ



def d010983
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (n : ℕ) (d : _root_.GD.N0232.N0719.N0816.d010976 k sizes) : ENNReal :=
  _root_.GD.N0232.N0719.N0816.d010979 k sizes hk hsizes
    (stage n).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage n).2) d



theorem d010984
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) :
    ∀ n, LowerSemicontinuous
      (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage n) := by
  intro n
  exact _root_.GD.N0232.N0719.N0816.d010981
    k sizes hk hsizes (stage n).1 (_root_.GD.N0232.N0719.N0815.d010938 (stage n).2)










theorem d010985
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (C : Set (_root_.GD.N0232.N0719.N0816.d010976 k sizes))
    (face : ℕ → Set (_root_.GD.N0232.N0719.N0816.d010976 k sizes))
    (htower : _root_.GD.N0230.N0583.d000745
      (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage) C face)
    (hCnonempty : C.Nonempty)
    (hCcompact : IsCompact C) :
    ∃ p, (∀ n, p ∈ face n) ∧
      _root_.GD.N0230.N0596.d000730
        (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage) C p := by
  exact _root_.GD.N0230.N0583.d000750
    (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage) C face htower
    hCnonempty hCcompact
    (fun n =>
      (_root_.GD.N0232.N0719.N0816.d010984
        k sizes hk hsizes stage n).lowerSemicontinuousOn (face n))



theorem d010986
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k)
    (C : Set (_root_.GD.N0232.N0719.N0816.d010976 k sizes))
    (face : ℕ → Set (_root_.GD.N0232.N0719.N0816.d010976 k sizes))
    (htower : _root_.GD.N0230.N0583.d000745
      (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage) C face)
    (hCnonempty : C.Nonempty)
    (hCcompact : IsCompact C) :
    ∀ n, (face n).Nonempty ∧ IsCompact (face n) ∧ IsClosed (face n) := by
  exact _root_.GD.N0230.N0583.d000748
    (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage) C face htower
    hCnonempty hCcompact
    (fun n =>
      (_root_.GD.N0232.N0719.N0816.d010984
        k sizes hk hsizes stage n).lowerSemicontinuousOn (face n))

end

end N0816
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0816.d010981
#print axioms _root_.GD.N0232.N0719.N0816.d010984
#print axioms _root_.GD.N0232.N0719.N0816.d010985
#print axioms _root_.GD.N0232.N0719.N0816.d010986
