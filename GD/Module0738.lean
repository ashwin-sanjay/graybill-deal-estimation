import GD.Module0737















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0812

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0811



theorem d011042
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {d : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes theta d ≤ 1 := by
  unfold _root_.GD.N0232.N0719.N0816.d010977
  calc
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta d / _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta ≤
        _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta /
          _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta :=
      ENNReal.div_le_div_right (hd theta)
        (_root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta)
    _ = 1 := ENNReal.div_self
      (_root_.GD.N0232.N0719.N0858.d010854 k sizes hk hsizes theta).ne'
      (by unfold _root_.GD.N0232.N0719.N0858.d010852; exact ENNReal.ofReal_ne_top)


theorem d011043
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    {d : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes theta d ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    (_root_.GD.N0232.N0719.N0812.d011042
      k sizes hk hsizes hd theta)


theorem d011044
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    0 ≤ _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta d := by
  unfold _root_.GD.N0232.N0719.N0811.d011036
  exact div_nonneg ENNReal.toReal_nonneg
    (_root_.GD.N0232.N0719.N0858.d010853 k sizes hk hsizes theta).le



theorem d011045
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    {d : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    (_root_.GD.N0232.N0719.N0816.d010977 k sizes hk hsizes theta d).toReal =
      _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta d := by
  have h := congrArg ENNReal.toReal
    (_root_.GD.N0232.N0719.N0811.d011041
      k sizes hk hsizes theta hd)
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0232.N0719.N0812.d011044
      k sizes hk hsizes theta d)] at h
  exact h.symm


def d011046
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    (d : _root_.GD.N0232.N0719.N0816.d010975 k sizes) : ℝ :=
  (_root_.GD.N0232.N0719.N0816.d010978
    k sizes hk hsizes active epsilon d).toReal



theorem d011047
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    {d : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon d =
      ⨆ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
          _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 d := by
  unfold _root_.GD.N0232.N0719.N0812.d011046 _root_.GD.N0232.N0719.N0816.d010978
  rw [ENNReal.toReal_iSup]
  · congr 1
    funext theta
    exact _root_.GD.N0232.N0719.N0812.d011045
      k sizes hk hsizes theta.1 hd
  · intro theta
    exact _root_.GD.N0232.N0719.N0812.d011043
      k sizes hk hsizes hd theta.1




theorem d011048
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    {d : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hcollar : Nonempty {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon}) :
    IsLUB
      (Set.range (fun theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
          _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon} ↦
        _root_.GD.N0232.N0719.N0811.d011036 k sizes hk hsizes theta.1 d))
      (_root_.GD.N0232.N0719.N0812.d011046
        k sizes hk hsizes active epsilon d) := by
  letI := hcollar
  rw [_root_.GD.N0232.N0719.N0812.d011047
    k sizes hk hsizes active epsilon hd]
  apply isLUB_ciSup
  refine ⟨1, ?_⟩
  rintro value ⟨theta, rfl⟩
  have hle := _root_.GD.N0232.N0719.N0812.d011042
    k sizes hk hsizes hd theta.1
  have hreal := ENNReal.toReal_mono ENNReal.one_ne_top hle
  rw [_root_.GD.N0232.N0719.N0812.d011045
    k sizes hk hsizes theta.1 hd, ENNReal.toReal_one] at hreal
  exact hreal

end

end N0812
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0812.d011042
#print axioms _root_.GD.N0232.N0719.N0812.d011047
#print axioms _root_.GD.N0232.N0719.N0812.d011048
