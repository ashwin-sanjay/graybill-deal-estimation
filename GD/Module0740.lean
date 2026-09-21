import GD.Module0739












open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0808

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0812
open _root_.GD.N0232.N0719.N0807
open _root_.GD.N0230.N0718



theorem d011051
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    {d : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon d ≤ 1 := by
  unfold _root_.GD.N0232.N0719.N0816.d010978
  apply iSup_le
  intro theta
  exact _root_.GD.N0232.N0719.N0812.d011042
    k sizes hk hsizes hd theta.1



theorem d011052
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    {d : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon d ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    (_root_.GD.N0232.N0719.N0808.d011051
      k sizes hk hsizes active epsilon hd)



theorem d011053
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    {d : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    ENNReal.ofReal
        (_root_.GD.N0232.N0719.N0812.d011046
          k sizes hk hsizes active epsilon d) =
      _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon d := by
  unfold _root_.GD.N0232.N0719.N0812.d011046
  exact ENNReal.ofReal_toReal
    (_root_.GD.N0232.N0719.N0808.d011052
      k sizes hk hsizes active epsilon hd)


theorem d011054
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    (d : _root_.GD.N0232.N0719.N0816.d010975 k sizes) :
    0 ≤ _root_.GD.N0232.N0719.N0812.d011046
      k sizes hk hsizes active epsilon d := by
  unfold _root_.GD.N0232.N0719.N0812.d011046
  exact ENNReal.toReal_nonneg




theorem d011055
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (detectorTax : _root_.GD.N0232.N0719.N0816.d010975 k sizes → _root_.GD.N0232.N0719.N0816.d010975 k sizes → ℝ)
    (hdetectorNonnegative : 0 ≤ detectorTax p q)
    (hreal :
      _root_.GD.N0232.N0719.N0812.d011046
            k sizes hk hsizes active epsilon (_root_.GD.N0230.N0718.d001528 p q) +
          detectorTax p q ≤
        (_root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon p +
          _root_.GD.N0232.N0719.N0812.d011046 k sizes hk hsizes active epsilon q) / 2) :
    _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon
          (_root_.GD.N0230.N0718.d001528 p q) + ENNReal.ofReal (detectorTax p q) ≤
      (_root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon p +
        _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon q) / 2 := by
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes := by
    unfold _root_.GD.N0230.N0718.d001528
    apply (_root_.GD.N0232.N0719.N0858.d010862 k sizes hk hsizes) hp hq
    · norm_num
    · norm_num
    · norm_num
  rw [← _root_.GD.N0232.N0719.N0808.d011053
        k sizes hk hsizes active epsilon hmid,
      ← _root_.GD.N0232.N0719.N0808.d011053
        k sizes hk hsizes active epsilon hp,
      ← _root_.GD.N0232.N0719.N0808.d011053
        k sizes hk hsizes active epsilon hq]
  rw [← ENNReal.ofReal_add
    (_root_.GD.N0232.N0719.N0808.d011054
      k sizes hk hsizes active epsilon (_root_.GD.N0230.N0718.d001528 p q))
    hdetectorNonnegative]
  calc
    ENNReal.ofReal
        (_root_.GD.N0232.N0719.N0812.d011046
            k sizes hk hsizes active epsilon (_root_.GD.N0230.N0718.d001528 p q) +
          detectorTax p q) ≤
        ENNReal.ofReal
          ((_root_.GD.N0232.N0719.N0812.d011046
                k sizes hk hsizes active epsilon p +
              _root_.GD.N0232.N0719.N0812.d011046
                k sizes hk hsizes active epsilon q) / 2) :=
      ENNReal.ofReal_le_ofReal hreal
    _ =
        (ENNReal.ofReal
              (_root_.GD.N0232.N0719.N0812.d011046
                k sizes hk hsizes active epsilon p) +
            ENNReal.ofReal
              (_root_.GD.N0232.N0719.N0812.d011046
                k sizes hk hsizes active epsilon q)) / 2 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [ENNReal.ofReal_add
        (_root_.GD.N0232.N0719.N0808.d011054
          k sizes hk hsizes active epsilon p)
        (_root_.GD.N0232.N0719.N0808.d011054
          k sizes hk hsizes active epsilon q)]
      norm_num




theorem d011056
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hcollar : Nonempty {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon})
    (detectorTax : _root_.GD.N0232.N0719.N0816.d010975 k sizes → _root_.GD.N0232.N0719.N0816.d010975 k sizes → ℝ)
    (hdetectorNonnegative : 0 ≤ detectorTax p q)
    (hnearActiveDetector : ∀ eta, 0 < eta →
      ∀ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
          _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
        _root_.GD.N0232.N0719.N0812.d011046
              k sizes hk hsizes active epsilon (_root_.GD.N0230.N0718.d001528 p q) - eta <
            _root_.GD.N0232.N0719.N0811.d011036
              k sizes hk hsizes theta.1 (_root_.GD.N0230.N0718.d001528 p q) →
          detectorTax p q ≤
            _root_.GD.N0232.N0719.N0811.d011037
              k sizes hk hsizes theta.1 p q) :
    _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon
          (_root_.GD.N0230.N0718.d001528 p q) + ENNReal.ofReal (detectorTax p q) ≤
      (_root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon p +
        _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon q) / 2 := by
  have hreal :=
    _root_.GD.N0232.N0719.N0807.d011049
      k sizes hk hsizes active epsilon hp hq hcollar detectorTax
      hnearActiveDetector
  exact _root_.GD.N0232.N0719.N0808.d011055
    k sizes hk hsizes active epsilon hp hq detectorTax
    hdetectorNonnegative hreal




theorem d011057
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (active : Finset (Fin k)) (epsilon : ℝ)
    {p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes}
    (hp : p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hq : q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes)
    (hcollar : Nonempty {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
      _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon})
    (detectorTax : _root_.GD.N0232.N0719.N0816.d010975 k sizes → _root_.GD.N0232.N0719.N0816.d010975 k sizes → ℝ)
    (hdetectorNonnegative : 0 ≤ detectorTax p q)
    (hcofinalRetention : ∀ eta, 0 < eta →
      ∃ theta : {theta : _root_.GD.N0232.N0719.N0859.d010809 k //
          _root_.GD.N0232.N0719.N0815.d010928 active theta ≤ epsilon},
        _root_.GD.N0232.N0719.N0812.d011046
              k sizes hk hsizes active epsilon (_root_.GD.N0230.N0718.d001528 p q) - eta <
            _root_.GD.N0232.N0719.N0811.d011036
              k sizes hk hsizes theta.1 (_root_.GD.N0230.N0718.d001528 p q) ∧
          detectorTax p q ≤
            _root_.GD.N0232.N0719.N0811.d011037
              k sizes hk hsizes theta.1 p q) :
    _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon
          (_root_.GD.N0230.N0718.d001528 p q) + ENNReal.ofReal (detectorTax p q) ≤
      (_root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon p +
        _root_.GD.N0232.N0719.N0816.d010978 k sizes hk hsizes active epsilon q) / 2 := by
  have hreal :=
    _root_.GD.N0232.N0719.N0807.d011050
      k sizes hk hsizes active epsilon hp hq hcollar detectorTax
      hcofinalRetention
  exact _root_.GD.N0232.N0719.N0808.d011055
    k sizes hk hsizes active epsilon hp hq detectorTax
    hdetectorNonnegative hreal

end

end N0808
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0808.d011051
#print axioms _root_.GD.N0232.N0719.N0808.d011053
#print axioms _root_.GD.N0232.N0719.N0808.d011055
#print axioms _root_.GD.N0232.N0719.N0808.d011056
#print axioms _root_.GD.N0232.N0719.N0808.d011057
