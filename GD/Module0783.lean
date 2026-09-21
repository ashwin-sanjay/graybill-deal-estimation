import GD.Module0782















namespace GD
namespace N0232
namespace N0719
namespace N0825

noncomputable section

open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0810
open _root_.GD.N0232.N0719.N0823
open _root_.GD.N0232.N0719.N0824
open _root_.GD.N0232.N0719.N0898
open _root_.GD.N0232.N0719.N0858



theorem d011920
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0823.d011711 k sizes hk hsizes ↔
      ¬ _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes := by
  constructor
  · intro hresidual hescape
    exact
      ((_root_.GD.N0232.N0719.N0824.d011726
        k sizes hk hsizes).2 hescape) hresidual
  · intro hnoEscape
    by_contra hfailure
    exact hnoEscape
      ((_root_.GD.N0232.N0719.N0824.d011726
        k sizes hk hsizes).1 hfailure)

variable {iota E : Type*}
  [Fintype iota] [Nonempty iota]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]




theorem d011921
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hcard : 3 ≤ Fintype.card iota)
    (active : Finset (Fin k)) (hactive : active.Nonempty)
    (response : _root_.GD.N0232.N0719.N0816.d010975 k sizes → iota → E)
    (hfaithful : _root_.GD.N0232.N0719.N0898.d011901 response)
    (hobservable : ∀ p q : _root_.GD.N0232.N0719.N0816.d010975 k sizes,
      p ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes →
      q ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes →
      _root_.GD.N0232.N0719.N0898.d011908
        k sizes hk hsizes active response p q) :
    ¬ _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes := by
  apply
    (_root_.GD.N0232.N0719.N0825.d011920
      k sizes hk hsizes).1
  exact _root_.GD.N0232.N0719.N0898.d011910
    k sizes hk hsizes hcard active hactive response hfaithful hobservable

end

end N0825
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0825.d011920
#print axioms _root_.GD.N0232.N0719.N0825.d011921
