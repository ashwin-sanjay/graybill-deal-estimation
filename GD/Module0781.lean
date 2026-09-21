import GD.Module0779
import GD.Module0774


















namespace GD
namespace N0232
namespace N0719
namespace N0846

noncomputable section

open _root_.GD.N0232.N0719.N0847
open _root_.GD.N0232.N0719.N0824
open _root_.GD.N0232.N0719.N0820



def d011893
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  ∃ z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes,
    z.1.active.card ≤ 2




def d011894
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  ∃ z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes,
    3 ≤ z.1.active.card



theorem d011895
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hescape : _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0846.d011893 k sizes hk hsizes ∨
      _root_.GD.N0232.N0719.N0846.d011894 k sizes hk hsizes := by
  exact _root_.GD.N0232.N0719.N0820.d011753
    k sizes hk hsizes hescape










theorem d011896
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes ∨
      _root_.GD.N0232.N0719.N0846.d011893 k sizes hk hsizes ∨
      _root_.GD.N0232.N0719.N0846.d011894 k sizes hk hsizes := by
  rcases _root_.GD.N0232.N0719.N0847.d011877
      k sizes hk hsizes with hterminal | hescape
  · exact Or.inl hterminal
  · rcases _root_.GD.N0232.N0719.N0846.d011895
        k sizes hk hsizes hescape with hlow | hinterior
    · exact Or.inr (Or.inl hlow)
    · exact Or.inr (Or.inr hinterior)





theorem d011897
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hnoTerminal : ¬ _root_.GD.N0232.N0719.N0847.d011875 k sizes) :
    _root_.GD.N0232.N0719.N0846.d011893 k sizes hk hsizes ∨
      _root_.GD.N0232.N0719.N0846.d011894 k sizes hk hsizes := by
  rcases _root_.GD.N0232.N0719.N0846.d011896
      k sizes hk hsizes with hterminal | hlow | hinterior
  · exact False.elim (hnoTerminal hterminal)
  · exact Or.inl hlow
  · exact Or.inr hinterior



theorem d011898
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hnoLow :
      ¬ _root_.GD.N0232.N0719.N0846.d011893 k sizes hk hsizes)
    (hnoInterior :
      ¬ _root_.GD.N0232.N0719.N0846.d011894 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes := by
  rcases _root_.GD.N0232.N0719.N0846.d011896
      k sizes hk hsizes with hterminal | hlow | hinterior
  · exact hterminal
  · exact False.elim (hnoLow hlow)
  · exact False.elim (hnoInterior hinterior)


theorem d011899
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hnoWitness :
      ¬ (_root_.GD.N0232.N0719.N0846.d011893 k sizes hk hsizes ∨
        _root_.GD.N0232.N0719.N0846.d011894 k sizes hk hsizes)) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes := by
  exact _root_.GD.N0232.N0719.N0846.d011898
    k sizes hk hsizes
    (fun hlow ↦ hnoWitness (Or.inl hlow))
    (fun hinterior ↦ hnoWitness (Or.inr hinterior))

end

end N0846
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0846.d011895
#print axioms _root_.GD.N0232.N0719.N0846.d011896
#print axioms _root_.GD.N0232.N0719.N0846.d011897
#print axioms _root_.GD.N0232.N0719.N0846.d011898
#print axioms _root_.GD.N0232.N0719.N0846.d011899
