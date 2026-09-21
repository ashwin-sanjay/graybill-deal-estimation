import GD.Module0772
import GD.Module0776


















open MeasureTheory

namespace GD
namespace N0232
namespace N0719
namespace N0847

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0815
open _root_.GD.N0232.N0719.N0809
open _root_.GD.N0232.N0719.N0823
open _root_.GD.N0232.N0719.N0824
open _root_.GD.N0232.N0719.N0849
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0946





def d011875
    (k : ℕ) (sizes : Fin k → ℕ) : Prop :=
  ∃ d : _root_.GD.N0232.N0719.N0815.d010956 k sizes,
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0719.d009173 k sizes) ↦
        g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) d.1 ∧
    (∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      _root_.GD.N0232.N0719.N0815.d010957 k sizes theta d <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) ∧
    _root_.GD.N0232.N0719.N0849.d011781 k sizes d



theorem d011876
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hresidual : _root_.GD.N0232.N0719.N0823.d011711
      k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes := by
  obtain ⟨p, hunique, hterminal⟩ :=
    _root_.GD.N0232.N0719.N0823.d011720
      k sizes hk hsizes hresidual
  obtain ⟨d, hequivariant, _hclass, hstrict, hrawTerminal⟩ :=
    _root_.GD.N0232.N0719.N0849.d011786
      k sizes hk hsizes (_root_.GD.N0232.N0719.N0809.d010966 k)
      p hunique hterminal
  exact ⟨d, hequivariant, hstrict, hrawTerminal⟩


theorem d011877
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes ∨
      _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes := by
  by_cases hresidual :
      _root_.GD.N0232.N0719.N0823.d011711 k sizes hk hsizes
  · exact Or.inl
      (_root_.GD.N0232.N0719.N0847.d011876
        k sizes hk hsizes hresidual)
  · exact Or.inr
      ((_root_.GD.N0232.N0719.N0824.d011726
        k sizes hk hsizes).1 hresidual)



theorem d011878
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hnoEscape :
      ¬ _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes := by
  have hresidual :
      _root_.GD.N0232.N0719.N0823.d011711 k sizes hk hsizes := by
    by_contra hfailure
    exact hnoEscape
      ((_root_.GD.N0232.N0719.N0824.d011726
        k sizes hk hsizes).1 hfailure)
  exact _root_.GD.N0232.N0719.N0847.d011876
    k sizes hk hsizes hresidual

#print axioms _root_.GD.N0232.N0719.N0847.d011876
#print axioms _root_.GD.N0232.N0719.N0847.d011877
#print axioms _root_.GD.N0232.N0719.N0847.d011878

end
end N0847
end N0719
end N0232
end GD
