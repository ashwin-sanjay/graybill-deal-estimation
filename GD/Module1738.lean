import GD.Module1737
import GD.Module1733

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0213.N0503
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0230.N0611
open _root_.GD.N0213.N0492 _root_.GD.N0213.N0515

variable (k : ℕ) (sizes : Fin k → ℕ)

theorem d028851
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    {f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f)
    (hGD : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) :
    f ∉ _root_.GD.N0232.N0719.N0962.d012185 k sizes := by
  intro ha
  exact _root_.GD.N0213.N0492.d028822 sizes hk hn
    (_root_.GD.N0213.N0492.d028819 sizes ⟨ha, hf.2⟩ ht) hGD

theorem d028852
    {f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hv : _root_.GD.N0232.N0719.N0962.d012187 k sizes f = _root_.GD.N0232.N0719.N0962.d012188 k sizes)
    (ht : ¬ _root_.GD.N0232.N0719.N0970.d012309 k sizes f) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes, _root_.GD.N0232.N0719.N0970.d012309 k sizes e ∧
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ e < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := by
  obtain ⟨e, he, het, hes⟩ := (_root_.GD.N0213.N0515.d023050 k sizes hf).mp ht
  exact ⟨e, he, het, le_antisymm
    ((_root_.GD.N0232.N0719.N0970.d012318 k sizes (fun θ => (hes θ).le)).trans_eq hv)
    (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) he.1), hes⟩

theorem d028853
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    ∃ a ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes a = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧
      ¬ _root_.GD.N0232.N0719.N0970.d012309 k sizes a ∧
      ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes, _root_.GD.N0232.N0719.N0970.d012309 k sizes e ∧
        e ∉ _root_.GD.N0232.N0719.N0962.d012185 k sizes ∧
        _root_.GD.N0232.N0719.N0962.d012187 k sizes e = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧
        ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ e < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ a := by
  by_cases htop : _root_.GD.N0232.N0719.N0962.d012188 k sizes = ⊤
  · obtain ⟨a, ha, hav, has⟩ := _root_.GD.N0232.N0719.N0970.d012330 k sizes hk hn htop
    have han : ¬ _root_.GD.N0232.N0719.N0970.d012309 k sizes a := by
      intro hat
      exact _root_.GD.N0213.N0492.d028822 sizes hk hn
        (_root_.GD.N0213.N0492.d028819 sizes ha hat) (fun θ => (has θ).le)
    obtain ⟨e, he, het, hev, hes⟩ := _root_.GD.N0213.N0503.d028852 k sizes
      ⟨ha.1.1, ha.2⟩ hav han
    exact ⟨a, ha, hav, han, e, he, het,
      _root_.GD.N0213.N0503.d028851 k sizes hk hn he het
        (fun θ => (hes θ).le.trans (has θ).le), hev, hes⟩
  · obtain ⟨a, ha, hav⟩ := _root_.GD.N0232.N0719.N0969.d012209 k sizes hk hn
    have han := _root_.GD.N0213.N0492.d028820 sizes hk hn htop ha hav
    obtain ⟨e, he, het, hev, hes⟩ := _root_.GD.N0213.N0503.d028852 k sizes
      ⟨ha.1.1, ha.2⟩ hav han
    refine ⟨a, ha, hav, han, e, he, het, ?_, hev, hes⟩
    intro hae
    exact (_root_.GD.N0213.N0504.d028824
      sizes hk hn htop hae hev) het

end
end GD.N0213.N0503

#print axioms _root_.GD.N0213.N0503.d028851
#print axioms _root_.GD.N0213.N0503.d028852
#print axioms _root_.GD.N0213.N0503.d028853
