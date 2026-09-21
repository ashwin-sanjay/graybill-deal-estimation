import GD.Module1732
import GD.Module1669

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0213.N0504
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0232.N0719.N0969
open _root_.GD.N0230.N0611
open _root_.GD.N0213.N0492

variable {k : ℕ} (sizes : Fin k → ℕ)

theorem d028823 (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    {f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes) (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes f = ⊤ := by
  by_contra hfinite
  let C := (_root_.GD.N0232.N0719.N0962.d012187 k sizes f).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hbound (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
      _root_.GD.N0232.N0719.N0962.d012186 k sizes theta f ≤ ENNReal.ofReal C := by
    rw [show ENNReal.ofReal C = _root_.GD.N0232.N0719.N0962.d012187 k sizes f from ENNReal.ofReal_toReal hfinite]
    exact le_iSup (fun theta => _root_.GD.N0232.N0719.N0962.d012186 k sizes theta f) theta
  have hphysical := _root_.GD.N0232.N0719.N0962.d012197 k sizes (by omega)
    (fun i => by have := hn i; omega) C hC f hbound
  exact hfinite (_root_.GD.N0213.N0492.d028818 sizes hk hn
    (_root_.GD.N0213.N0492.d028819 sizes ⟨hf, hphysical⟩ ht))

theorem d028824
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) (hfinite : _root_.GD.N0232.N0719.N0962.d012188 k sizes ≠ ⊤)
    {f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes)
    (hvalue : _root_.GD.N0232.N0719.N0962.d012187 k sizes f = _root_.GD.N0232.N0719.N0962.d012188 k sizes) :
    ¬ _root_.GD.N0232.N0719.N0970.d012309 k sizes f := by
  intro ht
  exact hfinite (hvalue.symm.trans (_root_.GD.N0213.N0504.d028823 sizes hk hn hf ht))

theorem d028825 (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≠ ⊤ :=
  ne_top_of_le_ne_top
    (_root_.GD.N0071.d028308 sizes (by omega) hn)
    (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0232.N0719.N0900.d009122 k sizes))

theorem d028826 (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i)
    {f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes)
    (hvalue : _root_.GD.N0232.N0719.N0962.d012187 k sizes f = _root_.GD.N0232.N0719.N0962.d012188 k sizes) :
    ¬ _root_.GD.N0232.N0719.N0970.d012309 k sizes f :=
  _root_.GD.N0213.N0492.d028820 sizes hk (fun i => by have := hn i; omega)
    (_root_.GD.N0213.N0504.d028825 sizes hk hn) hf hvalue

theorem d028827 (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) :
    ∃ f ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes f = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧ ¬ _root_.GD.N0232.N0719.N0970.d012309 k sizes f := by
  have hn2 : ∀ i, 2 ≤ sizes i := fun i => by have := hn i; omega
  obtain ⟨f, hf, hvalue⟩ := _root_.GD.N0232.N0719.N0969.d012209 k sizes hk hn2
  exact ⟨f, hf, hvalue, _root_.GD.N0213.N0504.d028826 sizes hk hn hf hvalue⟩

theorem d028828 (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) :
    ∃ f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes f = _root_.GD.N0232.N0719.N0962.d012188 k sizes ∧ _root_.GD.N0232.N0719.N0970.d012309 k sizes f ∧
      f ∉ _root_.GD.N0232.N0719.N0962.d012185 k sizes := by
  have hn2 : ∀ i, 2 ≤ sizes i := fun i => by have := hn i; omega
  exact ⟨_root_.GD.N0232.N0719.N0970.d012322 k sizes hk hn2, _root_.GD.N0232.N0719.N0970.d012323 k sizes hk hn2,
    _root_.GD.N0232.N0719.N0970.d012325 k sizes hk hn2, _root_.GD.N0232.N0719.N0970.d012326 k sizes hk hn2,
    _root_.GD.N0213.N0492.d028821 sizes hk hn2
      (_root_.GD.N0213.N0504.d028825 sizes hk hn)⟩

end
end GD.N0213.N0504

#print axioms _root_.GD.N0213.N0504.d028823
#print axioms _root_.GD.N0213.N0504.d028824
#print axioms _root_.GD.N0213.N0504.d028825
#print axioms _root_.GD.N0213.N0504.d028826
#print axioms _root_.GD.N0213.N0504.d028827
#print axioms _root_.GD.N0213.N0504.d028828
