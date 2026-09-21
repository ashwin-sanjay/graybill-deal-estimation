import GD.Module0802












set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0232.N0719.N0968

noncomputable section

open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0230.N0611

variable (k : ℕ) (sizes : Fin k → ℕ)

theorem d012200
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes) ≠ ⊤ := by
  have hmem : MemLp (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes) 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    simpa [_root_.GD.N0232.N0719.N0859.d010813, _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0859.d010810,
      _root_.GD.N0232.N0719.d009182] using
      _root_.GD.N0232.N0719.N0859.d010818 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)
  rw [_root_.GD.N0232.N0719.N0859.d010841 k sizes theta (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes) hmem]
  change _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes) ≠ ⊤
  rw [_root_.GD.N0232.N0719.N0859.d010824 k sizes hk hsizes theta]
  exact ENNReal.ofReal_ne_top



theorem d012201
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact _root_.GD.N0232.N0719.N1024.d010732 k sizes hk hsizes
  · intro b a ha omega
    exact _root_.GD.N0232.N0719.N1024.d010738
      k sizes hk hsizes b (ne_of_gt ha) omega
  · exact _root_.GD.N0232.N0719.N0968.d012200 k sizes hk hsizes

theorem d012202
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    (_root_.GD.N0232.N0719.N0962.d012191 k sizes).Nonempty :=
  ⟨_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hsizes,
    _root_.GD.N0232.N0719.N0968.d012201 k sizes hk hsizes⟩



theorem d012203
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (htop : _root_.GD.N0232.N0719.N0962.d012188 k sizes = ⊤) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e = _root_.GD.N0232.N0719.N0962.d012188 k sizes := by
  obtain ⟨e, he⟩ := _root_.GD.N0232.N0719.N0968.d012202 k sizes hk hsizes
  refine ⟨e, he, ?_⟩
  have hlower : _root_.GD.N0232.N0719.N0962.d012188 k sizes ≤ _root_.GD.N0232.N0719.N0962.d012187 k sizes e :=
    _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) he.1.1
  apply le_antisymm _ hlower
  rw [htop]
  exact le_top

end
end GD.N0232.N0719.N0968

#print axioms _root_.GD.N0232.N0719.N0968.d012200
#print axioms _root_.GD.N0232.N0719.N0968.d012201
#print axioms _root_.GD.N0232.N0719.N0968.d012202
#print axioms _root_.GD.N0232.N0719.N0968.d012203
