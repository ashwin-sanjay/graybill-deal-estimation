import GD.Module1548
import GD.Module1491

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0092
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0232.N0719.N0968
open _root_.GD.N0213.N0502
open _root_.GD.N0230.N0611

variable {k : ℕ} (sizes : Fin k → ℕ)

def d023977 : Set (_root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :=
  {e | Measurable e ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes e}




theorem d023978
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023977 sizes) =
      _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) := by
  apply le_antisymm
  · apply le_iInf
    intro e
    apply le_iInf
    intro he
    exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
      (show e ∈ _root_.GD.N0092.d023977 sizes from ⟨he.1.1, he.2.1⟩)
  · apply le_iInf
    intro e
    apply le_iInf
    intro he
    have heFin := _root_.GD.N0213.N0502.d022053 k sizes hk hn ⟨he.1, fun θ => (he.2 θ).le⟩
    have ht : _root_.GD.N0232.N0719.N0970.d012314 k sizes e heFin ∈ _root_.GD.N0092.d023968 k sizes :=
      ⟨_root_.GD.N0232.N0719.N0970.d012316 k sizes e heFin,
        _root_.GD.N0232.N0719.N0970.d012321 k sizes e heFin he.2,
        _root_.GD.N0232.N0719.N0970.d012317 k sizes e heFin⟩
    exact (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) ht).trans
      (_root_.GD.N0232.N0719.N0970.d012319 k sizes e heFin)




theorem d023979
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    (∃ e ∈ _root_.GD.N0092.d023977 sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e = _root_.GD.N0213.N0502.d022051 k sizes) ↔
    (∃ e ∈ _root_.GD.N0092.d023968 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e = _root_.GD.N0213.N0502.d022051 k sizes) := by
  constructor
  · rintro ⟨e, he, heValue⟩
    have heFin := _root_.GD.N0213.N0502.d022053 k sizes hk hn ⟨he.1, fun θ => (he.2 θ).le⟩
    have ht : _root_.GD.N0232.N0719.N0970.d012314 k sizes e heFin ∈ _root_.GD.N0092.d023968 k sizes :=
      ⟨_root_.GD.N0232.N0719.N0970.d012316 k sizes e heFin,
        _root_.GD.N0232.N0719.N0970.d012321 k sizes e heFin he.2,
        _root_.GD.N0232.N0719.N0970.d012317 k sizes e heFin⟩
    refine ⟨_, ht, le_antisymm ?_ ?_⟩
    · exact (_root_.GD.N0232.N0719.N0970.d012319 k sizes e heFin).trans_eq heValue
    · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
        (_root_.GD.N0092.d023969 k sizes ht)
  · rintro ⟨e, he, heValue⟩
    exact ⟨e, ⟨he.1.1, he.2.1⟩, heValue⟩

theorem d023980
    (hk : 3 ≤ k) (hn : ∀ i, 4 ≤ sizes i) :
    _root_.GD.N0213.N0502.d022051 k sizes ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (_root_.GD.N0021.d023355 sizes (by omega) hn)
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0213.N0502.d022052 k sizes)



theorem d023981
    (hk : 3 ≤ k) (hn : ∀ i, 4 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) =
      _root_.GD.N0213.N0502.d022051 k sizes := by
  exact _root_.GD.N0092.d023971 k sizes hk
    (fun i => by have := hn i; omega)
    (_root_.GD.N0021.d023355 sizes (by omega) hn)




theorem d023982
    (hk : 3 ≤ k) (hn : ∀ i, 4 ≤ sizes i) (ε : ℝ) (hε : 0 < ε) :
    ∃ e ∈ _root_.GD.N0092.d023968 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e <
        ENNReal.ofReal ((_root_.GD.N0213.N0502.d022051 k sizes).toReal + ε) := by
  have hn2 : ∀ i, 2 ≤ sizes i := fun i => by have := hn i; omega
  have hs := _root_.GD.N0232.N0719.N0968.d012201 k sizes hk hn2
  have hstrict := _root_.GD.N0232.N0719.N0970.d012329 k sizes hk hn2
  have hsfinite : _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hn2) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (_root_.GD.N0021.d023355 sizes (by omega) hn)
      (_root_.GD.N0232.N0719.N0970.d012318 k sizes fun θ => (hstrict θ).le)
  have hV := ENNReal.ofReal_toReal (_root_.GD.N0092.d023980 sizes hk hn)
  have hcap : _root_.GD.N0213.N0502.d022051 k sizes <
      ENNReal.ofReal ((_root_.GD.N0213.N0502.d022051 k sizes).toReal + ε) := by
    conv_lhs => rw [← hV]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    linarith
  obtain ⟨e, he, hes, het, hecap⟩ := _root_.GD.N0092.d023967
    k sizes hk hn2 (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hn2) ⟨hs.1.1, hs.2⟩ hstrict hsfinite _ hcap
  exact ⟨e, ⟨he, hes, het⟩, hecap⟩




theorem d023983
    (hk : 3 ≤ k) (hn : ∀ i, 4 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) =
      _root_.GD.N0232.N0719.N0962.d012188 k sizes ↔
      _root_.GD.N0213.N0502.d022051 k sizes = _root_.GD.N0232.N0719.N0962.d012188 k sizes := by
  rw [_root_.GD.N0092.d023981 sizes hk hn]

end
end GD.N0092

#print axioms _root_.GD.N0092.d023980
#print axioms _root_.GD.N0092.d023981
#print axioms _root_.GD.N0092.d023982
#print axioms _root_.GD.N0092.d023983
#print axioms _root_.GD.N0092.d023978
#print axioms _root_.GD.N0092.d023979
