import GD.Module1669
import GD.Module1549

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

theorem d028701
    (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0213.N0502.d022051 k sizes ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (_root_.GD.N0071.d028308 sizes (by omega) hn)
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0213.N0502.d022052 k sizes)



theorem d028702
    (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) =
      _root_.GD.N0213.N0502.d022051 k sizes := by
  exact _root_.GD.N0092.d023971 k sizes hk
    (fun i => by have := hn i; omega)
    (_root_.GD.N0071.d028308 sizes (by omega) hn)




theorem d028703
    (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) (ε : ℝ) (hε : 0 < ε) :
    ∃ e ∈ _root_.GD.N0092.d023968 k sizes,
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e <
        ENNReal.ofReal ((_root_.GD.N0213.N0502.d022051 k sizes).toReal + ε) := by
  have hn2 : ∀ i, 2 ≤ sizes i := fun i => by have := hn i; omega
  have hs := _root_.GD.N0232.N0719.N0968.d012201 k sizes hk hn2
  have hstrict := _root_.GD.N0232.N0719.N0970.d012329 k sizes hk hn2
  have hsfinite : _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hn2) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (_root_.GD.N0071.d028308 sizes (by omega) hn)
      (_root_.GD.N0232.N0719.N0970.d012318 k sizes fun θ => (hstrict θ).le)
  have hV := ENNReal.ofReal_toReal (_root_.GD.N0092.d028701 sizes hk hn)
  have hcap : _root_.GD.N0213.N0502.d022051 k sizes <
      ENNReal.ofReal ((_root_.GD.N0213.N0502.d022051 k sizes).toReal + ε) := by
    conv_lhs => rw [← hV]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    linarith
  obtain ⟨e, he, hes, het, hecap⟩ := _root_.GD.N0092.d023967
    k sizes hk hn2 (_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hn2) ⟨hs.1.1, hs.2⟩ hstrict hsfinite _ hcap
  exact ⟨e, ⟨he, hes, het⟩, hecap⟩




theorem d028704
    (hk : 3 ≤ k) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes) (_root_.GD.N0092.d023968 k sizes) =
      _root_.GD.N0232.N0719.N0962.d012188 k sizes ↔
      _root_.GD.N0213.N0502.d022051 k sizes = _root_.GD.N0232.N0719.N0962.d012188 k sizes := by
  rw [_root_.GD.N0092.d028702 sizes hk hn]


end
end GD.N0092

#print axioms _root_.GD.N0092.d028701
#print axioms _root_.GD.N0092.d028702
#print axioms _root_.GD.N0092.d028703
#print axioms _root_.GD.N0092.d028704
