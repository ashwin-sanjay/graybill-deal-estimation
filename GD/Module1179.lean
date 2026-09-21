import GD.Module1082
import GD.Module1161





























open MeasureTheory Filter Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1470

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1128
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1501

variable (m n : ℕ)



theorem d018968 (e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1501.d016291 m n (_root_.GD.N0232.N0720.N1501.d016291 m n e) = _root_.GD.N0232.N0720.N1501.d016291 m n e := by
  haveI : Fact (_root_.GD.N0232.N0720.N1501.d016287 m n ≤
      (inferInstance : MeasurableSpace (_root_.GD.N0232.N0720.N1080.d014170 m n))) :=
    ⟨_root_.GD.N0232.N0720.N1501.d016290 m n⟩
  rw [_root_.GD.N0232.N0720.N1501.d016292, _root_.GD.N0232.N0720.N1501.d016292]
  congr 1
  first
    | exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
        (condExpL2 ℝ ℝ (_root_.GD.N0232.N0720.N1501.d016290 m n) e)
    | (unfold condExpL2
       exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
        (condExpL2 ℝ ℝ (_root_.GD.N0232.N0720.N1501.d016290 m n) e))





theorem d018969
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d) :
    _root_.GD.N0232.N0720.N1501.d016291 m n d = d :=
  hd _ (fun θ => _root_.GD.N0232.N0720.N1501.d016299 m n hm hn θ d)



theorem d018970
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d) :
    ∃ g : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable g ∧
        (fun ω ↦ d ω) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] g ∘ _root_.GD.N0232.N0720.N1467.d012542 m n := by
  obtain ⟨g, hg, hae⟩ := _root_.GD.N0232.N0720.N1501.d016306 m n d
  rw [_root_.GD.N0232.N0720.N1470.d018969 m n hm hn d hd] at hae
  exact ⟨g, hg, hae⟩


theorem d018971 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1501.d016291 m n (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn) = _root_.GD.N0232.N0720.N1080.d014191 m n hm hn :=
  _root_.GD.N0232.N0720.N1470.d018969 m n hm hn _
    (_root_.GD.N0232.N0720.N1080.d014192 m n hm hn).2.1






theorem d018972
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (_hd : _root_.GD.N0232.N0720.N1501.d016291 m n d = d)
    (hsym : ∀ e, _root_.GD.N0232.N0720.N1501.d016291 m n e = e →
      _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e d → e = d) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d := by
  intro e he
  have hpfix : _root_.GD.N0232.N0720.N1501.d016291 m n (_root_.GD.N0232.N0720.N1501.d016291 m n e) = _root_.GD.N0232.N0720.N1501.d016291 m n e :=
    _root_.GD.N0232.N0720.N1470.d018968 m n e
  have hpdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1501.d016291 m n e) d :=
    fun θ => (_root_.GD.N0232.N0720.N1501.d016299 m n hm hn θ e).trans (he θ)
  have hpd : _root_.GD.N0232.N0720.N1501.d016291 m n e = d := hsym _ hpfix hpdom
  have hfin : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 e ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n]
    exact ENNReal.ofReal_ne_top
  have hint := _root_.GD.N0232.N0720.N1078.d016376 m n _root_.GD.N0232.N0720.N1080.d014169 e hfin
  have hle1 : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 e ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1501.d016291 m n e) := by
    rw [hpd]
    exact he _
  have hle2 : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1501.d016291 m n e) ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 e :=
    _root_.GD.N0232.N0720.N1501.d016299 m n hm hn _ e
  have heq : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 e =
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1501.d016291 m n e) := le_antisymm hle1 hle2
  have hpfin : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1501.d016291 m n e) ≠ ⊤ := by
    rw [← heq]
    exact hfin
  have hreal : (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 e).toReal =
      (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1501.d016291 m n e)).toReal := by
    rw [heq]
  rw [_root_.GD.N0232.N0720.N1128.d017097 m n _root_.GD.N0232.N0720.N1080.d014169 e hfin,
    _root_.GD.N0232.N0720.N1128.d017097 m n _root_.GD.N0232.N0720.N1080.d014169 (_root_.GD.N0232.N0720.N1501.d016291 m n e) hpfin] at hreal
  have hfix : e = _root_.GD.N0232.N0720.N1501.d016291 m n e :=
    (_root_.GD.N0232.N0720.N1501.d016305 m n hm hn _root_.GD.N0232.N0720.N1080.d014169 e hint).1 hreal
  rw [hfix]
  exact hpd


theorem d018973
    (hm : 2 ≤ m) (hn : 2 ≤ n) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d ↔
      _root_.GD.N0232.N0720.N1501.d016291 m n d = d ∧
        ∀ e, _root_.GD.N0232.N0720.N1501.d016291 m n e = e → _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e d → e = d := by
  constructor
  · intro hd
    exact ⟨_root_.GD.N0232.N0720.N1470.d018969 m n hm hn d hd,
      fun e _ he => hd e he⟩
  · rintro ⟨hd, hsym⟩
    exact _root_.GD.N0232.N0720.N1470.d018972 m n hm hn d hd hsym





theorem d018974
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1501.d016291 m n s.value = s.value ∧
          ∀ e, _root_.GD.N0232.N0720.N1501.d016291 m n e = e →
            _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e s.value → e = s.value := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hs, ht⟩
    obtain ⟨hsum, hsu⟩ :=
      (_root_.GD.N0232.N0720.N1470.d018973 m n hm hn s.value).1 ht
    exact ⟨s, hs, hsum, hsu⟩
  · rintro ⟨s, hs, hsum, hsu⟩
    exact ⟨s, hs,
      (_root_.GD.N0232.N0720.N1470.d018973 m n hm hn s.value).2
        ⟨hsum, hsu⟩⟩

end

end N1470
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1470.d018968
#print axioms _root_.GD.N0232.N0720.N1470.d018969
#print axioms _root_.GD.N0232.N0720.N1470.d018970
#print axioms _root_.GD.N0232.N0720.N1470.d018971
#print axioms _root_.GD.N0232.N0720.N1470.d018973
#print axioms _root_.GD.N0232.N0720.N1470.d018974
