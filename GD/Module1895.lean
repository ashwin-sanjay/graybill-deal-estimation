import GD.Module1894
import GD.Module1543
import GD.Module1890

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0041
noncomputable section
open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1228
open _root_.GD.N0230.N0611
open _root_.GD.N0082

theorem d030794 : _root_.GD.N0232.N0720.N1256.d015549 2 3=⊤ :=
  (_root_.GD.N0067.d023924 2 3 (by omega) (by omega)).mpr
    (Or.inl ⟨rfl,by omega⟩)

theorem d030795
    (d : _root_.GD.N0232.N0720.N1080.d014170 2 3 → ℝ) (hd : Measurable d) : _root_.GD.N0232.N0720.N1256.d015548 2 3 d=⊤ := by
  apply top_unique
  rw [← _root_.GD.N0041.d030794]
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 2 3) hd



theorem d030796 :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015552 2 3,
      0 < _root_.GD.N0232.N0720.N1228.d016752 2 3 (by omega) (by omega) d  ∧
      _root_.GD.N0232.N0720.N1256.d015548 2 3 d=⊤ := by
  obtain ⟨J,d,_hJ,hd,hcap⟩ := _root_.GD.N0053.d030787
  exact ⟨d,hd,_root_.GD.N0053.d030790 2 3 (by omega) (by omega)
    d (_root_.GD.N0082.d030599 J) (_root_.GD.N0082.d030600 J) hcap,
    _root_.GD.N0041.d030795 d hd.1.1⟩



theorem d030797 :
    0 < _root_.GD.N0232.N0720.N1228.d016753 2 3 (by omega) (by omega) (_root_.GD.N0232.N0720.N1256.d015551 2 3)  ∧
    0 < _root_.GD.N0232.N0720.N1228.d016753 2 3 (by omega) (by omega) (_root_.GD.N0232.N0720.N1256.d015552 2 3)  ∧
    _root_.GD.N0232.N0720.N1256.d015549 2 3=⊤ :=
  ⟨_root_.GD.N0053.d030792.1,
    _root_.GD.N0053.d030792.2,_root_.GD.N0041.d030794⟩

private theorem d030798 :
    0 < _root_.GD.N0232.N0720.N1228.d016753 3 3 (by omega) (by omega) (_root_.GD.N0232.N0720.N1256.d015551 3 3)  ∧
    0 < _root_.GD.N0232.N0720.N1228.d016753 3 3 (by omega) (by omega) (_root_.GD.N0232.N0720.N1256.d015552 3 3) := by
  obtain ⟨J,d,_hJ,hd,hcap⟩ := _root_.GD.N0082.N0328.d030760
  exact _root_.GD.N0053.d030791 3 3 (by omega) (by omega) d hd
    (_root_.GD.N0082.d030599 J) (_root_.GD.N0082.d030600 J) hcap



theorem d030799
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hnot22 : m ≠ 2  ∨  n ≠ 2) :
    (0 < _root_.GD.N0232.N0720.N1228.d016753 m n hm hn (_root_.GD.N0232.N0720.N1256.d015551 m n)  ∧
      0 < _root_.GD.N0232.N0720.N1228.d016753 m n hm hn (_root_.GD.N0232.N0720.N1256.d015552 m n))  ↔
      m ≤ 3  ∧  n ≤ 3 := by
  constructor
  · intro hp
    by_contra hnot
    have hlarge : 4 ≤ m  ∨  4 ≤ n := by omega
    have hz := _root_.GD.N0232.N0720.N1228.d016756 m n hm hn hlarge
    rw [hz.1] at hp
    exact lt_irrefl _ hp.1
  · rintro ⟨hm3,hn3⟩
    interval_cases m  <;>  interval_cases n
    · exact False.elim (hnot22.elim (fun h =>  h rfl) (fun h =>  h rfl))
    · exact _root_.GD.N0053.d030792
    · exact _root_.GD.N0053.d030793
    · exact _root_.GD.N0041.d030798


theorem d030800
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (hnot22 : m ≠ 2  ∨  n ≠ 2) :
    (_root_.GD.N0232.N0720.N1228.d016753 m n hm hn (_root_.GD.N0232.N0720.N1256.d015551 m n)=0  ∧
      _root_.GD.N0232.N0720.N1228.d016753 m n hm hn (_root_.GD.N0232.N0720.N1256.d015552 m n)=0)  ↔
      4 ≤ m  ∨  4 ≤ n := by
  constructor
  · intro hz
    by_contra hnot
    have hp := (_root_.GD.N0041.d030799 m n hm hn hnot22).mpr
      (by omega : m ≤ 3  ∧  n ≤ 3)
    rw [hz.1] at hp
    exact lt_irrefl _ hp.1
  · exact _root_.GD.N0232.N0720.N1228.d016756 m n hm hn



theorem d030801 :
    _root_.GD.N0232.N0720.N1228.d016753 2 4 (by omega) (by omega) (_root_.GD.N0232.N0720.N1256.d015551 2 4)  <
      _root_.GD.N0232.N0720.N1228.d016753 2 3 (by omega) (by omega) (_root_.GD.N0232.N0720.N1256.d015551 2 3)  ∧
    _root_.GD.N0232.N0720.N1228.d016753 2 4 (by omega) (by omega) (_root_.GD.N0232.N0720.N1256.d015552 2 4)  <
      _root_.GD.N0232.N0720.N1228.d016753 2 3 (by omega) (by omega) (_root_.GD.N0232.N0720.N1256.d015552 2 3)  ∧
    _root_.GD.N0232.N0720.N1256.d015549 2 3=⊤  ∧  _root_.GD.N0232.N0720.N1256.d015549 2 4=⊤ := by
  have hz := _root_.GD.N0232.N0720.N1228.d016756 2 4 (by omega) (by omega)
    (Or.inr (by omega))
  rw [hz.1,hz.2]
  exact ⟨_root_.GD.N0053.d030792.1,
    _root_.GD.N0053.d030792.2,_root_.GD.N0041.d030794,
    (_root_.GD.N0067.d023924 2 4 (by omega) (by omega)).mpr
      (Or.inl ⟨rfl,by omega⟩)⟩

end
end GD.N0041

#print axioms _root_.GD.N0041.d030795
#print axioms _root_.GD.N0041.d030796
#print axioms _root_.GD.N0041.d030797

#print axioms _root_.GD.N0041.d030799
#print axioms _root_.GD.N0041.d030800

#print axioms _root_.GD.N0041.d030801
