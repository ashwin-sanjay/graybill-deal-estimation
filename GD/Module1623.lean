import GD.Module1619
import GD.Module1620
import GD.Module1621
import GD.Module1622






set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

open Set
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1727
open _root_.GD.N0106.N0428.N0770.N1743

namespace GD.N0106.N0428.N0770.N1737



theorem d027692 : ∀ i < 28, _root_.GD.N0106.N0428.N0770.N1743.d027646 i = true := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027665
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027666
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027667
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027668
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027669
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027670
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027671
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027672
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027673
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027674
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027675
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027676
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027677
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027678
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027679
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027680
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027681
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027682
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027683
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027684
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027685
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027686
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027687
  · exact _root_.GD.N0106.N0428.N0770.N1739.d027664
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027688
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027689
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027690
  · exact _root_.GD.N0106.N0428.N0770.N1740.d027691




theorem d027693 {q ea Fa eb Fb : ℝ} (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hea : ea ∈ Icc (1 / 500 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 500 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (hFa : Fa ∈ Icc (1 / 1000 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 1000 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (heb : eb ∈ Icc (1 / 120 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 120 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (hFb : Fb ∈ Icc (20 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (20 + _root_.GD.N0106.N0428.N0770.N1725.d024118)) :
    0 < _root_.GD.N0106.N0428.N0770.N1727.d024439 q ea Fa eb Fb :=
  _root_.GD.N0106.N0428.N0770.N1743.d027657 _root_.GD.N0106.N0428.N0770.N1737.d027692 hq hea hFa heb hFb


theorem d027694 {q ea Fa eb Fb : ℝ} (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hea : ea ∈ Icc (1 / 500 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 500 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (hFa : Fa ∈ Icc (1 / 1000 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 1000 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (heb : eb ∈ Icc (1 / 120 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 120 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (hFb : Fb ∈ Icc (20 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (20 + _root_.GD.N0106.N0428.N0770.N1725.d024118)) :
    0 < 4 * _root_.GD.N0106.N0428.N0770.N1727.d024437 q eb Fb - 3 * _root_.GD.N0106.N0428.N0770.N1727.d024437 q ea Fa -
      (_root_.GD.N0106.N0428.N0770.N1725.d024119 / 2) * (9 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q ea Fa + 16 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q eb Fb) -
      (1 / 1000) * (_root_.GD.N0106.N0428.N0770.N1727.d024438 q ea Fa + _root_.GD.N0106.N0428.N0770.N1727.d024438 q eb Fb) :=
  _root_.GD.N0106.N0428.N0770.N1737.d027693 hq hea hFa heb hFb


theorem d027695 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (1 / 2)) :
    ∃ i ≤ 27, (_root_.GD.N0106.N0428.N0770.N1743.d027635 i).d006810 q :=
  _root_.GD.N0106.N0428.N0770.N1743.d027656 hq

end GD.N0106.N0428.N0770.N1737

#print axioms _root_.GD.N0106.N0428.N0770.N1737.d027692
#print axioms _root_.GD.N0106.N0428.N0770.N1737.d027693
#print axioms _root_.GD.N0106.N0428.N0770.N1737.d027694
#print axioms _root_.GD.N0106.N0428.N0770.N1737.d027695
