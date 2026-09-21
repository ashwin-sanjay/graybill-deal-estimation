import GD.Module1575





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set
open _root_.GD.N0232.N0720.N1164
open _root_.GD.N0106.N0428.N0770.N1719
open _root_.GD.N0106.N0428.N0770.N1728
open _root_.GD.N0106.N0428.N0770.N1727

namespace GD.N0106.N0428.N0770.N1704
noncomputable section

structure d026291 where
  interval : _root_.GD.N0232.N0720.N1164.d006809
  roots : Fin 4 → Fin 2 → _root_.GD.N0106.N0428.N0770.N1719.d024281

def d026292 : List _root_.GD.N0106.N0428.N0770.N1728.d024386 := [(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)]

theorem d026293 : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, i ∈ _root_.GD.N0106.N0428.N0770.N1704.d026292 := by decide +kernel

def d026294 (R : _root_.GD.N0106.N0428.N0770.N1719.d024281) (J K : _root_.GD.N0232.N0720.N1164.d006809) : Decidable (R.d024282 J K) := by
  letI (a b : ℚ) : Decidable (a < b) := _root_.GD.N0232.N0720.N1164.d006825 a b
  letI (a b : ℚ) : Decidable (a ≤ b) := _root_.GD.N0232.N0720.N1164.d006826 a b
  exact decidable_of_iff
    (0 < J.lo ∧ J.lo ≤ J.hi ∧ 0 ≤ R.ratioRoot.lo ∧ R.ratioRoot.lo ≤ R.ratioRoot.hi ∧
      R.ratioRoot.lo ^ 2 ≤ K.lo ∧ K.hi ≤ R.ratioRoot.hi ^ 2 ∧ 0 < R.nRoot.lo ∧
      R.nRoot.lo ≤ R.nRoot.hi ∧ R.nRoot.lo ^ 2 ≤ J.lo ∧ J.hi ≤ R.nRoot.hi ^ 2)
    ⟨fun ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ => ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩,
      fun h => ⟨h.nlo,h.norder,h.ratioLo,h.ratioOrder,h.ratioLower,h.ratioUpper,
        h.rootLo,h.rootOrder,h.rootLower,h.rootUpper⟩⟩

def d026295 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : _root_.GD.N0232.N0720.N1164.d006809 :=
  _root_.GD.N0106.N0428.N0770.N1719.d024260 (_root_.GD.N0106.N0428.N0770.N1727.d024430 i / (_root_.GD.N0106.N0428.N0770.N1727.d024429 i * (1 - _root_.GD.N0106.N0428.N0770.N1727.d024429 i)))

def d026296 (l : _root_.GD.N0106.N0428.N0770.N1704.d026291) (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : _root_.GD.N0232.N0720.N1164.d006809 :=
  _root_.GD.N0106.N0428.N0770.N1719.d024266 l.interval (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i)

def d026297 (l : _root_.GD.N0106.N0428.N0770.N1704.d026291) (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : Bool :=
  @decide ((l.roots i.1 i.2).d024282 (_root_.GD.N0106.N0428.N0770.N1704.d026296 l i) (_root_.GD.N0106.N0428.N0770.N1704.d026295 i))
    (_root_.GD.N0106.N0428.N0770.N1704.d026294 (l.roots i.1 i.2) (_root_.GD.N0106.N0428.N0770.N1704.d026296 l i) (_root_.GD.N0106.N0428.N0770.N1704.d026295 i))

def d026298 (l : _root_.GD.N0106.N0428.N0770.N1704.d026291) : ℚ :=
  (_root_.GD.N0106.N0428.N0770.N1727.d024433 l.interval 1 (fun i => l.roots i.1 i.2)).hi

def d026299 (l : _root_.GD.N0106.N0428.N0770.N1704.d026291) : Bool :=
  _root_.GD.N0106.N0428.N0770.N1704.d026292.all (_root_.GD.N0106.N0428.N0770.N1704.d026297 l) && @decide (_root_.GD.N0106.N0428.N0770.N1704.d026298 l < -47 / 200)
    (_root_.GD.N0232.N0720.N1164.d006825 (_root_.GD.N0106.N0428.N0770.N1704.d026298 l) (-47 / 200))

def d026300 (a b : ℚ) : Prop :=
  ∀ q : ℝ, q ∈ Icc 0 1 → (a : ℝ) ≤ q → q ≤ (b : ℝ) → _root_.GD.N0106.N0428.N0770.N1728.d024397 q < -47 / 200

theorem d026301 (l : _root_.GD.N0106.N0428.N0770.N1704.d026291) (hl : _root_.GD.N0106.N0428.N0770.N1704.d026299 l = true) :
    _root_.GD.N0106.N0428.N0770.N1704.d026300 l.interval.lo l.interval.hi := by
  intro q hq ha hb
  obtain ⟨hall,hcap⟩ := Bool.and_eq_true_iff.mp hl
  have hR : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, (l.roots i.1 i.2).d024282
      (_root_.GD.N0106.N0428.N0770.N1719.d024266 l.interval (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i))
      (_root_.GD.N0106.N0428.N0770.N1719.d024260 (_root_.GD.N0106.N0428.N0770.N1727.d024430 i / (_root_.GD.N0106.N0428.N0770.N1727.d024429 i * (1 - _root_.GD.N0106.N0428.N0770.N1727.d024429 i)))) := by
    intro i
    exact @of_decide_eq_true _ (_root_.GD.N0106.N0428.N0770.N1704.d026294 (l.roots i.1 i.2) (_root_.GD.N0106.N0428.N0770.N1704.d026296 l i) (_root_.GD.N0106.N0428.N0770.N1704.d026295 i))
      (List.all_eq_true.mp hall i (_root_.GD.N0106.N0428.N0770.N1704.d026293 i))
  have hbox := _root_.GD.N0106.N0428.N0770.N1727.d024435 hq (show l.interval.d006810 q from ⟨ha,hb⟩) hR
  have hc : _root_.GD.N0106.N0428.N0770.N1704.d026298 l < (-47 / 200 : ℚ) :=
    @of_decide_eq_true _ (_root_.GD.N0232.N0720.N1164.d006825 (_root_.GD.N0106.N0428.N0770.N1704.d026298 l) (-47 / 200)) hcap
  have hcR : ((_root_.GD.N0106.N0428.N0770.N1704.d026298 l : ℚ) : ℝ) < ((-47 / 200 : ℚ) : ℝ) := Rat.cast_lt.mpr hc
  norm_num at hcR
  apply hbox.2.trans_lt
  simpa only [_root_.GD.N0106.N0428.N0770.N1704.d026298, neg_div] using hcR

theorem d026302 {a b c : ℚ} (hab : _root_.GD.N0106.N0428.N0770.N1704.d026300 a b) (hbc : _root_.GD.N0106.N0428.N0770.N1704.d026300 b c) : _root_.GD.N0106.N0428.N0770.N1704.d026300 a c := by
  intro q hq ha hc
  by_cases hb : q ≤ (b : ℝ)
  · exact hab q hq ha hb
  · exact hbc q hq (not_le.mp hb).le hc

end
end GD.N0106.N0428.N0770.N1704

#print axioms _root_.GD.N0106.N0428.N0770.N1704.d026301
#print axioms _root_.GD.N0106.N0428.N0770.N1704.d026302
