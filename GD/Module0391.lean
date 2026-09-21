import GD.Module0190
import Mathlib.Tactic











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set
open scoped BigOperators

namespace GD.N0106.N0428.N0766.N1690
noncomputable section

open _root_.GD.N0232.N0720.N1254


def d005998 : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioi 0


def d005999 (ell h eta : ℝ) : Fin 8 → ℝ × ℝ :=
  ![(ell - 2 * h, eta), (ell - h, eta), (ell, eta),
    (ell + h, eta), (ell + 2 * h, eta),
    (ell - h, 2 * eta), (ell, 2 * eta), (ell + h, 2 * eta)]


def d006000 (alpha beta h eta : ℝ) : Fin 8 → ℝ :=
  ![_root_.GD.N0232.N0720.N1254.d002567 alpha beta h,
    _root_.GD.N0232.N0720.N1254.d002568 alpha beta h eta,
    _root_.GD.N0232.N0720.N1254.d002569 alpha beta h eta,
    _root_.GD.N0232.N0720.N1254.d002570 alpha beta h eta,
    _root_.GD.N0232.N0720.N1254.d002571 alpha beta h,
    _root_.GD.N0232.N0720.N1254.d002572 alpha beta h eta,
    _root_.GD.N0232.N0720.N1254.d002573 alpha beta eta,
    _root_.GD.N0232.N0720.N1254.d002574 alpha beta h eta]

def d006001 (g : Fin 8 → ℝ) : _root_.GD.N0232.N0720.N1254.d002559 where
  minusTwoEta := g 0
  minusEta := g 1
  zeroEta := g 2
  plusEta := g 3
  plusTwoEta := g 4
  minusTwoEtaLevel := g 5
  zeroTwoEtaLevel := g 6
  plusTwoEtaLevel := g 7


theorem d006002 (alpha beta h eta : ℝ)
    (hh : h ≠ 0) (heta : eta ≠ 0) (g : Fin 8 → ℝ) :
    (∑ i, _root_.GD.N0106.N0428.N0766.N1690.d006000 alpha beta h eta i * g i) =
      _root_.GD.N0232.N0720.N1254.d002566 alpha beta h eta (_root_.GD.N0106.N0428.N0766.N1690.d006001 g) := by
  rw [_root_.GD.N0232.N0720.N1254.d002575 alpha beta h eta hh heta]
  simp [Fin.sum_univ_succ, _root_.GD.N0106.N0428.N0766.N1690.d006000, _root_.GD.N0106.N0428.N0766.N1690.d006001] <;> ring


theorem d006003 (alpha beta ell h eta : ℝ)
    (hh : h ≠ 0) (heta : eta ≠ 0) (f : ℝ × ℝ → ℝ) :
    (∑ i, _root_.GD.N0106.N0428.N0766.N1690.d006000 alpha beta h eta i * f (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i)) =
      _root_.GD.N0232.N0720.N1254.d002566 alpha beta h eta
        (_root_.GD.N0106.N0428.N0766.N1690.d006001 (fun i => f (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i))) :=
  _root_.GD.N0106.N0428.N0766.N1690.d006002 alpha beta h eta hh heta _

theorem d006004 {ell h eta : ℝ} (hh : 0 < h) (i : Fin 8) :
    ell - 2 * h ≤ (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).1 ∧
      (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).1 ≤ ell + 2 * h := by
  fin_cases i <;> dsimp [_root_.GD.N0106.N0428.N0766.N1690.d005999] <;> constructor <;> linarith

theorem d006005 {ell h eta : ℝ} (heta : 0 < eta) (i : Fin 8) :
    eta ≤ (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).2 := by
  fin_cases i <;> dsimp [_root_.GD.N0106.N0428.N0766.N1690.d005999] <;> linarith



theorem d006006 {ell h eta : ℝ} (hh : 0 < h) (heta : 0 < eta)
    {i j : Fin 8} (hij : i ≠ j) :
    ((_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).1 + h ≤ (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta j).1 ∨
      (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta j).1 + h ≤ (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).1) ∨
    ((_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).2 + eta ≤ (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta j).2 ∨
      (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta j).2 + eta ≤ (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).2) := by
  fin_cases i <;> fin_cases j <;> (try exact (hij rfl).elim)
  all_goals
    dsimp [_root_.GD.N0106.N0428.N0766.N1690.d005999]
    first
    | exact Or.inl (Or.inl (by linarith))
    | exact Or.inl (Or.inr (by linarith))
    | exact Or.inr (Or.inl (by linarith))
    | exact Or.inr (Or.inr (by linarith))


def d006007 (z : ℝ × ℝ) (w : ℝ) : Set (ℝ × ℝ) :=
  Icc (z.1 - w) (z.1 + w) ×ˢ Icc (z.2 - w) (z.2 + w)

theorem d006008 (z : ℝ × ℝ) (w : ℝ) :
    IsCompact (_root_.GD.N0106.N0428.N0766.N1690.d006007 z w) :=
  isCompact_Icc.prod isCompact_Icc



def d006009 (ell h eta : ℝ) : ℝ :=
  min (min h eta) (min (ell - 2 * h) (1 - ell - 2 * h)) / 4

theorem d006010 {ell h eta : ℝ}
    (hh : 0 < h) (heta : 0 < eta)
    (hleft : 0 < ell - 2 * h) (hright : 0 < 1 - ell - 2 * h) :
    0 < _root_.GD.N0106.N0428.N0766.N1690.d006009 ell h eta ∧
      4 * _root_.GD.N0106.N0428.N0766.N1690.d006009 ell h eta ≤ h ∧
      4 * _root_.GD.N0106.N0428.N0766.N1690.d006009 ell h eta ≤ eta ∧
      4 * _root_.GD.N0106.N0428.N0766.N1690.d006009 ell h eta ≤ ell - 2 * h ∧
      4 * _root_.GD.N0106.N0428.N0766.N1690.d006009 ell h eta ≤ 1 - ell - 2 * h := by
  let m := min (min h eta) (min (ell - 2 * h) (1 - ell - 2 * h))
  have hm : 0 < m := lt_min (lt_min hh heta) (lt_min hleft hright)
  have hm_h : m ≤ h := (min_le_left _ _).trans (min_le_left _ _)
  have hm_eta : m ≤ eta := (min_le_left _ _).trans (min_le_right _ _)
  have hm_left : m ≤ ell - 2 * h := (min_le_right _ _).trans (min_le_left _ _)
  have hm_right : m ≤ 1 - ell - 2 * h := (min_le_right _ _).trans (min_le_right _ _)
  change 0 < m / 4 ∧ 4 * (m / 4) ≤ h ∧ 4 * (m / 4) ≤ eta ∧
    4 * (m / 4) ≤ ell - 2 * h ∧ 4 * (m / 4) ≤ 1 - ell - 2 * h
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem d006011 {ell h eta w : ℝ}
    (hh : 0 < h) (heta : 0 < eta)
    (hleft : 0 < ell - 2 * h) (hright : 0 < 1 - ell - 2 * h)
    (hw : 0 < w) (hwsmall : w ≤ _root_.GD.N0106.N0428.N0766.N1690.d006009 ell h eta) (i : Fin 8) :
    _root_.GD.N0106.N0428.N0766.N1690.d006007 (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i) w ⊆ _root_.GD.N0106.N0428.N0766.N1690.d005998 := by
  obtain ⟨_, _, hwe, hwl, hwr⟩ := _root_.GD.N0106.N0428.N0766.N1690.d006010 hh heta hleft hright
  obtain ⟨hlo, hhi⟩ := _root_.GD.N0106.N0428.N0766.N1690.d006004 (ell := ell) (eta := eta) hh i
  have hv := _root_.GD.N0106.N0428.N0766.N1690.d006005 (ell := ell) (h := h) heta i
  intro x hx
  change ((_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).1 - w ≤ x.1 ∧
      x.1 ≤ (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).1 + w) ∧
      ((_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).2 - w ≤ x.2 ∧
      x.2 ≤ (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).2 + w) at hx
  change (0 < x.1 ∧ x.1 < 1) ∧ 0 < x.2
  exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩,
    by linarith [hx.2.1]⟩

theorem d006012 {ell h eta w : ℝ}
    (hh : 0 < h) (heta : 0 < eta)
    (hleft : 0 < ell - 2 * h) (hright : 0 < 1 - ell - 2 * h)
    (hw : 0 < w) (hwsmall : w ≤ _root_.GD.N0106.N0428.N0766.N1690.d006009 ell h eta) :
    Pairwise (fun i j : Fin 8 => Disjoint
      (_root_.GD.N0106.N0428.N0766.N1690.d006007 (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i) w)
      (_root_.GD.N0106.N0428.N0766.N1690.d006007 (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta j) w)) := by
  obtain ⟨_, hwh, hwe, _, _⟩ := _root_.GD.N0106.N0428.N0766.N1690.d006010 hh heta hleft hright
  have hsep_h : 2 * w < h := by linarith
  have hsep_eta : 2 * w < eta := by linarith
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  change ((_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).1 - w ≤ x.1 ∧
      x.1 ≤ (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).1 + w) ∧
      ((_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).2 - w ≤ x.2 ∧
      x.2 ≤ (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta i).2 + w) at hi
  change ((_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta j).1 - w ≤ x.1 ∧
      x.1 ≤ (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta j).1 + w) ∧
      ((_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta j).2 - w ≤ x.2 ∧
      x.2 ≤ (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta j).2 + w) at hj
  rcases _root_.GD.N0106.N0428.N0766.N1690.d006006 hh heta hij with (hijx | hjix) | (hijy | hjiy)
  · linarith [hi.1.2, hj.1.1]
  · linarith [hj.1.2, hi.1.1]
  · linarith [hi.2.2, hj.2.1]
  · linarith [hj.2.2, hi.2.1]

def d006013 (alpha beta : ℝ) (N : ℕ) : Fin 8 → ℝ × ℝ :=
  _root_.GD.N0106.N0428.N0766.N1690.d005999 (_root_.GD.N0232.N0720.N1254.d002514 alpha beta)
    (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N)

def d006014 (alpha beta : ℝ) (N : ℕ) : Fin 8 → ℝ :=
  _root_.GD.N0106.N0428.N0766.N1690.d006000 alpha beta (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N)

def d006015 (alpha beta : ℝ) (N : ℕ) : ℝ :=
  _root_.GD.N0106.N0428.N0766.N1690.d006009 (_root_.GD.N0232.N0720.N1254.d002514 alpha beta)
    (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N)


theorem d006016 {alpha beta : ℝ} {N : ℕ}
    (ha : 0 < alpha) (hb : 0 < beta) (hN : 1 ≤ N) (i : Fin 8) :
    _root_.GD.N0232.N0720.N1254.d002576 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).1
      (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).2 := by
  have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    _root_.GD.N0232.N0720.N1254.d002579 ha hb hNpos
  fin_cases i
  · simpa [_root_.GD.N0106.N0428.N0766.N1690.d006013, _root_.GD.N0106.N0428.N0766.N1690.d005999] using h0
  · simpa [_root_.GD.N0106.N0428.N0766.N1690.d006013, _root_.GD.N0106.N0428.N0766.N1690.d005999] using h1
  · simpa [_root_.GD.N0106.N0428.N0766.N1690.d006013, _root_.GD.N0106.N0428.N0766.N1690.d005999] using h2
  · simpa [_root_.GD.N0106.N0428.N0766.N1690.d006013, _root_.GD.N0106.N0428.N0766.N1690.d005999] using h3
  · simpa [_root_.GD.N0106.N0428.N0766.N1690.d006013, _root_.GD.N0106.N0428.N0766.N1690.d005999] using h4
  · simpa [_root_.GD.N0106.N0428.N0766.N1690.d006013, _root_.GD.N0106.N0428.N0766.N1690.d005999] using h5
  · simpa [_root_.GD.N0106.N0428.N0766.N1690.d006013, _root_.GD.N0106.N0428.N0766.N1690.d005999] using h6
  · simpa [_root_.GD.N0106.N0428.N0766.N1690.d006013, _root_.GD.N0106.N0428.N0766.N1690.d005999] using h7



theorem d006017 {alpha beta : ℝ} {N : ℕ}
    (ha : 0 < alpha) (hb : 0 < beta) (hN : 1 ≤ N) :
    0 < _root_.GD.N0106.N0428.N0766.N1690.d006015 alpha beta N ∧
      ∀ w : ℝ, 0 < w → w ≤ _root_.GD.N0106.N0428.N0766.N1690.d006015 alpha beta N →
        (∀ i : Fin 8, IsCompact (_root_.GD.N0106.N0428.N0766.N1690.d006007 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i) w) ∧
          _root_.GD.N0106.N0428.N0766.N1690.d006007 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i) w ⊆ _root_.GD.N0106.N0428.N0766.N1690.d005998) ∧
        Pairwise (fun i j : Fin 8 => Disjoint
          (_root_.GD.N0106.N0428.N0766.N1690.d006007 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i) w)
          (_root_.GD.N0106.N0428.N0766.N1690.d006007 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N j) w)) := by
  have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hh := _root_.GD.N0232.N0720.N1254.d002528 ha hb hNpos
  have heta := _root_.GD.N0232.N0720.N1254.d002529 ha hb hNpos
  have h0 := _root_.GD.N0106.N0428.N0766.N1690.d006016 ha hb hN (0 : Fin 8)
  have h4 := _root_.GD.N0106.N0428.N0766.N1690.d006016 ha hb hN (4 : Fin 8)
  have hleft : 0 < _root_.GD.N0232.N0720.N1254.d002514 alpha beta - 2 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N := by
    simpa [_root_.GD.N0232.N0720.N1254.d002576, _root_.GD.N0106.N0428.N0766.N1690.d006013, _root_.GD.N0106.N0428.N0766.N1690.d005999] using h0.1
  have hright : 0 < 1 - _root_.GD.N0232.N0720.N1254.d002514 alpha beta - 2 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N := by
    have hh4 : _root_.GD.N0232.N0720.N1254.d002514 alpha beta + 2 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N < 1 := by
      simpa [_root_.GD.N0106.N0428.N0766.N1690.d006013, _root_.GD.N0106.N0428.N0766.N1690.d005999] using h4.2.1
    linarith
  refine ⟨(_root_.GD.N0106.N0428.N0766.N1690.d006010 hh heta hleft hright).1, ?_⟩
  intro w hw hwsmall
  constructor
  · intro i
    exact ⟨_root_.GD.N0106.N0428.N0766.N1690.d006008 _ _,
      _root_.GD.N0106.N0428.N0766.N1690.d006011 hh heta hleft hright hw hwsmall i⟩
  · exact _root_.GD.N0106.N0428.N0766.N1690.d006012 hh heta hleft hright hw hwsmall

end
end GD.N0106.N0428.N0766.N1690

#print axioms _root_.GD.N0106.N0428.N0766.N1690.d006002
#print axioms _root_.GD.N0106.N0428.N0766.N1690.d006006
#print axioms _root_.GD.N0106.N0428.N0766.N1690.d006010
#print axioms _root_.GD.N0106.N0428.N0766.N1690.d006011
#print axioms _root_.GD.N0106.N0428.N0766.N1690.d006012
#print axioms _root_.GD.N0106.N0428.N0766.N1690.d006017
