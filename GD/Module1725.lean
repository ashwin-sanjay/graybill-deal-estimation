import GD.Module1724
import GD.Module1564
import GD.Module0520






set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace GD.N0106.N0428.N0766
noncomputable section

open Set MeasureTheory
open scoped BigOperators
open _root_.GD.N0232.N0720.N1254
open _root_.GD.N0106.N0428.N0766.N1692 _root_.GD.N0106.N0428.N0766.N1691 _root_.GD.N0106.N0428.N0766.N1690 _root_.GD.N0106.N0428.N0766.N1692.N1763
open _root_.GD.N0118




structure d028750 (alpha beta : ℝ) (N : ℕ) (w : ℝ) : Prop where
  resolution_pos : 1 ≤ N
  width_pos : 0 < w
  width_le : w ≤ _root_.GD.N0106.N0428.N0766.N1690.d006015 alpha beta N
  continuous : Continuous (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w)
  compact : HasCompactSupport (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w)
  inside : tsupport (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844
  bounded : ∃ B > 0, ∀ x, |_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w x| ≤ B
  tent_supports : ∀ i : Fin 8,
    HasCompactSupport (_root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).1
      (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).2 w) ∧
    tsupport (_root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).1
      (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).2 w) ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844
  disjoint : Pairwise fun i j : Fin 8 => Disjoint
    (tsupport (_root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).1 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).2 w))
    (tsupport (_root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N j).1 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N j).2 w))
  trace_integrable : ∀ e ∈ Icc (0 : ℝ) 1,
    Integrable (fun x => _root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w x * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x))
      (volume.prod volume)
  energy_integrable : ∀ e ∈ Icc (0 : ℝ) 1,
    Integrable (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * _root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w x ^ 2)
      (volume.prod volume)
  improves : ∃ epsilon > 0, ∀ e ∈ Icc (0 : ℝ) 1,
    2 * epsilon * _root_.GD.N0106.N0428.N0766.d028738 alpha beta (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) e +
      epsilon ^ 2 * _root_.GD.N0106.N0428.N0766.d028739 alpha beta (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) e < 0

theorem d028751 {alpha beta w J : ℝ} {N : ℕ}
    (ha : 0 < alpha) (hb : 0 < beta) (hN : 1 ≤ N) (hw : 0 < w)
    (hwsmall : w ≤ _root_.GD.N0106.N0428.N0766.N1690.d006015 alpha beta N) (hJ : 0 < J)
    (htrace : ∀ e ∈ Icc (0 : ℝ) 1,
      _root_.GD.N0106.N0428.N0766.d028738 alpha beta (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) e ≤ -5 * J / 8) :
    _root_.GD.N0106.N0428.N0766.d028750 alpha beta N w := by
  obtain ⟨hc, hk, hs⟩ := _root_.GD.N0106.N0428.N0766.d028748 ha hb hN hw hwsmall
  obtain ⟨K, hK, henergy⟩ := _root_.GD.N0106.N0428.N0766.d024115 ha hb hN hw hwsmall
  let coeff : Fin 8 → ℝ := fun i => _root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N i /
    _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i)
  let M := 1 + 4 * K / (9 * w ^ 2) * ∑ i, coeff i ^ 2
  have hsum : 0 ≤ ∑ i, coeff i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hM : 0 < M := by dsimp [M]; positivity
  let delta := 5 * J / 8
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨hrect, hdisj⟩ := (_root_.GD.N0106.N0428.N0766.N1690.d006017 ha hb hN).2 w hw hwsmall
  refine ⟨hN, hw, hwsmall, hc, hk, hs, ?_, ?_, ?_,
    (fun e he => _root_.GD.N0106.N0428.N0766.d028749 ha hb he hc hk hs),
    (fun e he => (henergy e he).1), ?_⟩
  · let B := (∑ i, |coeff i|) * (w⁻¹)^2
    have hB : 0 ≤ B := mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (sq_nonneg _)
    refine ⟨B + 1, by linarith, ?_⟩
    intro x
    exact (_root_.GD.N0106.N0428.N0766.N1691.d024089 _ coeff hw x).trans (by dsimp [B]; linarith)
  · intro i
    exact ⟨_root_.GD.N0106.N0428.N0766.N1691.d024080 _ _ _ hw.le,
      (_root_.GD.N0106.N0428.N0766.N1691.d024079 _ _ _ hw.le).trans (hrect i).2⟩
  · intro i j hij
    exact (hdisj hij).mono (_root_.GD.N0106.N0428.N0766.N1691.d024079 _ _ _ hw.le)
      (_root_.GD.N0106.N0428.N0766.N1691.d024079 _ _ _ hw.le)
  · refine ⟨delta / M, div_pos hdelta hM, ?_⟩
    intro e he
    have hT : _root_.GD.N0106.N0428.N0766.d028738 alpha beta (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) e ≤ -delta := by
      dsimp [delta]
      linarith [htrace e he]
    have hE : _root_.GD.N0106.N0428.N0766.d028739 alpha beta (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) e ≤ M := by
      have h := (henergy e he).2
      change _root_.GD.N0106.N0428.N0766.d028739 alpha beta (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) e ≤
        4 * K / (9 * w ^ 2) * ∑ i, coeff i ^ 2 at h
      dsimp [M]
      linarith
    exact (_root_.GD.N0232.N0720.N1254.d002590 hT hE hdelta hM).2

def d028752 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) : ℝ :=
  (_root_.GD.N0232.N0720.N1254.d002512 a.val b.val) ^ (-_root_.GD.N0232.N0720.N1254.d002513 a.val b.val)

theorem d028753 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) : 0 < _root_.GD.N0106.N0428.N0766.d028752 a b :=
  Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1254.d002523 a.property b.property) _

theorem d028754 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) :
    ∃ width > 0, width ≤ _root_.GD.N0106.N0428.N0766.N1690.d006015 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) ∧
      ∀ w, 0 < w → w ≤ width → ∀ e ∈ Icc (0 : ℝ) 1,
        _root_.GD.N0106.N0428.N0766.d028738 a.val b.val (_root_.GD.N0106.N0428.N0766.N1691.d024093 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) w) e ≤
          -5 * _root_.GD.N0106.N0428.N0766.d028752 a b / 8 :=
  _root_.GD.N0106.N0428.N0766.d028744 a.property b.property (_root_.GD.N0106.N0428.N0766.N1692.d007800 a b).1
    (_root_.GD.N0106.N0428.N0766.d028753 a b) (_root_.GD.N0106.N0428.N0766.N1692.d007800 a b).2

def d028755 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) : ℝ := Classical.choose (_root_.GD.N0106.N0428.N0766.d028754 a b)

theorem d028756 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) :
    0 < _root_.GD.N0106.N0428.N0766.d028755 a b ∧
      _root_.GD.N0106.N0428.N0766.d028755 a b ≤ _root_.GD.N0106.N0428.N0766.N1690.d006015 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) ∧
      ∀ w, 0 < w → w ≤ _root_.GD.N0106.N0428.N0766.d028755 a b → ∀ e ∈ Icc (0 : ℝ) 1,
        _root_.GD.N0106.N0428.N0766.d028738 a.val b.val (_root_.GD.N0106.N0428.N0766.N1691.d024093 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) w) e ≤
          -5 * _root_.GD.N0106.N0428.N0766.d028752 a b / 8 := Classical.choose_spec (_root_.GD.N0106.N0428.N0766.d028754 a b)

def d028757 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) : ℝ := min (_root_.GD.N0106.N0428.N0766.d028755 a b) (_root_.GD.N0106.N0428.N0766.d028755 b a)

theorem d028758 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) : _root_.GD.N0106.N0428.N0766.d028757 b a = _root_.GD.N0106.N0428.N0766.d028757 a b :=
  min_comm _ _

theorem d028759 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) : 0 < _root_.GD.N0106.N0428.N0766.d028757 a b :=
  lt_min (_root_.GD.N0106.N0428.N0766.d028756 a b).1 (_root_.GD.N0106.N0428.N0766.d028756 b a).1




theorem d028760 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) :
    _root_.GD.N0106.N0428.N0766.d028750 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) (_root_.GD.N0106.N0428.N0766.d028757 a b) := by
  have hw := _root_.GD.N0106.N0428.N0766.d028759 a b
  have hsmall : _root_.GD.N0106.N0428.N0766.d028757 a b ≤ _root_.GD.N0106.N0428.N0766.d028755 a b := min_le_left _ _
  exact _root_.GD.N0106.N0428.N0766.d028751 a.property b.property (_root_.GD.N0106.N0428.N0766.N1692.d007800 a b).1
    hw (hsmall.trans (_root_.GD.N0106.N0428.N0766.d028756 a b).2.1) (_root_.GD.N0106.N0428.N0766.d028753 a b)
    ((_root_.GD.N0106.N0428.N0766.d028756 a b).2.2 _ hw hsmall)



theorem d028761 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0766.N1691.d024093 b.val a.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 b a) (_root_.GD.N0106.N0428.N0766.d028757 b a) (_root_.GD.N0106.N0428.N0766.N1691.d024094 x) =
      -_root_.GD.N0106.N0428.N0766.N1691.d024093 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) (_root_.GD.N0106.N0428.N0766.d028757 a b) x := by
  rw [_root_.GD.N0106.N0428.N0766.N1692.d007799, _root_.GD.N0106.N0428.N0766.d028758]
  exact _root_.GD.N0106.N0428.N0766.N1691.d024109 a.property b.property (_root_.GD.N0106.N0428.N0766.d028759 a b) _ x



theorem d028762 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) (i : Fin 8) :
    (∫ x, _root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) i).1
      (_root_.GD.N0106.N0428.N0766.N1690.d006013 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) i).2 (_root_.GD.N0106.N0428.N0766.d028757 a b) x
      ∂(volume.prod volume)) = 1 ∧
    (∫ x, _root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) i).1
      (_root_.GD.N0106.N0428.N0766.N1690.d006013 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) i).2 (_root_.GD.N0106.N0428.N0766.d028757 a b) x ^ 2
      ∂(volume.prod volume)) = 4 / (9 * _root_.GD.N0106.N0428.N0766.d028757 a b ^ 2) :=
  ⟨_root_.GD.N0118.d008601 _ _ _ (_root_.GD.N0106.N0428.N0766.d028759 a b),
    _root_.GD.N0118.d008602 _ _ _ (_root_.GD.N0106.N0428.N0766.d028759 a b)⟩

end
end GD.N0106.N0428.N0766

#print axioms _root_.GD.N0106.N0428.N0766.d028751
#print axioms _root_.GD.N0106.N0428.N0766.d028760
#print axioms _root_.GD.N0106.N0428.N0766.d028761

#print axioms _root_.GD.N0106.N0428.N0766.d028762
