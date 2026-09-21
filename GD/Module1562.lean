import GD.Module0523
import GD.Module1561
import GD.Module0391






set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace GD.N0106.N0428.N0766.N1691
noncomputable section

open _root_.GD.N0232.N0720.N1254
open _root_.GD.N0106.N0428.N0766.N1690 _root_.GD.N0106.N0428.N0766.N1692.N1763



def d024093 (alpha beta : ℝ) (N : ℕ) (w : ℝ) (x : ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0766.N1691.d024082 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N)
    (fun i => _root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N i /
      _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i)) w x

def d024094 (x : ℝ × ℝ) : ℝ × ℝ := (1 - x.1, x.2)


def d024095 : Fin 8 → Fin 8 := ![4, 3, 2, 1, 0, 7, 6, 5]

theorem d024096 : Function.Involutive _root_.GD.N0106.N0428.N0766.N1691.d024095 := by
  intro i
  fin_cases i <;> rfl

theorem d024097 (g : Fin 8 → ℝ) :
    (∑ i, g (_root_.GD.N0106.N0428.N0766.N1691.d024095 i)) = ∑ i, g i := by
  simp [Fin.sum_univ_succ, _root_.GD.N0106.N0428.N0766.N1691.d024095] <;> ring

theorem d024098 (alpha beta : ℝ) (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 beta alpha (_root_.GD.N0106.N0428.N0766.N1691.d024094 x) = _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta x := by
  dsimp [_root_.GD.N0106.N0428.N0766.N1692.N1763.d007846, _root_.GD.N0106.N0428.N0766.N1691.d024094]
  rw [show 1 - (1 - x.1) = x.1 by ring]
  ring

theorem d024099 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 0 < beta) :
    _root_.GD.N0232.N0720.N1254.d002514 beta alpha = 1 - _root_.GD.N0232.N0720.N1254.d002514 alpha beta := by
  obtain ⟨_, _, _, _, hA, _, _⟩ :=
    _root_.GD.N0232.N0720.N1254.d002583 alpha beta 0 (_root_.GD.N0232.N0720.N1254.d002522 ha hb).ne'
  unfold _root_.GD.N0232.N0720.N1254.d002515 at hA
  linarith

theorem d024100 (alpha beta : ℝ) (N : ℕ) :
    _root_.GD.N0232.N0720.N1254.d002519 beta alpha N = _root_.GD.N0232.N0720.N1254.d002519 alpha beta N := by
  unfold _root_.GD.N0232.N0720.N1254.d002519 _root_.GD.N0232.N0720.N1254.d002518 _root_.GD.N0232.N0720.N1254.d002510
  rw [min_comm beta alpha, add_comm beta alpha]

theorem d024101 (alpha beta : ℝ) (N : ℕ) :
    _root_.GD.N0232.N0720.N1254.d002520 beta alpha N = _root_.GD.N0232.N0720.N1254.d002520 alpha beta N := by
  unfold _root_.GD.N0232.N0720.N1254.d002520 _root_.GD.N0232.N0720.N1254.d002512 _root_.GD.N0232.N0720.N1254.d002510
  rw [mul_comm beta alpha, add_comm beta alpha]

theorem d024102 (ell h eta : ℝ) (i : Fin 8) :
    _root_.GD.N0106.N0428.N0766.N1690.d005999 (1 - ell) h eta i =
      _root_.GD.N0106.N0428.N0766.N1691.d024094 (_root_.GD.N0106.N0428.N0766.N1690.d005999 ell h eta (_root_.GD.N0106.N0428.N0766.N1691.d024095 i)) := by
  fin_cases i <;> apply Prod.ext <;>
    dsimp [_root_.GD.N0106.N0428.N0766.N1690.d005999, _root_.GD.N0106.N0428.N0766.N1691.d024095, _root_.GD.N0106.N0428.N0766.N1691.d024094] <;> ring

theorem d024103 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (N : ℕ) (i : Fin 8) :
    _root_.GD.N0106.N0428.N0766.N1690.d006013 beta alpha N i =
      _root_.GD.N0106.N0428.N0766.N1691.d024094 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i)) := by
  unfold _root_.GD.N0106.N0428.N0766.N1690.d006013
  rw [_root_.GD.N0106.N0428.N0766.N1691.d024099 ha hb, _root_.GD.N0106.N0428.N0766.N1691.d024100 alpha beta N,
    _root_.GD.N0106.N0428.N0766.N1691.d024101 alpha beta N]
  exact _root_.GD.N0106.N0428.N0766.N1691.d024102 _ _ _ i



theorem d024104 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (h eta : ℝ) (i : Fin 8) :
    _root_.GD.N0106.N0428.N0766.N1690.d006000 beta alpha h eta i =
      -_root_.GD.N0106.N0428.N0766.N1690.d006000 alpha beta h eta (_root_.GD.N0106.N0428.N0766.N1691.d024095 i) := by
  obtain ⟨h00, h10, h20, h30, h01, h11⟩ := _root_.GD.N0232.N0720.N1254.d002584 ha hb
  fin_cases i <;>
    simp [_root_.GD.N0106.N0428.N0766.N1690.d006000, _root_.GD.N0106.N0428.N0766.N1691.d024095, _root_.GD.N0232.N0720.N1254.d002567, _root_.GD.N0232.N0720.N1254.d002568,
      _root_.GD.N0232.N0720.N1254.d002569, _root_.GD.N0232.N0720.N1254.d002570, _root_.GD.N0232.N0720.N1254.d002571, _root_.GD.N0232.N0720.N1254.d002572,
      _root_.GD.N0232.N0720.N1254.d002573, _root_.GD.N0232.N0720.N1254.d002574, h00, h10, h20, h30, h01, h11] <;>
    ring

theorem d024105 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (N : ℕ) (i : Fin 8) :
    _root_.GD.N0106.N0428.N0766.N1690.d006014 beta alpha N i =
      -_root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i) := by
  unfold _root_.GD.N0106.N0428.N0766.N1690.d006014
  rw [_root_.GD.N0106.N0428.N0766.N1691.d024100 alpha beta N, _root_.GD.N0106.N0428.N0766.N1691.d024101 alpha beta N]
  exact _root_.GD.N0106.N0428.N0766.N1691.d024104 ha hb _ _ i

theorem d024106 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (N : ℕ) (i : Fin 8) :
    _root_.GD.N0106.N0428.N0766.N1690.d006014 beta alpha N i / _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 beta alpha (_root_.GD.N0106.N0428.N0766.N1690.d006013 beta alpha N i) =
      -(_root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i) /
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i))) := by
  rw [_root_.GD.N0106.N0428.N0766.N1691.d024105 ha hb, _root_.GD.N0106.N0428.N0766.N1691.d024103 ha hb, _root_.GD.N0106.N0428.N0766.N1691.d024098,
    neg_div]

theorem d024107 (ell h eta : ℝ) :
    _root_.GD.N0106.N0428.N0766.N1690.d006009 (1 - ell) h eta = _root_.GD.N0106.N0428.N0766.N1690.d006009 ell h eta := by
  unfold _root_.GD.N0106.N0428.N0766.N1690.d006009
  rw [show 1 - (1 - ell) - 2 * h = ell - 2 * h by ring,
    min_comm (1 - ell - 2 * h) (ell - 2 * h)]


theorem d024108 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (N : ℕ) :
    _root_.GD.N0106.N0428.N0766.N1690.d006015 beta alpha N = _root_.GD.N0106.N0428.N0766.N1690.d006015 alpha beta N := by
  unfold _root_.GD.N0106.N0428.N0766.N1690.d006015
  rw [_root_.GD.N0106.N0428.N0766.N1691.d024099 ha hb, _root_.GD.N0106.N0428.N0766.N1691.d024100 alpha beta N,
    _root_.GD.N0106.N0428.N0766.N1691.d024101 alpha beta N, _root_.GD.N0106.N0428.N0766.N1691.d024107]



theorem d024109 {alpha beta w : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (hw : 0 < w) (N : ℕ) (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0766.N1691.d024093 beta alpha N w (_root_.GD.N0106.N0428.N0766.N1691.d024094 x) =
      -_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w x := by
  have hterm (i : Fin 8) :
      (_root_.GD.N0106.N0428.N0766.N1690.d006014 beta alpha N i /
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 beta alpha (_root_.GD.N0106.N0428.N0766.N1690.d006013 beta alpha N i)) *
        _root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 beta alpha N i).1
          (_root_.GD.N0106.N0428.N0766.N1690.d006013 beta alpha N i).2 w (_root_.GD.N0106.N0428.N0766.N1691.d024094 x) =
      -((_root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i) /
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i))) *
        _root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i)).1
          (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i)).2 w x) := by
    rw [_root_.GD.N0106.N0428.N0766.N1691.d024106 ha hb]
    simp only [_root_.GD.N0106.N0428.N0766.N1691.d024103 ha hb, _root_.GD.N0106.N0428.N0766.N1691.d024094]
    rw [_root_.GD.N0106.N0428.N0766.N1691.d024075 _ _ _ x hw]
    ring
  unfold _root_.GD.N0106.N0428.N0766.N1691.d024093 _root_.GD.N0106.N0428.N0766.N1691.d024082
  calc
    _ = ∑ i, -((_root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i) /
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i))) *
        _root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i)).1
          (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i)).2 w x) :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    _ = -(∑ i, (_root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i) /
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i))) *
        _root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i)).1
          (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N (_root_.GD.N0106.N0428.N0766.N1691.d024095 i)).2 w x) :=
      by rw [Finset.sum_neg_distrib]
    _ = _ := congrArg Neg.neg (_root_.GD.N0106.N0428.N0766.N1691.d024097 (fun i =>
      (_root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N i / _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i)) *
      _root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).1
        (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).2 w x))


theorem d024110 {alpha w : ℝ}
    (ha : 0 < alpha) (hw : 0 < w) (N : ℕ) (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0766.N1691.d024093 alpha alpha N w (_root_.GD.N0106.N0428.N0766.N1691.d024094 x) =
      -_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha alpha N w x :=
  _root_.GD.N0106.N0428.N0766.N1691.d024109 ha ha hw N x

theorem d024111 {alpha w : ℝ}
    (ha : 0 < alpha) (hw : 0 < w) (N : ℕ) (F : ℝ) :
    _root_.GD.N0106.N0428.N0766.N1691.d024093 alpha alpha N w ((1 : ℝ) / 2, F) = 0 := by
  have h := _root_.GD.N0106.N0428.N0766.N1691.d024110 ha hw N ((1 : ℝ) / 2, F)
  have hfix : _root_.GD.N0106.N0428.N0766.N1691.d024094 ((1 : ℝ) / 2, F) = ((1 : ℝ) / 2, F) := by
    ext <;> norm_num [_root_.GD.N0106.N0428.N0766.N1691.d024094]
  rw [hfix] at h
  linarith

end
end GD.N0106.N0428.N0766.N1691

#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024098
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024103
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024105
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024106
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024108
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024109
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024110
#print axioms _root_.GD.N0106.N0428.N0766.N1691.d024111
