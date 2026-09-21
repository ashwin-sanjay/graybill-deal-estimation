import GD.Module1554
import GD.Module1142









set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0232.N0720.N1474
noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1126 _root_.GD.N0232.N0720.N1125
open _root_.GD.N0232.N0720.N1130 _root_.GD.N0232.N0720.N1062
open _root_.GD.N0232.N0720.N1473
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608

variable (m n : ℕ)


def d024010 (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  ‖s‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2


theorem d024011
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hs : _root_.GD.N0232.N0720.N1159.d014637 m n s)
    (C : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1474.d024010 m n s ≤ _root_.GD.N0232.N0720.N1062.d018360 C s := by
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s
  have hpbelow := (_root_.GD.N0232.N0720.N1159.d014634 m n s).1
  have hpfinite : _root_.GD.N0232.N0720.N1159.d014637 m n p := fun θ ↦
    ne_top_of_le_ne_top (hs θ) (hpbelow θ)
  have hdist := _root_.GD.N0232.N0720.N1125.d017259
    C.packet C.weight C.weight_nonneg p (fun i ↦ hpfinite (C.packet i))
  rw [_root_.GD.N0232.N0720.N1125.d017257] at hdist
  have hmin : _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n) C.packet C.weight ≤
      _root_.GD.N0232.N0720.N1125.d017249 C.packet C.weight p := by
    nlinarith [sq_nonneg ‖p - _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
      C.packet C.weight C.weight_nonneg‖]
  have hsum : (∑ i, C.weight i * (_root_.GD.N0232.N0720.N1080.d014182 m n (C.packet i) p).toReal) ≤
      ∑ i, C.weight i * (_root_.GD.N0232.N0720.N1080.d014182 m n (C.packet i) s).toReal := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (hs (C.packet i)) (hpbelow (C.packet i)))
      (C.weight_nonneg i)
  unfold _root_.GD.N0232.N0720.N1474.d024010 _root_.GD.N0232.N0720.N1062.d018360 _root_.GD.N0232.N0720.N1125.d017249
  dsimp only [_root_.GD.N0232.N0720.N1125.d017249, p] at hmin hsum
  linarith


theorem d024012
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hs : _root_.GD.N0232.N0720.N1159.d014637 m n s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1062.d018360 C s < _root_.GD.N0232.N0720.N1474.d024010 m n s + ε := by
  obtain ⟨C, hC⟩ := _root_.GD.N0232.N0720.N1473.d024009 m n s hs
    (show ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2 - ε <
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2 by linarith)
  refine ⟨C, ?_⟩
  unfold _root_.GD.N0232.N0720.N1474.d024010 _root_.GD.N0232.N0720.N1062.d018360 _root_.GD.N0232.N0720.N1125.d017249
  unfold _root_.GD.N0232.N0720.N1473.d024008 at hC
  linarith


theorem d024013
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hs : _root_.GD.N0232.N0720.N1159.d014637 m n s) :
    (⨅ C : _root_.GD.N0232.N0720.N1130.d017074, _root_.GD.N0232.N0720.N1062.d018360 C s) =
      _root_.GD.N0232.N0720.N1474.d024010 m n s := by
  letI : Nonempty _root_.GD.N0232.N0720.N1130.d017074 :=
    ⟨⟨0, Fin.elim0, Fin.elim0, fun i ↦ Fin.elim0 i⟩⟩
  have hbounded : BddBelow (range fun C : _root_.GD.N0232.N0720.N1130.d017074 ↦
      _root_.GD.N0232.N0720.N1062.d018360 C s) := by
    refine ⟨_root_.GD.N0232.N0720.N1474.d024010 m n s, ?_⟩
    rintro _ ⟨C, rfl⟩
    exact _root_.GD.N0232.N0720.N1474.d024011 m n s hs C
  apply le_antisymm
  · by_contra hnot
    have hpos : 0 <
        (⨅ C : _root_.GD.N0232.N0720.N1130.d017074, _root_.GD.N0232.N0720.N1062.d018360 C s) -
          _root_.GD.N0232.N0720.N1474.d024010 m n s := sub_pos.mpr (lt_of_not_ge hnot)
    obtain ⟨C, hC⟩ := _root_.GD.N0232.N0720.N1474.d024012 m n s hs hpos
    have hle := ciInf_le hbounded C
    linarith
  · exact le_ciInf (fun C ↦ _root_.GD.N0232.N0720.N1474.d024011 m n s hs C)


theorem d024014
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hs : _root_.GD.N0232.N0720.N1159.d014637 m n s) :
    (⨅ C : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1062.d018367 C s / _root_.GD.N0232.N0720.N1062.d018364 C) =
        _root_.GD.N0232.N0720.N1474.d024010 m n s := by
  simp only [_root_.GD.N0232.N0720.N1062.d018368]
  exact _root_.GD.N0232.N0720.N1474.d024013 m n s hs


theorem d024015
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1474.d024010 m n s = 0 ↔ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s := by
  rw [← _root_.GD.N0232.N0720.N1159.d014635 m n s]
  constructor
  · intro hgap
    have htax := _root_.GD.N0232.N0720.N1159.d014648 m n s s
      (show s ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s from fun _ ↦ le_rfl)
    change ‖s - _root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2 ≤ _root_.GD.N0232.N0720.N1474.d024010 m n s at htax
    rw [hgap] at htax
    have hnorm : ‖s - _root_.GD.N0232.N0720.N1159.d014633 m n s‖ = 0 := by
      nlinarith [norm_nonneg (s - _root_.GD.N0232.N0720.N1159.d014633 m n s)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm
  · intro heq
    simp [_root_.GD.N0232.N0720.N1474.d024010, heq]



theorem d024016
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hs : _root_.GD.N0232.N0720.N1159.d014637 m n s) :
    (⨅ C : _root_.GD.N0232.N0720.N1130.d017074, _root_.GD.N0232.N0720.N1062.d018360 C s) = 0 ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s := by
  rw [_root_.GD.N0232.N0720.N1474.d024013 m n s hs]
  exact _root_.GD.N0232.N0720.N1474.d024015 m n s

end
end GD.N0232.N0720.N1474

#print axioms _root_.GD.N0232.N0720.N1474.d024013
#print axioms _root_.GD.N0232.N0720.N1474.d024014
#print axioms _root_.GD.N0232.N0720.N1474.d024016
