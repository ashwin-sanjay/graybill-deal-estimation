import GD.Module1159
import GD.Module1160
import GD.Module1161






















open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1299

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1064
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1116
open _root_.GD.N0232.N0720.N1117
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1158
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1202
open _root_.GD.N0232.N0720.N1406
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1448
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}




def d018704
    (W : ℕ) (A : ℝ) (c : _root_.GD.N0232.N0720.N1130.d017074) : Prop :=
  c.width ≤ W ∧ ∀ i, |(c.packet i).location| ≤ A



theorem d018705
    (c : _root_.GD.N0232.N0720.N1130.d017074)
    (W : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hbox : _root_.GD.N0232.N0720.N1299.d018704 W A c) :
    _root_.GD.N0232.N0720.N1126.d016418 c.packet ≤ Real.sqrt ((W : ℝ) * A ^ 2) := by
  unfold _root_.GD.N0232.N0720.N1126.d016418
  apply Real.sqrt_le_sqrt
  calc
    ∑ i, (c.packet i).location ^ 2 ≤ ∑ _i : Fin c.width, A ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      have hsquare : |(c.packet i).location| ^ 2 ≤ A ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hA).2 (hbox.2 i)
      simpa only [sq_abs] using hsquare
    _ = (c.width : ℝ) * A ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    _ ≤ (W : ℝ) * A ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr hbox.1) (sq_nonneg A)





theorem d018706
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hbound : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet) atTop atTop)
    (W : ℕ) (A : ℝ) (hA : 0 ≤ A) (N : ℕ) :
    ∃ j : ℕ, N ≤ j ∧
      (W < (candidate j).width ∨
        ∃ i : Fin (candidate j).width,
          A < |((candidate j).packet i).location|) := by
  let B : ℝ := Real.sqrt ((W : ℝ) * A ^ 2)
  have hlarge : ∀ᶠ j in atTop,
      B + 1 ≤ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet :=
    (tendsto_atTop.1 hbound) (B + 1)
  have hlate : ∀ᶠ j : ℕ in atTop, N ≤ j := eventually_ge_atTop N
  obtain ⟨j, hjN, hjlarge⟩ := (hlate.and hlarge).exists
  refine ⟨j, hjN, ?_⟩
  by_contra hescape
  have hwidth : (candidate j).width ≤ W := by
    exact Nat.le_of_not_gt (fun hgt ↦ hescape (Or.inl hgt))
  have hlocation : ∀ i : Fin (candidate j).width,
      |((candidate j).packet i).location| ≤ A := by
    intro i
    exact le_of_not_gt (fun hgt ↦ hescape (Or.inr ⟨i, hgt⟩))
  have hupper : _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet ≤ B := by
    exact _root_.GD.N0232.N0720.N1299.d018705
      (candidate j) W A hA ⟨hwidth, hlocation⟩
  linarith



theorem d018707
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hbound : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet) atTop atTop) :
    ¬ ∃ (W : ℕ) (A : ℝ), 0 ≤ A ∧
      ∀ᶠ j in atTop, _root_.GD.N0232.N0720.N1299.d018704 W A (candidate j) := by
  rintro ⟨W, A, hA, hbox⟩
  have hupper : ∀ᶠ j in atTop,
      _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet ≤
        Real.sqrt ((W : ℝ) * A ^ 2) := by
    filter_upwards [hbox] with j hj
    exact _root_.GD.N0232.N0720.N1299.d018705
      (candidate j) W A hA hj
  have hlower : ∀ᶠ j in atTop,
      Real.sqrt ((W : ℝ) * A ^ 2) + 1 ≤
        _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet :=
    (tendsto_atTop.1 hbound)
      (Real.sqrt ((W : ℝ) * A ^ 2) + 1)
  obtain ⟨j, hjupper, hjlower⟩ := (hupper.and hlower).exists
  linarith



theorem d018708
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hmaster : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0)
    (row : _root_.GD.N0232.N0720.N1103.d018281 s)
    (W : ℕ) (A : ℝ) (hA : 0 ≤ A) (N : ℕ) :
    ∃ j : ℕ, N ≤ j ∧
      (W < (row.candidate j).width ∨
        ∃ i : Fin (row.candidate j).width,
          A < |((row.candidate j).packet i).location|) := by
  apply
    _root_.GD.N0232.N0720.N1299.d018706
      row.candidate
      (_root_.GD.N0232.N0720.N1202.d018581
        s hmaster row)
      W A hA N




theorem d018709
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hmaster : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0) :
    Tendsto (_root_.GD.N0232.N0720.N1406.d018587 s) atTop
        (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) ∧
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418
          ((_root_.GD.N0232.N0720.N1117.d018547 s).candidate j).packet)
        atTop atTop := by
  exact ⟨_root_.GD.N0232.N0720.N1406.d018588 s,
    _root_.GD.N0232.N0720.N1202.d018581
      s hmaster (_root_.GD.N0232.N0720.N1117.d018547 s)⟩





theorem d018710
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value)
    (row : _root_.GD.N0232.N0720.N1103.d018281 s) :
    Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j))
        atTop (nhds s.value) ∧
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (row.candidate j).packet)
        atTop atTop := by
  have hself : _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value :=
    _root_.GD.N0232.N0720.N1409.d018608 s hterminal
  have hmaster : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 :=
    _root_.GD.N0232.N0720.N1409.d018610 s hterminal
  constructor
  · simpa only [hself] using
      (_root_.GD.N0232.N0720.N1448.d018476 s row)
  · exact
      _root_.GD.N0232.N0720.N1202.d018581
        s hmaster row





theorem d018711
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          Tendsto (_root_.GD.N0232.N0720.N1406.d018587 s) atTop
            (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) ∧
          _root_.GD.N0232.N0720.N1146.d015228 m n
              (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
            _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∧
          _root_.GD.N0232.N0720.N1146.d015229 m n
              (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
            _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∧
          Tendsto
            (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418
              ((_root_.GD.N0232.N0720.N1117.d018547 s).candidate j).packet)
            atTop atTop := by
  rw [_root_.GD.N0232.N0720.N1482.d015173
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hmaster⟩
    have henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 :=
      (_root_.GD.N0232.N0720.N1477.d015755
        (m := m) (n := n) s).1 hmaster
    have hfixed :=
      (_root_.GD.N0232.N0720.N1158.d018490 s).1 henergy
    have hsplit :=
      _root_.GD.N0232.N0720.N1299.d018709
        s hmaster
    exact ⟨s, hstrict, hsplit.1, hfixed.1, hfixed.2, hsplit.2⟩
  · rintro ⟨s, hstrict, _hconv, htwo, hthree, _hescape⟩
    refine ⟨s, hstrict, ?_⟩
    apply
      (_root_.GD.N0232.N0720.N1477.d015755
        (m := m) (n := n) s).2
    exact
      (_root_.GD.N0232.N0720.N1158.d018490 s).2
        ⟨htwo, hthree⟩






theorem d018712
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value ∧
          Tendsto (_root_.GD.N0232.N0720.N1406.d018587 s) atTop (nhds s.value) ∧
          Tendsto
            (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418
              ((_root_.GD.N0232.N0720.N1117.d018547 s).candidate j).packet)
            atTop atTop := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hterminal⟩
    have hsplit :=
      _root_.GD.N0232.N0720.N1299.d018710
        s hterminal (_root_.GD.N0232.N0720.N1117.d018547 s)
    have hconv :
        Tendsto (_root_.GD.N0232.N0720.N1406.d018587 s) atTop (nhds s.value) := by
      change Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n
          ((_root_.GD.N0232.N0720.N1117.d018547 s).candidate j))
        atTop (nhds s.value)
      exact hsplit.1
    exact ⟨s, hstrict, hterminal, hconv, hsplit.2⟩
  · rintro ⟨s, hstrict, hterminal, _hconv, _hescape⟩
    exact ⟨s, hstrict, hterminal⟩

end

end N1299
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1299.d018705
#print axioms _root_.GD.N0232.N0720.N1299.d018706
#print axioms _root_.GD.N0232.N0720.N1299.d018707
#print axioms _root_.GD.N0232.N0720.N1299.d018708
#print axioms _root_.GD.N0232.N0720.N1299.d018709
#print axioms _root_.GD.N0232.N0720.N1299.d018710
#print axioms _root_.GD.N0232.N0720.N1299.d018711
#print axioms _root_.GD.N0232.N0720.N1299.d018712
