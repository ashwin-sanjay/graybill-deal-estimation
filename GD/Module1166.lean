import GD.Module1165





















open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1298

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1202
open _root_.GD.N0232.N0720.N1299
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}




def d018713
    (c : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  ((Finset.univ.sup fun i : Fin c.width ↦
    (⟨|(c.packet i).location|, abs_nonneg _⟩ : NNReal)) : NNReal)

theorem d018714
    (c : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1298.d018713 c := by
  unfold _root_.GD.N0232.N0720.N1298.d018713
  exact NNReal.coe_nonneg _


theorem d018715
    (c : _root_.GD.N0232.N0720.N1130.d017074) (i : Fin c.width) :
    |(c.packet i).location| ≤ _root_.GD.N0232.N0720.N1298.d018713 c := by
  have hnn :
      (⟨|(c.packet i).location|, abs_nonneg _⟩ : NNReal) ≤
        Finset.univ.sup (fun j : Fin c.width ↦
          (⟨|(c.packet j).location|, abs_nonneg _⟩ : NNReal)) :=
    Finset.le_sup
      (s := (Finset.univ : Finset (Fin c.width)))
      (f := fun j : Fin c.width ↦
        (⟨|(c.packet j).location|, abs_nonneg _⟩ : NNReal))
      (Finset.mem_univ i)
  unfold _root_.GD.N0232.N0720.N1298.d018713
  exact (NNReal.coe_le_coe.mpr hnn)


theorem d018716
    (c : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1126.d016418 c.packet ≤
      Real.sqrt ((c.width : ℝ) * _root_.GD.N0232.N0720.N1298.d018713 c ^ 2) := by
  exact _root_.GD.N0232.N0720.N1299.d018705
    c c.width (_root_.GD.N0232.N0720.N1298.d018713 c)
      (_root_.GD.N0232.N0720.N1298.d018714 c)
      ⟨le_rfl, _root_.GD.N0232.N0720.N1298.d018715 c⟩





theorem d018717
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hbound : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet) atTop atTop)
    (W : ℕ)
    (hwidth : ∀ᶠ j in atTop, (candidate j).width ≤ W) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1298.d018713 (candidate j))
      atTop atTop := by
  refine tendsto_atTop.2 (fun A ↦ ?_)
  let A₀ : ℝ := max A 0
  let B : ℝ := Real.sqrt ((W : ℝ) * A₀ ^ 2)
  have hlarge : ∀ᶠ j in atTop,
      B + 1 ≤ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet :=
    (tendsto_atTop.1 hbound) (B + 1)
  filter_upwards [hwidth, hlarge] with j hjwidth hjlarge
  have hA₀ : 0 ≤ A₀ := le_max_right A 0
  have hmax : A₀ < _root_.GD.N0232.N0720.N1298.d018713 (candidate j) := by
    by_contra hnot
    have hmaxle : _root_.GD.N0232.N0720.N1298.d018713 (candidate j) ≤ A₀ :=
      le_of_not_gt hnot
    have hbox : _root_.GD.N0232.N0720.N1299.d018704 W A₀ (candidate j) := by
      refine ⟨hjwidth, fun i ↦ ?_⟩
      exact (_root_.GD.N0232.N0720.N1298.d018715 (candidate j) i).trans hmaxle
    have hupper : _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet ≤ B := by
      exact _root_.GD.N0232.N0720.N1299.d018705
        (candidate j) W A₀ hA₀ hbox
    linarith
  exact (le_max_left A 0).trans hmax.le



theorem d018718
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hbound : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet) atTop atTop)
    (hwidth : ∃ W : ℕ, ∀ᶠ j in atTop, (candidate j).width ≤ W) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1298.d018713 (candidate j))
      atTop atTop := by
  obtain ⟨W, hW⟩ := hwidth
  exact
    _root_.GD.N0232.N0720.N1298.d018717
      candidate hbound W hW



theorem d018719
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hbound : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet) atTop atTop)
    (A : ℝ)
    (hlocation : ∀ᶠ j in atTop,
      _root_.GD.N0232.N0720.N1298.d018713 (candidate j) ≤ A) :
    Tendsto (fun j ↦ (candidate j).width) atTop atTop := by
  refine tendsto_atTop.2 (fun W ↦ ?_)
  let A₀ : ℝ := max A 0
  let B : ℝ := Real.sqrt ((W : ℝ) * A₀ ^ 2)
  have hlarge : ∀ᶠ j in atTop,
      B + 1 ≤ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet :=
    (tendsto_atTop.1 hbound) (B + 1)
  filter_upwards [hlocation, hlarge] with j hjlocation hjlarge
  have hA₀ : 0 ≤ A₀ := le_max_right A 0
  have hjlocation₀ : _root_.GD.N0232.N0720.N1298.d018713 (candidate j) ≤ A₀ :=
    hjlocation.trans (le_max_left A 0)
  by_contra hnot
  have hjwidth : (candidate j).width ≤ W := Nat.le_of_not_ge hnot
  have hbox : _root_.GD.N0232.N0720.N1299.d018704 W A₀ (candidate j) := by
    refine ⟨hjwidth, fun i ↦ ?_⟩
    exact (_root_.GD.N0232.N0720.N1298.d018715 (candidate j) i).trans
      hjlocation₀
  have hupper : _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet ≤ B := by
    exact _root_.GD.N0232.N0720.N1299.d018705
      (candidate j) W A₀ hA₀ hbox
  linarith



theorem d018720
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hbound : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet) atTop atTop)
    (hlocation : ∃ A : ℝ, ∀ᶠ j in atTop,
      _root_.GD.N0232.N0720.N1298.d018713 (candidate j) ≤ A) :
    Tendsto (fun j ↦ (candidate j).width) atTop atTop := by
  obtain ⟨A, hA⟩ := hlocation
  exact
    _root_.GD.N0232.N0720.N1298.d018719
      candidate hbound A hA





theorem d018721
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hbound : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet) atTop atTop) :
    (∃ extraction : ℕ → ℕ, StrictMono extraction ∧
      Tendsto (fun k ↦ (candidate (extraction k)).width) atTop atTop) ∨
    (∃ extraction : ℕ → ℕ, StrictMono extraction ∧
      Tendsto
        (fun k ↦ _root_.GD.N0232.N0720.N1298.d018713 (candidate (extraction k)))
        atTop atTop) := by
  classical
  by_cases hwidth : ∃ W : ℕ, ∀ᶠ j in atTop, (candidate j).width ≤ W
  · right
    refine ⟨id, strictMono_id, ?_⟩
    simpa using
      _root_.GD.N0232.N0720.N1298.d018718
        candidate hbound hwidth
  · left
    have hfrequent : ∀ W : ℕ, ∃ᶠ j in atTop, W < (candidate j).width := by
      intro W
      have hnot : ¬ ∀ᶠ j in atTop, (candidate j).width ≤ W := by
        intro hW
        exact hwidth ⟨W, hW⟩
      simpa only [not_le] using (not_eventually.mp hnot)
    obtain ⟨extraction, hextraction, hlarge⟩ :=
      extraction_forall_of_frequently hfrequent
    refine ⟨extraction, hextraction, ?_⟩
    refine tendsto_atTop.2 (fun W ↦ ?_)
    filter_upwards [eventually_ge_atTop W] with k hk
    exact hk.trans (hlarge k).le



theorem d018722
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hbound : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet) atTop atTop) :
    (∃ extraction : ℕ → ℕ, StrictMono extraction ∧
      Tendsto (fun k ↦ (candidate (extraction k)).width) atTop atTop) ∨
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1298.d018713 (candidate j))
      atTop atTop := by
  classical
  by_cases hwidth : ∃ W : ℕ, ∀ᶠ j in atTop, (candidate j).width ≤ W
  · exact Or.inr
      (_root_.GD.N0232.N0720.N1298.d018718
        candidate hbound hwidth)
  · left
    have hfrequent : ∀ W : ℕ, ∃ᶠ j in atTop, W < (candidate j).width := by
      intro W
      have hnot : ¬ ∀ᶠ j in atTop, (candidate j).width ≤ W := by
        intro hW
        exact hwidth ⟨W, hW⟩
      simpa only [not_le] using (not_eventually.mp hnot)
    obtain ⟨extraction, hextraction, hlarge⟩ :=
      extraction_forall_of_frequently hfrequent
    refine ⟨extraction, hextraction, ?_⟩
    refine tendsto_atTop.2 (fun W ↦ ?_)
    filter_upwards [eventually_ge_atTop W] with k hk
    exact hk.trans (hlarge k).le



theorem d018723
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hbound : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet) atTop atTop) :
    Tendsto (fun j ↦ (candidate j).width) atTop atTop ∨
      (∃ extraction : ℕ → ℕ, StrictMono extraction ∧
        Tendsto
          (fun k ↦ _root_.GD.N0232.N0720.N1298.d018713 (candidate (extraction k)))
          atTop atTop) := by
  classical
  by_cases hlocation : ∃ A : ℝ, ∀ᶠ j in atTop,
      _root_.GD.N0232.N0720.N1298.d018713 (candidate j) ≤ A
  · exact Or.inl
      (_root_.GD.N0232.N0720.N1298.d018720
        candidate hbound hlocation)
  · right
    have hfrequent : ∀ L : ℕ, ∃ᶠ j in atTop,
        (L : ℝ) < _root_.GD.N0232.N0720.N1298.d018713 (candidate j) := by
      intro L
      have hnot : ¬ ∀ᶠ j in atTop,
          _root_.GD.N0232.N0720.N1298.d018713 (candidate j) ≤ (L : ℝ) := by
        intro hL
        exact hlocation ⟨(L : ℝ), hL⟩
      simpa only [not_le] using (not_eventually.mp hnot)
    obtain ⟨extraction, hextraction, hlarge⟩ :=
      extraction_forall_of_frequently hfrequent
    refine ⟨extraction, hextraction, ?_⟩
    refine tendsto_atTop.2 (fun A ↦ ?_)
    obtain ⟨L : ℕ, hAL⟩ := exists_nat_ge A
    filter_upwards [eventually_ge_atTop L] with k hk
    exact hAL.trans (Nat.cast_le.mpr hk) |>.trans (hlarge k).le




theorem d018724
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hbound : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet) atTop atTop)
    (hwidth : ¬ Tendsto (fun j ↦ (candidate j).width) atTop atTop)
    (hlocation : ¬ Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1298.d018713 (candidate j)) atTop atTop) :
    (∃ extraction : ℕ → ℕ, StrictMono extraction ∧
      Tendsto (fun k ↦ (candidate (extraction k)).width) atTop atTop) ∧
    (∃ extraction : ℕ → ℕ, StrictMono extraction ∧
      Tendsto
        (fun k ↦ _root_.GD.N0232.N0720.N1298.d018713 (candidate (extraction k)))
        atTop atTop) := by
  exact ⟨
    (_root_.GD.N0232.N0720.N1298.d018722 candidate hbound).resolve_right
      hlocation,
    (_root_.GD.N0232.N0720.N1298.d018723 candidate hbound).resolve_left
      hwidth⟩





theorem d018725
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hmaster : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0)
    (row : _root_.GD.N0232.N0720.N1103.d018281 s) :
    (∃ extraction : ℕ → ℕ, StrictMono extraction ∧
      Tendsto (fun k ↦ (row.candidate (extraction k)).width) atTop atTop) ∨
    (∃ extraction : ℕ → ℕ, StrictMono extraction ∧
      Tendsto
        (fun k ↦ _root_.GD.N0232.N0720.N1298.d018713
          (row.candidate (extraction k))) atTop atTop) := by
  exact
    _root_.GD.N0232.N0720.N1298.d018721
      row.candidate
      (_root_.GD.N0232.N0720.N1202.d018581
        s hmaster row)



theorem d018726
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hmaster : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0)
    (row : _root_.GD.N0232.N0720.N1103.d018281 s)
    (W : ℕ)
    (hwidth : ∀ᶠ j in atTop, (row.candidate j).width ≤ W) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1298.d018713 (row.candidate j))
      atTop atTop := by
  exact
    _root_.GD.N0232.N0720.N1298.d018717
      row.candidate
      (_root_.GD.N0232.N0720.N1202.d018581
        s hmaster row)
      W hwidth



theorem d018727
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hmaster : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0)
    (row : _root_.GD.N0232.N0720.N1103.d018281 s)
    (A : ℝ)
    (hlocation : ∀ᶠ j in atTop,
      _root_.GD.N0232.N0720.N1298.d018713 (row.candidate j) ≤ A) :
    Tendsto (fun j ↦ (row.candidate j).width) atTop atTop := by
  exact
    _root_.GD.N0232.N0720.N1298.d018719
      row.candidate
      (_root_.GD.N0232.N0720.N1202.d018581
        s hmaster row)
      A hlocation




def d018728 (k : ℕ) : ℕ :=
  if Even k then (k + 1) ^ 2 else 1


def d018729 (k : ℕ) : ℕ :=
  if Even k then 1 else (k + 1) ^ 2

theorem d018730 (k : ℕ) :
    _root_.GD.N0232.N0720.N1298.d018728 k * _root_.GD.N0232.N0720.N1298.d018729 k = (k + 1) ^ 2 := by
  by_cases hk : Even k <;> simp [_root_.GD.N0232.N0720.N1298.d018728,
    _root_.GD.N0232.N0720.N1298.d018729, hk]

theorem d018731 :
    Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1298.d018728 k * _root_.GD.N0232.N0720.N1298.d018729 k)
      atTop atTop := by
  refine tendsto_atTop.2 (fun N ↦ ?_)
  filter_upwards [eventually_ge_atTop N] with k hk
  rw [_root_.GD.N0232.N0720.N1298.d018730]
  calc
    N ≤ k := hk
    _ ≤ (k + 1) ^ 2 := by nlinarith

theorem d018732 (k : ℕ) :
    _root_.GD.N0232.N0720.N1298.d018728 (2 * k) = (2 * k + 1) ^ 2 := by
  simp [_root_.GD.N0232.N0720.N1298.d018728]

theorem d018733 (k : ℕ) :
    _root_.GD.N0232.N0720.N1298.d018728 (2 * k + 1) = 1 := by
  simp [_root_.GD.N0232.N0720.N1298.d018728]

theorem d018734 (k : ℕ) :
    _root_.GD.N0232.N0720.N1298.d018729 (2 * k) = 1 := by
  simp [_root_.GD.N0232.N0720.N1298.d018729]

theorem d018735 (k : ℕ) :
    _root_.GD.N0232.N0720.N1298.d018729 (2 * k + 1) = (2 * k + 2) ^ 2 := by
  simp [_root_.GD.N0232.N0720.N1298.d018729]


theorem d018736 :
    ¬ Tendsto _root_.GD.N0232.N0720.N1298.d018728 atTop atTop := by
  intro h
  have hmono : StrictMono (fun k : ℕ ↦ 2 * k + 1) := by
    apply strictMono_nat_of_lt_succ
    intro k
    omega
  have hodd := h.comp hmono.tendsto_atTop
  have hone : Tendsto (fun _k : ℕ ↦ 1) atTop atTop := by
    have hfun :
        (_root_.GD.N0232.N0720.N1298.d018728 ∘ fun k : ℕ ↦ 2 * k + 1) =
          (fun _k : ℕ ↦ 1) := by
      funext k
      exact _root_.GD.N0232.N0720.N1298.d018733 k
    rw [hfun] at hodd
    exact hodd
  have hlarge := (tendsto_atTop.1 hone) 2
  obtain ⟨k, hk⟩ := hlarge.exists
  omega


theorem d018737 :
    ¬ Tendsto _root_.GD.N0232.N0720.N1298.d018729 atTop atTop := by
  intro h
  have hmono : StrictMono (fun k : ℕ ↦ 2 * k) := by
    apply strictMono_nat_of_lt_succ
    intro k
    omega
  have heven := h.comp hmono.tendsto_atTop
  have hone : Tendsto (fun _k : ℕ ↦ 1) atTop atTop := by
    have hfun :
        (_root_.GD.N0232.N0720.N1298.d018729 ∘ fun k : ℕ ↦ 2 * k) =
          (fun _k : ℕ ↦ 1) := by
      funext k
      exact _root_.GD.N0232.N0720.N1298.d018734 k
    rw [hfun] at heven
    exact heven
  have hlarge := (tendsto_atTop.1 hone) 2
  obtain ⟨k, hk⟩ := hlarge.exists
  omega





theorem d018738 :
    Tendsto
        (fun k ↦ _root_.GD.N0232.N0720.N1298.d018728 k * _root_.GD.N0232.N0720.N1298.d018729 k)
        atTop atTop ∧
      ¬ Tendsto _root_.GD.N0232.N0720.N1298.d018728 atTop atTop ∧
      ¬ Tendsto _root_.GD.N0232.N0720.N1298.d018729 atTop atTop :=
  ⟨_root_.GD.N0232.N0720.N1298.d018731,
    _root_.GD.N0232.N0720.N1298.d018736,
    _root_.GD.N0232.N0720.N1298.d018737⟩

end

end N1298
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1298.d018716
#print axioms _root_.GD.N0232.N0720.N1298.d018717
#print axioms _root_.GD.N0232.N0720.N1298.d018719
#print axioms _root_.GD.N0232.N0720.N1298.d018721
#print axioms _root_.GD.N0232.N0720.N1298.d018724
#print axioms _root_.GD.N0232.N0720.N1298.d018725
#print axioms _root_.GD.N0232.N0720.N1298.d018726
#print axioms _root_.GD.N0232.N0720.N1298.d018727
#print axioms _root_.GD.N0232.N0720.N1298.d018738
