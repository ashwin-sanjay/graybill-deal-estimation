import GD.Module0519






set_option autoImplicit false
set_option warningAsError true

open Set

namespace GD.N0106.N0428.N0766.N1692
noncomputable section

open _root_.GD.N0106.N0428.N0766.N1692.N1762 _root_.GD.N0232.N0720.N1254

def d007794 : Type := {a : ℝ // 0 < a}



theorem d007795 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0, ∀ e ∈ Icc (0 : ℝ) 1,
      _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 a.val b.val N e ≤
        -3 * (_root_.GD.N0232.N0720.N1254.d002512 a.val b.val) ^ (-_root_.GD.N0232.N0720.N1254.d002513 a.val b.val) / 4 := by
  let target := (_root_.GD.N0232.N0720.N1254.d002512 a.val b.val) ^ (-_root_.GD.N0232.N0720.N1254.d002513 a.val b.val)
  have htarget : 0 < target :=
    Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1254.d002523 a.property b.property) _
  obtain ⟨N0, hN0, hclose⟩ :=
    _root_.GD.N0106.N0428.N0766.N1692.N1762.d007792 a.property b.property (target / 4) (by positivity)
  refine ⟨N0, hN0, ?_⟩
  intro N hN e he
  have herr := hclose N hN e he
  have hupp := le_abs_self (_root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 a.val b.val N e + target)
  change _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 a.val b.val N e ≤ -3 * target / 4
  linarith

def d007796 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) : ℕ := Classical.choose (_root_.GD.N0106.N0428.N0766.N1692.d007795 a b)

theorem d007797 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) :
    1 ≤ _root_.GD.N0106.N0428.N0766.N1692.d007796 a b ∧ ∀ N ≥ _root_.GD.N0106.N0428.N0766.N1692.d007796 a b, ∀ e ∈ Icc (0 : ℝ) 1,
      _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 a.val b.val N e ≤
        -3 * (_root_.GD.N0232.N0720.N1254.d002512 a.val b.val) ^ (-_root_.GD.N0232.N0720.N1254.d002513 a.val b.val) / 4 :=
  Classical.choose_spec (_root_.GD.N0106.N0428.N0766.N1692.d007795 a b)


def d007798 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) : ℕ :=
  max (_root_.GD.N0106.N0428.N0766.N1692.d007796 a b) (_root_.GD.N0106.N0428.N0766.N1692.d007796 b a)

theorem d007799 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) :
    _root_.GD.N0106.N0428.N0766.N1692.d007798 b a = _root_.GD.N0106.N0428.N0766.N1692.d007798 a b := by
  exact max_comm _ _

theorem d007800 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) :
    1 ≤ _root_.GD.N0106.N0428.N0766.N1692.d007798 a b ∧ ∀ e ∈ Icc (0 : ℝ) 1,
      _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) e ≤
        -3 * (_root_.GD.N0232.N0720.N1254.d002512 a.val b.val) ^ (-_root_.GD.N0232.N0720.N1254.d002513 a.val b.val) / 4 := by
  have hab : _root_.GD.N0106.N0428.N0766.N1692.d007796 a b ≤ _root_.GD.N0106.N0428.N0766.N1692.d007798 a b := le_max_left _ _
  exact ⟨(_root_.GD.N0106.N0428.N0766.N1692.d007797 a b).1.trans hab,
    (_root_.GD.N0106.N0428.N0766.N1692.d007797 a b).2 (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) hab⟩



theorem d007801 :
    ∃ N : _root_.GD.N0106.N0428.N0766.N1692.d007794 → _root_.GD.N0106.N0428.N0766.N1692.d007794 → ℕ,
      (∀ a b, N b a = N a b) ∧ ∀ a b,
        1 ≤ N a b ∧ ∀ e ∈ Icc (0 : ℝ) 1,
          _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 a.val b.val (N a b) e ≤
            -3 * (_root_.GD.N0232.N0720.N1254.d002512 a.val b.val) ^ (-_root_.GD.N0232.N0720.N1254.d002513 a.val b.val) / 4 :=
  ⟨_root_.GD.N0106.N0428.N0766.N1692.d007798, _root_.GD.N0106.N0428.N0766.N1692.d007799, _root_.GD.N0106.N0428.N0766.N1692.d007800⟩

end
end GD.N0106.N0428.N0766.N1692

#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007795
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007797
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007799
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007800
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007801
