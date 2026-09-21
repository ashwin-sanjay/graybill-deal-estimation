import GD.Module0042
import GD.Module0963




















open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1477

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0230.N0558
open _root_.GD.N0230.N0602
open RealInnerProductSpace
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)

abbrev d015740 :=
  _root_.GD.N0232.N0719.N0946.d009229









noncomputable def d015741
    (g : _root_.GD.N0232.N0720.N1477.d015740) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1159.d014642 m n g p hp - p




noncomputable def d015742
    (g : _root_.GD.N0232.N0720.N1477.d015740) (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1159.d014642 m n g p hp -
    _root_.GD.N0232.N0720.N1159.d014642 m n g q hq






theorem d015743
    (g h : _root_.GD.N0232.N0720.N1477.d015740) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1477.d015741 m n (g * h) p hp =
      _root_.GD.N0232.N0720.N1477.d015742 m n g
        (_root_.GD.N0232.N0720.N1159.d014642 m n h p hp) p
        (_root_.GD.N0232.N0720.N1482.d015158
          (m := m) (n := n) h p hp) hp +
      _root_.GD.N0232.N0720.N1477.d015741 m n g p hp := by
  unfold _root_.GD.N0232.N0720.N1477.d015741 _root_.GD.N0232.N0720.N1477.d015742
  rw [_root_.GD.N0232.N0720.N1482.d015161]
  abel


noncomputable def d015744
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1477.d015740) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1 -
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value


noncomputable def d015745
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1477.d015740) : ℝ :=
  ⟪_root_.GD.N0232.N0720.N1159.d014633 m n s.value,
    _root_.GD.N0232.N0720.N1477.d015744 m n s g⟫



theorem d015746
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1477.d015740) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g =
      ‖_root_.GD.N0232.N0720.N1477.d015744 m n s g‖ ^ 2 +
        2 * _root_.GD.N0232.N0720.N1477.d015745 m n s g := by
  unfold _root_.GD.N0232.N0720.N1159.d014647 _root_.GD.N0232.N0720.N1477.d015744
    _root_.GD.N0232.N0720.N1477.d015745
  exact _root_.GD.N0230.N0558.d000529 _ _



theorem d015747
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1477.d015740) :
    0 ≤ _root_.GD.N0232.N0720.N1477.d015745 m n s g := by
  unfold _root_.GD.N0232.N0720.N1477.d015745 _root_.GD.N0232.N0720.N1477.d015744
  apply _root_.GD.N0230.N0558.d000531
  exact
    _root_.GD.N0232.N0720.N1159.d014648 m n s.value
      (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1
      (_root_.GD.N0232.N0720.N1159.d014645 m n s g (_root_.GD.N0232.N0720.N1159.d014646 m n s)).2



theorem d015748
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1477.d015740) :
    ‖_root_.GD.N0232.N0720.N1477.d015744 m n s g‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1159.d014647 m n s g := by
  rw [_root_.GD.N0232.N0720.N1477.d015746]
  nlinarith [_root_.GD.N0232.N0720.N1477.d015747 m n s g]


noncomputable def d015749
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : ℝ :=
  ‖_root_.GD.N0232.N0720.N1477.d015744 m n s _root_.GD.N0232.N0720.N1482.d015130‖ ^ 2 +
    ‖_root_.GD.N0232.N0720.N1477.d015744 m n s _root_.GD.N0232.N0720.N1482.d015131‖ ^ 2


noncomputable def d015750
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : ℝ :=
  2 * (_root_.GD.N0232.N0720.N1477.d015745 m n s _root_.GD.N0232.N0720.N1482.d015130 +
    _root_.GD.N0232.N0720.N1477.d015745 m n s _root_.GD.N0232.N0720.N1482.d015131)



theorem d015751
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s =
      _root_.GD.N0232.N0720.N1477.d015749 m n s +
        _root_.GD.N0232.N0720.N1477.d015750 m n s := by
  rw [_root_.GD.N0232.N0720.N1482.d015169,
    _root_.GD.N0232.N0720.N1477.d015746,
    _root_.GD.N0232.N0720.N1477.d015746]
  unfold _root_.GD.N0232.N0720.N1477.d015749 _root_.GD.N0232.N0720.N1477.d015750
  ring


theorem d015752
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1477.d015750 m n s := by
  unfold _root_.GD.N0232.N0720.N1477.d015750
  nlinarith [_root_.GD.N0232.N0720.N1477.d015747 m n s _root_.GD.N0232.N0720.N1482.d015130,
    _root_.GD.N0232.N0720.N1477.d015747 m n s _root_.GD.N0232.N0720.N1482.d015131]



theorem d015753
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s ≤
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s := by
  rw [_root_.GD.N0232.N0720.N1477.d015751]
  exact le_add_of_nonneg_right (_root_.GD.N0232.N0720.N1477.d015752 m n s)



theorem d015754
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 ↔
      _root_.GD.N0232.N0720.N1159.d014645 m n s _root_.GD.N0232.N0720.N1482.d015130
          (_root_.GD.N0232.N0720.N1159.d014646 m n s) =
            _root_.GD.N0232.N0720.N1159.d014646 m n s ∧
      _root_.GD.N0232.N0720.N1159.d014645 m n s _root_.GD.N0232.N0720.N1482.d015131
          (_root_.GD.N0232.N0720.N1159.d014646 m n s) =
            _root_.GD.N0232.N0720.N1159.d014646 m n s := by
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  let q₂ := (_root_.GD.N0232.N0720.N1159.d014645 m n s _root_.GD.N0232.N0720.N1482.d015130
    (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1
  let q₃ := (_root_.GD.N0232.N0720.N1159.d014645 m n s _root_.GD.N0232.N0720.N1482.d015131
    (_root_.GD.N0232.N0720.N1159.d014646 m n s)).1
  change ‖q₂ - p‖ ^ 2 + ‖q₃ - p‖ ^ 2 = 0 ↔ _
  constructor
  · intro hzero
    have h₂ : ‖q₂ - p‖ = 0 := by
      nlinarith [sq_nonneg ‖q₂ - p‖, sq_nonneg ‖q₃ - p‖,
        norm_nonneg (q₂ - p), norm_nonneg (q₃ - p)]
    have h₃ : ‖q₃ - p‖ = 0 := by
      nlinarith [sq_nonneg ‖q₂ - p‖, sq_nonneg ‖q₃ - p‖,
        norm_nonneg (q₂ - p), norm_nonneg (q₃ - p)]
    constructor <;> apply Subtype.ext
    · exact sub_eq_zero.mp (norm_eq_zero.mp h₂)
    · exact sub_eq_zero.mp (norm_eq_zero.mp h₃)
  · rintro ⟨h₂, h₃⟩
    have h₂v := congrArg Subtype.val h₂
    have h₃v := congrArg Subtype.val h₃
    change q₂ = p at h₂v
    change q₃ = p at h₃v
    rw [h₂v, h₃v, sub_self, norm_zero]
    norm_num




theorem d015755
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 ↔
      _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  rw [_root_.GD.N0232.N0720.N1477.d015754]
  constructor
  · intro hmaster
    have hall :=
      (_root_.GD.N0232.N0720.N1482.d015171
        (m := m) (n := n) s).1 hmaster
    exact ⟨(_root_.GD.N0232.N0720.N1159.d014651 m n s _root_.GD.N0232.N0720.N1482.d015130).1
        (hall _root_.GD.N0232.N0720.N1482.d015130),
      (_root_.GD.N0232.N0720.N1159.d014651 m n s
        _root_.GD.N0232.N0720.N1482.d015131).1 (hall _root_.GD.N0232.N0720.N1482.d015131)⟩
  · rintro ⟨h₂, h₃⟩
    change _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 +
      _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015131 = 0
    rw [(_root_.GD.N0232.N0720.N1159.d014651 m n s _root_.GD.N0232.N0720.N1482.d015130).2 h₂,
      (_root_.GD.N0232.N0720.N1159.d014651 m n s
        _root_.GD.N0232.N0720.N1482.d015131).2 h₃, add_zero]

end
end N1477
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1477.d015746
#print axioms _root_.GD.N0232.N0720.N1477.d015743
#print axioms _root_.GD.N0232.N0720.N1477.d015747
#print axioms _root_.GD.N0232.N0720.N1477.d015751
#print axioms _root_.GD.N0232.N0720.N1477.d015753
#print axioms _root_.GD.N0232.N0720.N1477.d015754
#print axioms _root_.GD.N0232.N0720.N1477.d015755
