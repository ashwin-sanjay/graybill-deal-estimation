import GD.Module0986
import GD.Module1171
import GD.Module0963
import Mathlib.Tactic































open Filter Topology MeasureTheory
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1453

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1288
open _root_.GD.N0232.N0720.N1369
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

abbrev d018879 :=
  _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)



theorem d018880 :
    Continuous (fun g : _root_.GD.N0232.N0720.N1453.d018879 ↦ g.d009239) :=
  Real.continuous_exp.comp _root_.GD.N0232.N0720.N1482.d015126

theorem d018881 :
    Continuous (fun g : _root_.GD.N0232.N0720.N1453.d018879 ↦ g⁻¹) := by
  rw [← _root_.GD.N0232.N0720.N1482.d015124.comp_continuous_iff]
  have hcoord : _root_.GD.N0232.N0720.N1482.d015121 ∘ (fun g : _root_.GD.N0232.N0720.N1453.d018879 ↦ g⁻¹) =
      fun g ↦ (-g.logScale, -(Real.exp (-g.logScale) * g.shift)) := by
    funext g
    rfl
  rw [hcoord]
  exact _root_.GD.N0232.N0720.N1482.d015126.neg.prodMk
    ((Real.continuous_exp.comp _root_.GD.N0232.N0720.N1482.d015126.neg).mul _root_.GD.N0232.N0720.N1482.d015127).neg


theorem d018882 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Continuous (fun g : _root_.GD.N0232.N0720.N1453.d018879 ↦ _root_.GD.N0232.N0720.N1215.d014272 g theta) := by
  rw [← _root_.GD.N0232.N0720.N1499.d014996.comp_continuous_iff]
  have hcoord : _root_.GD.N0232.N0720.N1499.d014993 ∘
      (fun g : _root_.GD.N0232.N0720.N1453.d018879 ↦ _root_.GD.N0232.N0720.N1215.d014272 g theta) =
      fun g ↦ (g.shift + g.d009239 * theta.location,
        (g.d009239 * theta.scale₁, g.d009239 * theta.scale₂)) := by
    funext g
    rfl
  rw [hcoord]
  exact (_root_.GD.N0232.N0720.N1482.d015127.add (_root_.GD.N0232.N0720.N1453.d018880.mul continuous_const)).prodMk
    ((_root_.GD.N0232.N0720.N1453.d018880.mul continuous_const).prodMk
      (_root_.GD.N0232.N0720.N1453.d018880.mul continuous_const))



theorem d018883 :
    Continuous (fun g : _root_.GD.N0232.N0720.N1453.d018879 ↦
      _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) :=
  (_root_.GD.N0232.N0720.N1453.d018882 _root_.GD.N0232.N0720.N1080.d014169).comp _root_.GD.N0232.N0720.N1453.d018881





theorem d018884 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Continuous (fun g : _root_.GD.N0232.N0720.N1453.d018879 ↦ _root_.GD.N0232.N0720.N1159.d014647 m n s g) := by
  have hfun : (fun g : _root_.GD.N0232.N0720.N1453.d018879 ↦ _root_.GD.N0232.N0720.N1159.d014647 m n s g) =
      fun g ↦ g.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)).toReal -
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 :=
    funext (_root_.GD.N0232.N0720.N1288.d015630 m n s)
  rw [hfun]
  exact ((_root_.GD.N0232.N0720.N1453.d018880.pow 2).mul
    ((_root_.GD.N0232.N0720.N1369.d018805 _
      (_root_.GD.N0232.N0720.N1369.d018804 s)).comp
        _root_.GD.N0232.N0720.N1453.d018883)).sub continuous_const





def d018885 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Subgroup _root_.GD.N0232.N0720.N1453.d018879 where
  carrier := {g | _root_.GD.N0232.N0720.N1159.d014642 m n g
    (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
    (_root_.GD.N0232.N0720.N1369.d018804 s) =
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value}
  one_mem' := _root_.GD.N0232.N0720.N1482.d015159 (m := m) (n := n) _ _
  mul_mem' := by
    intro g h hg hh
    have hg' : _root_.GD.N0232.N0720.N1159.d014642 m n g
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1369.d018804 s) =
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value := hg
    have hh' : _root_.GD.N0232.N0720.N1159.d014642 m n h
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1369.d018804 s) =
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value := hh
    show _root_.GD.N0232.N0720.N1159.d014642 m n (g * h)
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1369.d018804 s) =
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value
    have h1 := _root_.GD.N0232.N0720.N1482.d015161 (m := m) (n := n) g h
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
      (_root_.GD.N0232.N0720.N1369.d018804 s)
    simp only [hh'] at h1
    exact h1.symm.trans hg'
  inv_mem' := by
    intro g hg
    have hg' : _root_.GD.N0232.N0720.N1159.d014642 m n g
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1369.d018804 s) =
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value := hg
    show _root_.GD.N0232.N0720.N1159.d014642 m n g⁻¹
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1369.d018804 s) =
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value
    have h1 := _root_.GD.N0232.N0720.N1482.d015161 (m := m) (n := n) g⁻¹ g
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
      (_root_.GD.N0232.N0720.N1369.d018804 s)
    rw [inv_mul_cancel, _root_.GD.N0232.N0720.N1482.d015159] at h1
    simp only [hg'] at h1
    exact h1

theorem d018886 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1453.d018879) :
    g ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s ↔
      _root_.GD.N0232.N0720.N1159.d014642 m n g (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
        (_root_.GD.N0232.N0720.N1369.d018804 s) =
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value :=
  Iff.rfl


theorem d018887
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (g : _root_.GD.N0232.N0720.N1453.d018879) :
    g ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s ↔ _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
  rw [_root_.GD.N0232.N0720.N1159.d014651, Subtype.ext_iff,
    _root_.GD.N0232.N0720.N1453.d018886]
  exact Iff.rfl

theorem d018888 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (_root_.GD.N0232.N0720.N1453.d018885 m n s : Set _root_.GD.N0232.N0720.N1453.d018879) =
      {g | _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0} := by
  ext g
  exact _root_.GD.N0232.N0720.N1453.d018887 m n s g



theorem d018889 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    IsClosed (_root_.GD.N0232.N0720.N1453.d018885 m n s : Set _root_.GD.N0232.N0720.N1453.d018879) := by
  rw [_root_.GD.N0232.N0720.N1453.d018888]
  exact isClosed_eq (_root_.GD.N0232.N0720.N1453.d018884 m n s) continuous_const


theorem d018890 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    IsOpen {g : _root_.GD.N0232.N0720.N1453.d018879 | 0 < _root_.GD.N0232.N0720.N1159.d014647 m n s g} :=
  isOpen_lt continuous_const (_root_.GD.N0232.N0720.N1453.d018884 m n s)


theorem d018891 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (_root_.GD.N0232.N0720.N1453.d018885 m n s : Set _root_.GD.N0232.N0720.N1453.d018879)ᶜ =
      {g : _root_.GD.N0232.N0720.N1453.d018879 | 0 < _root_.GD.N0232.N0720.N1159.d014647 m n s g} := by
  ext g
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, SetLike.mem_coe,
    _root_.GD.N0232.N0720.N1453.d018887]
  constructor
  · intro h
    exact lt_of_le_of_ne (_root_.GD.N0232.N0720.N1159.d014650 m n s g) (Ne.symm h)
  · intro h
    exact h.ne'


theorem d018892 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s 1 = 0 :=
  (_root_.GD.N0232.N0720.N1453.d018887 m n s 1).1
    (_root_.GD.N0232.N0720.N1453.d018885 m n s).one_mem


theorem d018893 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Tendsto (fun g : _root_.GD.N0232.N0720.N1453.d018879 ↦ _root_.GD.N0232.N0720.N1159.d014647 m n s g)
      (𝓝 1) (𝓝 0) := by
  have h := (_root_.GD.N0232.N0720.N1453.d018884 m n s).tendsto 1
  rwa [_root_.GD.N0232.N0720.N1453.d018892] at h





theorem d018894 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (Γ : Subgroup _root_.GD.N0232.N0720.N1453.d018879) (hΓ : Dense (Γ : Set _root_.GD.N0232.N0720.N1453.d018879))
    (hle : Γ ≤ _root_.GD.N0232.N0720.N1453.d018885 m n s) :
    _root_.GD.N0232.N0720.N1453.d018885 m n s = ⊤ := by
  have hsub : closure (Γ : Set _root_.GD.N0232.N0720.N1453.d018879) ⊆
      (_root_.GD.N0232.N0720.N1453.d018885 m n s : Set _root_.GD.N0232.N0720.N1453.d018879) :=
    closure_minimal (SetLike.coe_subset_coe.2 hle)
      (_root_.GD.N0232.N0720.N1453.d018889 m n s)
  rw [hΓ.closure_eq] at hsub
  exact (Subgroup.eq_top_iff' _).2 (fun g ↦ hsub (Set.mem_univ g))



theorem d018895 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (h2 : _root_.GD.N0232.N0720.N1482.d015130 ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s)
    (h3 : _root_.GD.N0232.N0720.N1482.d015131 ∈ _root_.GD.N0232.N0720.N1453.d018885 m n s) :
    _root_.GD.N0232.N0720.N1453.d018885 m n s = ⊤ := by
  apply _root_.GD.N0232.N0720.N1453.d018894 m n s _root_.GD.N0232.N0720.N1482.d015132
    _root_.GD.N0232.N0720.N1482.d015157
  unfold _root_.GD.N0232.N0720.N1482.d015132
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · exact h2
  · exact h3



theorem d018896
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 ↔
      _root_.GD.N0232.N0720.N1453.d018885 m n s = ⊤ := by
  rw [_root_.GD.N0232.N0720.N1482.d015171,
    Subgroup.eq_top_iff']
  exact forall_congr' (fun g ↦
    (_root_.GD.N0232.N0720.N1453.d018887 m n s g).symm)

theorem d018897 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1453.d018885 m n s = ⊤ ↔
      Dense (_root_.GD.N0232.N0720.N1453.d018885 m n s : Set _root_.GD.N0232.N0720.N1453.d018879) := by
  constructor
  · intro h
    rw [h, Subgroup.coe_top]
    exact dense_univ
  · intro hd
    exact _root_.GD.N0232.N0720.N1453.d018894 m n s _ hd le_rfl


theorem d018898
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 ↔
      Dense (_root_.GD.N0232.N0720.N1453.d018885 m n s : Set _root_.GD.N0232.N0720.N1453.d018879) :=
  (_root_.GD.N0232.N0720.N1453.d018896 m n s).trans
    (_root_.GD.N0232.N0720.N1453.d018897 m n s)



theorem d018899 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    0 < _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s ↔
      ¬ Dense (_root_.GD.N0232.N0720.N1453.d018885 m n s : Set _root_.GD.N0232.N0720.N1453.d018879) := by
  rw [← _root_.GD.N0232.N0720.N1453.d018898]
  constructor
  · intro h
    exact h.ne'
  · intro h
    exact lt_of_le_of_ne (_root_.GD.N0232.N0720.N1482.d015170 (m := m) (n := n) s)
      (Ne.symm h)


theorem d018900 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (Γ : Subgroup _root_.GD.N0232.N0720.N1453.d018879) (hΓ : Dense (Γ : Set _root_.GD.N0232.N0720.N1453.d018879))
    (hle : Γ ≤ _root_.GD.N0232.N0720.N1453.d018885 m n s) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 :=
  (_root_.GD.N0232.N0720.N1453.d018896 m n s).2
    (_root_.GD.N0232.N0720.N1453.d018894 m n s Γ hΓ hle)

end

end N1453
end N0720
end N0232
end GD
