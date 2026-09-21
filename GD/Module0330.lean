import GD.Module0272
import GD.Module0329
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix
























open scoped BigOperators

namespace GD
namespace N0233
namespace N0729

noncomputable section

open Set Matrix
open _root_.GD.N0233.N0733
open _root_.GD.N0234.N0741

variable {Θ m n : Type*}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]


def d004921 (B : Matrix m n ℝ) : Matrix n n ℝ :=
  B.transpose * B





abbrev d004922 :=
  ↥(Finset.univ.powersetCard (Fintype.card n) : Finset (Finset m))







def d004923 (B : Matrix m n ℝ) (g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n)) :
    Matrix n n ℝ :=
  _root_.GD.N0233.N0733.d004025 B.transpose
    (_root_.GD.N0233.N0733.d004028 (n := n) g.1 g.2)


def d004924
    (B : Matrix m n ℝ) (g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n)) : ℝ :=
  det (_root_.GD.N0233.N0729.d004923 B g) ^ 2


def d004925 (B : Matrix m n ℝ) : ℝ :=
  ∑ g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n), _root_.GD.N0233.N0729.d004924 B g

omit [DecidableEq m] in

theorem d004926
    (B : Matrix m n ℝ) (g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n)) :
    0 ≤ _root_.GD.N0233.N0729.d004924 B g :=
  sq_nonneg _

omit [DecidableEq m] in

theorem d004927 (B : Matrix m n ℝ) :
    0 ≤ _root_.GD.N0233.N0729.d004925 B :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

omit [Fintype n] [DecidableEq n] in




theorem d004928 (B : Matrix m n ℝ) :
    _root_.GD.N0233.N0733.d004019 B.transpose (fun _ ↦ (1 : ℝ)) = _root_.GD.N0233.N0729.d004921 B := by
  simp [_root_.GD.N0233.N0733.d004019, _root_.GD.N0233.N0729.d004921]





theorem d004929
    (B : Matrix m n ℝ)
    (s : Finset m)
    (hs : s ∈ Finset.univ.powersetCard (Fintype.card n)) :
    _root_.GD.N0233.N0733.d004029 B.transpose (fun _ ↦ (1 : ℝ)) s =
      _root_.GD.N0233.N0729.d004924 B ⟨s, hs⟩ := by
  simp [_root_.GD.N0233.N0733.d004029, hs, _root_.GD.N0233.N0729.d004924, _root_.GD.N0233.N0729.d004923]






theorem d004930 (B : Matrix m n ℝ) :
    det (_root_.GD.N0233.N0729.d004921 B) = _root_.GD.N0233.N0729.d004925 B := by
  rw [← _root_.GD.N0233.N0729.d004928 B,
    _root_.GD.N0233.N0733.d004030]
  unfold _root_.GD.N0233.N0729.d004925
  rw [Finset.sum_subtype
    (p := fun s : Finset m ↦
      s ∈ Finset.univ.powersetCard (Fintype.card n))
    (Finset.univ.powersetCard (Fintype.card n))
    (fun _ ↦ Iff.rfl)
    (_root_.GD.N0233.N0733.d004029 B.transpose (fun _ ↦ (1 : ℝ)))]
  apply Finset.sum_congr rfl
  intro g hg
  exact
    _root_.GD.N0233.N0729.d004929
      B g.1 g.2

omit [DecidableEq m] in




theorem d004931
    (B : Matrix m n ℝ) :
    det (_root_.GD.N0233.N0729.d004921 B) ≠ 0 ↔ Function.Injective B.mulVec := by
  rw [_root_.GD.N0234.N0741.d004817]
  change
    Function.Injective (_root_.GD.N0233.N0729.d004921 B).mulVecLin ↔
      Function.Injective B.mulVecLin
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot,
    _root_.GD.N0233.N0729.d004921, Matrix.ker_mulVecLin_transpose_mul_self]

omit [DecidableEq m] in




theorem d004932
    (B : Matrix m n ℝ) :
    _root_.GD.N0233.N0729.d004925 B ≠ 0 ↔
      ∃ g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n),
        det (_root_.GD.N0233.N0729.d004923 B g) ≠ 0 := by
  constructor
  · intro hnonzero
    by_contra h
    push Not at h
    apply hnonzero
    unfold _root_.GD.N0233.N0729.d004925
    apply Finset.sum_eq_zero
    intro g hg
    simp [_root_.GD.N0233.N0729.d004924, h g]
  · rintro ⟨g, hg⟩
    have hpositive : 0 < _root_.GD.N0233.N0729.d004925 B := by
      unfold _root_.GD.N0233.N0729.d004925
      apply Finset.sum_pos'
      · intro j hj
        exact _root_.GD.N0233.N0729.d004926 B j
      · refine ⟨g, Finset.mem_univ g, ?_⟩
        exact sq_pos_of_ne_zero hg
    exact ne_of_gt hpositive




theorem d004933
    (B : Matrix m n ℝ) :
    Function.Injective B.mulVec ↔
      ∃ g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n),
        det (_root_.GD.N0233.N0729.d004923 B g) ≠ 0 := by
  rw [← _root_.GD.N0233.N0729.d004931,
    _root_.GD.N0233.N0729.d004930,
    _root_.GD.N0233.N0729.d004932]

omit [DecidableEq m] in




theorem d004934
    (B : Matrix m n ℝ) :
    _root_.GD.N0233.N0729.d004925 B = 0 ↔
      ∀ g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n),
        det (_root_.GD.N0233.N0729.d004923 B g) = 0 := by
  constructor
  · intro hzero g
    by_contra hminor
    exact
      (_root_.GD.N0233.N0729.d004932 B).2
        ⟨g, hminor⟩ hzero
  · intro hall
    by_contra hnonzero
    obtain ⟨g, hg⟩ :=
      (_root_.GD.N0233.N0729.d004932 B).1
        hnonzero
    exact hg (hall g)

section Parameterized

variable [TopologicalSpace Θ]


def d004935 (B : Θ → Matrix m n ℝ) : Set Θ :=
  {θ | _root_.GD.N0233.N0729.d004925 (B θ) ≠ 0}


def d004936
    (B : Θ → Matrix m n ℝ)
    (g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n)) : Set Θ :=
  {θ | det (_root_.GD.N0233.N0729.d004923 (B θ) g) ≠ 0}



theorem d004937
    (B : Θ → Matrix m n ℝ) (hB : Continuous B) :
    Continuous fun θ ↦ _root_.GD.N0233.N0729.d004925 (B θ) := by
  rw [show (fun θ ↦ _root_.GD.N0233.N0729.d004925 (B θ)) =
      fun θ ↦ det (_root_.GD.N0233.N0729.d004921 (B θ)) by
        funext θ
        exact (_root_.GD.N0233.N0729.d004930 (B θ)).symm]
  exact (hB.matrix_transpose.matrix_mul hB).matrix_det

omit [DecidableEq m] in

theorem d004938
    (B : Θ → Matrix m n ℝ) (hB : Continuous B)
    (g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n)) :
    Continuous fun θ ↦ det (_root_.GD.N0233.N0729.d004923 (B θ) g) := by
  exact
    ((hB.matrix_transpose).matrix_submatrix id
      (Subtype.val ∘
        _root_.GD.N0233.N0733.d004028 (n := n) g.1 g.2)).matrix_det


theorem d004939
    (B : Θ → Matrix m n ℝ) (hB : Continuous B) :
    IsOpen (_root_.GD.N0233.N0729.d004935 B) := by
  change
    IsOpen
      ((fun θ ↦ _root_.GD.N0233.N0729.d004925 (B θ)) ⁻¹'
        ({0}ᶜ : Set ℝ))
  exact
    isOpen_compl_singleton.preimage
      (_root_.GD.N0233.N0729.d004937 B hB)

omit [DecidableEq m] in

theorem d004940
    (B : Θ → Matrix m n ℝ) (hB : Continuous B)
    (g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n)) :
    IsOpen (_root_.GD.N0233.N0729.d004936 B g) := by
  change
    IsOpen
      ((fun θ ↦ det (_root_.GD.N0233.N0729.d004923 (B θ) g)) ⁻¹'
        ({0}ᶜ : Set ℝ))
  exact
    isOpen_compl_singleton.preimage
      (_root_.GD.N0233.N0729.d004938 B hB g)

omit [TopologicalSpace Θ] [DecidableEq m] in




theorem d004941
    (B : Θ → Matrix m n ℝ) :
    _root_.GD.N0233.N0729.d004935 B =
      ⋃ g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n), _root_.GD.N0233.N0729.d004936 B g := by
  ext θ
  simp only [_root_.GD.N0233.N0729.d004935, _root_.GD.N0233.N0729.d004936, Set.mem_setOf_eq,
    Set.mem_iUnion]
  exact _root_.GD.N0233.N0729.d004932 (B θ)

omit [TopologicalSpace Θ] [DecidableEq m] in




theorem d004942
    (B : Θ → Matrix m n ℝ) (θ : Θ)
    (g₀ g₁ : _root_.GD.N0233.N0729.d004922 (m := m) (n := n))
    (_hvanish : det (_root_.GD.N0233.N0729.d004923 (B θ) g₀) = 0)
    (hsurvive : det (_root_.GD.N0233.N0729.d004923 (B θ) g₁) ≠ 0) :
    θ ∈ _root_.GD.N0233.N0729.d004935 B := by
  exact
    (_root_.GD.N0233.N0729.d004932 (B θ)).2
      ⟨g₁, hsurvive⟩

end Parameterized

end

end N0729
end N0233
end GD
