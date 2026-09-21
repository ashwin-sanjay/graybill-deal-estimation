import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0005.N0248

open Set Polynomial

noncomputable section

def d030070 (a x u : ℝ) : ℝ := a + (u - x)^2

def d030071 (m n a b x y u : ℝ) : ℝ :=
  -(m * Real.log (_root_.GD.N0005.N0248.d030070 a x u) +
    n * Real.log (_root_.GD.N0005.N0248.d030070 b y u)) / 2

def d030072 (m n a b x y u : ℝ) : ℝ :=
  m * (u-x) * _root_.GD.N0005.N0248.d030070 b y u +
    n * (u-y) * _root_.GD.N0005.N0248.d030070 a x u

def d030073 (m n a b x y : ℝ) : ℝ[X] :=
  C (m+n) * X^3 - C (m*(x+2*y)+n*(y+2*x)) * X^2 +
    C (m*(b+y^2+2*x*y)+n*(a+x^2+2*x*y)) * X -
    C (m*x*(b+y^2)+n*y*(a+x^2))

theorem d030074 {a : ℝ} (ha : 0 < a) (x u : ℝ) :
    0 < _root_.GD.N0005.N0248.d030070 a x u := by
  dsimp [_root_.GD.N0005.N0248.d030070]
  positivity

theorem d030075 (m n a b x y u : ℝ) :
    (_root_.GD.N0005.N0248.d030073 m n a b x y).eval u = _root_.GD.N0005.N0248.d030072 m n a b x y u := by
  simp only [_root_.GD.N0005.N0248.d030073, eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  dsimp [_root_.GD.N0005.N0248.d030072, _root_.GD.N0005.N0248.d030070]
  ring

theorem d030076 (m n a b x y : ℝ) :
    (_root_.GD.N0005.N0248.d030073 m n a b x y).natDegree ≤ 3 := by
  unfold _root_.GD.N0005.N0248.d030073
  compute_degree!

theorem d030077 (m n a b x y : ℝ) :
    (_root_.GD.N0005.N0248.d030073 m n a b x y).coeff 3 = m+n := by
  simp only [_root_.GD.N0005.N0248.d030073, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

theorem d030078 {m n : ℝ} (hm : 0 < m) (hn : 0 < n)
    (a b x y : ℝ) : _root_.GD.N0005.N0248.d030073 m n a b x y ≠ 0 := by
  intro hz
  have := _root_.GD.N0005.N0248.d030077 m n a b x y
  rw [hz, coeff_zero] at this
  linarith

theorem d030079 {m n a b x y u : ℝ} (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (_root_.GD.N0005.N0248.d030071 m n a b x y)
      (-_root_.GD.N0005.N0248.d030072 m n a b x y u /
        (_root_.GD.N0005.N0248.d030070 a x u * _root_.GD.N0005.N0248.d030070 b y u)) u := by
  have hA : HasDerivAt (_root_.GD.N0005.N0248.d030070 a x) (2*(u-x)) u := by
    simpa only [_root_.GD.N0005.N0248.d030070, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one] using! (((hasDerivAt_id u).sub_const x).pow 2).const_add a
  have hB : HasDerivAt (_root_.GD.N0005.N0248.d030070 b y) (2*(u-y)) u := by
    simpa only [_root_.GD.N0005.N0248.d030070, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one] using! (((hasDerivAt_id u).sub_const y).pow 2).const_add b
  have hA0 := (_root_.GD.N0005.N0248.d030074 ha x u).ne'
  have hB0 := (_root_.GD.N0005.N0248.d030074 hb y u).ne'
  have h := (((hA.log hA0).const_mul m).add ((hB.log hB0).const_mul n)).neg.div_const 2
  have heq : -_root_.GD.N0005.N0248.d030072 m n a b x y u /
      (_root_.GD.N0005.N0248.d030070 a x u * _root_.GD.N0005.N0248.d030070 b y u) =
      -(m * (2*(u-x) / _root_.GD.N0005.N0248.d030070 a x u) +
        n * (2*(u-y) / _root_.GD.N0005.N0248.d030070 b y u)) / 2 := by
    unfold _root_.GD.N0005.N0248.d030072
    field_simp
  rw [heq]
  exact h

theorem d030080 {m n a b x y u : ℝ} (ha : 0 < a) (hb : 0 < b) :
    deriv (_root_.GD.N0005.N0248.d030071 m n a b x y) u = 0 ↔
      (_root_.GD.N0005.N0248.d030073 m n a b x y).eval u = 0 := by
  rw [(_root_.GD.N0005.N0248.d030079 ha hb).deriv, _root_.GD.N0005.N0248.d030075]
  rw [div_eq_zero_iff]
  simp [ne_of_gt (_root_.GD.N0005.N0248.d030074 ha x u),
    ne_of_gt (_root_.GD.N0005.N0248.d030074 hb y u)]

theorem d030081 {m n a b x y u : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (hu : deriv (_root_.GD.N0005.N0248.d030071 m n a b x y) u = 0) :
    u ∈ Icc (min x y) (max x y) := by
  have heq : _root_.GD.N0005.N0248.d030072 m n a b x y u = 0 := by
    simpa only [_root_.GD.N0005.N0248.d030075] using (_root_.GD.N0005.N0248.d030080 ha hb).1 hu
  have hA := _root_.GD.N0005.N0248.d030074 ha x u
  have hB := _root_.GD.N0005.N0248.d030074 hb y u
  constructor
  · by_contra hl
    have hux : u-x < 0 := by have := min_le_left x y; simp only [not_le] at hl; linarith
    have huy : u-y < 0 := by have := min_le_right x y; simp only [not_le] at hl; linarith
    have h1 := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hm hux) hB
    have h2 := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hn huy) hA
    dsimp [_root_.GD.N0005.N0248.d030072] at heq
    linarith
  · by_contra hr
    have hux : 0 < u-x := by have := le_max_left x y; simp only [not_le] at hr; linarith
    have huy : 0 < u-y := by have := le_max_right x y; simp only [not_le] at hr; linarith
    have h1 := mul_pos (mul_pos hm hux) hB
    have h2 := mul_pos (mul_pos hn huy) hA
    dsimp [_root_.GD.N0005.N0248.d030072] at heq
    linarith

theorem d030082 {m n a b x y : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) :
    ∃ S : Finset ℝ, S.card ≤ 3 ∧
      ∀ u : ℝ, u ∈ S ↔ deriv (_root_.GD.N0005.N0248.d030071 m n a b x y) u = 0 := by
  classical
  refine ⟨(_root_.GD.N0005.N0248.d030073 m n a b x y).roots.toFinset, ?_, ?_⟩
  · exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (_root_.GD.N0005.N0248.d030076 m n a b x y))
  · intro u
    rw [Multiset.mem_toFinset, mem_roots (_root_.GD.N0005.N0248.d030078 hm hn a b x y)]
    exact (_root_.GD.N0005.N0248.d030080 ha hb).symm

theorem d030083 {m n a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Continuous (_root_.GD.N0005.N0248.d030071 m n a b x y) := by
  have hA : Continuous (fun u => Real.log (_root_.GD.N0005.N0248.d030070 a x u)) := by
    apply Continuous.log
    · unfold _root_.GD.N0005.N0248.d030070
      fun_prop
    · intro u
      exact (_root_.GD.N0005.N0248.d030074 ha x u).ne'
  have hB : Continuous (fun u => Real.log (_root_.GD.N0005.N0248.d030070 b y u)) := by
    apply Continuous.log
    · unfold _root_.GD.N0005.N0248.d030070
      fun_prop
    · intro u
      exact (_root_.GD.N0005.N0248.d030074 hb y u).ne'
  exact ((hA.const_mul m).add (hB.const_mul n)).neg.div_const 2

theorem d030084 {m n a b x y u v : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (ha : 0 < a) (hb : 0 < b)
    (hA : _root_.GD.N0005.N0248.d030070 a x v ≤ _root_.GD.N0005.N0248.d030070 a x u)
    (hB : _root_.GD.N0005.N0248.d030070 b y v ≤ _root_.GD.N0005.N0248.d030070 b y u) :
    _root_.GD.N0005.N0248.d030071 m n a b x y u ≤ _root_.GD.N0005.N0248.d030071 m n a b x y v := by
  have h1 := mul_le_mul_of_nonneg_left
    (Real.log_le_log (_root_.GD.N0005.N0248.d030074 ha x v) hA) hm
  have h2 := mul_le_mul_of_nonneg_left
    (Real.log_le_log (_root_.GD.N0005.N0248.d030074 hb y v) hB) hn
  dsimp [_root_.GD.N0005.N0248.d030071]
  linarith

theorem d030085 {m n a b x y : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (ha : 0 < a) (hb : 0 < b) :
    ∃ u ∈ Icc (min x y) (max x y),
      ∀ v : ℝ, _root_.GD.N0005.N0248.d030071 m n a b x y v ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u := by
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.2 min_le_max) (_root_.GD.N0005.N0248.d030083 ha hb).continuousOn
  refine ⟨u, hu, ?_⟩
  intro v
  by_cases hl : v < min x y
  · apply le_trans (_root_.GD.N0005.N0248.d030084 hm hn ha hb ?_ ?_)
      (hmax (left_mem_Icc.2 min_le_max))
    · have h1 := min_le_left x y
      dsimp [_root_.GD.N0005.N0248.d030070]
      nlinarith [sq_nonneg (min x y-v), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hl.le)]
    · have h1 := min_le_right x y
      dsimp [_root_.GD.N0005.N0248.d030070]
      nlinarith [sq_nonneg (min x y-v), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hl.le)]
  · by_cases hr : max x y < v
    · apply le_trans (_root_.GD.N0005.N0248.d030084 hm hn ha hb ?_ ?_)
        (hmax (right_mem_Icc.2 min_le_max))
      · have h1 := le_max_left x y
        dsimp [_root_.GD.N0005.N0248.d030070]
        nlinarith [sq_nonneg (v-max x y), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hr.le)]
      · have h1 := le_max_right x y
        dsimp [_root_.GD.N0005.N0248.d030070]
        nlinarith [sq_nonneg (v-max x y), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hr.le)]
    · exact hmax ⟨le_of_not_gt hl, le_of_not_gt hr⟩

theorem d030086 {m n a b x y u : ℝ}
    (hmax : ∀ v : ℝ, _root_.GD.N0005.N0248.d030071 m n a b x y v ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u) :
    deriv (_root_.GD.N0005.N0248.d030071 m n a b x y) u = 0 := by
  exact ((isMaxOn_univ_iff.2 hmax).isLocalMax (Filter.univ_mem)).deriv_eq_zero

def d030087 (m n : ℕ) (a b x y u : ℝ) : ℝ :=
  _root_.GD.N0005.N0248.d030070 a x u ^ m * _root_.GD.N0005.N0248.d030070 b y u ^ n

theorem d030088 (m n : ℕ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x y u : ℝ) :
    0 < _root_.GD.N0005.N0248.d030087 m n a b x y u :=
  mul_pos (pow_pos (_root_.GD.N0005.N0248.d030074 ha x u) m) (pow_pos (_root_.GD.N0005.N0248.d030074 hb y u) n)

theorem d030089 (m n : ℕ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x y u : ℝ) :
    _root_.GD.N0005.N0248.d030071 m n a b x y u = -Real.log (_root_.GD.N0005.N0248.d030087 m n a b x y u) / 2 := by
  rw [_root_.GD.N0005.N0248.d030087, Real.log_mul
    (pow_ne_zero _ (_root_.GD.N0005.N0248.d030074 ha x u).ne')
    (pow_ne_zero _ (_root_.GD.N0005.N0248.d030074 hb y u).ne'), Real.log_pow, Real.log_pow]
  rfl

theorem d030090 (m n : ℕ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x y u v : ℝ) :
    _root_.GD.N0005.N0248.d030071 m n a b x y u ≤ _root_.GD.N0005.N0248.d030071 m n a b x y v ↔
      _root_.GD.N0005.N0248.d030087 m n a b x y v ≤ _root_.GD.N0005.N0248.d030087 m n a b x y u := by
  rw [_root_.GD.N0005.N0248.d030089 m n ha hb,
    _root_.GD.N0005.N0248.d030089 m n ha hb]
  constructor
  · intro h
    apply (Real.log_le_log_iff (_root_.GD.N0005.N0248.d030088 m n ha hb x y v)
      (_root_.GD.N0005.N0248.d030088 m n ha hb x y u)).1
    linarith
  · intro h
    have := (Real.log_le_log_iff (_root_.GD.N0005.N0248.d030088 m n ha hb x y v)
      (_root_.GD.N0005.N0248.d030088 m n ha hb x y u)).2 h
    linarith

end
end GD.N0005.N0248

#print axioms _root_.GD.N0005.N0248.d030082
#print axioms _root_.GD.N0005.N0248.d030085
#print axioms _root_.GD.N0005.N0248.d030090
