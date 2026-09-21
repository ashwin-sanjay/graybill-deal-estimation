import Mathlib.Analysis.InnerProductSpace.Basic















open scoped BigOperators RealInnerProductSpace

namespace GD
namespace N0234
namespace N0736

noncomputable section

variable {ι E : Type*}
  [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]


def d003267 (x : ι → E) : E :=
  ((Fintype.card ι : ℝ)⁻¹) • ∑ i, x i


def d003268 (x : ι → E) : ℝ :=
  ∑ i, ‖x i - _root_.GD.N0234.N0736.d003267 x‖ ^ 2


def d003269 (x : ι → E) : ℝ :=
  ∑ i, ∑ j, ‖x i - x j‖ ^ 2


theorem d003270 (x : ι → E) :
    ∑ i, x i = (Fintype.card ι : ℝ) • _root_.GD.N0234.N0736.d003267 x := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  simp [_root_.GD.N0234.N0736.d003267, smul_smul, hn]


theorem d003271 : 0 < (Fintype.card ι : ℝ) := by
  exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card ι)


theorem d003272 (x : ι → E) :
    (∑ i, inner ℝ (x i) (_root_.GD.N0234.N0736.d003267 x)) =
      (Fintype.card ι : ℝ) * ‖_root_.GD.N0234.N0736.d003267 x‖ ^ 2 := by
  rw [← sum_inner, _root_.GD.N0234.N0736.d003270,
    real_inner_smul_left, real_inner_self_eq_norm_sq]


theorem d003273 (x : ι → E) :
    (∑ i, inner ℝ (_root_.GD.N0234.N0736.d003267 x) (x i)) =
      (Fintype.card ι : ℝ) * ‖_root_.GD.N0234.N0736.d003267 x‖ ^ 2 := by
  rw [← inner_sum, _root_.GD.N0234.N0736.d003270,
    real_inner_smul_right, real_inner_self_eq_norm_sq]


theorem d003274
    (x : ι → E) :
    _root_.GD.N0234.N0736.d003268 x =
      (∑ i, ‖x i‖ ^ 2) -
        (Fintype.card ι : ℝ) * ‖_root_.GD.N0234.N0736.d003267 x‖ ^ 2 := by
  rw [_root_.GD.N0234.N0736.d003268]
  simp_rw [norm_sub_sq_real]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, _root_.GD.N0234.N0736.d003272]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

omit [Nonempty ι] [InnerProductSpace ℝ E] in
omit [Nonempty ι] [InnerProductSpace ℝ E] in

theorem d003275 (x : ι → E) :
    (∑ i : ι, ∑ _j : ι, ‖x i‖ ^ 2) =
      (Fintype.card ι : ℝ) * ∑ i, ‖x i‖ ^ 2 := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]

omit [Nonempty ι] [InnerProductSpace ℝ E] in
omit [Nonempty ι] [InnerProductSpace ℝ E] in

theorem d003276 (x : ι → E) :
    (∑ _i : ι, ∑ j : ι, ‖x j‖ ^ 2) =
      (Fintype.card ι : ℝ) * ∑ j, ‖x j‖ ^ 2 := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [Nonempty ι] in
omit [Nonempty ι] in

theorem d003277 (x : ι → E) :
    (∑ i, ∑ j, inner ℝ (x i) (x j)) =
      ‖∑ i, x i‖ ^ 2 := by
  calc
    (∑ i, ∑ j, inner ℝ (x i) (x j)) =
        ∑ i, inner ℝ (x i) (∑ j, x j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [inner_sum]
    _ = inner ℝ (∑ i, x i) (∑ j, x j) := by
      rw [sum_inner]
    _ = ‖∑ i, x i‖ ^ 2 :=
      real_inner_self_eq_norm_sq _

omit [Nonempty ι] in
omit [Nonempty ι] in

theorem d003278 (x : ι → E) :
    (∑ i, ∑ j, inner ℝ (x j) (x i)) =
      ‖∑ i, x i‖ ^ 2 := by
  calc
    (∑ i, ∑ j, inner ℝ (x j) (x i)) =
        ∑ i, inner ℝ (∑ j, x j) (x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [sum_inner]
    _ = inner ℝ (∑ j, x j) (∑ i, x i) := by
      rw [inner_sum]
    _ = ‖∑ i, x i‖ ^ 2 :=
      real_inner_self_eq_norm_sq _

omit [Nonempty ι] in

theorem d003279 (x : ι → E) :
    (∑ i, ∑ j, 2 * inner ℝ (x i) (x j)) =
      2 * ‖∑ i, x i‖ ^ 2 := by
  calc
    (∑ i, ∑ j, 2 * inner ℝ (x i) (x j)) =
        ∑ i, 2 * (∑ j, inner ℝ (x i) (x j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = 2 * (∑ i, ∑ j, inner ℝ (x i) (x j)) := by
      rw [Finset.mul_sum]
    _ = 2 * ‖∑ i, x i‖ ^ 2 := by
      rw [_root_.GD.N0234.N0736.d003277]

omit [Nonempty ι] in

theorem d003280
    (x : ι → E) :
    _root_.GD.N0234.N0736.d003269 x =
      2 * (Fintype.card ι : ℝ) * (∑ i, ‖x i‖ ^ 2) -
        2 * ‖∑ i, x i‖ ^ 2 := by
  rw [_root_.GD.N0234.N0736.d003269]
  simp_rw [norm_sub_sq_real]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [_root_.GD.N0234.N0736.d003275, _root_.GD.N0234.N0736.d003276]
  rw [_root_.GD.N0234.N0736.d003279]
  ring





theorem d003281
    (x : ι → E) :
    2 * (Fintype.card ι : ℝ) * _root_.GD.N0234.N0736.d003268 x =
      _root_.GD.N0234.N0736.d003269 x := by
  have hsum :
      ∑ i, x i = (Fintype.card ι : ℝ) • _root_.GD.N0234.N0736.d003267 x :=
    _root_.GD.N0234.N0736.d003270 x
  rw [_root_.GD.N0234.N0736.d003274, _root_.GD.N0234.N0736.d003280, hsum]
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (_root_.GD.N0234.N0736.d003271 (ι := ι)).le, mul_pow]
  ring


theorem d003282
    (x : ι → E) :
    _root_.GD.N0234.N0736.d003268 x =
      (2 * (Fintype.card ι : ℝ))⁻¹ * _root_.GD.N0234.N0736.d003269 x := by
  have hn : (2 * (Fintype.card ι : ℝ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (ne_of_gt (_root_.GD.N0234.N0736.d003271 (ι := ι)))
  exact (eq_inv_mul_iff_mul_eq₀ hn).2
    (_root_.GD.N0234.N0736.d003281 x)

omit [Nonempty ι] [InnerProductSpace ℝ E] in
omit [Nonempty ι] [InnerProductSpace ℝ E] in

theorem d003283 (x : ι → E) :
    0 ≤ _root_.GD.N0234.N0736.d003269 x := by
  exact Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ sq_nonneg ‖x i - x j‖

omit [Nonempty ι] [InnerProductSpace ℝ E] in
omit [Nonempty ι] [InnerProductSpace ℝ E] in

theorem d003284
    (x : ι → E) :
    _root_.GD.N0234.N0736.d003269 x = 0 ↔
      ∀ i j, x i = x j := by
  constructor
  · intro hzero i j
    have hi :
        (∑ j, ‖x i - x j‖ ^ 2) = 0 := by
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun k _ ↦
            Finset.sum_nonneg fun l _ ↦
              sq_nonneg ‖x k - x l‖)).mp
          hzero i (Finset.mem_univ i)
    have hij : ‖x i - x j‖ ^ 2 = 0 := by
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun k _ ↦ sq_nonneg ‖x i - x k‖)).mp
          hi j (Finset.mem_univ j)
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hij))
  · intro hcons
    unfold _root_.GD.N0234.N0736.d003269
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [hcons i j, sub_self, norm_zero, zero_pow (by norm_num)]


theorem d003285
    (x : ι → E) :
    _root_.GD.N0234.N0736.d003268 x = 0 ↔
      ∀ i j, x i = x j := by
  rw [_root_.GD.N0234.N0736.d003282,
    mul_eq_zero]
  have hn : (2 * (Fintype.card ι : ℝ))⁻¹ ≠ 0 := by
    exact inv_ne_zero <| mul_ne_zero (by norm_num)
      (ne_of_gt (_root_.GD.N0234.N0736.d003271 (ι := ι)))
  simp only [hn, false_or, _root_.GD.N0234.N0736.d003284]

end

end N0736
end N0234
end GD
