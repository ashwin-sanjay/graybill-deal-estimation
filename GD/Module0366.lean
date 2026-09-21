import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic






























set_option autoImplicit false
set_option warningAsError true

open Matrix Finset

namespace GD.N0106.N0428.N0765.N1567

variable {ι : Type*} [Fintype ι]


theorem d005495 (M : Matrix ι ι ℝ) (x : ι → ℝ) (i : ι) :
    |(M *ᵥ x) i| ≤ ∑ j, |M i j| * |x j| := by
  simp only [Matrix.mulVec, dotProduct]
  calc |∑ j, M i j * x j| ≤ ∑ j, |M i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |M i j| * |x j| := by simp only [abs_mul]



theorem d005496 (C E Cabs R : Matrix ι ι ℝ)
    (hC : ∀ i k, |C i k| ≤ Cabs i k) (hE : ∀ k j, |E k j| ≤ R k j) (i j : ι) :
    |(C * E) i j| ≤ ∑ k, Cabs i k * R k j := by
  rw [Matrix.mul_apply]
  calc |∑ k, C i k * E k j| ≤ ∑ k, |C i k * E k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |C i k| * |E k j| := by simp only [abs_mul]
    _ ≤ ∑ k, Cabs i k * R k j := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul (hC i k) (hE k j) (abs_nonneg _) ((abs_nonneg _).trans (hC i k))


theorem d005497 (C E Cabs R : Matrix ι ι ℝ)
    (hC : ∀ i k, |C i k| ≤ Cabs i k) (hE : ∀ k j, |E k j| ≤ R k j) (i j : ι) :
    0 ≤ ∑ k, Cabs i k * R k j :=
  Finset.sum_nonneg fun k _ =>
    mul_nonneg ((abs_nonneg _).trans (hC i k)) ((abs_nonneg _).trans (hE k j))



theorem d005498 (C E Cabs R : Matrix ι ι ℝ) (q : ℝ)
    (hC : ∀ i k, |C i k| ≤ Cabs i k) (hE : ∀ k j, |E k j| ≤ R k j)
    (hq : ∀ i, ∑ j, ∑ k, Cabs i k * R k j ≤ q)
    (x : ι → ℝ) (Mx : ℝ) (hx : ∀ j, |x j| ≤ Mx) (i : ι) :
    |(C *ᵥ (E *ᵥ x)) i| ≤ q * Mx := by
  have hMx : 0 ≤ Mx := (abs_nonneg _).trans (hx i)
  rw [Matrix.mulVec_mulVec]
  calc |((C * E) *ᵥ x) i| ≤ ∑ j, |(C * E) i j| * |x j| := _root_.GD.N0106.N0428.N0765.N1567.d005495 _ _ _
    _ ≤ ∑ j, (∑ k, Cabs i k * R k j) * Mx := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul (_root_.GD.N0106.N0428.N0765.N1567.d005496 C E Cabs R hC hE i j) (hx j) (abs_nonneg _)
          (_root_.GD.N0106.N0428.N0765.N1567.d005497 C E Cabs R hC hE i j)
    _ = (∑ j, ∑ k, Cabs i k * R k j) * Mx := by rw [Finset.sum_mul]
    _ ≤ q * Mx := mul_le_mul_of_nonneg_right (hq i) hMx

variable [DecidableEq ι]



theorem d005499 (A A₀ C : Matrix ι ι ℝ) (hCA : C * A₀ = 1)
    (x b : ι → ℝ) (hAx : A *ᵥ x = b) :
    x - C *ᵥ b = -(C *ᵥ ((A - A₀) *ᵥ x)) := by
  have h1 : C *ᵥ (A₀ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hCA, Matrix.one_mulVec]
  have h2 : (A - A₀) *ᵥ x = b - A₀ *ᵥ x := by
    rw [Matrix.sub_mulVec, hAx]
  rw [h2, Matrix.mulVec_sub, h1, neg_sub]


theorem d005500 (A A₀ C : Matrix ι ι ℝ) (hCA : C * A₀ = 1)
    (x b : ι → ℝ) (hAx : A *ᵥ x = b) (i : ι) :
    x i - (C *ᵥ b) i = -((C *ᵥ ((A - A₀) *ᵥ x)) i) := by
  have h := congrFun (_root_.GD.N0106.N0428.N0765.N1567.d005499 A A₀ C hCA x b hAx) i
  simpa only [Pi.sub_apply, Pi.neg_apply] using h


theorem d005501 (A A₀ R : Matrix ι ι ℝ)
    (hbox : ∀ k j, |A k j - A₀ k j| ≤ R k j) (k j : ι) :
    |(A - A₀) k j| ≤ R k j := by
  simpa only [Matrix.sub_apply] using hbox k j



theorem d005502 (A A₀ C Cabs R : Matrix ι ι ℝ) (q : ℝ)
    (hCA : C * A₀ = 1) (hC : ∀ i k, |C i k| ≤ Cabs i k)
    (hbox : ∀ k j, |A k j - A₀ k j| ≤ R k j)
    (hq : ∀ i, ∑ j, ∑ k, Cabs i k * R k j ≤ q) (hq1 : q < 1) :
    Function.Injective A.mulVec := by
  intro x y hxy
  have hzero : A *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨i, hi⟩ : ∃ i, (x - y) i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => |(x - y) j|)
    ⟨i, Finset.mem_univ i⟩
  have hbound := _root_.GD.N0106.N0428.N0765.N1567.d005498 C (A - A₀) Cabs R q hC (_root_.GD.N0106.N0428.N0765.N1567.d005501 A A₀ R hbox)
    hq (x - y) (|(x - y) m|) (fun j => hm j (Finset.mem_univ j)) m
  have hrep := _root_.GD.N0106.N0428.N0765.N1567.d005500 A A₀ C hCA (x - y) 0 hzero m
  rw [Matrix.mulVec_zero, Pi.zero_apply, sub_zero] at hrep
  have hzm : |(x - y) m| ≤ q * |(x - y) m| := by
    calc |(x - y) m| = |(C *ᵥ ((A - A₀) *ᵥ (x - y))) m| := by rw [hrep, abs_neg]
      _ ≤ q * |(x - y) m| := hbound
  have hpos : 0 < |(x - y) m| :=
    lt_of_lt_of_le (abs_pos.mpr hi) (hm i (Finset.mem_univ i))
  nlinarith [mul_pos (sub_pos.mpr hq1) hpos]


theorem d005503 (A A₀ C Cabs R : Matrix ι ι ℝ) (q : ℝ)
    (hCA : C * A₀ = 1) (hC : ∀ i k, |C i k| ≤ Cabs i k)
    (hbox : ∀ k j, |A k j - A₀ k j| ≤ R k j)
    (hq : ∀ i, ∑ j, ∑ k, Cabs i k * R k j ≤ q) (hq1 : q < 1) :
    IsUnit A :=
  Matrix.mulVec_injective_iff_isUnit.mp
    (_root_.GD.N0106.N0428.N0765.N1567.d005502 A A₀ C Cabs R q hCA hC hbox hq hq1)


theorem d005504 (A A₀ C Cabs R : Matrix ι ι ℝ) (q : ℝ)
    (hCA : C * A₀ = 1) (hC : ∀ i k, |C i k| ≤ Cabs i k)
    (hbox : ∀ k j, |A k j - A₀ k j| ≤ R k j)
    (hq : ∀ i, ∑ j, ∑ k, Cabs i k * R k j ≤ q) (hq1 : q < 1) (b : ι → ℝ) :
    ∃! x, A *ᵥ x = b := by
  have hu := _root_.GD.N0106.N0428.N0765.N1567.d005503 A A₀ C Cabs R q hCA hC hbox hq hq1
  obtain ⟨x, hx⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hu b
  exact ⟨x, hx, fun y hy => Matrix.mulVec_injective_iff_isUnit.mpr hu (hy.trans hx.symm)⟩



theorem d005505 (A A₀ C Cabs R : Matrix ι ι ℝ) (q : ℝ)
    (hCA : C * A₀ = 1) (hC : ∀ i k, |C i k| ≤ Cabs i k)
    (hbox : ∀ k j, |A k j - A₀ k j| ≤ R k j)
    (hq : ∀ i, ∑ j, ∑ k, Cabs i k * R k j ≤ q) (hq1 : q < 1)
    (x b : ι → ℝ) (hAx : A *ᵥ x = b) (N : ℝ) (hN : ∀ i, |(C *ᵥ b) i| ≤ N) (i : ι) :
    |x i - (C *ᵥ b) i| ≤ q * N / (1 - q) := by
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun j => |x j - (C *ᵥ b) j|)
    ⟨i, Finset.mem_univ i⟩
  have hxbound : ∀ j, |x j| ≤ N + |x m - (C *ᵥ b) m| := by
    intro j
    calc |x j| = |(C *ᵥ b) j + (x j - (C *ᵥ b) j)| := by congr 1; ring
      _ ≤ |(C *ᵥ b) j| + |x j - (C *ᵥ b) j| := abs_add_le _ _
      _ ≤ N + |x m - (C *ᵥ b) m| := add_le_add (hN j) (hm j (Finset.mem_univ j))
  have hbound := _root_.GD.N0106.N0428.N0765.N1567.d005498 C (A - A₀) Cabs R q hC (_root_.GD.N0106.N0428.N0765.N1567.d005501 A A₀ R hbox)
    hq x (N + |x m - (C *ᵥ b) m|) hxbound m
  have hrep := _root_.GD.N0106.N0428.N0765.N1567.d005500 A A₀ C hCA x b hAx m
  have hDle : |x m - (C *ᵥ b) m| ≤ q * (N + |x m - (C *ᵥ b) m|) := by
    calc |x m - (C *ᵥ b) m| = |(C *ᵥ ((A - A₀) *ᵥ x)) m| := by rw [hrep, abs_neg]
      _ ≤ q * (N + |x m - (C *ᵥ b) m|) := hbound
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hD : |x m - (C *ᵥ b) m| ≤ q * N / (1 - q) := by
    rw [le_div_iff₀ h1q]
    nlinarith [hDle]
  exact (hm i (Finset.mem_univ i)).trans hD


theorem d005506 (x x₀ : ι → ℝ) (err : ℝ)
    (h : ∀ i, |x i - x₀ i| ≤ err) (i : ι) : x₀ i - err ≤ x i := by
  have := (abs_le.mp (h i)).1
  linarith

end GD.N0106.N0428.N0765.N1567
