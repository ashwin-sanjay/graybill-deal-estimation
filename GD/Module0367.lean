import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

























set_option autoImplicit false
set_option warningAsError true

open Finset

namespace GD.N0106.N0428.N0765.N1568
noncomputable section


def d005507 (cL h : ℝ) (m : ℕ) : ℝ := cL - m * h


def d005508 (cR h : ℝ) (m : ℕ) : ℝ := cR + m * h


def d005509 (h M α c : ℝ) : ℝ :=
  h * M * Real.exp (α * c) / (1 - Real.exp (-(α * h)))


def d005510 (h M α c : ℝ) : ℝ :=
  h * M * Real.exp (-(α * c)) / (1 - Real.exp (-(α * h)))

theorem d005511 (h M α c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1568.d005509 h M α c = h * M * Real.exp (α * c) / (1 - Real.exp (-(α * h))) := rfl

theorem d005512 (h M α c : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1568.d005510 h M α c = h * M * Real.exp (-(α * c)) / (1 - Real.exp (-(α * h))) := rfl

theorem d005513 (cL : ℝ) {h : ℝ} (hh : 0 ≤ h) (m : ℕ) : _root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m ≤ cL := by
  unfold _root_.GD.N0106.N0428.N0765.N1568.d005507
  have : 0 ≤ (m : ℝ) * h := mul_nonneg (Nat.cast_nonneg m) hh
  linarith

theorem d005514 (cR : ℝ) {h : ℝ} (hh : 0 ≤ h) (m : ℕ) : cR ≤ _root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m := by
  unfold _root_.GD.N0106.N0428.N0765.N1568.d005508
  have : 0 ≤ (m : ℝ) * h := mul_nonneg (Nat.cast_nonneg m) hh
  linarith

theorem d005515 {α h : ℝ} (hα : 0 < α) (hh : 0 < h) :
    Real.exp (-(α * h)) < 1 := by
  have hpos := mul_pos hα hh
  have h1 : Real.exp (-(α * h)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
  rwa [Real.exp_zero] at h1

theorem d005516 {α h : ℝ} (hα : 0 < α) (hh : 0 < h) :
    0 < 1 - Real.exp (-(α * h)) :=
  sub_pos.mpr (_root_.GD.N0106.N0428.N0765.N1568.d005515 hα hh)

theorem d005517 (α cL h : ℝ) (m : ℕ) :
    Real.exp (α * _root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m) = Real.exp (α * cL) * Real.exp (-(α * h)) ^ m := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  unfold _root_.GD.N0106.N0428.N0765.N1568.d005507
  ring

theorem d005518 (α cR h : ℝ) (m : ℕ) :
    Real.exp (-(α * _root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m)) = Real.exp (-(α * cR)) * Real.exp (-(α * h)) ^ m := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  unfold _root_.GD.N0106.N0428.N0765.N1568.d005508
  ring



theorem d005519 {g : ℝ → ℝ} {M α cL h : ℝ} (hα : 0 < α) (hh : 0 < h)
    (hg0 : ∀ m : ℕ, 0 ≤ g (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m))
    (hg : ∀ m : ℕ, g (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m) ≤ M * Real.exp (α * _root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m)) :
    Summable (fun m : ℕ => h * g (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m)) ∧
      ∑' m : ℕ, h * g (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m) ≤ _root_.GD.N0106.N0428.N0765.N1568.d005509 h M α cL := by
  have hr0 : 0 ≤ Real.exp (-(α * h)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(α * h)) < 1 := _root_.GD.N0106.N0428.N0765.N1568.d005515 hα hh
  have hdom : Summable (fun m : ℕ =>
      (h * M * Real.exp (α * cL)) * Real.exp (-(α * h)) ^ m) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hle : ∀ m : ℕ, h * g (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m) ≤
      (h * M * Real.exp (α * cL)) * Real.exp (-(α * h)) ^ m := by
    intro m
    calc h * g (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m) ≤ h * (M * Real.exp (α * _root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m)) :=
          mul_le_mul_of_nonneg_left (hg m) hh.le
      _ = (h * M * Real.exp (α * cL)) * Real.exp (-(α * h)) ^ m := by
          rw [_root_.GD.N0106.N0428.N0765.N1568.d005517]; ring
  have hsum : Summable (fun m : ℕ => h * g (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m)) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg hh.le (hg0 m)) hle hdom
  refine ⟨hsum, ?_⟩
  calc ∑' m : ℕ, h * g (_root_.GD.N0106.N0428.N0765.N1568.d005507 cL h m)
      ≤ ∑' m : ℕ, (h * M * Real.exp (α * cL)) * Real.exp (-(α * h)) ^ m :=
        hsum.tsum_le_tsum hle hdom
    _ = (h * M * Real.exp (α * cL)) * (1 - Real.exp (-(α * h)))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ = _root_.GD.N0106.N0428.N0765.N1568.d005509 h M α cL := by
        unfold _root_.GD.N0106.N0428.N0765.N1568.d005509
        rw [div_eq_mul_inv]



theorem d005520 {g : ℝ → ℝ} {M α cR h : ℝ} (hα : 0 < α) (hh : 0 < h)
    (hg0 : ∀ m : ℕ, 0 ≤ g (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m))
    (hg : ∀ m : ℕ, g (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m) ≤ M * Real.exp (-(α * _root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m))) :
    Summable (fun m : ℕ => h * g (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m)) ∧
      ∑' m : ℕ, h * g (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m) ≤ _root_.GD.N0106.N0428.N0765.N1568.d005510 h M α cR := by
  have hr0 : 0 ≤ Real.exp (-(α * h)) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(α * h)) < 1 := _root_.GD.N0106.N0428.N0765.N1568.d005515 hα hh
  have hdom : Summable (fun m : ℕ =>
      (h * M * Real.exp (-(α * cR))) * Real.exp (-(α * h)) ^ m) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hle : ∀ m : ℕ, h * g (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m) ≤
      (h * M * Real.exp (-(α * cR))) * Real.exp (-(α * h)) ^ m := by
    intro m
    calc h * g (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m) ≤ h * (M * Real.exp (-(α * _root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m))) :=
          mul_le_mul_of_nonneg_left (hg m) hh.le
      _ = (h * M * Real.exp (-(α * cR))) * Real.exp (-(α * h)) ^ m := by
          rw [_root_.GD.N0106.N0428.N0765.N1568.d005518]; ring
  have hsum : Summable (fun m : ℕ => h * g (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m)) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg hh.le (hg0 m)) hle hdom
  refine ⟨hsum, ?_⟩
  calc ∑' m : ℕ, h * g (_root_.GD.N0106.N0428.N0765.N1568.d005508 cR h m)
      ≤ ∑' m : ℕ, (h * M * Real.exp (-(α * cR))) * Real.exp (-(α * h)) ^ m :=
        hsum.tsum_le_tsum hle hdom
    _ = (h * M * Real.exp (-(α * cR))) * (1 - Real.exp (-(α * h)))⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ = _root_.GD.N0106.N0428.N0765.N1568.d005510 h M α cR := by
        unfold _root_.GD.N0106.N0428.N0765.N1568.d005510
        rw [div_eq_mul_inv]




theorem d005521 {f : ℝ → ℝ} {c₀ h τL τR : ℝ} {N : ℕ}
    (hL : HasSum (fun m : ℕ => h * f (_root_.GD.N0106.N0428.N0765.N1568.d005507 (c₀ - h) h m)) τL)
    (hR : HasSum (fun m : ℕ => h * f (_root_.GD.N0106.N0428.N0765.N1568.d005508 (c₀ + N * h) h m)) τR) :
    HasSum (fun k : ℤ => h * f (c₀ + (k : ℝ) * h))
      ((∑ i ∈ range N, h * f (c₀ + (i : ℝ) * h)) + τR + τL) := by
  have hR' : HasSum (fun n : ℕ => h * f (c₀ + ((n + N : ℕ) : ℝ) * h)) τR := by
    have e : (fun n : ℕ => h * f (c₀ + ((n + N : ℕ) : ℝ) * h)) =
        fun m : ℕ => h * f (_root_.GD.N0106.N0428.N0765.N1568.d005508 (c₀ + N * h) h m) := by
      funext n
      rw [show c₀ + ((n + N : ℕ) : ℝ) * h = _root_.GD.N0106.N0428.N0765.N1568.d005508 (c₀ + N * h) h n by
        unfold _root_.GD.N0106.N0428.N0765.N1568.d005508; push_cast; ring]
    rw [e]
    exact hR
  have hnat : HasSum (fun n : ℕ => h * f (c₀ + (n : ℝ) * h))
      (τR + ∑ i ∈ range N, h * f (c₀ + (i : ℝ) * h)) :=
    (hasSum_nat_add_iff (f := fun n : ℕ => h * f (c₀ + (n : ℝ) * h)) N).mp hR'
  have hpos : HasSum (fun n : ℕ => h * f (c₀ + (((n : ℤ) + 1 : ℤ) : ℝ) * h))
      (τR + ∑ i ∈ range N, h * f (c₀ + (i : ℝ) * h) - h * f (c₀ + ((0 : ℕ) : ℝ) * h)) := by
    have h1 := (hasSum_nat_add_iff' (f := fun n : ℕ => h * f (c₀ + (n : ℝ) * h)) 1).mpr hnat
    rw [Finset.sum_range_one] at h1
    have e : (fun n : ℕ => h * f (c₀ + (((n : ℤ) + 1 : ℤ) : ℝ) * h)) =
        fun n : ℕ => h * f (c₀ + ((n + 1 : ℕ) : ℝ) * h) := by
      funext n
      rw [show (((n : ℤ) + 1 : ℤ) : ℝ) = ((n + 1 : ℕ) : ℝ) by push_cast <;> ring]
    rw [e]
    exact h1
  have hneg : HasSum (fun n : ℕ => h * f (c₀ + ((-((n : ℤ) + 1) : ℤ) : ℝ) * h)) τL := by
    have e : (fun n : ℕ => h * f (c₀ + ((-((n : ℤ) + 1) : ℤ) : ℝ) * h)) =
        fun m : ℕ => h * f (_root_.GD.N0106.N0428.N0765.N1568.d005507 (c₀ - h) h m) := by
      funext n
      rw [show c₀ + ((-((n : ℤ) + 1) : ℤ) : ℝ) * h = _root_.GD.N0106.N0428.N0765.N1568.d005507 (c₀ - h) h n by
        unfold _root_.GD.N0106.N0428.N0765.N1568.d005507; push_cast; ring]
    rw [e]
    exact hL
  have hall := HasSum.of_add_one_of_neg_add_one
    (f := fun k : ℤ => h * f (c₀ + (k : ℝ) * h)) hpos hneg
  simp only [Nat.cast_zero, Int.cast_zero, zero_mul, add_zero] at hall
  convert hall using 1
  ring



theorem d005522 {f : ℝ → ℝ} {c₀ h τL τR : ℝ} {N : ℕ}
    (hf : ∀ c, 0 ≤ f c) (hh : 0 ≤ h)
    (hL : HasSum (fun m : ℕ => h * f (_root_.GD.N0106.N0428.N0765.N1568.d005507 (c₀ - h) h m)) τL)
    (hR : HasSum (fun m : ℕ => h * f (_root_.GD.N0106.N0428.N0765.N1568.d005508 (c₀ + N * h) h m)) τR) :
    (∑ i ∈ range N, h * f (c₀ + (i : ℝ) * h)) ≤ ∑' k : ℤ, h * f (c₀ + (k : ℝ) * h) ∧
      ∑' k : ℤ, h * f (c₀ + (k : ℝ) * h) ≤
        (∑ i ∈ range N, h * f (c₀ + (i : ℝ) * h)) + τR + τL := by
  have hall := _root_.GD.N0106.N0428.N0765.N1568.d005521 hL hR
  rw [hall.tsum_eq]
  have hτL : 0 ≤ τL :=
    hasSum_le (fun m => mul_nonneg hh (hf (_root_.GD.N0106.N0428.N0765.N1568.d005507 (c₀ - h) h m))) hasSum_zero hL
  have hτR : 0 ≤ τR :=
    hasSum_le (fun m => mul_nonneg hh (hf (_root_.GD.N0106.N0428.N0765.N1568.d005508 (c₀ + N * h) h m))) hasSum_zero hR
  constructor <;> linarith





theorem d005523 {I T S Sm Sp τ ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hrel : |I - T| ≤ ε * I) (hSm : Sm ≤ S) (hSp : S ≤ Sp)
    (hST : S ≤ T) (hTS : T ≤ S + τ) :
    Sm / (1 + ε) ≤ I ∧ I ≤ (Sp + τ) / (1 - ε) := by
  obtain ⟨h1, h2⟩ := abs_le.mp hrel
  constructor
  · rw [div_le_iff₀ (by linarith)]
    nlinarith
  · rw [le_div_iff₀ (by linarith)]
    nlinarith


theorem d005524 {I₀ I₁ l₀ u₀ l₁ u₁ : ℝ} (hl₀ : 0 < l₀) (hl₁ : 0 ≤ l₁)
    (h₀ : l₀ ≤ I₀ ∧ I₀ ≤ u₀) (h₁ : l₁ ≤ I₁ ∧ I₁ ≤ u₁) :
    l₁ / u₀ ≤ I₁ / I₀ ∧ I₁ / I₀ ≤ u₁ / l₀ := by
  have hI₀ : 0 < I₀ := lt_of_lt_of_le hl₀ h₀.1
  have hu₀ : 0 < u₀ := lt_of_lt_of_le hI₀ h₀.2
  constructor
  · calc l₁ / u₀ ≤ I₁ / u₀ := div_le_div_of_nonneg_right h₁.1 hu₀.le
      _ ≤ I₁ / I₀ := div_le_div_of_nonneg_left (hl₁.trans h₁.1) hI₀ h₀.2
  · calc I₁ / I₀ ≤ u₁ / I₀ := div_le_div_of_nonneg_right h₁.2 hI₀.le
      _ ≤ u₁ / l₀ := div_le_div_of_nonneg_left (hl₁.trans (h₁.1.trans h₁.2)) hl₀ h₀.1


theorem d005525 {f : ℝ → ℝ} {c₀ h I ε Sm Sp τL τR : ℝ} {N : ℕ}
    (hf : ∀ c, 0 ≤ f c) (hh : 0 ≤ h)
    (hL : Summable (fun m : ℕ => h * f (_root_.GD.N0106.N0428.N0765.N1568.d005507 (c₀ - h) h m)))
    (hLb : ∑' m : ℕ, h * f (_root_.GD.N0106.N0428.N0765.N1568.d005507 (c₀ - h) h m) ≤ τL)
    (hR : Summable (fun m : ℕ => h * f (_root_.GD.N0106.N0428.N0765.N1568.d005508 (c₀ + N * h) h m)))
    (hRb : ∑' m : ℕ, h * f (_root_.GD.N0106.N0428.N0765.N1568.d005508 (c₀ + N * h) h m) ≤ τR)
    (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hrel : |I - ∑' k : ℤ, h * f (c₀ + (k : ℝ) * h)| ≤ ε * I)
    (hSm : Sm ≤ ∑ i ∈ range N, h * f (c₀ + (i : ℝ) * h))
    (hSp : ∑ i ∈ range N, h * f (c₀ + (i : ℝ) * h) ≤ Sp) :
    Sm / (1 + ε) ≤ I ∧ I ≤ (Sp + (τL + τR)) / (1 - ε) := by
  obtain ⟨hST, hTS⟩ := _root_.GD.N0106.N0428.N0765.N1568.d005522 hf hh hL.hasSum hR.hasSum
  exact _root_.GD.N0106.N0428.N0765.N1568.d005523 hε hε1 hrel hSm hSp hST (hTS.trans (by linarith))

end
end GD.N0106.N0428.N0765.N1568

#print axioms _root_.GD.N0106.N0428.N0765.N1568.d005519
#print axioms _root_.GD.N0106.N0428.N0765.N1568.d005520
#print axioms _root_.GD.N0106.N0428.N0765.N1568.d005521
#print axioms _root_.GD.N0106.N0428.N0765.N1568.d005522
#print axioms _root_.GD.N0106.N0428.N0765.N1568.d005523
#print axioms _root_.GD.N0106.N0428.N0765.N1568.d005524
#print axioms _root_.GD.N0106.N0428.N0765.N1568.d005525
