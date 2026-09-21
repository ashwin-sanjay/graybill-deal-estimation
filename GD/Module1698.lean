import GD.Module1697
import GD.Module1481
import GD.Module1505

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped BigOperators

namespace GD.N0213.N0486
noncomputable section
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0072 _root_.GD.N0021
open _root_.GD.N0213.N0523 _root_.GD.N0213.N0517 _root_.GD.N0213.N0482
open _root_.GD.N0213.N0485
open _root_.GD.N0101.N0411

def d028577 {n : ℕ} (sizes : Fin (n + 1) → ℕ) : Prop :=
  2 * n < ∑ i, (sizes i - 1) ∧
    ∀ i, n * (sizes i - 1) < ∑ j, (sizes j - 1)

theorem d028578 (t α : ℝ) (ht : t ≠ 0) :
    _root_.GD.N0213.N0523.d023144 (t * (1 - α)) (1 / t) = 1 + (t - 1) * (1 - α) := by
  unfold _root_.GD.N0213.N0523.d023144
  field_simp
  ring

theorem d028579 {n : ℕ} (sizes : Fin (n + 1) → ℕ) :
    _root_.GD.N0213.N0517.d023248 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ↔ _root_.GD.N0213.N0486.d028577 sizes := by
  have hsum : (∑ i, _root_.GD.N0232.N0719.N0954.d009355 sizes i) =
      ((∑ i, (sizes i - 1) : ℕ) : ℝ) / 2 := by
    simp only [_root_.GD.N0232.N0719.N0954.d009355, Nat.cast_sum, Finset.sum_div]
  unfold _root_.GD.N0213.N0517.d023248 _root_.GD.N0213.N0486.d028577
  rw [hsum]
  simp only [_root_.GD.N0232.N0719.N0954.d009355,
    Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  constructor
  · rintro ⟨hA, hi⟩
    constructor
    · have h : (2 : ℝ) * n < ((∑ i, (sizes i - 1) : ℕ) : ℝ) := by linarith
      exact_mod_cast h
    · intro i
      have h : (n : ℝ) * ((sizes i - 1 : ℕ) : ℝ) <
          ((∑ j, (sizes j - 1) : ℕ) : ℝ) := by linarith [hi i]
      exact_mod_cast h
  · rintro ⟨hA, hi⟩
    constructor
    · have h : (2 : ℝ) * n < ((∑ i, (sizes i - 1) : ℕ) : ℝ) := by exact_mod_cast hA
      linarith
    · intro i
      have h : (n : ℝ) * ((sizes i - 1 : ℕ) : ℝ) <
          ((∑ j, (sizes j - 1) : ℕ) : ℝ) := by exact_mod_cast hi i
      linarith

theorem d028580 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    (∃ ρ : ℝ, ρ < 1 ∧ (∀ i, 0 < 1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) ∧
      ∑ i, (1 - ρ * _root_.GD.N0232.N0719.N0954.d009355 sizes i) = 1) ↔ _root_.GD.N0213.N0486.d028577 sizes := by
  rw [_root_.GD.N0213.N0482.d023263 _ (_root_.GD.N0232.N0719.N0954.d009358 hn), _root_.GD.N0213.N0486.d028579]

theorem d028581 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hcone : _root_.GD.N0213.N0486.d028577 sizes) : _root_.GD.N0213.N0485.d028566 sizes := by
  obtain ⟨ρ, hρ, hα, hsum⟩ := (_root_.GD.N0213.N0486.d028580 sizes hn).mpr hcone
  unfold _root_.GD.N0213.N0485.d028566
  rw [_root_.GD.N0021.d023315]
  exact _root_.GD.N0101.N0356.d023492
    sizes hn ρ hρ hα hsum _root_.GD.N0021.d023313 _root_.GD.N0021.d023314
    (_root_.GD.N0101.N0411.d028560 (Nat.succ_pos _)) (_root_.GD.N0101.N0411.d028561 (Nat.succ_pos _))
    _root_.GD.N0101.N0411.d028562

theorem d028582 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hk : 3 ≤ n + 1) (hn : ∀ i, 2 ≤ sizes i)
    (hcone : _root_.GD.N0213.N0486.d028577 sizes) :
    _root_.GD.N0213.N0485.d028566 sizes ∧ _root_.GD.N0213.N0485.d028572 sizes ∧
      _root_.GD.N0213.N0485.d028573 sizes :=
  ⟨_root_.GD.N0213.N0486.d028581 sizes hn hcone,
    _root_.GD.N0213.N0485.d028574 sizes hk hn,
    _root_.GD.N0213.N0485.d028575 sizes hk hn⟩

theorem d028583 (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0213.N0486.d028577 sizes ↔ 3 ≤ sizes 0 ∨ 3 ≤ sizes 1 := by
  have h0 := hn 0
  have h1 := hn 1
  have hsum : (∑ i : Fin 2, (sizes i - 1)) = (sizes 0 - 1) + (sizes 1 - 1) :=
    Fin.sum_univ_two _
  unfold _root_.GD.N0213.N0486.d028577
  rw [hsum]
  norm_num only [Nat.reduceAdd, Nat.reduceMul, one_mul]
  constructor
  · intro h
    omega
  · intro h
    refine ⟨by omega, ?_⟩
    intro i
    fin_cases i <;> dsimp <;> omega

theorem d028584 (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hlarge : 3 ≤ sizes 0 ∨ 3 ≤ sizes 1) : _root_.GD.N0213.N0485.d028566 sizes :=
  _root_.GD.N0213.N0486.d028581 sizes hn ((_root_.GD.N0213.N0486.d028583 sizes hn).mpr hlarge)

theorem d028585 {n m : ℕ} (hm : 3 ≤ m) :
    _root_.GD.N0213.N0486.d028577 (Fin.cons 2 (fun _ : Fin n => m)) := by
  have hm0 : 0 < m - 1 := by omega
  have hm2 : 2 ≤ m - 1 := by omega
  have hsum : (∑ i : Fin (n + 1), (Fin.cons 2 (fun _ : Fin n => m) i - 1)) =
      1 + n * (m - 1) := by
    simp [Fin.sum_univ_succ]
  unfold _root_.GD.N0213.N0486.d028577
  rw [hsum]
  constructor
  · nlinarith
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero, Nat.reduceSub, mul_one]
      nlinarith
    · simp only [Fin.cons_succ]
      omega

theorem d028586 {n m : ℕ} (hm : 3 ≤ m) :
    _root_.GD.N0213.N0485.d028566 (Fin.cons 2 (fun _ : Fin n => m)) := by
  apply _root_.GD.N0213.N0486.d028581 _ _ (_root_.GD.N0213.N0486.d028585 hm)
  intro i
  refine Fin.cases (by norm_num) (fun _ => ?_) i
  simpa only [Fin.cons_succ] using (show 2 ≤ m by omega)

end
end GD.N0213.N0486

#print axioms _root_.GD.N0213.N0486.d028580
#print axioms _root_.GD.N0213.N0486.d028581
#print axioms _root_.GD.N0213.N0486.d028582
#print axioms _root_.GD.N0213.N0486.d028583
#print axioms _root_.GD.N0213.N0486.d028584
#print axioms _root_.GD.N0213.N0486.d028586
#print axioms _root_.GD.N0213.N0486.d028578
