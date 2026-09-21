import GD.Module1696
import GD.Module1480
import GD.Module0809

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped BigOperators

namespace GD.N0213.N0485
noncomputable section
open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0954
open _root_.GD.N0072
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0213.N0523 _root_.GD.N0213.N0517
open _root_.GD.N0101.N0411

variable {k : ℕ}

def d028566 (sizes : Fin k → ℕ) : Prop :=
  ¬ ∃ w : (Fin k → ℝ) → Fin k → ℝ,
    Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
    (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes)) ∧
    ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes)

theorem d028567 (sizes : Fin k → ℕ) (hn : ∀ i, 3 ≤ sizes i) (i : Fin k) :
    1 ≤ _root_.GD.N0232.N0719.N0954.d009355 sizes i := by
  have h : (2 : ℝ) ≤ ((sizes i - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ sizes i - 1 by have := hn i; omega)
  unfold _root_.GD.N0232.N0719.N0954.d009355
  linarith

theorem d028568 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 3 ≤ sizes i)
    (hbalance : ∀ i, n * (sizes i - 1) < ∑ j, (sizes j - 1)) :
    _root_.GD.N0213.N0517.d023248 (_root_.GD.N0232.N0719.N0954.d009355 sizes) := by
  have hsum : (n + 1 : ℝ) ≤ ∑ i, _root_.GD.N0232.N0719.N0954.d009355 sizes i := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] using
      (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
        _root_.GD.N0213.N0485.d028567 sizes hn i))
  refine ⟨?_, ?_⟩
  · simp only [Nat.cast_add, Nat.cast_one]
    linarith
  · intro i
    have h : (n : ℝ) * ((sizes i - 1 : ℕ) : ℝ) <
        ∑ j, ((sizes j - 1 : ℕ) : ℝ) := by exact_mod_cast (hbalance i)
    simp only [_root_.GD.N0232.N0719.N0954.d009355, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [← Finset.sum_div]
    linarith

theorem d028569 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hn : ∀ i, 3 ≤ sizes i)
    (hbalance : ∀ i, n * (sizes i - 1) < ∑ j, (sizes j - 1)) :
    _root_.GD.N0213.N0485.d028566 sizes := by
  have ha : ∀ i, 0 < _root_.GD.N0232.N0719.N0954.d009355 sizes i := fun i =>
    lt_of_lt_of_le zero_lt_one (_root_.GD.N0213.N0485.d028567 sizes hn i)
  have h := _root_.GD.N0213.N0517.d023250 (_root_.GD.N0232.N0719.N0954.d009355 sizes) ha
    (_root_.GD.N0213.N0485.d028568 sizes hn hbalance)
  exact _root_.GD.N0101.N0411.d028565 sizes hn
    (_root_.GD.N0213.N0523.d023154 (_root_.GD.N0232.N0719.N0954.d009355 sizes)) h.1 h.2.1 h.2.2

theorem d028570 {n m : ℕ} (hm : 3 ≤ m) :
    _root_.GD.N0213.N0485.d028566 (fun _ : Fin (n + 1) => m) := by
  apply _root_.GD.N0213.N0485.d028569 _ (fun _ => hm)
  intro i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : 0 < m - 1 := by omega
  nlinarith

theorem d028571 (sizes : Fin k → ℕ)
    (hn : ∀ i, 0 < sizes i) (h : _root_.GD.N0213.N0485.d028566 sizes) :
    ¬ ∃ w : (Fin k → ℝ) → Fin k → ℝ,
      Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) := by
  rintro ⟨w, hw, hunit, hweak, hstrict⟩
  apply h
  refine ⟨fun t => w (fun i => (sizes i : ℝ) * t i), by fun_prop,
    fun t => hunit _, ?_, ?_⟩
  · simpa only [_root_.GD.N0072.d023294 sizes hn w] using hweak
  · simpa only [_root_.GD.N0072.d023294 sizes hn w] using hstrict

def d028572 (sizes : Fin k → ℕ) : Prop :=
  ∃ g : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ,
    Measurable g ∧
    (∀ (b c : ℝ), 0 < c → ∀ s, g (_root_.GD.N0232.N0719.N0900.d009101 b c s) = b + c * g s) ∧
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (g ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes)

def d028573 (sizes : Fin k → ℕ) : Prop :=
  ∃ d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ,
    Measurable d ∧ ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes)

theorem d028574 (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0213.N0485.d028572 sizes := by
  let g := _root_.GD.N0232.N0719.N1018.d010022
    (_root_.GD.N0232.N0719.N1024.d010710 hk) (_root_.GD.N0232.N0719.N1024.d010727 k sizes hk)
  refine ⟨g, _root_.GD.N0232.N0719.N1018.d010045 _ _, ?_, ?_⟩
  · intro b c hc s
    exact _root_.GD.N0232.N0719.N1018.d010058 (by omega)
      (_root_.GD.N0232.N0719.N1024.d010710 hk) (_root_.GD.N0232.N0719.N1024.d010727 k sizes hk)
      b hc.ne' s
  · intro θ
    exact _root_.GD.N0232.N0719.N0970.d012329 k sizes hk hn θ

theorem d028575 (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0213.N0485.d028573 sizes := by
  exact ⟨_root_.GD.N0232.N0719.N0859.d010816 k sizes hk hn,
    _root_.GD.N0232.N0719.N1024.d010732 k sizes hk hn,
    _root_.GD.N0232.N0719.N0970.d012329 k sizes hk hn⟩

theorem d028576 {n : ℕ}
    (sizes : Fin (n + 1) → ℕ) (hk : 3 ≤ n + 1) (hn : ∀ i, 3 ≤ sizes i)
    (hbalance : ∀ i, n * (sizes i - 1) < ∑ j, (sizes j - 1)) :
    _root_.GD.N0213.N0485.d028566 sizes ∧
      _root_.GD.N0213.N0485.d028572 sizes ∧ _root_.GD.N0213.N0485.d028573 sizes := by
  exact ⟨_root_.GD.N0213.N0485.d028569 sizes hn hbalance,
    _root_.GD.N0213.N0485.d028574 sizes hk (fun i => by have := hn i; omega),
    _root_.GD.N0213.N0485.d028575 sizes hk (fun i => by have := hn i; omega)⟩

end
end GD.N0213.N0485

#print axioms _root_.GD.N0213.N0485.d028569
#print axioms _root_.GD.N0213.N0485.d028570
#print axioms _root_.GD.N0213.N0485.d028571
#print axioms _root_.GD.N0213.N0485.d028574
#print axioms _root_.GD.N0213.N0485.d028576
