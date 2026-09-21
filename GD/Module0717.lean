import GD.Module0701
import GD.Module0693
import Mathlib.MeasureTheory.Order.Lattice

















open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0232.N0719.N1003

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0852
open _root_.GD.N0232.N0719.N0875
open _root_.GD.N0137 _root_.GD.N0232.N0719.N1009 _root_.GD.N0232.N0719.N0933


def d010642
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) (i : Fin (n + 1)) : ℝ :=
  _root_.GD.N0232.N0719.N0875.d010340 (sizes i) i beta s


def d010643
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) (i : Fin (n + 1)) : ℝ :=
  _root_.GD.N0232.N0719.N0875.d010341 (sizes i) i beta s


def d010644
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (_root_.GD.N0232.N0719.N1003.d010642 sizes beta s)



def d010645
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) : ℝ :=
  -Finset.univ.sup' Finset.univ_nonempty
    (fun i => -_root_.GD.N0232.N0719.N1003.d010643 sizes beta s i)



def d010646 {n : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) : ℝ :=
  -Finset.univ.sup' Finset.univ_nonempty (fun i => -s.mean i)


def d010647
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) : ℝ :=
  if _root_.GD.N0232.N0719.N1003.d010644 sizes beta s ≤ _root_.GD.N0232.N0719.N1003.d010645 sizes beta s then
    _root_.GD.N0232.N0719.N1003.d010644 sizes beta s
  else _root_.GD.N0232.N0719.N1003.d010646 s


def d010648
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) : ℝ :=
  if _root_.GD.N0232.N0719.N1003.d010644 sizes beta s ≤ _root_.GD.N0232.N0719.N1003.d010645 sizes beta s then
    _root_.GD.N0232.N0719.N1003.d010645 sizes beta s
  else _root_.GD.N0232.N0719.N1003.d010646 s

theorem d010649
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) (i : Fin (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010642 sizes beta s i ≤ _root_.GD.N0232.N0719.N1003.d010644 sizes beta s := by
  exact Finset.le_sup' _ (Finset.mem_univ i)

theorem d010650
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) (i : Fin (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010645 sizes beta s ≤ _root_.GD.N0232.N0719.N1003.d010643 sizes beta s i := by
  have h := Finset.le_sup'
    (fun j : Fin (n + 1) => -_root_.GD.N0232.N0719.N1003.d010643 sizes beta s j)
    (Finset.mem_univ i)
  unfold _root_.GD.N0232.N0719.N1003.d010645
  linarith

theorem d010651
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta mu : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010644 sizes beta s ≤ mu ↔
      ∀ i, _root_.GD.N0232.N0719.N1003.d010642 sizes beta s i ≤ mu := by
  unfold _root_.GD.N0232.N0719.N1003.d010644
  constructor
  · intro h i
    exact (Finset.le_sup' _ (Finset.mem_univ i)).trans h
  · intro h
    exact Finset.sup'_le Finset.univ_nonempty _
      (fun i _ => h i)

theorem d010652
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta mu : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    mu ≤ _root_.GD.N0232.N0719.N1003.d010645 sizes beta s ↔
      ∀ i, mu ≤ _root_.GD.N0232.N0719.N1003.d010643 sizes beta s i := by
  unfold _root_.GD.N0232.N0719.N1003.d010645
  constructor
  · intro h i
    exact h.trans (_root_.GD.N0232.N0719.N1003.d010650 sizes beta s i)
  · intro h
    have hsup : Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin (n + 1) => -_root_.GD.N0232.N0719.N1003.d010643 sizes beta s i) ≤ -mu := by
      apply Finset.sup'_le Finset.univ_nonempty
      intro i _
      linarith [h i]
    linarith

theorem d010653
    {n : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    ∃ i, _root_.GD.N0232.N0719.N1003.d010646 s = s.mean i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty (fun i : Fin (n + 1) => -s.mean i)
  refine ⟨i, ?_⟩
  unfold _root_.GD.N0232.N0719.N1003.d010646
  linarith

theorem d010654
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010647 sizes beta s ≤ _root_.GD.N0232.N0719.N1003.d010648 sizes beta s := by
  unfold _root_.GD.N0232.N0719.N1003.d010647 _root_.GD.N0232.N0719.N1003.d010648
  split_ifs with h
  · exact h
  · exact le_rfl




theorem d010655
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta mu : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    (_root_.GD.N0232.N0719.N1003.d010647 sizes beta s ≤ mu ∧
        mu ≤ _root_.GD.N0232.N0719.N1003.d010648 sizes beta s) ↔
      (∀ i, _root_.GD.N0232.N0719.N1003.d010642 sizes beta s i ≤ mu ∧
        mu ≤ _root_.GD.N0232.N0719.N1003.d010643 sizes beta s i) ∨
      (_root_.GD.N0232.N0719.N1003.d010645 sizes beta s < _root_.GD.N0232.N0719.N1003.d010644 sizes beta s ∧
        _root_.GD.N0232.N0719.N1003.d010646 s = mu) := by
  by_cases hnonempty :
      _root_.GD.N0232.N0719.N1003.d010644 sizes beta s ≤ _root_.GD.N0232.N0719.N1003.d010645 sizes beta s
  · simp only [_root_.GD.N0232.N0719.N1003.d010647, _root_.GD.N0232.N0719.N1003.d010648, if_pos hnonempty]
    rw [_root_.GD.N0232.N0719.N1003.d010651, _root_.GD.N0232.N0719.N1003.d010652]
    constructor
    · rintro ⟨hlow, hupp⟩
      exact Or.inl (fun i => ⟨hlow i, hupp i⟩)
    · rintro (hall | himpossible)
      · exact ⟨fun i => (hall i).1, fun i => (hall i).2⟩
      · exact False.elim ((not_lt_of_ge hnonempty) himpossible.1)
  · have hempty : _root_.GD.N0232.N0719.N1003.d010645 sizes beta s <
        _root_.GD.N0232.N0719.N1003.d010644 sizes beta s := lt_of_not_ge hnonempty
    simp only [_root_.GD.N0232.N0719.N1003.d010647, _root_.GD.N0232.N0719.N1003.d010648, if_neg hnonempty]
    constructor
    · rintro ⟨hlow, hupp⟩
      have hcenter : _root_.GD.N0232.N0719.N1003.d010646 s = mu := le_antisymm hlow hupp
      exact Or.inr ⟨hempty, hcenter⟩
    · rintro (hall | hrepair)
      · have hL : _root_.GD.N0232.N0719.N1003.d010644 sizes beta s ≤ mu :=
          (_root_.GD.N0232.N0719.N1003.d010651 sizes beta mu s).2
            (fun i => (hall i).1)
        have hU : mu ≤ _root_.GD.N0232.N0719.N1003.d010645 sizes beta s :=
          (_root_.GD.N0232.N0719.N1003.d010652 sizes beta mu s).2
            (fun i => (hall i).2)
        exact False.elim ((not_lt_of_ge (hL.trans hU)) hempty)
      · rw [hrepair.2]
        exact ⟨le_rfl, le_rfl⟩

theorem d010656
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N1003.d010644 sizes beta) := by
  unfold _root_.GD.N0232.N0719.N1003.d010644 _root_.GD.N0232.N0719.N1003.d010642
  fun_prop

theorem d010657
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N1003.d010645 sizes beta) := by
  unfold _root_.GD.N0232.N0719.N1003.d010645 _root_.GD.N0232.N0719.N1003.d010643
  fun_prop

theorem d010658 {n : ℕ} :
    Measurable (_root_.GD.N0232.N0719.N1003.d010646 : _root_.GD.N0232.N0719.N0900.d009096 (n + 1) → ℝ) := by
  unfold _root_.GD.N0232.N0719.N1003.d010646
  fun_prop

theorem d010659
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N1003.d010647 sizes beta) := by
  unfold _root_.GD.N0232.N0719.N1003.d010647
  exact Measurable.ite
    (measurableSet_le
      (_root_.GD.N0232.N0719.N1003.d010656 sizes beta)
      (_root_.GD.N0232.N0719.N1003.d010657 sizes beta))
    (_root_.GD.N0232.N0719.N1003.d010656 sizes beta)
    _root_.GD.N0232.N0719.N1003.d010658

theorem d010660
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N1003.d010648 sizes beta) := by
  unfold _root_.GD.N0232.N0719.N1003.d010648
  exact Measurable.ite
    (measurableSet_le
      (_root_.GD.N0232.N0719.N1003.d010656 sizes beta)
      (_root_.GD.N0232.N0719.N1003.d010657 sizes beta))
    (_root_.GD.N0232.N0719.N1003.d010657 sizes beta)
    _root_.GD.N0232.N0719.N1003.d010658



theorem d010661
    {n : ℕ} (f : Fin (n + 1) → ℝ)
    (sigma : Equiv.Perm (Fin (n + 1))) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => f (sigma i)) =
      Finset.univ.sup' Finset.univ_nonempty f := by
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro i _
    exact Finset.le_sup' f (Finset.mem_univ (sigma i))
  · apply Finset.sup'_le Finset.univ_nonempty
    intro i _
    have h := Finset.le_sup' (fun j => f (sigma j))
      (Finset.mem_univ (sigma.symm i))
    simpa using h

theorem d010662
    {n : ℕ} (f : Fin (n + 1) → ℝ)
    (shift scale : ℝ) (hscale : 0 < scale) :
    Finset.univ.sup' Finset.univ_nonempty
        (fun i => shift + scale * f i) =
      shift + scale * Finset.univ.sup' Finset.univ_nonempty f := by
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro i _
    simpa [add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_left
        (Finset.le_sup' f (Finset.mem_univ i)) hscale.le) shift
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
      Finset.univ_nonempty f
    have h := Finset.le_sup' (fun j => shift + scale * f j)
      (Finset.mem_univ i)
    simpa [hi] using h

theorem d010663
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (sigma : Equiv.Perm (Fin (n + 1))) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) (i : Fin (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010642 (sizes ∘ sigma) beta (_root_.GD.N0232.N0719.N0852.d010153 sigma s) i =
      _root_.GD.N0232.N0719.N1003.d010642 sizes beta s (sigma i) := by
  simp [_root_.GD.N0232.N0719.N1003.d010642, _root_.GD.N0232.N0719.N0875.d010340, Function.comp_apply]

theorem d010664
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (sigma : Equiv.Perm (Fin (n + 1))) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) (i : Fin (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010643 (sizes ∘ sigma) beta (_root_.GD.N0232.N0719.N0852.d010153 sigma s) i =
      _root_.GD.N0232.N0719.N1003.d010643 sizes beta s (sigma i) := by
  simp [_root_.GD.N0232.N0719.N1003.d010643, _root_.GD.N0232.N0719.N0875.d010341, Function.comp_apply]

theorem d010665
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (sigma : Equiv.Perm (Fin (n + 1))) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010644 (sizes ∘ sigma) beta (_root_.GD.N0232.N0719.N0852.d010153 sigma s) =
      _root_.GD.N0232.N0719.N1003.d010644 sizes beta s := by
  unfold _root_.GD.N0232.N0719.N1003.d010644
  simp_rw [_root_.GD.N0232.N0719.N1003.d010663]
  exact _root_.GD.N0232.N0719.N1003.d010661 _ sigma

theorem d010666
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (sigma : Equiv.Perm (Fin (n + 1))) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010645 (sizes ∘ sigma) beta (_root_.GD.N0232.N0719.N0852.d010153 sigma s) =
      _root_.GD.N0232.N0719.N1003.d010645 sizes beta s := by
  unfold _root_.GD.N0232.N0719.N1003.d010645
  simp_rw [_root_.GD.N0232.N0719.N1003.d010664]
  congr 1
  exact _root_.GD.N0232.N0719.N1003.d010661
    (fun i => -_root_.GD.N0232.N0719.N1003.d010643 sizes beta s i) sigma

theorem d010667
    {n : ℕ} (sigma : Equiv.Perm (Fin (n + 1)))
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010646 (_root_.GD.N0232.N0719.N0852.d010153 sigma s) = _root_.GD.N0232.N0719.N1003.d010646 s := by
  unfold _root_.GD.N0232.N0719.N1003.d010646
  simp only [_root_.GD.N0232.N0719.N0852.d010154]
  congr 1
  exact _root_.GD.N0232.N0719.N1003.d010661 (fun i => -s.mean i) sigma



theorem d010668
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (sigma : Equiv.Perm (Fin (n + 1))) (beta : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010647 (sizes ∘ sigma) beta (_root_.GD.N0232.N0719.N0852.d010153 sigma s) =
        _root_.GD.N0232.N0719.N1003.d010647 sizes beta s ∧
      _root_.GD.N0232.N0719.N1003.d010648 (sizes ∘ sigma) beta (_root_.GD.N0232.N0719.N0852.d010153 sigma s) =
        _root_.GD.N0232.N0719.N1003.d010648 sizes beta s := by
  unfold _root_.GD.N0232.N0719.N1003.d010647 _root_.GD.N0232.N0719.N1003.d010648
  rw [_root_.GD.N0232.N0719.N1003.d010665, _root_.GD.N0232.N0719.N1003.d010666,
    _root_.GD.N0232.N0719.N1003.d010667]
  exact ⟨rfl, rfl⟩

theorem d010669
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta shift : ℝ)
    {scale : ℝ} (hscale : 0 < scale)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) (i : Fin (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010642 sizes beta (_root_.GD.N0232.N0719.N0900.d009101 shift scale s) i =
      shift + scale * _root_.GD.N0232.N0719.N1003.d010642 sizes beta s i := by
  have hsqrt :
      Real.sqrt (scale ^ 2 * s.meanVariance i) =
        scale * Real.sqrt (s.meanVariance i) := by
    rw [Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq_eq_abs,
      abs_of_pos hscale]
  unfold _root_.GD.N0232.N0719.N1003.d010642 _root_.GD.N0232.N0719.N0875.d010340 _root_.GD.N0232.N0719.N0900.d009101
  simp only [hsqrt]
  ring

theorem d010670
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta shift : ℝ)
    {scale : ℝ} (hscale : 0 < scale)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) (i : Fin (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010643 sizes beta (_root_.GD.N0232.N0719.N0900.d009101 shift scale s) i =
      shift + scale * _root_.GD.N0232.N0719.N1003.d010643 sizes beta s i := by
  have hsqrt :
      Real.sqrt (scale ^ 2 * s.meanVariance i) =
        scale * Real.sqrt (s.meanVariance i) := by
    rw [Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq_eq_abs,
      abs_of_pos hscale]
  unfold _root_.GD.N0232.N0719.N1003.d010643 _root_.GD.N0232.N0719.N0875.d010341 _root_.GD.N0232.N0719.N0900.d009101
  simp only [hsqrt]
  ring

theorem d010671
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta shift : ℝ)
    {scale : ℝ} (hscale : 0 < scale)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010644 sizes beta (_root_.GD.N0232.N0719.N0900.d009101 shift scale s) =
      shift + scale * _root_.GD.N0232.N0719.N1003.d010644 sizes beta s := by
  unfold _root_.GD.N0232.N0719.N1003.d010644
  simp_rw [_root_.GD.N0232.N0719.N1003.d010669 sizes beta shift hscale s]
  exact _root_.GD.N0232.N0719.N1003.d010662 _ shift scale hscale

theorem d010672
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta shift : ℝ)
    {scale : ℝ} (hscale : 0 < scale)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010645 sizes beta (_root_.GD.N0232.N0719.N0900.d009101 shift scale s) =
      shift + scale * _root_.GD.N0232.N0719.N1003.d010645 sizes beta s := by
  unfold _root_.GD.N0232.N0719.N1003.d010645
  simp_rw [_root_.GD.N0232.N0719.N1003.d010670 sizes beta shift hscale s]
  have hsup := _root_.GD.N0232.N0719.N1003.d010662
    (fun i : Fin (n + 1) => -_root_.GD.N0232.N0719.N1003.d010643 sizes beta s i)
    (-shift) scale hscale
  have heq :
      Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (n + 1) => -(shift + scale *
            _root_.GD.N0232.N0719.N1003.d010643 sizes beta s i)) =
        -shift + scale * Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (n + 1) => -_root_.GD.N0232.N0719.N1003.d010643 sizes beta s i) := by
    have hfun :
        (fun i : Fin (n + 1) => -(shift + scale *
          _root_.GD.N0232.N0719.N1003.d010643 sizes beta s i)) =
          fun i => -shift + scale * (-_root_.GD.N0232.N0719.N1003.d010643 sizes beta s i) := by
      funext i
      ring
    rw [hfun]
    exact hsup
  rw [heq]
  ring

theorem d010673
    {n : ℕ} (shift : ℝ) {scale : ℝ} (hscale : 0 < scale)
    (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010646 (_root_.GD.N0232.N0719.N0900.d009101 shift scale s) =
      shift + scale * _root_.GD.N0232.N0719.N1003.d010646 s := by
  unfold _root_.GD.N0232.N0719.N1003.d010646 _root_.GD.N0232.N0719.N0900.d009101
  simp only
  have hsup := _root_.GD.N0232.N0719.N1003.d010662
    (fun i : Fin (n + 1) => -s.mean i) (-shift) scale hscale
  have heq :
      Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (n + 1) => -(shift + scale * s.mean i)) =
        -shift + scale * Finset.univ.sup' Finset.univ_nonempty
          (fun i : Fin (n + 1) => -s.mean i) := by
    have hfun :
        (fun i : Fin (n + 1) => -(shift + scale * s.mean i)) =
          fun i => -shift + scale * (-s.mean i) := by
      funext i
      ring
    rw [hfun]
    exact hsup
  rw [heq]
  ring



theorem d010674
    {n : ℕ} (sizes : Fin (n + 1) → ℕ) (beta shift : ℝ)
    {scale : ℝ} (hscale : 0 < scale) (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)) :
    _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0900.d009101 shift scale s) =
        shift + scale * _root_.GD.N0232.N0719.N1003.d010647 sizes beta s ∧
      _root_.GD.N0232.N0719.N1003.d010648 sizes beta (_root_.GD.N0232.N0719.N0900.d009101 shift scale s) =
        shift + scale * _root_.GD.N0232.N0719.N1003.d010648 sizes beta s := by
  have hL := _root_.GD.N0232.N0719.N1003.d010671
    sizes beta shift hscale s
  have hU := _root_.GD.N0232.N0719.N1003.d010672
    sizes beta shift hscale s
  have hC := _root_.GD.N0232.N0719.N1003.d010673 shift hscale s
  have hbranch :
      (_root_.GD.N0232.N0719.N1003.d010644 sizes beta (_root_.GD.N0232.N0719.N0900.d009101 shift scale s) ≤
          _root_.GD.N0232.N0719.N1003.d010645 sizes beta (_root_.GD.N0232.N0719.N0900.d009101 shift scale s)) ↔
        _root_.GD.N0232.N0719.N1003.d010644 sizes beta s ≤ _root_.GD.N0232.N0719.N1003.d010645 sizes beta s := by
    rw [hL, hU]
    exact (add_le_add_iff_left shift).trans
      (mul_le_mul_iff_of_pos_left hscale)
  by_cases h : _root_.GD.N0232.N0719.N1003.d010644 sizes beta s ≤ _root_.GD.N0232.N0719.N1003.d010645 sizes beta s
  · have ht := hbranch.2 h
    constructor
    · unfold _root_.GD.N0232.N0719.N1003.d010647
      rw [if_pos ht, if_pos h, hL]
    · unfold _root_.GD.N0232.N0719.N1003.d010648
      rw [if_pos ht, if_pos h, hU]
  · have ht : ¬ _root_.GD.N0232.N0719.N1003.d010644 sizes beta (_root_.GD.N0232.N0719.N0900.d009101 shift scale s) ≤
        _root_.GD.N0232.N0719.N1003.d010645 sizes beta (_root_.GD.N0232.N0719.N0900.d009101 shift scale s) :=
      fun htransformed => h (hbranch.1 htransformed)
    constructor
    · unfold _root_.GD.N0232.N0719.N1003.d010647
      rw [if_neg ht, if_neg h, hC]
    · unfold _root_.GD.N0232.N0719.N1003.d010648
      rw [if_neg ht, if_neg h, hC]





def d010675
    (n : ℕ) (location beta : ℝ) : Set (_root_.GD.N0137.d008894 n) :=
  {x | _root_.GD.N0232.N0719.N0875.d010329 location (_root_.GD.N0232.N0719.N1009.d009272 n x) ∈
    Set.Icc (_root_.GD.N0232.N0719.N0875.d010338 n beta) (_root_.GD.N0232.N0719.N0875.d010339 n beta)}

theorem d010676
    (n : ℕ) (location beta : ℝ) :
    MeasurableSet (_root_.GD.N0232.N0719.N1003.d010675 n location beta) := by
  exact measurableSet_Icc.preimage
    ((_root_.GD.N0232.N0719.N0875.d010330 location).comp
      (_root_.GD.N0232.N0719.N1009.d009277 n))



theorem d010677
    {n : ℕ} (hn : 2 ≤ n) {beta : ℝ}
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (location : ℝ) {scale : ℝ} (hscale : 0 < scale) :
    _root_.GD.N0232.N0719.d009175 n location scale (_root_.GD.N0232.N0719.N1003.d010675 n location beta) =
      ENNReal.ofReal (1 - beta) := by
  let f : _root_.GD.N0137.d008894 n → ℝ :=
    _root_.GD.N0232.N0719.N0875.d010329 location ∘ _root_.GD.N0232.N0719.N1009.d009272 n
  have hf : Measurable f :=
    (_root_.GD.N0232.N0719.N0875.d010330 location).comp
      (_root_.GD.N0232.N0719.N1009.d009277 n)
  have hmap : (_root_.GD.N0232.N0719.d009175 n location scale).map f =
      _root_.GD.N0232.N0719.N0875.d010321 n := by
    calc
      (_root_.GD.N0232.N0719.d009175 n location scale).map f =
          ((_root_.GD.N0232.N0719.d009175 n location scale).map (_root_.GD.N0232.N0719.N1009.d009272 n)).map
            (_root_.GD.N0232.N0719.N0875.d010329 location) := by
              rw [Measure.map_map
                (_root_.GD.N0232.N0719.N0875.d010330 location)
                (_root_.GD.N0232.N0719.N1009.d009277 n)]
      _ = (_root_.GD.N0232.N0719.N1009.d009276 n location scale).map
            (_root_.GD.N0232.N0719.N0875.d010329 location) := by
              rw [_root_.GD.N0232.N0719.N1009.d009281 hn location scale]
      _ = _root_.GD.N0232.N0719.N0875.d010321 n :=
        _root_.GD.N0232.N0719.N0875.d010332 hn location hscale
  calc
    _root_.GD.N0232.N0719.d009175 n location scale (_root_.GD.N0232.N0719.N1003.d010675 n location beta) =
        ((_root_.GD.N0232.N0719.d009175 n location scale).map f)
          (Set.Icc (_root_.GD.N0232.N0719.N0875.d010338 n beta) (_root_.GD.N0232.N0719.N0875.d010339 n beta)) := by
            rw [Measure.map_apply hf measurableSet_Icc]
            rfl
    _ = _root_.GD.N0232.N0719.N0875.d010321 n
          (Set.Icc (_root_.GD.N0232.N0719.N0875.d010338 n beta) (_root_.GD.N0232.N0719.N0875.d010339 n beta)) := by
            rw [hmap]
    _ = ENNReal.ofReal (1 - beta) :=
      _root_.GD.N0232.N0719.N0875.d010348 hn hb0 hb1



def d010678
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (location beta : ℝ) : Set (_root_.GD.N0232.N0719.d009173 (n + 1) sizes) :=
  Set.pi Set.univ
    (fun i => _root_.GD.N0232.N0719.N1003.d010675 (sizes i) location beta)

theorem d010679
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) {beta : ℝ}
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
        (_root_.GD.N0232.N0719.N1003.d010678 sizes location beta) =
      ∏ _i : Fin (n + 1), ENNReal.ofReal (1 - beta) := by
  unfold _root_.GD.N0232.N0719.d009176 _root_.GD.N0232.N0719.N1003.d010678
  rw [Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  exact _root_.GD.N0232.N0719.N1003.d010677 (hsizes i) hb0 hb1
    location (hscales i)



theorem d010680
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) {beta : ℝ}
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
        {omega | ∀ i,
          _root_.GD.N0232.N0719.N1003.d010642 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) i ≤
              location ∧
            location ≤ _root_.GD.N0232.N0719.N1003.d010643 sizes beta
              (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) i} =
      ∏ _i : Fin (n + 1), ENNReal.ofReal (1 - beta) := by
  let mu := _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
  have hpos := _root_.GD.N0232.N0719.N0875.d010352
    sizes hsizes location scales hscales
  calc
    mu {omega | ∀ i,
          _root_.GD.N0232.N0719.N1003.d010642 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) i ≤
              location ∧
            location ≤ _root_.GD.N0232.N0719.N1003.d010643 sizes beta
              (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) i} =
        mu (_root_.GD.N0232.N0719.N1003.d010678 sizes location beta) := by
          apply measure_congr
          filter_upwards [hpos] with omega homega
          apply propext
          constructor
          · intro hall i _
            change _root_.GD.N0232.N0719.N0875.d010329 location
                (_root_.GD.N0232.N0719.N1009.d009272 (sizes i) (omega i)) ∈
              Set.Icc (_root_.GD.N0232.N0719.N0875.d010338 (sizes i) beta)
                (_root_.GD.N0232.N0719.N0875.d010339 (sizes i) beta)
            exact (_root_.GD.N0232.N0719.N0875.d010351 (homega i)).1 (hall i)
          · intro hrectangle i
            have hi := hrectangle i (Set.mem_univ i)
            change _root_.GD.N0232.N0719.N0875.d010329 location
                (_root_.GD.N0232.N0719.N1009.d009272 (sizes i) (omega i)) ∈
              Set.Icc (_root_.GD.N0232.N0719.N0875.d010338 (sizes i) beta)
                (_root_.GD.N0232.N0719.N0875.d010339 (sizes i) beta) at hi
            exact (_root_.GD.N0232.N0719.N0875.d010351 (homega i)).2 hi
    _ = ∏ i : Fin (n + 1), ENNReal.ofReal (1 - beta) :=
      _root_.GD.N0232.N0719.N1003.d010679 sizes hsizes hb0 hb1
        location scales hscales





theorem d010681
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) (i : Fin (n + 1))
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
        {omega | (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega).mean i = location} = 0 := by
  let mu := _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
  let f := _root_.GD.N0232.N0719.N0875.d010333 i ∘ _root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes
  have hf : Measurable f :=
    (_root_.GD.N0232.N0719.N0875.d010334 i).comp
      (_root_.GD.N0232.N0719.N0900.d009115 (n + 1) sizes)
  have hmap : mu.map f =
      _root_.GD.N0232.N0719.N1009.d009276 (sizes i) location (scales i) :=
    _root_.GD.N0232.N0719.N0875.d010336 sizes hsizes i location scales
  have hnpos : 0 < sizes i :=
    lt_of_lt_of_le (by decide : 0 < 2) (hsizes i)
  have hvariance : scales i ^ 2 / (sizes i : ℝ) ≠ 0 := by
    exact div_ne_zero (pow_ne_zero 2 (hscales i).ne')
      (Nat.cast_ne_zero.mpr hnpos.ne')
  letI : NoAtoms (_root_.GD.N0232.N0719.N0933.d009288 (sizes i) location (scales i)) := by
    rw [_root_.GD.N0232.N0719.N0933.d009297 hnpos]
    exact noAtoms_gaussianReal (by
      intro hzero
      have := congrArg (fun q : ℝ≥0 => (q : ℝ)) hzero
      exact hvariance this)
  let A : Set (ℝ × ℝ) := ({location} : Set ℝ) ×ˢ Set.univ
  calc
    mu {omega | (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega).mean i = location} =
        mu (f ⁻¹' A) := by
          congr 1
          ext omega
          simp [f, A, _root_.GD.N0232.N0719.N0875.d010333]
    _ = (mu.map f) A := by
          rw [Measure.map_apply hf]
          exact (measurableSet_singleton location).prod MeasurableSet.univ
    _ = _root_.GD.N0232.N0719.N1009.d009276 (sizes i) location (scales i) A := by
          rw [hmap]
    _ = 0 := by
          rw [_root_.GD.N0232.N0719.N0933.d009298, Measure.prod_prod]
          simp



theorem d010682
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
        {omega | _root_.GD.N0232.N0719.N1003.d010646 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = location} =
      0 := by
  let mu := _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
  let E : Fin (n + 1) → Set (_root_.GD.N0232.N0719.d009173 (n + 1) sizes) :=
    fun i => {omega |
      (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega).mean i = location}
  have hnullUnion : mu (⋃ i, E i) = 0 := by
    apply measure_iUnion_null
    intro i
    exact _root_.GD.N0232.N0719.N1003.d010681 sizes hsizes i
      location scales hscales
  apply measure_mono_null (t := ⋃ i, E i) _ hnullUnion
  intro omega homega
  obtain ⟨i, hi⟩ :=
    _root_.GD.N0232.N0719.N1003.d010653 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)
  exact Set.mem_iUnion.mpr ⟨i, by
    change (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega).mean i = location
    rw [← hi]
    exact homega⟩



theorem d010683
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) {beta : ℝ}
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
        {omega |
          _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ≤
              location ∧
            location ≤ _root_.GD.N0232.N0719.N1003.d010648 sizes beta
              (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)} =
      ∏ _i : Fin (n + 1), ENNReal.ofReal (1 - beta) := by
  let mu := _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
  have hcenter : ∀ᵐ omega ∂mu,
      _root_.GD.N0232.N0719.N1003.d010646 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ≠ location := by
    rw [ae_iff]
    simpa only [mem_setOf_eq, Classical.not_not] using
      _root_.GD.N0232.N0719.N1003.d010682 sizes hsizes
        location scales hscales
  calc
    mu {omega |
          _root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ≤
              location ∧
            location ≤ _root_.GD.N0232.N0719.N1003.d010648 sizes beta
              (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)} =
        mu {omega | ∀ i,
          _root_.GD.N0232.N0719.N1003.d010642 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) i ≤
              location ∧
            location ≤ _root_.GD.N0232.N0719.N1003.d010643 sizes beta
              (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) i} := by
          apply measure_congr
          filter_upwards [hcenter] with omega homega
          apply propext
          change
            (_root_.GD.N0232.N0719.N1003.d010647 sizes beta (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ≤
                location ∧
              location ≤ _root_.GD.N0232.N0719.N1003.d010648 sizes beta
                (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) ↔
              ∀ i,
                _root_.GD.N0232.N0719.N1003.d010642 sizes beta
                    (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) i ≤ location ∧
                  location ≤ _root_.GD.N0232.N0719.N1003.d010643 sizes beta
                    (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) i
          rw [_root_.GD.N0232.N0719.N1003.d010655]
          simp [homega]
    _ = ∏ _i : Fin (n + 1), ENNReal.ofReal (1 - beta) :=
      _root_.GD.N0232.N0719.N1003.d010680 sizes hsizes hb0 hb1
        location scales hscales





def d010684 (n : ℕ) (alpha : ℝ) : ℝ :=
  Real.rpow (1 - alpha) (((n + 1 : ℕ) : ℝ)⁻¹)


def d010685 (n : ℕ) (alpha : ℝ) : ℝ :=
  1 - _root_.GD.N0232.N0719.N1003.d010684 n alpha

theorem d010686
    (n : ℕ) {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    0 < _root_.GD.N0232.N0719.N1003.d010684 n alpha ∧ _root_.GD.N0232.N0719.N1003.d010684 n alpha < 1 := by
  have hbase0 : 0 < 1 - alpha := by linarith
  have hbase1 : 1 - alpha < 1 := by linarith
  have hexponent : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := by positivity
  constructor
  · exact Real.rpow_pos_of_pos hbase0 _
  · exact Real.rpow_lt_one hbase0.le hbase1 hexponent

theorem d010687
    (n : ℕ) {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    _root_.GD.N0232.N0719.N1003.d010685 n alpha ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨hq0, hq1⟩ := _root_.GD.N0232.N0719.N1003.d010686 n ha0 ha1
  constructor <;> unfold _root_.GD.N0232.N0719.N1003.d010685 <;> linarith

theorem d010688
    (n : ℕ) {alpha : ℝ} (_ha0 : 0 < alpha) (ha1 : alpha < 1) :
    _root_.GD.N0232.N0719.N1003.d010684 n alpha ^ (n + 1) = 1 - alpha := by
  have hbase0 : 0 ≤ 1 - alpha := by linarith
  unfold _root_.GD.N0232.N0719.N1003.d010684
  simpa using
    (Real.rpow_inv_natCast_pow hbase0 (Nat.succ_ne_zero n))

theorem d010689
    (n : ℕ) {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    (∏ _i : Fin (n + 1),
        ENNReal.ofReal (1 - _root_.GD.N0232.N0719.N1003.d010685 n alpha)) =
      ENNReal.ofReal (1 - alpha) := by
  have hpow := _root_.GD.N0232.N0719.N1003.d010688 n ha0 ha1
  simp only [_root_.GD.N0232.N0719.N1003.d010685, sub_sub_cancel,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow]
  · rw [hpow]
  · exact (_root_.GD.N0232.N0719.N1003.d010686 n ha0 ha1).1.le







theorem d010690
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) {alpha : ℝ}
    (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
        {omega |
          _root_.GD.N0232.N0719.N1003.d010647 sizes (_root_.GD.N0232.N0719.N1003.d010685 n alpha)
                (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ≤ location ∧
            location ≤
              _root_.GD.N0232.N0719.N1003.d010648 sizes (_root_.GD.N0232.N0719.N1003.d010685 n alpha)
                (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)} =
      ENNReal.ofReal (1 - alpha) := by
  obtain ⟨hb0, hb1⟩ :=
    _root_.GD.N0232.N0719.N1003.d010687 n ha0 ha1
  rw [_root_.GD.N0232.N0719.N1003.d010683 sizes hsizes hb0 hb1
    location scales hscales]
  exact _root_.GD.N0232.N0719.N1003.d010689 n ha0 ha1





theorem d010691
    {n : ℕ} (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) {alpha : ℝ}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    Measurable
        (_root_.GD.N0232.N0719.N1003.d010647 sizes (_root_.GD.N0232.N0719.N1003.d010685 n alpha)) ∧
      Measurable
        (_root_.GD.N0232.N0719.N1003.d010648 sizes (_root_.GD.N0232.N0719.N1003.d010685 n alpha)) ∧
      (∀ s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1),
        _root_.GD.N0232.N0719.N1003.d010647 sizes (_root_.GD.N0232.N0719.N1003.d010685 n alpha) s ≤
          _root_.GD.N0232.N0719.N1003.d010648 sizes (_root_.GD.N0232.N0719.N1003.d010685 n alpha) s) ∧
      (∀ (location : ℝ) (scales : Fin (n + 1) → ℝ),
        (∀ i, 0 < scales i) →
        _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
            {omega |
              _root_.GD.N0232.N0719.N1003.d010647 sizes (_root_.GD.N0232.N0719.N1003.d010685 n alpha)
                    (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ≤ location ∧
                location ≤ _root_.GD.N0232.N0719.N1003.d010648 sizes
                  (_root_.GD.N0232.N0719.N1003.d010685 n alpha)
                    (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)} =
          ENNReal.ofReal (1 - alpha)) ∧
      (∀ (sigma : Equiv.Perm (Fin (n + 1))) (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1)),
        _root_.GD.N0232.N0719.N1003.d010647 (sizes ∘ sigma)
              (_root_.GD.N0232.N0719.N1003.d010685 n alpha)
              (_root_.GD.N0232.N0719.N0852.d010153 sigma s) =
            _root_.GD.N0232.N0719.N1003.d010647 sizes (_root_.GD.N0232.N0719.N1003.d010685 n alpha) s ∧
          _root_.GD.N0232.N0719.N1003.d010648 (sizes ∘ sigma)
              (_root_.GD.N0232.N0719.N1003.d010685 n alpha)
              (_root_.GD.N0232.N0719.N0852.d010153 sigma s) =
            _root_.GD.N0232.N0719.N1003.d010648 sizes (_root_.GD.N0232.N0719.N1003.d010685 n alpha) s) ∧
      (∀ (shift : ℝ) {scale : ℝ}, 0 < scale →
        ∀ s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1),
          _root_.GD.N0232.N0719.N1003.d010647 sizes (_root_.GD.N0232.N0719.N1003.d010685 n alpha)
                (_root_.GD.N0232.N0719.N0900.d009101 shift scale s) =
              shift + scale * _root_.GD.N0232.N0719.N1003.d010647 sizes
                (_root_.GD.N0232.N0719.N1003.d010685 n alpha) s ∧
            _root_.GD.N0232.N0719.N1003.d010648 sizes (_root_.GD.N0232.N0719.N1003.d010685 n alpha)
                (_root_.GD.N0232.N0719.N0900.d009101 shift scale s) =
              shift + scale * _root_.GD.N0232.N0719.N1003.d010648 sizes
                (_root_.GD.N0232.N0719.N1003.d010685 n alpha) s) := by
  refine ⟨_root_.GD.N0232.N0719.N1003.d010659 _ _, _root_.GD.N0232.N0719.N1003.d010660 _ _,
    _root_.GD.N0232.N0719.N1003.d010654 _ _, ?_, ?_, ?_⟩
  · intro location scales hscales
    exact _root_.GD.N0232.N0719.N1003.d010690 sizes hsizes ha0 ha1
      location scales hscales
  · intro sigma s
    exact _root_.GD.N0232.N0719.N1003.d010668 sizes sigma _ s
  · intro shift scale hscale s
    exact _root_.GD.N0232.N0719.N1003.d010674 sizes _ shift hscale s

#print axioms _root_.GD.N0232.N0719.N1003.d010654
#print axioms _root_.GD.N0232.N0719.N1003.d010655
#print axioms _root_.GD.N0232.N0719.N1003.d010659
#print axioms _root_.GD.N0232.N0719.N1003.d010660
#print axioms _root_.GD.N0232.N0719.N1003.d010668
#print axioms _root_.GD.N0232.N0719.N1003.d010674
#print axioms _root_.GD.N0232.N0719.N1003.d010690
#print axioms _root_.GD.N0232.N0719.N1003.d010691

end

end GD.N0232.N0719.N1003
