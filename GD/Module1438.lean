import GD.Module1287
import GD.Module1298
import GD.Module0379


















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace GD.N0106.N0428.N0765.N1609

noncomputable section

open _root_.GD.N0106.N0428.N0765.N1611 _root_.GD.N0106.N0428.N0765.N1607 _root_.GD.N0106.N0428.N0765.N1610 _root_.GD.N0106.N0428.N0765.N1529 _root_.GD.N0106.N0428.N0765.N1627
open _root_.GD.N0232.N0720.N1249
open _root_.GD.N0106.N0428.N0765.N1603 _root_.GD.N0106.N0428.N0765.N1604 _root_.GD.N0106.N0428.N0765.N1625 _root_.GD.N0106.N0428.N0765.N1622


theorem d022863 (v : Fin 5 → ℝ)
    (hv : ∀ k : Fin 5, ∑ a : Fin 5, _root_.GD.N0106.N0428.N0765.N1627.d021098 k a * v a = 0) :
    v = 0 := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have h4 := hv 4
  norm_num [_root_.GD.N0106.N0428.N0765.N1627.d021098, Fin.sum_univ_five, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    at h0 h1 h2 h3 h4
  funext k
  fin_cases k
  · change v 0 = 0
    exact h0
  · change v 1 = 0
    linarith only [h0, h1]
  · change v 2 = 0
    linarith only [h0, h1, h2]
  · change v 3 = 0
    linarith only [h0, h1, h2, h3]
  · change v 4 = 0
    linarith only [h0, h1, h2, h3, h4]



theorem d022864 (location eta : ℝ) (heta : 0 < eta)
    (k : Fin 5) (j : Fin 2) :
    _root_.GD.N0106.N0428.N0765.N1627.d021105 location eta (k, j) =
      ∑ a : Fin 5, _root_.GD.N0106.N0428.N0765.N1627.d021098 k a * _root_.GD.N0106.N0428.N0765.N1529.d020807 eta (a, j) := by
  rw [_root_.GD.N0106.N0428.N0765.N1627.d021112 location eta heta]
  simp only [_root_.GD.N0106.N0428.N0765.N1529.d020833 location eta heta, _root_.GD.N0106.N0428.N0765.N1529.d020807]

theorem d022865 (location eta : ℝ) (heta : 0 < eta)
    (j : _root_.GD.N0106.N0428.N0765.N1607.d012643) :
    _root_.GD.N0106.N0428.N0765.N1627.d021105 location eta j = _root_.GD.N0106.N0428.N0765.N1627.d021105 0 eta j := by
  rw [_root_.GD.N0106.N0428.N0765.N1627.d021114 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1627.d021114 0 eta heta]

section FiniteFamily

variable {ι : Type*} [Fintype ι]



theorem d022866
    (eta weight : ι → ℝ) (heta : ∀ i, 0 < eta i)
    (hbalance : ∀ k j, ∑ i, weight i * _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (eta i) (k, j) = 0) :
    ∀ j : _root_.GD.N0106.N0428.N0765.N1607.d012643, ∑ i, weight i * _root_.GD.N0106.N0428.N0765.N1529.d020807 (eta i) j = 0 := by
  intro j
  let v : Fin 5 → ℝ := fun a => ∑ i, weight i * _root_.GD.N0106.N0428.N0765.N1529.d020807 (eta i) (a, j.2)
  have hv : ∀ k : Fin 5, ∑ a : Fin 5, _root_.GD.N0106.N0428.N0765.N1627.d021098 k a * v a = 0 := by
    intro k
    calc
      _ = ∑ i, weight i *
          (∑ a : Fin 5, _root_.GD.N0106.N0428.N0765.N1627.d021098 k a * _root_.GD.N0106.N0428.N0765.N1529.d020807 (eta i) (a, j.2)) := by
        simp only [v, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = ∑ i, weight i * _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (eta i) (k, j.2) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [_root_.GD.N0106.N0428.N0765.N1609.d022864 0 (eta i) (heta i)]
      _ = 0 := hbalance k j.2
  have hz := congrFun (_root_.GD.N0106.N0428.N0765.N1609.d022863 v hv) j.1
  simpa only [v, Prod.mk.eta, Pi.zero_apply] using hz



theorem d022867
    (eta weight : ι → ℝ) (heta : ∀ i, 0 < eta i)
    (hbalance : ∀ k j, ∑ i, weight i * _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (eta i) (k, j) = 0) :
    (∀ location (j : _root_.GD.N0106.N0428.N0765.N1607.d012643),
      ∑ i, weight i * _root_.GD.N0106.N0428.N0765.N1627.d021105 location (eta i) j = 0) ∧
    (∀ location (j : _root_.GD.N0106.N0428.N0765.N1607.d012643),
      ∑ i, weight i * _root_.GD.N0106.N0428.N0765.N1607.d012683 location (eta i) j = 0) := by
  constructor
  · intro location j
    have heq (i : ι) : _root_.GD.N0106.N0428.N0765.N1627.d021105 location (eta i) j =
        _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (eta i) j :=
      _root_.GD.N0106.N0428.N0765.N1609.d022865 location (eta i) (heta i) j
    simp_rw [heq]
    exact hbalance j.1 j.2
  · intro location j
    have hpure := _root_.GD.N0106.N0428.N0765.N1609.d022866 eta weight heta hbalance j
    have heq (i : ι) : _root_.GD.N0106.N0428.N0765.N1607.d012683 location (eta i) j = _root_.GD.N0106.N0428.N0765.N1529.d020807 (eta i) j :=
      _root_.GD.N0106.N0428.N0765.N1529.d020833 location (eta i) (heta i) j
    simpa only [heq] using hpure

end FiniteFamily

def d022868 (eta : ℝ) (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) : ℝ :=
  ∑ j, b j * _root_.GD.N0106.N0428.N0765.N1529.d020807 eta j

def d022869 (eta : ℝ) (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) : ℝ :=
  ∑ i, ∑ j, b i * b j * _root_.GD.N0106.N0428.N0765.N1529.d020808 eta i j

theorem d022870 (eta : ℝ) : Continuous (_root_.GD.N0106.N0428.N0765.N1609.d022869 eta) := by
  unfold _root_.GD.N0106.N0428.N0765.N1609.d022869
  fun_prop

theorem d022871 (eta a : ℝ) (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) :
    _root_.GD.N0106.N0428.N0765.N1609.d022869 eta (a • b) = a ^ 2 * _root_.GD.N0106.N0428.N0765.N1609.d022869 eta b := by
  simp only [_root_.GD.N0106.N0428.N0765.N1609.d022869, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem d022872 (eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (hb : b ≠ 0) : 0 < _root_.GD.N0106.N0428.N0765.N1609.d022869 eta b :=
  _root_.GD.N0106.N0428.N0765.N1615.d020926 eta heta b hb

theorem d022873 (eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1609.d022869 eta b := by
  by_cases hb : b = 0
  · simp [hb, _root_.GD.N0106.N0428.N0765.N1609.d022869]
  · exact (_root_.GD.N0106.N0428.N0765.N1609.d022872 eta heta b hb).le

theorem d022874 (location eta : ℝ) (heta : 0 < eta)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) :
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) - _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 =
      2 * _root_.GD.N0106.N0428.N0765.N1609.d022868 eta b + _root_.GD.N0106.N0428.N0765.N1609.d022869 eta b :=
  _root_.GD.N0106.N0428.N0765.N1529.d020837 location eta heta b




theorem d022875
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (eta weight : ι → ℝ) (heta : ∀ i, 0 < eta i)
    (hweight : ∀ i, 0 < weight i)
    (hbalance : ∀ k j, ∑ i, weight i * _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (eta i) (k, j) = 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ, ∃ i : ι, ∀ location : ℝ,
      κ * ‖b‖ ^ 2 ≤ _root_.GD.N0106.N0428.N0765.N1610.d020776 location (eta i) (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) -
        _root_.GD.N0106.N0428.N0765.N1610.d020776 location (eta i) _root_.GD.N0106.N0428.N0765.N1611.d012593 := by
  have hpure := _root_.GD.N0106.N0428.N0765.N1609.d022866 eta weight heta hbalance
  have hlinear : ∀ b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ,
      ∑ i, weight i * _root_.GD.N0106.N0428.N0765.N1609.d022868 (eta i) b = 0 := by
    intro b
    simp only [_root_.GD.N0106.N0428.N0765.N1609.d022868, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    calc
      ∑ i, weight i * (b j * _root_.GD.N0106.N0428.N0765.N1529.d020807 (eta i) j) =
          b j * (∑ i, weight i * _root_.GD.N0106.N0428.N0765.N1529.d020807 (eta i) j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hpure j, mul_zero]
  obtain ⟨κ, hκ, hbound⟩ := _root_.GD.N0106.N0428.N0765.N1622.d005775
    weight (fun i => _root_.GD.N0106.N0428.N0765.N1609.d022868 (eta i)) (fun i => _root_.GD.N0106.N0428.N0765.N1609.d022869 (eta i))
    hweight hlinear (fun i => _root_.GD.N0106.N0428.N0765.N1609.d022870 (eta i))
    (fun i a b => _root_.GD.N0106.N0428.N0765.N1609.d022871 (eta i) a b)
    (fun i b => _root_.GD.N0106.N0428.N0765.N1609.d022873 (eta i) (heta i) b)
    (fun i b hb => _root_.GD.N0106.N0428.N0765.N1609.d022872 (eta i) (heta i) b hb)
  refine ⟨κ, hκ, ?_⟩
  intro b
  obtain ⟨i, hi⟩ := hbound b
  refine ⟨i, fun location => ?_⟩
  rw [_root_.GD.N0106.N0428.N0765.N1609.d022874 location (eta i) (heta i)]
  exact hi

abbrev d022876 := Sum (Fin 5) (Fin 5)


def d022877 (eta : Fin 5 → ℝ) : _root_.GD.N0106.N0428.N0765.N1609.d022876 → ℝ
  | Sum.inl i => eta i
  | Sum.inr i => (eta i)⁻¹

theorem d022878 (eta : Fin 5 → ℝ) (heta : ∀ i, 0 < eta i) :
    ∀ atom, 0 < _root_.GD.N0106.N0428.N0765.N1609.d022877 eta atom := by
  intro atom
  cases atom with
  | inl i => exact heta i
  | inr i => exact inv_pos.mpr (heta i)

def d022879 (eta : Fin 5 → ℝ) (i k : Fin 5) (j : Fin 2) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (eta i) (k, j)

def d022880 (eta : Fin 5 → ℝ) (i k : Fin 5) (j : Fin 2) : ℝ :=
  _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (eta i)⁻¹ (k, j)

theorem d022881 (eta : Fin 5 → ℝ) (atom : _root_.GD.N0106.N0428.N0765.N1609.d022876)
    (k : Fin 5) (j : Fin 2) :
    _root_.GD.N0232.N0720.N1249.d002218 (_root_.GD.N0106.N0428.N0765.N1609.d022879 eta) (_root_.GD.N0106.N0428.N0765.N1609.d022880 eta) atom k j =
      _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta atom) (k, j) := by
  cases atom <;> rfl



theorem d022882 (eta : Fin 5 → ℝ) (heta : ∀ i, 0 < eta i)
    (i k : Fin 5) (j : Fin 2) :
    eta i * _root_.GD.N0106.N0428.N0765.N1609.d022880 eta i k j =
      -((-1 : ℝ) ^ (k : ℕ)) * _root_.GD.N0106.N0428.N0765.N1609.d022879 eta i k j := by
  have h := _root_.GD.N0106.N0428.N0765.N1627.d021122 0 (eta i) (heta i) (k, j)
  have hs : (-((-1 : ℝ) ^ (k : ℕ))) ^ 2 = 1 := by
    fin_cases k <;> norm_num
  dsimp [_root_.GD.N0106.N0428.N0765.N1609.d022879, _root_.GD.N0106.N0428.N0765.N1609.d022880]
  calc
    eta i * _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (eta i)⁻¹ (k, j) =
        (-((-1 : ℝ) ^ (k : ℕ))) ^ 2 *
          (eta i * _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (eta i)⁻¹ (k, j)) := by rw [hs]; ring
    _ = -((-1 : ℝ) ^ (k : ℕ)) * _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (eta i) (k, j) := by
      rw [h]
      ring



def d022883 (eta : Fin 5 → ℝ) (colScale : Fin 5 → ℝ) : Prop :=
  ∀ c (r : Fin 4),
    |_root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 (_root_.GD.N0106.N0428.N0765.N1609.d022879 eta)) colScale c r -
      _root_.GD.N0106.N0428.N0765.N1603.d005578 r.castSucc c| ≤ 2000 * _root_.GD.N0106.N0428.N0765.N1603.d005579 r.castSucc c



def d022884 (eta : Fin 5 → ℝ) (colScale : Fin 5 → ℝ) : Prop :=
  ∀ c (r : Fin 4),
    (_root_.GD.N0106.N0428.N0765.N1604.d005547 r.castSucc c : ℝ) ≤
      _root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 (_root_.GD.N0106.N0428.N0765.N1609.d022879 eta)) colScale c r ∧
    _root_.GD.N0106.N0428.N0765.N1603.d005614 (_root_.GD.N0106.N0428.N0765.N1603.d005619 (_root_.GD.N0106.N0428.N0765.N1609.d022879 eta)) colScale c r ≤
      (_root_.GD.N0106.N0428.N0765.N1604.d005548 r.castSucc c : ℝ)



theorem d022885
    (eta colScale : Fin 5 → ℝ) (heta : ∀ i, 0 < eta i)
    (hcol : ∀ i, 0 < colScale i) (hbox : _root_.GD.N0106.N0428.N0765.N1609.d022883 eta colScale) :
    ∃ alpha : Fin 5 → ℝ,
      (∀ atom, 0 < _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom) ∧
      (∀ location (j : _root_.GD.N0106.N0428.N0765.N1607.d012643), ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
        _root_.GD.N0106.N0428.N0765.N1627.d021105 location (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta atom) j = 0) ∧
      (∀ location (j : _root_.GD.N0106.N0428.N0765.N1607.d012643), ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
        _root_.GD.N0106.N0428.N0765.N1607.d012683 location (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta atom) j = 0) := by
  obtain ⟨alpha, hweight, hbalance⟩ := _root_.GD.N0106.N0428.N0765.N1625.d005799
    eta (_root_.GD.N0106.N0428.N0765.N1609.d022879 eta) (_root_.GD.N0106.N0428.N0765.N1609.d022880 eta) colScale heta hcol hbox
    (_root_.GD.N0106.N0428.N0765.N1609.d022882 eta heta)
  have hactual : ∀ k j, ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
      _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta atom) (k, j) = 0 := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1609.d022881] using hbalance
  have hboth := _root_.GD.N0106.N0428.N0765.N1609.d022867 (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta)
    (_root_.GD.N0232.N0720.N1249.d002217 eta alpha) (_root_.GD.N0106.N0428.N0765.N1609.d022878 eta heta) hactual
  exact ⟨alpha, hweight, hboth.1, hboth.2⟩




theorem d022886
    (eta colScale : Fin 5 → ℝ) (heta : ∀ i, 0 < eta i)
    (hcol : ∀ i, 0 < colScale i) (hbox : _root_.GD.N0106.N0428.N0765.N1609.d022884 eta colScale) :
    ∃ alpha : Fin 5 → ℝ,
      (∀ atom, 0 < _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom) ∧
      (∀ location (j : _root_.GD.N0106.N0428.N0765.N1607.d012643), ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
        _root_.GD.N0106.N0428.N0765.N1627.d021105 location (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta atom) j = 0) ∧
      (∀ location (j : _root_.GD.N0106.N0428.N0765.N1607.d012643), ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
        _root_.GD.N0106.N0428.N0765.N1607.d012683 location (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta atom) j = 0) := by
  obtain ⟨alpha, hweight, hbalance⟩ := _root_.GD.N0106.N0428.N0765.N1603.d005621
    eta (_root_.GD.N0106.N0428.N0765.N1609.d022879 eta) (_root_.GD.N0106.N0428.N0765.N1609.d022880 eta) colScale heta hcol hbox
    (_root_.GD.N0106.N0428.N0765.N1609.d022882 eta heta)
  have hactual : ∀ k j, ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
      _root_.GD.N0106.N0428.N0765.N1627.d021105 0 (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta atom) (k, j) = 0 := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1609.d022881] using hbalance
  have hboth := _root_.GD.N0106.N0428.N0765.N1609.d022867 (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta)
    (_root_.GD.N0232.N0720.N1249.d002217 eta alpha) (_root_.GD.N0106.N0428.N0765.N1609.d022878 eta heta) hactual
  exact ⟨alpha, hweight, hboth.1, hboth.2⟩





theorem d022887
    (eta colScale : Fin 5 → ℝ) (heta : ∀ i, 0 < eta i)
    (hcol : ∀ i, 0 < colScale i) (hbox : _root_.GD.N0106.N0428.N0765.N1609.d022883 eta colScale) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ, ∃ atom : _root_.GD.N0106.N0428.N0765.N1609.d022876, ∀ location : ℝ,
      κ * ‖b‖ ^ 2 ≤ _root_.GD.N0106.N0428.N0765.N1610.d020776 location (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta atom) (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) -
        _root_.GD.N0106.N0428.N0765.N1610.d020776 location (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta atom) _root_.GD.N0106.N0428.N0765.N1611.d012593 := by
  obtain ⟨alpha, hweight, hcentered, _⟩ :=
    _root_.GD.N0106.N0428.N0765.N1609.d022885 eta colScale heta hcol hbox
  exact _root_.GD.N0106.N0428.N0765.N1609.d022875
    (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta) (_root_.GD.N0232.N0720.N1249.d002217 eta alpha) (_root_.GD.N0106.N0428.N0765.N1609.d022878 eta heta) hweight
    (fun k j => hcentered 0 (k, j))

theorem d022888
    (eta colScale : Fin 5 → ℝ) (heta : ∀ i, 0 < eta i)
    (hcol : ∀ i, 0 < colScale i) (hbox : _root_.GD.N0106.N0428.N0765.N1609.d022884 eta colScale) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ, ∃ atom : _root_.GD.N0106.N0428.N0765.N1609.d022876, ∀ location : ℝ,
      κ * ‖b‖ ^ 2 ≤ _root_.GD.N0106.N0428.N0765.N1610.d020776 location (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta atom) (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) -
        _root_.GD.N0106.N0428.N0765.N1610.d020776 location (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta atom) _root_.GD.N0106.N0428.N0765.N1611.d012593 := by
  obtain ⟨alpha, hweight, hcentered, _⟩ :=
    _root_.GD.N0106.N0428.N0765.N1609.d022886 eta colScale heta hcol hbox
  exact _root_.GD.N0106.N0428.N0765.N1609.d022875
    (_root_.GD.N0106.N0428.N0765.N1609.d022877 eta) (_root_.GD.N0232.N0720.N1249.d002217 eta alpha) (_root_.GD.N0106.N0428.N0765.N1609.d022878 eta heta) hweight
    (fun k j => hcentered 0 (k, j))



theorem d022889
    (colScale : Fin 5 → ℝ) (hcol : ∀ i, 0 < colScale i)
    (hbox : _root_.GD.N0106.N0428.N0765.N1609.d022883 _root_.GD.N0232.N0720.N1249.d002227 colScale) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ, ∃ atom : _root_.GD.N0106.N0428.N0765.N1609.d022876, ∀ location : ℝ,
      κ * ‖b‖ ^ 2 ≤ _root_.GD.N0106.N0428.N0765.N1610.d020776 location (_root_.GD.N0106.N0428.N0765.N1609.d022877 _root_.GD.N0232.N0720.N1249.d002227 atom) (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) -
        _root_.GD.N0106.N0428.N0765.N1610.d020776 location (_root_.GD.N0106.N0428.N0765.N1609.d022877 _root_.GD.N0232.N0720.N1249.d002227 atom) _root_.GD.N0106.N0428.N0765.N1611.d012593 :=
  _root_.GD.N0106.N0428.N0765.N1609.d022887 _root_.GD.N0232.N0720.N1249.d002227 colScale
    (fun i => lt_trans zero_lt_one (_root_.GD.N0232.N0720.N1249.d002228 i)) hcol hbox



theorem d022890
    (colScale : Fin 5 → ℝ) (hcol : ∀ i, 0 < colScale i)
    (hbox : _root_.GD.N0106.N0428.N0765.N1609.d022883 _root_.GD.N0232.N0720.N1249.d002227 colScale)
    (b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ) (hb : b ≠ 0) :
    ∃ atom : _root_.GD.N0106.N0428.N0765.N1609.d022876, ∀ location : ℝ,
      _root_.GD.N0106.N0428.N0765.N1610.d020776 location (_root_.GD.N0106.N0428.N0765.N1609.d022877 _root_.GD.N0232.N0720.N1249.d002227 atom) _root_.GD.N0106.N0428.N0765.N1611.d012593 <
        _root_.GD.N0106.N0428.N0765.N1610.d020776 location (_root_.GD.N0106.N0428.N0765.N1609.d022877 _root_.GD.N0232.N0720.N1249.d002227 atom) (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) := by
  obtain ⟨κ, hκ, hbound⟩ := _root_.GD.N0106.N0428.N0765.N1609.d022889 colScale hcol hbox
  obtain ⟨atom, hatom⟩ := hbound b
  have hpos : 0 < κ * ‖b‖ ^ 2 := mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr hb))
  refine ⟨atom, fun location => ?_⟩
  linarith [hatom location]

theorem d022891
    (colScale : Fin 5 → ℝ) (hcol : ∀ i, 0 < colScale i)
    (hbox : _root_.GD.N0106.N0428.N0765.N1609.d022883 _root_.GD.N0232.N0720.N1249.d002227 colScale) :
    ¬ ∃ b : _root_.GD.N0106.N0428.N0765.N1607.d012643 → ℝ, b ≠ 0 ∧ ∀ eta : ℝ, 0 < eta →
      _root_.GD.N0106.N0428.N0765.N1610.d020776 0 eta (_root_.GD.N0106.N0428.N0765.N1607.d012648 b) ≤ _root_.GD.N0106.N0428.N0765.N1610.d020776 0 eta _root_.GD.N0106.N0428.N0765.N1611.d012593 := by
  rintro ⟨b, hb, hweak⟩
  obtain ⟨atom, hatom⟩ := _root_.GD.N0106.N0428.N0765.N1609.d022890 colScale hcol hbox b hb
  exact (not_lt_of_ge (hweak (_root_.GD.N0106.N0428.N0765.N1609.d022877 _root_.GD.N0232.N0720.N1249.d002227 atom)
    (_root_.GD.N0106.N0428.N0765.N1609.d022878 _root_.GD.N0232.N0720.N1249.d002227
      (fun i => lt_trans zero_lt_one (_root_.GD.N0232.N0720.N1249.d002228 i)) atom))) (hatom 0)

end

end GD.N0106.N0428.N0765.N1609

#print axioms _root_.GD.N0106.N0428.N0765.N1609.d022863
#print axioms _root_.GD.N0106.N0428.N0765.N1609.d022867
#print axioms _root_.GD.N0106.N0428.N0765.N1609.d022875
#print axioms _root_.GD.N0106.N0428.N0765.N1609.d022885
#print axioms _root_.GD.N0106.N0428.N0765.N1609.d022887
#print axioms _root_.GD.N0106.N0428.N0765.N1609.d022888
#print axioms _root_.GD.N0106.N0428.N0765.N1609.d022889
#print axioms _root_.GD.N0106.N0428.N0765.N1609.d022890
#print axioms _root_.GD.N0106.N0428.N0765.N1609.d022891
