import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0024.N0265

variable {I X : Type*}

def d005117 (s : Finset I) (w a : I → ℝ) : ℝ :=
  ∑ i ∈ s, w i * a i

def d005118 (s : Finset I) (w b v : I → ℝ) : ℝ :=
  _root_.GD.N0024.N0265.d005117 s w (fun i => min (b i) (v i))

def d005119 (s : Finset I) (w b v : I → ℝ) : ℝ :=
  _root_.GD.N0024.N0265.d005117 s w (fun i => max (v i - b i) 0)

def d005120 (s : Finset I) (w a : I → ℝ) (B : ℝ) : ℝ :=
  _root_.GD.N0024.N0265.d005117 s w a - B

theorem d005121 (b v : ℝ) :
    min b v = v - max (v - b) 0 := by
  rcases le_total b v with h | h
  · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h), sub_zero]

theorem d005122 (w b v r : ℝ) :
    w * r - w * min b v = w * max (v - b) 0 - (w * v - w * r) := by
  rw [_root_.GD.N0024.N0265.d005121]
  ring

theorem d005123 (s : Finset I) (w b v : I → ℝ) :
    _root_.GD.N0024.N0265.d005118 s w b v = _root_.GD.N0024.N0265.d005117 s w v - _root_.GD.N0024.N0265.d005119 s w b v := by
  simp only [_root_.GD.N0024.N0265.d005118, _root_.GD.N0024.N0265.d005117, _root_.GD.N0024.N0265.d005119, _root_.GD.N0024.N0265.d005121, mul_sub, Finset.sum_sub_distrib]

theorem d005124 (s : Finset I) (w b v : I → ℝ) :
    _root_.GD.N0024.N0265.d005118 s w b v = _root_.GD.N0024.N0265.d005118 s w v b := by
  simp only [_root_.GD.N0024.N0265.d005118, min_comm]

theorem d005125 (s : Finset I) (w b v : I → ℝ) (B : ℝ) :
    B - _root_.GD.N0024.N0265.d005118 s w b v = _root_.GD.N0024.N0265.d005119 s w b v - _root_.GD.N0024.N0265.d005120 s w v B := by
  rw [_root_.GD.N0024.N0265.d005123]
  unfold _root_.GD.N0024.N0265.d005120
  ring

theorem d005126
    (s : Finset I) (w b v : I → ℝ) (B : ℝ) :
    B ≤ _root_.GD.N0024.N0265.d005118 s w b v ↔ _root_.GD.N0024.N0265.d005119 s w b v ≤ _root_.GD.N0024.N0265.d005120 s w v B := by
  have h := _root_.GD.N0024.N0265.d005125 s w b v B
  constructor <;> intro h' <;> linarith

theorem d005127
    (s : Finset I) (w b v : I → ℝ) (B : ℝ) :
    B ≤ _root_.GD.N0024.N0265.d005118 s w b v ↔ _root_.GD.N0024.N0265.d005119 s w v b ≤ _root_.GD.N0024.N0265.d005120 s w b B := by
  rw [_root_.GD.N0024.N0265.d005124, _root_.GD.N0024.N0265.d005126]

theorem d005128
    (s : Finset I) (w b v : I → ℝ) (B : ℝ) :
    _root_.GD.N0024.N0265.d005118 s w b v < B ↔ _root_.GD.N0024.N0265.d005120 s w v B < _root_.GD.N0024.N0265.d005119 s w b v := by
  have h := _root_.GD.N0024.N0265.d005125 s w b v B
  constructor <;> intro h' <;> linarith

theorem d005129 (s : Finset I) (w b v : I → ℝ) :
    _root_.GD.N0024.N0265.d005119 s w b v - _root_.GD.N0024.N0265.d005119 s w v b =
      _root_.GD.N0024.N0265.d005117 s w v - _root_.GD.N0024.N0265.d005117 s w b := by
  have h₁ := _root_.GD.N0024.N0265.d005123 s w b v
  have h₂ := _root_.GD.N0024.N0265.d005123 s w v b
  rw [← _root_.GD.N0024.N0265.d005124 s w b v] at h₂
  linarith

theorem d005130
    (s : Finset I) (w b v : I → ℝ) :
    _root_.GD.N0024.N0265.d005118 s w b v = min (_root_.GD.N0024.N0265.d005117 s w b) (_root_.GD.N0024.N0265.d005117 s w v) -
      min (_root_.GD.N0024.N0265.d005119 s w b v) (_root_.GD.N0024.N0265.d005119 s w v b) := by
  have h₁ := _root_.GD.N0024.N0265.d005123 s w b v
  have h₂ := _root_.GD.N0024.N0265.d005123 s w v b
  rw [← _root_.GD.N0024.N0265.d005124 s w b v] at h₂
  rcases le_total (_root_.GD.N0024.N0265.d005117 s w b) (_root_.GD.N0024.N0265.d005117 s w v) with h | h
  · rw [min_eq_left h, min_eq_right (by linarith)]
    exact h₂
  · rw [min_eq_right h, min_eq_left (by linarith)]
    exact h₁

theorem d005131 (s : Finset I) (w b v : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ _root_.GD.N0024.N0265.d005119 s w b v := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (le_max_right _ _))

theorem d005132 (s : Finset I) (w b v : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (j : I) (hj : j ∈ s) :
    w j * max (v j - b j) 0 ≤ _root_.GD.N0024.N0265.d005119 s w b v := by
  unfold _root_.GD.N0024.N0265.d005119 _root_.GD.N0024.N0265.d005117
  exact Finset.single_le_sum
    (fun i hi => mul_nonneg (hw i hi) (le_max_right (v i - b i) 0)) hj

theorem d005133 (s : Finset I) (w b v r : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hb : ∀ i ∈ s, r i ≤ b i) (hv : ∀ i ∈ s, r i ≤ v i) :
    _root_.GD.N0024.N0265.d005117 s w r ≤ _root_.GD.N0024.N0265.d005118 s w b v := by
  exact Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (le_min (hb i hi) (hv i hi)) (hw i hi)

theorem d005134
    (s : Finset I) (w b v r : I → ℝ) (B : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hB : B ≤ _root_.GD.N0024.N0265.d005117 s w r)
    (hb : ∀ i ∈ s, r i ≤ b i) (hv : ∀ i ∈ s, r i ≤ v i) :
    _root_.GD.N0024.N0265.d005119 s w b v ≤ _root_.GD.N0024.N0265.d005120 s w v B := by
  exact (_root_.GD.N0024.N0265.d005126 s w b v B).mp
    (hB.trans (_root_.GD.N0024.N0265.d005133 s w b v r hw hb hv))

theorem d005135
    (s : Finset I) (w b v : I → ℝ) (risk : X → I → ℝ) (B : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hB : ∀ x, B ≤ _root_.GD.N0024.N0265.d005117 s w (risk x))
    (hgap : _root_.GD.N0024.N0265.d005120 s w v B < _root_.GD.N0024.N0265.d005119 s w b v) :
    ¬ ∃ x, (∀ i ∈ s, risk x i ≤ b i) ∧ (∀ i ∈ s, risk x i ≤ v i) := by
  rintro ⟨x, hb, hv⟩
  exact (not_le.mpr hgap)
    (_root_.GD.N0024.N0265.d005134 s w b v (risk x) B hw (hB x) hb hv)

theorem d005136
    (s : Finset I) (w b v : I → ℝ) (risk : X → I → ℝ) (B ε : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hB : ∀ x, B ≤ _root_.GD.N0024.N0265.d005117 s w (risk x))
    (hsharp : _root_.GD.N0024.N0265.d005120 s w v B ≤ ε)
    (hexcess : ε < _root_.GD.N0024.N0265.d005119 s w b v) :
    ¬ ∃ x, (∀ i ∈ s, risk x i ≤ b i) ∧ (∀ i ∈ s, risk x i ≤ v i) := by
  exact _root_.GD.N0024.N0265.d005135 s w b v risk B hw hB
    (hsharp.trans_lt hexcess)

theorem d005137
    (s : Finset I) (w b v : I → ℝ) (risk : X → I → ℝ) (B : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hB : ∀ x, B ≤ _root_.GD.N0024.N0265.d005117 s w (risk x))
    (j : I) (hj : j ∈ s)
    (hgap : _root_.GD.N0024.N0265.d005120 s w v B < w j * max (v j - b j) 0) :
    ¬ ∃ x, (∀ i ∈ s, risk x i ≤ b i) ∧ (∀ i ∈ s, risk x i ≤ v i) := by
  exact _root_.GD.N0024.N0265.d005135 s w b v risk B hw hB
    (hgap.trans_le (_root_.GD.N0024.N0265.d005132 s w b v hw j hj))

theorem d005138
    (s : Finset I) (w b v r : I → ℝ) (B : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hB : B ≤ _root_.GD.N0024.N0265.d005117 s w r)
    (hb : ∀ i ∈ s, r i ≤ b i) (hv : ∀ i ∈ s, r i ≤ v i)
    (hsharp : _root_.GD.N0024.N0265.d005120 s w v B = 0)
    (j : I) (hj : j ∈ s) (hwj : 0 < w j) : v j ≤ b j := by
  have he := _root_.GD.N0024.N0265.d005134 s w b v r B hw hB hb hv
  rw [hsharp] at he
  have ha := (_root_.GD.N0024.N0265.d005132 s w b v hw j hj).trans he
  have ham : w j * max (v j - b j) 0 ≤ w j * 0 := by simpa using ha
  have hm : max (v j - b j) 0 ≤ 0 := le_of_mul_le_mul_left ham hwj
  have hd := (le_max_left (v j - b j) 0).trans hm
  linarith

theorem d005139
    (s A : Finset I) (w b v τ : I → ℝ) (δ : ℝ)
    (hAs : A ⊆ s) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hseparation : ∀ i ∈ A, δ * τ i ≤ v i - b i) :
    δ * _root_.GD.N0024.N0265.d005117 A w τ ≤ _root_.GD.N0024.N0265.d005119 s w b v := by
  calc
    δ * _root_.GD.N0024.N0265.d005117 A w τ = ∑ i ∈ A, w i * (δ * τ i) := by
      simp only [_root_.GD.N0024.N0265.d005117, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ A, w i * max (v i - b i) 0 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        ((hseparation i hi).trans (le_max_left _ _)) (hw i (hAs hi))
    _ ≤ _root_.GD.N0024.N0265.d005119 s w b v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hAs
        (fun i hi _ => mul_nonneg (hw i hi) (le_max_right _ _))

theorem d005140
    (s A : Finset I) (w b v τ : I → ℝ) (B δ : ℝ)
    (hAs : A ⊆ s) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hseparation : ∀ i ∈ A, δ * τ i ≤ v i - b i)
    (hcap : B ≤ _root_.GD.N0024.N0265.d005118 s w b v) :
    δ * _root_.GD.N0024.N0265.d005117 A w τ ≤ _root_.GD.N0024.N0265.d005120 s w v B := by
  exact (_root_.GD.N0024.N0265.d005139 s A w b v τ δ hAs hw hseparation).trans
    ((_root_.GD.N0024.N0265.d005126 s w b v B).mp hcap)

theorem d005141
    (s A : Finset I) (w b v τ : I → ℝ) (B δ T : ℝ)
    (hAs : A ⊆ s) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hδ : 0 < δ) (hT : 0 < T)
    (hseparation : ∀ i ∈ A, δ * τ i ≤ v i - b i)
    (hcap : B ≤ _root_.GD.N0024.N0265.d005118 s w b v) :
    _root_.GD.N0024.N0265.d005117 A w τ / T ≤ _root_.GD.N0024.N0265.d005120 s w v B / (δ * T) := by
  have h := _root_.GD.N0024.N0265.d005140
    s A w b v τ B δ hAs hw hseparation hcap
  apply (div_le_div_iff₀ hT (mul_pos hδ hT)).mpr
  nlinarith

#print axioms _root_.GD.N0024.N0265.d005121
#print axioms _root_.GD.N0024.N0265.d005122
#print axioms _root_.GD.N0024.N0265.d005123
#print axioms _root_.GD.N0024.N0265.d005124
#print axioms _root_.GD.N0024.N0265.d005125
#print axioms _root_.GD.N0024.N0265.d005126
#print axioms _root_.GD.N0024.N0265.d005127
#print axioms _root_.GD.N0024.N0265.d005128
#print axioms _root_.GD.N0024.N0265.d005129
#print axioms _root_.GD.N0024.N0265.d005130
#print axioms _root_.GD.N0024.N0265.d005131
#print axioms _root_.GD.N0024.N0265.d005132
#print axioms _root_.GD.N0024.N0265.d005133
#print axioms _root_.GD.N0024.N0265.d005134
#print axioms _root_.GD.N0024.N0265.d005135
#print axioms _root_.GD.N0024.N0265.d005136
#print axioms _root_.GD.N0024.N0265.d005137
#print axioms _root_.GD.N0024.N0265.d005138
#print axioms _root_.GD.N0024.N0265.d005139
#print axioms _root_.GD.N0024.N0265.d005140
#print axioms _root_.GD.N0024.N0265.d005141

end GD.N0024.N0265
