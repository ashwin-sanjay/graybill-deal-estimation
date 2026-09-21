import GD.Module0370








set_option autoImplicit false
set_option warningAsError true

open Matrix Finset
open _root_.GD.N0106.N0428.N0765.N1567
open _root_.GD.N0106.N0428.N0765.N1604
open _root_.GD.N0106.N0428.N0765.N1603
open _root_.GD.N0232.N0720.N1247

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

namespace GD.N0106.N0428.N0765.N1626
noncomputable section

def d005785 (t : ℝ) (A : Matrix (Fin 5) (Fin 5) ℝ) : Prop :=
  ∀ i j, |A i j - _root_.GD.N0106.N0428.N0765.N1603.d005578 i j| ≤ t * _root_.GD.N0106.N0428.N0765.N1603.d005579 i j

theorem d005786 (i j : Fin 5) : 0 ≤ _root_.GD.N0106.N0428.N0765.N1603.d005579 i j := by
  rw [_root_.GD.N0106.N0428.N0765.N1603.d005584]
  exact_mod_cast (show (0 : ℚ) ≤ _root_.GD.N0106.N0428.N0765.N1604.d005550 i j from by
    rw [_root_.GD.N0106.N0428.N0765.N1604.d005555]
    exact div_nonneg (sub_nonneg.mpr (_root_.GD.N0106.N0428.N0765.N1604.d005558 i j)) (by norm_num))

theorem d005787 {s t : ℝ} (hst : s ≤ t)
    {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : _root_.GD.N0106.N0428.N0765.N1626.d005785 s A) : _root_.GD.N0106.N0428.N0765.N1626.d005785 t A := by
  intro i j
  exact (hA i j).trans (mul_le_mul_of_nonneg_right hst (_root_.GD.N0106.N0428.N0765.N1626.d005786 i j))

theorem d005788 {t : ℝ} (ht : 0 ≤ t) (i : Fin 5) :
    ∑ j, ∑ k, _root_.GD.N0106.N0428.N0765.N1603.d005581 i k * (t * _root_.GD.N0106.N0428.N0765.N1603.d005579 k j) ≤ t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) := by
  calc
    ∑ j, ∑ k, _root_.GD.N0106.N0428.N0765.N1603.d005581 i k * (t * _root_.GD.N0106.N0428.N0765.N1603.d005579 k j)
        = t * (∑ j, ∑ k, _root_.GD.N0106.N0428.N0765.N1603.d005581 i k * _root_.GD.N0106.N0428.N0765.N1603.d005579 k j) := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ ≤ t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) := mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1603.d005591 i) ht


theorem d005789 {t : ℝ} (ht : 0 ≤ t) (htq : t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) < 1)
    {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : _root_.GD.N0106.N0428.N0765.N1626.d005785 t A) :
    ∃! w : Fin 5 → ℝ, A *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582 ∧
      ∀ i, |w i - (_root_.GD.N0232.N0720.N1247.d002170 i : ℝ)| ≤
        t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) * (_root_.GD.N0232.N0720.N1247.d002170 1 : ℝ) / (1 - t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ)) := by
  let R : Matrix (Fin 5) (Fin 5) ℝ := fun i j => t * _root_.GD.N0106.N0428.N0765.N1603.d005579 i j
  have hex := _root_.GD.N0106.N0428.N0765.N1567.d005504 A _root_.GD.N0106.N0428.N0765.N1603.d005578 _root_.GD.N0106.N0428.N0765.N1603.d005580 _root_.GD.N0106.N0428.N0765.N1603.d005581 R (t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ))
    _root_.GD.N0106.N0428.N0765.N1603.d005589 _root_.GD.N0106.N0428.N0765.N1603.d005590 hA (_root_.GD.N0106.N0428.N0765.N1626.d005788 ht) htq _root_.GD.N0106.N0428.N0765.N1603.d005582
  obtain ⟨w, hw, huniq⟩ := hex
  refine ⟨w, ⟨hw, ?_⟩, fun y hy => huniq y hy.1⟩
  intro i
  have h := _root_.GD.N0106.N0428.N0765.N1567.d005505 A _root_.GD.N0106.N0428.N0765.N1603.d005578 _root_.GD.N0106.N0428.N0765.N1603.d005580 _root_.GD.N0106.N0428.N0765.N1603.d005581 R (t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ))
    _root_.GD.N0106.N0428.N0765.N1603.d005589 _root_.GD.N0106.N0428.N0765.N1603.d005590 hA (_root_.GD.N0106.N0428.N0765.N1626.d005788 ht) htq
    w _root_.GD.N0106.N0428.N0765.N1603.d005582 hw (_root_.GD.N0232.N0720.N1247.d002170 1 : ℝ) _root_.GD.N0106.N0428.N0765.N1603.d005594 i
  simpa only [_root_.GD.N0106.N0428.N0765.N1603.d005593] using h

theorem d005790 {t : ℝ} {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : _root_.GD.N0106.N0428.N0765.N1626.d005785 t A) (j : Fin 5) : A (Fin.last 4) j = 1 := by
  have hc : _root_.GD.N0106.N0428.N0765.N1603.d005578 (Fin.last 4) j = 1 := by
    rw [_root_.GD.N0106.N0428.N0765.N1603.d005583, _root_.GD.N0106.N0428.N0765.N1604.d005554, _root_.GD.N0106.N0428.N0765.N1604.d005560, _root_.GD.N0106.N0428.N0765.N1604.d005561]
    norm_num
  have hr : _root_.GD.N0106.N0428.N0765.N1603.d005579 (Fin.last 4) j = 0 := by
    rw [_root_.GD.N0106.N0428.N0765.N1603.d005584, _root_.GD.N0106.N0428.N0765.N1604.d005555, _root_.GD.N0106.N0428.N0765.N1604.d005560, _root_.GD.N0106.N0428.N0765.N1604.d005561]
    norm_num
  have h := hA (Fin.last 4) j
  rw [hc, hr, mul_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

theorem d005791 {t : ℝ} {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : _root_.GD.N0106.N0428.N0765.N1626.d005785 t A) {w : Fin 5 → ℝ} (hw : A *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582) : ∑ i, w i = 1 := by
  have h := congrFun hw (Fin.last 4)
  simpa only [Matrix.mulVec, dotProduct, _root_.GD.N0106.N0428.N0765.N1626.d005790 hA, one_mul, _root_.GD.N0106.N0428.N0765.N1603.d005588] using h




theorem d005792 {t : ℝ} (ht : 0 ≤ t)
    (hmargin : t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) * ((_root_.GD.N0232.N0720.N1247.d002170 1 : ℝ) + (_root_.GD.N0232.N0720.N1247.d002170 3 : ℝ)) <
      (_root_.GD.N0232.N0720.N1247.d002170 3 : ℝ))
    {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : _root_.GD.N0106.N0428.N0765.N1626.d005785 t A) :
    ∃! w : Fin 5 → ℝ, A *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582 ∧ (∑ i, w i = 1) ∧ ∀ i, 0 < w i := by
  have hN : 0 < (_root_.GD.N0232.N0720.N1247.d002170 1 : ℝ) := by exact_mod_cast _root_.GD.N0232.N0720.N1247.d002175 1
  have hm : 0 < (_root_.GD.N0232.N0720.N1247.d002170 3 : ℝ) := by exact_mod_cast _root_.GD.N0232.N0720.N1247.d002175 3
  have hq : 0 < (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) := by exact_mod_cast _root_.GD.N0232.N0720.N1247.d002173
  have htq0 : 0 ≤ t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) := mul_nonneg ht hq.le
  have htq : t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) < 1 := by nlinarith
  have herrlt : t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) * (_root_.GD.N0232.N0720.N1247.d002170 1 : ℝ) /
      (1 - t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ)) < (_root_.GD.N0232.N0720.N1247.d002170 3 : ℝ) := by
    rw [div_lt_iff₀ (sub_pos.mpr htq)]
    nlinarith
  obtain ⟨w, ⟨hw, herr⟩, _⟩ := _root_.GD.N0106.N0428.N0765.N1626.d005789 ht htq hA
  refine ⟨w, ⟨hw, _root_.GD.N0106.N0428.N0765.N1626.d005791 hA hw, ?_⟩, ?_⟩
  · intro i
    have hlow := (abs_le.mp (herr i)).1
    have hmin : (_root_.GD.N0232.N0720.N1247.d002170 3 : ℝ) ≤ (_root_.GD.N0232.N0720.N1247.d002170 i : ℝ) := by
      exact_mod_cast _root_.GD.N0106.N0428.N0765.N1604.d005570 i
    linarith
  · intro y hy
    have hu := _root_.GD.N0106.N0428.N0765.N1567.d005503 A _root_.GD.N0106.N0428.N0765.N1603.d005578 _root_.GD.N0106.N0428.N0765.N1603.d005580 _root_.GD.N0106.N0428.N0765.N1603.d005581
      (fun i j => t * _root_.GD.N0106.N0428.N0765.N1603.d005579 i j) (t * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ)) _root_.GD.N0106.N0428.N0765.N1603.d005589
      _root_.GD.N0106.N0428.N0765.N1603.d005590 hA (_root_.GD.N0106.N0428.N0765.N1626.d005788 ht) htq
    exact Matrix.mulVec_injective_iff_isUnit.mpr hu (hy.1.trans hw.symm)

theorem d005793 : (2000 : ℝ) * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) < 1 := by
  norm_num [_root_.GD.N0232.N0720.N1247.d002169]

theorem d005794 :
    (1 / 20 : ℝ) < (_root_.GD.N0232.N0720.N1247.d002170 3 : ℝ) -
      2000 * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ) * (_root_.GD.N0232.N0720.N1247.d002170 1 : ℝ) / (1 - 2000 * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ)) := by
  norm_num [_root_.GD.N0232.N0720.N1247.d002170, _root_.GD.N0232.N0720.N1247.d002169]



theorem d005795
    {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : _root_.GD.N0106.N0428.N0765.N1626.d005785 2000 A) :
    ∃! w : Fin 5 → ℝ, A *ᵥ w = _root_.GD.N0106.N0428.N0765.N1603.d005582 ∧ (∑ i, w i = 1) ∧ ∀ i, (1 / 20 : ℝ) < w i := by
  obtain ⟨w, ⟨hw, herr⟩, huniq⟩ := _root_.GD.N0106.N0428.N0765.N1626.d005789 (by norm_num)
    _root_.GD.N0106.N0428.N0765.N1626.d005793 hA
  refine ⟨w, ⟨hw, _root_.GD.N0106.N0428.N0765.N1626.d005791 hA hw, ?_⟩, ?_⟩
  · intro i
    have hlow := (abs_le.mp (herr i)).1
    have hmin : (_root_.GD.N0232.N0720.N1247.d002170 3 : ℝ) ≤ (_root_.GD.N0232.N0720.N1247.d002170 i : ℝ) := by
      exact_mod_cast _root_.GD.N0106.N0428.N0765.N1604.d005570 i
    linarith [_root_.GD.N0106.N0428.N0765.N1626.d005794]
  · intro y hy
    have hunit := _root_.GD.N0106.N0428.N0765.N1567.d005503 A _root_.GD.N0106.N0428.N0765.N1603.d005578 _root_.GD.N0106.N0428.N0765.N1603.d005580 _root_.GD.N0106.N0428.N0765.N1603.d005581
      (fun i j => (2000 : ℝ) * _root_.GD.N0106.N0428.N0765.N1603.d005579 i j) (2000 * (_root_.GD.N0232.N0720.N1247.d002169 : ℝ))
      _root_.GD.N0106.N0428.N0765.N1603.d005589 _root_.GD.N0106.N0428.N0765.N1603.d005590 hA (_root_.GD.N0106.N0428.N0765.N1626.d005788 (by norm_num))
      _root_.GD.N0106.N0428.N0765.N1626.d005793
    exact Matrix.mulVec_injective_iff_isUnit.mpr hunit (hy.1.trans hw.symm)

end
end GD.N0106.N0428.N0765.N1626
