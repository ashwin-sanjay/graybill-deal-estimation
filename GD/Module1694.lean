import GD.Module1693

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace GD.N0083
noncomputable section

open _root_.GD.N0072 _root_.GD.N0089
open _root_.GD.N0102.N0422

variable {k : ℕ}

theorem d028547 (v : Fin k → ℝ)
    (hv : ∀ j, 0 < v j) (i : Fin k) : _root_.GD.N0089.d028298 v ≤ v i := by
  have hs : (v i)⁻¹ ≤ _root_.GD.N0102.N0422.d028281 v :=
    Finset.single_le_sum (fun j _ => (inv_pos.mpr (hv j)).le) (Finset.mem_univ i)
  simpa only [_root_.GD.N0089.d028298, one_div, inv_inv] using
    one_div_le_one_div_of_le (inv_pos.mpr (hv i)) hs

theorem d028548 (shape : Fin k → ℝ) (i : Fin k)
    (w : (Fin k → ℝ) → Fin k → ℝ) {M : ℝ} (hM : 0 < M) :
    ENNReal.ofReal M * _root_.GD.N0083.d028537 shape (_root_.GD.N0083.d028535 i M) w i ≤
      _root_.GD.N0083.d028538 shape (_root_.GD.N0083.d028535 i M) w := by
  rw [_root_.GD.N0083.d028537, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  change ENNReal.ofReal M * ENNReal.ofReal (w x i ^ 2) ≤
    ENNReal.ofReal (_root_.GD.N0072.d007621 (_root_.GD.N0083.d028535 i M) (w x))
  rw [← ENNReal.ofReal_mul hM.le]
  apply ENNReal.ofReal_le_ofReal
  have hh : w x i ^ 2 * _root_.GD.N0083.d028535 i M i ≤ _root_.GD.N0072.d007621 (_root_.GD.N0083.d028535 i M) (w x) :=
    Finset.single_le_sum (fun j _ => mul_nonneg (sq_nonneg _)
      (_root_.GD.N0083.d028539 i hM j).le) (Finset.mem_univ i)
  simpa only [_root_.GD.N0083.d028535, Function.update_self, mul_comm] using hh

theorem d028549 {shape : Fin k → ℝ}
    (hk : 0 < k) (hshape : ∀ j, 0 < shape j) (i : Fin k)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ x, ∑ j, w x j = 1)
    (hzero : _root_.GD.N0083.d028537 shape (fun _ => 1) w i = 0)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    ENNReal.ofReal (_root_.GD.N0089.d028298 (fun _ : Fin k => 1)) ≤
      _root_.GD.N0083.d028538 shape (_root_.GD.N0083.d028535 i e) w := by
  letI := _root_.GD.N0083.d028543 hshape (_root_.GD.N0083.d028539 i he)
  have hAE := _root_.GD.N0083.d028546 hshape i w hw hzero he he1
  calc
    _ = ∫⁻ _x : Fin k → ℝ, ENNReal.ofReal (_root_.GD.N0089.d028298 (fun _ : Fin k => 1))
        ∂_root_.GD.N0083.d028536 shape (_root_.GD.N0083.d028535 i e) := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [hAE] with x hx
      apply ENNReal.ofReal_le_ofReal
      have hh := _root_.GD.N0089.d028300 hk (fun _ => 1) (w x)
        (fun _ => by norm_num) (hunit x)
      have heq : _root_.GD.N0072.d007621 (_root_.GD.N0083.d028535 i e) (w x) = _root_.GD.N0072.d007621 (fun _ => 1) (w x) := by
        unfold _root_.GD.N0072.d007621
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = i
        · subst j; simp [hx]
        · simp [_root_.GD.N0083.d028535, Function.update_of_ne hj]
      rw [heq]
      exact hh



theorem d028550 {shape : Fin k → ℝ}
    (hk : 2 ≤ k) (hshape : ∀ j, 0 < shape j) (i : Fin k) (hi : shape i < 1)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ x, ∑ j, w x j = 1) (C : ℝ) (hC : 0 ≤ C) :
    ¬ (∀ v : Fin k → ℝ, (∀ j, 0 < v j) →
      _root_.GD.N0083.d028538 shape v w ≤ ENNReal.ofReal (C * _root_.GD.N0089.d028298 v)) := by
  intro hcap
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card (Fin k) by simpa using (show 1 < k by omega)) i
  have hzero : _root_.GD.N0083.d028537 shape (fun _ => 1) w i = 0 := by
    apply _root_.GD.N0083.d028544 hshape i hi w hC
    intro M hM
    have hMp : 0 < M := lt_of_lt_of_le (by norm_num) hM
    have hHv : _root_.GD.N0089.d028298 (_root_.GD.N0083.d028535 i M) ≤ 1 := by
      have hh := _root_.GD.N0083.d028547 (_root_.GD.N0083.d028535 i M) (_root_.GD.N0083.d028539 i hMp) j
      simpa [_root_.GD.N0083.d028535, Function.update_of_ne hj] using hh
    calc
      _ ≤ _root_.GD.N0083.d028538 shape (_root_.GD.N0083.d028535 i M) w := _root_.GD.N0083.d028548 shape i w hMp
      _ ≤ ENNReal.ofReal (C * _root_.GD.N0089.d028298 (_root_.GD.N0083.d028535 i M)) :=
        hcap _ (_root_.GD.N0083.d028539 i hMp)
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by nlinarith)
  let B := _root_.GD.N0089.d028298 (fun _ : Fin k => 1)
  have hB : 0 < B := _root_.GD.N0089.d028299 (by omega) _ (fun _ => by norm_num)
  have hB1 : B ≤ 1 := _root_.GD.N0083.d028547 _ (fun _ => by norm_num) i
  let e := B / (C + 1)
  have hden : 0 < C + 1 := by linarith
  have he : 0 < e := div_pos hB hden
  have he1 : e ≤ 1 := (div_le_one hden).2 (by linarith)
  have heq : e * (C + 1) = B := div_mul_cancel₀ B hden.ne'
  have hCB : C * e < B := by nlinarith
  have hH : _root_.GD.N0089.d028298 (_root_.GD.N0083.d028535 i e) ≤ e := by
    simpa only [_root_.GD.N0083.d028535, Function.update_self] using
      _root_.GD.N0083.d028547 (_root_.GD.N0083.d028535 i e) (_root_.GD.N0083.d028539 i he) i
  have hh : ENNReal.ofReal B ≤ ENNReal.ofReal (C * e) := by
    calc
      _ ≤ _root_.GD.N0083.d028538 shape (_root_.GD.N0083.d028535 i e) w :=
        _root_.GD.N0083.d028549 (by omega) hshape i w hw hunit hzero he he1
      _ ≤ ENNReal.ofReal (C * _root_.GD.N0089.d028298 (_root_.GD.N0083.d028535 i e)) :=
        hcap _ (_root_.GD.N0083.d028539 i he)
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hH hC)
  exact (not_le_of_gt hCB) ((ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC he.le)).mp hh)

end
end GD.N0083

#print axioms _root_.GD.N0083.d028549
#print axioms _root_.GD.N0083.d028550
