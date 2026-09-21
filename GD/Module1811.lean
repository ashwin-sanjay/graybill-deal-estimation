import GD.Module0812

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace GD.N0046.N0302

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0843 _root_.GD.N0232.N0719.N0966
open _root_.GD.N0230.N0602

theorem d030041 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (p q : H) :
    ‖(1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q‖ ^ 2 + ‖p - q‖ ^ 2 / 4 =
      (‖p‖ ^ 2 + ‖q‖ ^ 2) / 2 := by
  rw [← smul_add, norm_smul, Real.norm_eq_abs]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [mul_pow, norm_add_sq_real, norm_sub_sq_real]
  ring

variable (k : ℕ) (sizes : Fin k → ℕ)

def d030042 (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ)
    (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) : ℝ :=
  C * γ.value (_root_.GD.N0232.N0719.N0859.d010810 k) + ∑ θ ∈ F, w θ * (C * γ.value θ) -
    _root_.GD.N0232.N0719.N0966.d012351 k sizes F w

theorem d030043
    (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ) (hC : 0 ≤ C)
    (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ)
    {p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)}
    (hp : p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C) (hq : q ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C) :
    ‖p - q‖ ^ 2 / 4 ≤ _root_.GD.N0046.N0302.d030042 k sizes γ C F w := by
  classical
  let z := (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q
  have hz : z ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C :=
    _root_.GD.N0232.N0719.N0843.d012218 k sizes γ C hp hq (by norm_num) (by norm_num) (by norm_num)
  have hb := _root_.GD.N0232.N0719.N0966.d012352 k sizes F w hw z
    (_root_.GD.N0232.N0719.N0843.d012219 k sizes γ hz)
  have hsum : (∑ θ ∈ F, w θ * (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ z).toReal) ≤
      ∑ θ ∈ F, w θ * (C * γ.value θ) := by
    apply Finset.sum_le_sum
    intro θ hθ
    apply mul_le_mul_of_nonneg_left _ (hw θ hθ)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hz θ)).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hC (γ.positive θ).le))
  have hpE := _root_.GD.N0232.N0719.N0843.d012220 k sizes γ hC hp
  have hqE := _root_.GD.N0232.N0719.N0843.d012220 k sizes γ hC hq
  have hid := _root_.GD.N0046.N0302.d030041 p q
  change ‖z‖ ^ 2 + ‖p - q‖ ^ 2 / 4 = (‖p‖ ^ 2 + ‖q‖ ^ 2) / 2 at hid
  unfold _root_.GD.N0046.N0302.d030042
  linarith

theorem d030044
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ) (hC : 0 ≤ C) :
    (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ C).Nonempty ↔
      ∀ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) → 0 ≤ _root_.GD.N0046.N0302.d030042 k sizes γ C F w := by
  rw [_root_.GD.N0232.N0719.N0966.d012355 k sizes hk hsizes γ C hC]
  simp only [_root_.GD.N0046.N0302.d030042, sub_nonneg]

theorem d030045
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ) (hC : 0 ≤ C) :
    _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C = ∅ ↔
      ∃ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ _root_.GD.N0046.N0302.d030042 k sizes γ C F w < 0 := by
  classical
  rw [← Set.not_nonempty_iff_eq_empty, _root_.GD.N0046.N0302.d030044 k sizes hk hsizes γ C hC]
  push Not
  rfl

theorem d030046
    (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ) (hC : 0 ≤ C)
    (hsaturation : ∀ ε : ℝ, 0 < ε →
      ∃ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ _root_.GD.N0046.N0302.d030042 k sizes γ C F w < ε) :
    (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ C).Subsingleton := by
  intro p hp q hq
  by_contra hne
  have hd : 0 < ‖p - q‖ ^ 2 / 4 :=
    div_pos (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))) (by norm_num)
  obtain ⟨F, w, hw, hgap⟩ := hsaturation _ hd
  exact (not_lt_of_ge (_root_.GD.N0046.N0302.d030043 k sizes γ C hC F w hw hp hq)) hgap

theorem d030047
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ) (hC : 0 ≤ C)
    (hfeasible : ∀ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) → 0 ≤ _root_.GD.N0046.N0302.d030042 k sizes γ C F w)
    (hsaturation : ∀ ε : ℝ, 0 < ε →
      ∃ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ _root_.GD.N0046.N0302.d030042 k sizes γ C F w < ε) :
    ∃! p, p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C := by
  obtain ⟨p, hp⟩ :=
    (_root_.GD.N0046.N0302.d030044 k sizes hk hsizes γ C hC).mpr hfeasible
  exact ⟨p, hp, fun q hq => _root_.GD.N0046.N0302.d030046 k sizes γ C hC hsaturation hq hp⟩

theorem d030048
    (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ) (hC : 0 ≤ C)
    {p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)}
    (hp : p ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C) (hq : q ∈ _root_.GD.N0232.N0719.N0843.d012216 k sizes γ C) (hne : p ≠ q) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) → ε ≤ _root_.GD.N0046.N0302.d030042 k sizes γ C F w := by
  refine ⟨‖p - q‖ ^ 2 / 4, ?_, fun F w hw =>
    _root_.GD.N0046.N0302.d030043 k sizes γ C hC F w hw hp hq⟩
  exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))) (by norm_num)

theorem d030049
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (γ η : _root_.GD.N0232.N0719.N0843.d012215 k) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ a ∩ _root_.GD.N0232.N0719.N0843.d012216 k sizes η b).Nonempty ↔
      ∀ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) → _root_.GD.N0232.N0719.N0966.d012351 k sizes F w ≤
          min (a * γ.value (_root_.GD.N0232.N0719.N0859.d010810 k)) (b * η.value (_root_.GD.N0232.N0719.N0859.d010810 k)) +
            ∑ θ ∈ F, w θ * min (a * γ.value θ) (b * η.value θ) := by
  have hset : _root_.GD.N0232.N0719.N0843.d012216 k sizes (_root_.GD.N0232.N0719.N0972.d012345 k γ η a b ha hb) 1 =
      _root_.GD.N0232.N0719.N0843.d012216 k sizes γ a ∩ _root_.GD.N0232.N0719.N0843.d012216 k sizes η b := by
    ext p
    exact _root_.GD.N0232.N0719.N0972.d012346 k sizes γ η a b ha hb p
  rw [← hset, _root_.GD.N0232.N0719.N0966.d012355 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0972.d012345 k γ η a b ha hb) 1 (by norm_num)]
  simp only [_root_.GD.N0232.N0719.N0972.d012345, one_mul]

end

end GD.N0046.N0302

#print axioms _root_.GD.N0046.N0302.d030041
#print axioms _root_.GD.N0046.N0302.d030043
#print axioms _root_.GD.N0046.N0302.d030044
#print axioms _root_.GD.N0046.N0302.d030045
#print axioms _root_.GD.N0046.N0302.d030046
#print axioms _root_.GD.N0046.N0302.d030047
#print axioms _root_.GD.N0046.N0302.d030048
#print axioms _root_.GD.N0046.N0302.d030049
