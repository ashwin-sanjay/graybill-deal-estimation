import GD.Module0943

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace GD.N0207.N0452

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1309 _root_.GD.N0232.N0720.N1311
open _root_.GD.N0232.N0720.N1328 _root_.GD.N0232.N0720.N1436

noncomputable section

theorem d023493 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 1 < beta)
    (hcap : ∀ epsilon : ℝ, 0 < epsilon → _root_.GD.N0232.N0720.N1309.d013070 alpha beta epsilon ≤ epsilon) :
    alpha ≤ beta - 1 := by
  let epsilon : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have he : Tendsto epsilon atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hepos (n : ℕ) : 0 < epsilon n := by unfold epsilon; positivity
  have hlim := _root_.GD.N0232.N0720.N1309.d013079 ha hb he hepos
  have hle : alpha / (beta - 1) ≤ 1 :=
    le_of_tendsto hlim (Eventually.of_forall fun n ↦
      (div_le_one (hepos n)).2 (hcap (epsilon n) (hepos n)))
  exact (div_le_one (sub_pos.mpr hb)).1 hle

theorem d023494 {epsilon : ℝ} (he : 0 < epsilon) :
    (1 / epsilon) / (1 + 1 / epsilon) ^ 2 = epsilon / (1 + epsilon) ^ 2 := by
  have hd : 1 + epsilon ≠ 0 := by positivity
  have hi : 1 + 1 / epsilon ≠ 0 := by positivity
  field_simp [he.ne', hd, hi]
  ring

theorem d023495 {epsilon : ℝ} (he : 0 < epsilon) :
    epsilon / (1 + epsilon) ^ 2 ≤ epsilon := by
  apply (div_le_iff₀ (sq_pos_of_pos (show 0 < 1 + epsilon by positivity))).2
  nlinarith [sq_nonneg epsilon]

theorem d023496 {alpha beta : ℝ}
    (ha : 1 < alpha) (hb : 1 < beta) :
    ¬ (∀ epsilon : ℝ, 0 < epsilon →
      _root_.GD.N0232.N0720.N1309.d013070 alpha beta epsilon ≤ epsilon / (1 + epsilon) ^ 2) := by
  intro hcap
  have hab : alpha ≤ beta - 1 := _root_.GD.N0207.N0452.d023493
    (lt_trans zero_lt_one ha) hb (fun e he ↦ (hcap e he).trans (_root_.GD.N0207.N0452.d023495 he))
  have hba : beta ≤ alpha - 1 := _root_.GD.N0207.N0452.d023493
    (lt_trans zero_lt_one hb) ha (by
      intro e he
      have h := hcap (1 / e) (one_div_pos.mpr he)
      rw [← _root_.GD.N0232.N0720.N1311.d013609 (lt_trans zero_lt_one hb)
        (lt_trans zero_lt_one ha) he, _root_.GD.N0207.N0452.d023494 he] at h
      exact h.trans (_root_.GD.N0207.N0452.d023495 he))
  linarith

theorem d023497 {m n : ℕ}
    (hm : 4 ≤ m) (hn : 4 ≤ n) :
    ¬ (∀ p : ℝ, p ∈ Ioo (0 : ℝ) 1 →
      (∫ x, (_root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 - p) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 m n p) ≤ p * (1 - p)) := by
  have hm2 : 2 ≤ m := by omega
  have hn2 : 2 ≤ n := by omega
  have ha : 1 < _root_.GD.N0232.N0720.N1436.d013207 m := by
    unfold _root_.GD.N0232.N0720.N1436.d013207
    have h : (3 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ m - 1 by omega)
    linarith
  have hb : 1 < _root_.GD.N0232.N0720.N1436.d013208 n := by
    unfold _root_.GD.N0232.N0720.N1436.d013208
    have h : (3 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ n - 1 by omega)
    linarith
  intro hcap
  apply _root_.GD.N0207.N0452.d023496 ha hb
  intro e he
  have hd : 0 < 1 + e := by positivity
  have hp : 1 / (1 + e) ∈ Ioo (0 : ℝ) 1 :=
    ⟨one_div_pos.mpr hd, (div_lt_one hd).2 (by linarith)⟩
  have h := hcap (1 / (1 + e)) hp
  rw [_root_.GD.N0232.N0720.N1328.d014766 hm2 hn2 he] at h
  have hid : 1 / (1 + e) * (1 - 1 / (1 + e)) = e / (1 + e) ^ 2 := by
    field_simp [hd.ne']
    ring
  rwa [hid] at h

end
end GD.N0207.N0452

#print axioms _root_.GD.N0207.N0452.d023493
#print axioms _root_.GD.N0207.N0452.d023496
#print axioms _root_.GD.N0207.N0452.d023497
