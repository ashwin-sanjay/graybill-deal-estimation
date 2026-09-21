import GD.Module0943

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace GD.N0206.N0450
noncomputable section

open _root_.GD.N0232.N0720.N1310
open _root_.GD.N0232.N0720.N1309
open _root_.GD.N0232.N0720.N1313
open _root_.GD.N0232.N0720.N1091

theorem d023498 {a : ℝ} (ha : 0 < a) (C : ℝ) :
    ∃ e : ℝ, 0 < e ∧ C * e < _root_.GD.N0232.N0720.N1309.d013070 a 1 e := by
  let L : ℝ := (a + 1) * (|C| + 1) + a
  have hL : 0 < L := by dsimp [L]; positivity
  have haL : a < L := by
    dsimp [L]
    have : 0 < (a + 1) * (|C| + 1) := by positivity
    linarith
  let b : ℝ := 1 + a / L
  have hb : 1 < b := by dsimp [b]; linarith [div_pos ha hL]
  have hb2 : b ≤ 2 := by
    dsimp [b]
    have : a / L ≤ 1 := (div_le_one hL).2 haL.le
    linarith
  let e : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hlim := _root_.GD.N0232.N0720.N1309.d013079 ha hb he hepos
  have hvalue : a / (b - 1) = L := by
    dsimp [b]
    field_simp [ha.ne', hL.ne']
    ring
  rw [hvalue] at hlim
  have hCL : (a + 1) * C < L := by
    dsimp [L]
    have hC : C ≤ |C| := le_abs_self C
    nlinarith
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).1 ((a + 1) * C) hCL).exists
  have hbound := _root_.GD.N0232.N0720.N1313.d013092 ha hb.le hb2 (hepos n).le
  have hn' := (lt_div_iff₀ (hepos n)).1 hn
  refine ⟨e n, hepos n, ?_⟩
  nlinarith

theorem d023499 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hb1 : b ≤ 1) (u : ℝ) :
    betaPDFReal a 1 u ≤
      (a * ProbabilityTheory.beta a b) * betaPDFReal a b u := by
  by_cases hu : u ∈ Ioo (0 : ℝ) 1
  · have hpow : (1 : ℝ) ≤ (1 - u) ^ (b - 1) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge (sub_pos.mpr hu.2)
        (show 1 - u ≤ 1 by linarith [hu.1]) (show b - 1 ≤ 0 by linarith)
    have hp : 0 ≤ u ^ (a - 1) := Real.rpow_nonneg hu.1.le _
    rw [betaPDFReal, if_pos (show 0 < u ∧ u < 1 from hu), _root_.GD.N0232.N0720.N1313.d013083 ha,
      betaPDFReal, if_pos (show 0 < u ∧ u < 1 from hu)]
    simp only [sub_self, Real.rpow_zero, mul_one, one_div_div, div_one]
    have heq : (a * ProbabilityTheory.beta a b) *
        (1 / ProbabilityTheory.beta a b * u ^ (a - 1) * (1 - u) ^ (b - 1)) =
        a * u ^ (a - 1) * (1 - u) ^ (b - 1) := by
      field_simp [(beta_pos ha hb).ne']
    rw [heq]
    exact le_mul_of_one_le_right (mul_nonneg ha.le hp) hpow
  · simp only [betaPDFReal, if_neg (show ¬ (0 < u ∧ u < 1) from hu)]
    norm_num

theorem d023500 {a b e : ℝ} (ha : 0 < a) (hb : 0 < b)
    (he : 0 ≤ e) : Integrable (fun u ↦ betaPDFReal a b u *
      (_root_.GD.N0232.N0720.N1310.d013058 e (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 e) ^ 2) := by
  apply Integrable.mono' (_root_.GD.N0232.N0720.N1091.d012772 ha hb)
    (show Measurable (fun u ↦ betaPDFReal a b u *
      (_root_.GD.N0232.N0720.N1310.d013058 e (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 e) ^ 2) from by
      unfold _root_.GD.N0232.N0720.N1310.d013058 _root_.GD.N0232.N0720.N1309.d013069
      fun_prop).aestronglyMeasurable
  filter_upwards with u
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (_root_.GD.N0235.d004040 ha hb u),
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hg := _root_.GD.N0232.N0720.N1313.d013088 e (u / (1 - u))
  have ht := _root_.GD.N0232.N0720.N1313.d013089 he
  have hsq : (_root_.GD.N0232.N0720.N1310.d013058 e (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 e) ^ 2 ≤ 1 := by
    apply (sq_le_one_iff_abs_le_one _).2
    exact abs_le.mpr ⟨by linarith [hg.1, ht.2], by linarith [hg.2, ht.1]⟩
  exact mul_le_of_le_one_right (_root_.GD.N0235.d004040 ha hb u) hsq

theorem d023501 {a b e : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hb1 : b ≤ 1) (he : 0 ≤ e) :
    _root_.GD.N0232.N0720.N1309.d013070 a 1 e ≤ (a * ProbabilityTheory.beta a b) * _root_.GD.N0232.N0720.N1309.d013070 a b e := by
  unfold _root_.GD.N0232.N0720.N1309.d013070
  rw [_root_.GD.N0235.d004041 ha zero_lt_one,
    _root_.GD.N0235.d004041 ha hb,
    ← integral_const_mul]
  apply integral_mono (_root_.GD.N0206.N0450.d023500 ha zero_lt_one he)
    ((_root_.GD.N0206.N0450.d023500 ha hb he).const_mul (a * ProbabilityTheory.beta a b))
  intro u
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (_root_.GD.N0206.N0450.d023499 ha hb hb1 u)
    (sq_nonneg (_root_.GD.N0232.N0720.N1310.d013058 e (u / (1 - u)) - _root_.GD.N0232.N0720.N1309.d013069 e))

theorem d023502 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1)
    (C : ℝ) : ∃ e : ℝ, 0 < e ∧ C * e < _root_.GD.N0232.N0720.N1309.d013070 a b e := by
  have hA : 0 < a * ProbabilityTheory.beta a b := mul_pos ha (beta_pos ha hb)
  obtain ⟨e, he, hroot⟩ := _root_.GD.N0206.N0450.d023498 ha ((a * ProbabilityTheory.beta a b) * C)
  have hbound := _root_.GD.N0206.N0450.d023501 ha hb hb1 he.le
  refine ⟨e, he, ?_⟩
  nlinarith

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1311 _root_.GD.N0232.N0720.N1328 _root_.GD.N0232.N0720.N1436

theorem d023503 {alpha beta : ℝ}
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

theorem d023504 {epsilon : ℝ} (he : 0 < epsilon) :
    (1 / epsilon) / (1 + 1 / epsilon) ^ 2 = epsilon / (1 + epsilon) ^ 2 := by
  have hd : 1 + epsilon ≠ 0 := by positivity
  have hi : 1 + 1 / epsilon ≠ 0 := by positivity
  field_simp [he.ne', hd, hi]
  ring

theorem d023505 {epsilon : ℝ} (he : 0 < epsilon) :
    epsilon / (1 + epsilon) ^ 2 ≤ epsilon := by
  apply (div_le_iff₀ (sq_pos_of_pos (show 0 < 1 + epsilon by positivity))).2
  nlinarith [sq_nonneg epsilon]

theorem d023506 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (hb1 : beta ≤ 1) (C : ℝ) (hC : 0 ≤ C) :
    ¬ (∀ epsilon : ℝ, 0 < epsilon →
      _root_.GD.N0232.N0720.N1309.d013070 alpha beta epsilon ≤ C * (epsilon / (1 + epsilon) ^ 2)) := by
  intro hcap
  obtain ⟨e, he, hroot⟩ := _root_.GD.N0206.N0450.d023502 ha hb hb1 C
  have hbound := (hcap e he).trans (mul_le_mul_of_nonneg_left (_root_.GD.N0206.N0450.d023505 he) hC)
  exact (not_le_of_gt hroot) hbound

theorem d023507 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (hsmall : alpha ≤ 1 ∨ beta ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) :
    ¬ (∀ epsilon : ℝ, 0 < epsilon →
      _root_.GD.N0232.N0720.N1309.d013070 alpha beta epsilon ≤ C * (epsilon / (1 + epsilon) ^ 2)) := by
  rcases hsmall with ha1 | hb1
  · intro hcap
    apply _root_.GD.N0206.N0450.d023506 hb ha ha1 C hC
    intro e he
    have h := hcap (1 / e) (one_div_pos.mpr he)
    rwa [← _root_.GD.N0232.N0720.N1311.d013609 hb ha he, _root_.GD.N0206.N0450.d023504 he] at h
  · exact _root_.GD.N0206.N0450.d023506 ha hb hb1 C hC

theorem d023508 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ¬ (∀ epsilon : ℝ, 0 < epsilon →
      _root_.GD.N0232.N0720.N1309.d013070 alpha beta epsilon ≤ epsilon / (1 + epsilon) ^ 2) := by
  by_cases ha1 : alpha ≤ 1
  · simpa only [one_mul] using _root_.GD.N0206.N0450.d023507 ha hb (Or.inl ha1) 1 zero_le_one
  by_cases hb1 : beta ≤ 1
  · simpa only [one_mul] using _root_.GD.N0206.N0450.d023507 ha hb (Or.inr hb1) 1 zero_le_one
  intro hcap
  have hab : alpha ≤ beta - 1 := _root_.GD.N0206.N0450.d023503
    ha (lt_of_not_ge hb1) (fun e he ↦ (hcap e he).trans (_root_.GD.N0206.N0450.d023505 he))
  have hba : beta ≤ alpha - 1 := _root_.GD.N0206.N0450.d023503
    hb (lt_of_not_ge ha1) (by
      intro e he
      have h := hcap (1 / e) (one_div_pos.mpr he)
      rw [← _root_.GD.N0232.N0720.N1311.d013609 hb ha he, _root_.GD.N0206.N0450.d023504 he] at h
      exact h.trans (_root_.GD.N0206.N0450.d023505 he))
  linarith

theorem d023509 {m n : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (C : ℝ)
    (hcap : ∀ p : ℝ, p ∈ Ioo (0 : ℝ) 1 →
      (∫ x, (_root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 - p) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 m n p) ≤ C * p * (1 - p)) :
    ∀ e : ℝ, 0 < e → _root_.GD.N0232.N0720.N1309.d013070 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) e ≤
      C * (e / (1 + e) ^ 2) := by
  intro e he
  have hd : 0 < 1 + e := by positivity
  have hp : 1 / (1 + e) ∈ Ioo (0 : ℝ) 1 :=
    ⟨one_div_pos.mpr hd, (div_lt_one hd).2 (by linarith)⟩
  have h := hcap (1 / (1 + e)) hp
  rw [_root_.GD.N0232.N0720.N1328.d014766 hm hn he] at h
  have hid : C * (1 / (1 + e)) * (1 - 1 / (1 + e)) = C * (e / (1 + e) ^ 2) := by
    field_simp [hd.ne']
    ring
  rwa [hid] at h

theorem d023510 {m n : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ (∀ p : ℝ, p ∈ Ioo (0 : ℝ) 1 →
      (∫ x, (_root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 - p) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 m n p) ≤ p * (1 - p)) := by
  intro hcap
  apply _root_.GD.N0206.N0450.d023508 (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn)
  simpa only [one_mul] using _root_.GD.N0206.N0450.d023509 hm hn 1 (by simpa using hcap)

theorem d023511 {m n : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hsmall : m ≤ 3 ∨ n ≤ 3) (C : ℝ) (hC : 0 ≤ C) :
    ¬ (∀ p : ℝ, p ∈ Ioo (0 : ℝ) 1 →
      (∫ x, (_root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 - p) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 m n p) ≤ C * p * (1 - p)) := by
  intro hcap
  apply _root_.GD.N0206.N0450.d023507 (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn)
    (C := C) (hC := hC) ?_ (_root_.GD.N0206.N0450.d023509 hm hn C hcap)
  rcases hsmall with h | h
  · left
    unfold _root_.GD.N0232.N0720.N1436.d013207
    have h' : ((m - 1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show m - 1 ≤ 2 by omega)
    linarith
  · right
    unfold _root_.GD.N0232.N0720.N1436.d013208
    have h' : ((n - 1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (show n - 1 ≤ 2 by omega)
    linarith

end
end GD.N0206.N0450

#print axioms _root_.GD.N0206.N0450.d023502
#print axioms _root_.GD.N0206.N0450.d023510
#print axioms _root_.GD.N0206.N0450.d023511
