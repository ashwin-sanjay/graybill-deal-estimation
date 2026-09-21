import GD.Module1480

set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators

namespace GD.N0213.N0482
noncomputable section
open _root_.GD.N0213.N0523 _root_.GD.N0213.N0517

variable {k : ℕ} [NeZero k]

theorem d023256 (a : ℝ) :
    _root_.GD.N0213.N0517.d023248 (fun _ : Fin k => a) ↔ ((k : ℝ) - 1) / k < a := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (NeZero.pos k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (NeZero.pos k)
  simp only [_root_.GD.N0213.N0517.d023248, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, div_lt_iff₀ hk]
  constructor
  · intro h
    nlinarith [h.1]
  · intro h
    have ha : 0 < a := (mul_pos_iff_of_pos_left hk).mp
      (show 0 < (k : ℝ) * a by nlinarith)
    constructor
    · nlinarith
    · intro i
      nlinarith

theorem d023257 {a : ℝ} (ha : 1 ≤ a) :
    _root_.GD.N0213.N0517.d023248 (fun _ : Fin k => a) := by
  apply (_root_.GD.N0213.N0482.d023256 a).mpr
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (NeZero.pos k)
  apply (div_lt_iff₀ hk).mpr
  nlinarith

omit [NeZero k] in
theorem d023258 (a : Fin k → ℝ) (c : ℝ) :
    _root_.GD.N0213.N0523.d023154 (fun i => c * a i) = _root_.GD.N0213.N0523.d023154 a / c := by
  unfold _root_.GD.N0213.N0523.d023154
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

omit [NeZero k] in
theorem d023259 (a : Fin k → ℝ) {c : ℝ} (hc : c ≠ 0) :
    _root_.GD.N0213.N0523.d023155 (fun i => c * a i) = _root_.GD.N0213.N0523.d023155 a := by
  funext i
  unfold _root_.GD.N0213.N0523.d023155
  rw [_root_.GD.N0213.N0482.d023258]
  field_simp

theorem d023260 {a : ℝ} (ha : a ≠ 0) :
    _root_.GD.N0213.N0523.d023155 (fun _ : Fin k => a) = fun _ => (k : ℝ)⁻¹ := by
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  funext i
  unfold _root_.GD.N0213.N0523.d023155 _root_.GD.N0213.N0523.d023154
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem d023261 {a : ℝ} (ha : a ≠ 0) :
    _root_.GD.N0213.N0523.d023144 a (_root_.GD.N0213.N0523.d023154 (fun _ : Fin k => a)) = a + (k : ℝ)⁻¹ := by
  let i : Fin k := ⟨0, NeZero.pos k⟩
  have h := congrFun (_root_.GD.N0213.N0482.d023260 (k := k) ha) i
  simp only [_root_.GD.N0213.N0523.d023155] at h
  unfold _root_.GD.N0213.N0523.d023144
  nlinarith

omit [NeZero k] in
theorem d023262 (a : Fin k → ℝ) (hA : (∑ i, a i) ≠ 0)
    (ρ : ℝ) (hsum : ∑ i, (1 - ρ * a i) = 1) :
    ρ = _root_.GD.N0213.N0523.d023154 a := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hsum
  apply (eq_div_iff hA).mpr
  linarith

theorem d023263 (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    (∃ ρ : ℝ, ρ < 1 ∧ (∀ i, 0 < 1 - ρ * a i) ∧
      ∑ i, (1 - ρ * a i) = 1) ↔ _root_.GD.N0213.N0517.d023248 a := by
  constructor
  · rintro ⟨ρ, hρ, hα, hsum⟩
    have hA : (∑ i, a i) ≠ 0 :=
      (Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty).ne'
    have heq := _root_.GD.N0213.N0482.d023262 a hA ρ hsum
    subst ρ
    exact (_root_.GD.N0213.N0523.d023157 a ha).mp ⟨hρ, hα⟩
  · intro h
    exact ⟨_root_.GD.N0213.N0523.d023154 a, _root_.GD.N0213.N0517.d023250 a ha h⟩

theorem d023264 (a : Fin k → ℝ) (ha : ∀ i, 0 < a i)
    {c : ℝ} (hc : 0 < c) :
    _root_.GD.N0213.N0517.d023248 (fun i => c * a i) ↔
      _root_.GD.N0213.N0523.d023154 a < c ∧ (∀ i, 0 < _root_.GD.N0213.N0523.d023155 a i) := by
  unfold _root_.GD.N0213.N0517.d023248
  rw [← _root_.GD.N0213.N0523.d023157 _ (fun i => mul_pos hc (ha i)),
    _root_.GD.N0213.N0482.d023258, _root_.GD.N0213.N0482.d023259 a hc.ne', div_lt_one hc]

theorem d023265 (hk : 2 ≤ k)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    _root_.GD.N0213.N0517.d023248 a ↔ ∃ t : ℝ, 1 < t ∧
      ∃ α : Fin k → ℝ, (∀ i, α i ∈ Set.Ioo 0 1) ∧
        (∑ i, α i = 1) ∧ ∀ i, a i = t * (1 - α i) := by
  have hkm : (0 : ℝ) < (k : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hA : 0 < ∑ i, a i :=
    Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  constructor
  · intro h
    have hc := _root_.GD.N0213.N0517.d023250 a ha h
    have hρ : 0 < _root_.GD.N0213.N0523.d023154 a := div_pos hkm hA
    refine ⟨(∑ i, a i) / ((k : ℝ) - 1), ?_, _root_.GD.N0213.N0523.d023155 a, ?_, hc.2.2, ?_⟩
    · apply (lt_div_iff₀ hkm).mpr
      simpa only [one_mul] using h.1
    · intro i
      exact ⟨hc.2.1 i, by
        unfold _root_.GD.N0213.N0523.d023155
        have := mul_pos hρ (ha i)
        linarith⟩
    · intro i
      unfold _root_.GD.N0213.N0523.d023155 _root_.GD.N0213.N0523.d023154
      field_simp [hA.ne', hkm.ne']
      ring
  · rintro ⟨t, ht, α, hα, hsum, heq⟩
    have ht0 : 0 < t := zero_lt_one.trans ht
    apply (_root_.GD.N0213.N0482.d023263 a ha).mp
    have hid : (fun i => 1 - (1 / t) * a i) = α := by
      funext i
      rw [heq i]
      field_simp [ht0.ne']
      ring
    refine ⟨1 / t, (div_lt_one ht0).mpr ht, ?_, ?_⟩
    · intro i
      rw [congrFun hid i]
      exact (hα i).1
    · rw [show (fun i => 1 - 1 / t * a i) = α from hid]
      exact hsum

end
end GD.N0213.N0482

#print axioms _root_.GD.N0213.N0482.d023256
#print axioms _root_.GD.N0213.N0482.d023259
#print axioms _root_.GD.N0213.N0482.d023260
#print axioms _root_.GD.N0213.N0482.d023261
#print axioms _root_.GD.N0213.N0482.d023263
#print axioms _root_.GD.N0213.N0482.d023264
#print axioms _root_.GD.N0213.N0482.d023265
