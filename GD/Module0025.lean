import GD.Module0024























namespace GD
namespace N0230
namespace N0638

open _root_.GD.N0230.N0640

noncomputable section


def d000278 (a u : ℝ) : ℝ :=
  u * a / (a + u) ^ 2


def d000279 (a u : ℝ) : ℝ :=
  a / (a + u) - a / (a + 2 * u)


def d000280 (a u : ℝ) : ℝ :=
  u / (a + u)

theorem d000281
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) :
    0 ≤ _root_.GD.N0230.N0638.d000278 a u := by
  unfold _root_.GD.N0230.N0638.d000278
  exact div_nonneg (mul_nonneg hu ha) (sq_nonneg _)


theorem d000282
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) :
    _root_.GD.N0230.N0638.d000278 a u ≤ 1 / 4 := by
  have hsum : 0 < a + u := add_pos_of_nonneg_of_pos ha hu
  unfold _root_.GD.N0230.N0638.d000278
  apply (div_le_iff₀ (sq_pos_of_pos hsum)).2
  nlinarith [sq_nonneg (a - u)]



theorem d000283
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) :
    u * _root_.GD.N0230.N0638.d000278 a u ≤ a := by
  have hsum : 0 < a + u := add_pos_of_nonneg_of_pos ha hu
  unfold _root_.GD.N0230.N0638.d000278
  calc
    u * (u * a / (a + u) ^ 2) = u ^ 2 * a / (a + u) ^ 2 := by ring
    _ ≤ a := by
      apply (div_le_iff₀ (sq_pos_of_pos hsum)).2
      nlinarith [sq_nonneg a, mul_nonneg ha (sq_nonneg (a + u))]


theorem d000284
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) :
    _root_.GD.N0230.N0638.d000279 a u =
      a * u / ((a + u) * (a + 2 * u)) := by
  have h₁ : a + u ≠ 0 :=
    (add_pos_of_nonneg_of_pos ha hu).ne'
  have h₂ : a + 2 * u ≠ 0 := by
    positivity
  unfold _root_.GD.N0230.N0638.d000279
  field_simp [h₁, h₂]
  ring


theorem d000285
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) :
    _root_.GD.N0230.N0638.d000279 a u ≤ _root_.GD.N0230.N0638.d000278 a u := by
  rw [_root_.GD.N0230.N0638.d000284 ha hu]
  unfold _root_.GD.N0230.N0638.d000278
  have h₁ : 0 < a + u := add_pos_of_nonneg_of_pos ha hu
  have h₂ : 0 < a + 2 * u := by positivity
  have hd₁ : 0 < (a + u) * (a + 2 * u) := mul_pos h₁ h₂
  have hd₂ : 0 < (a + u) ^ 2 := sq_pos_of_pos h₁
  apply (div_le_div_iff₀ hd₁ hd₂).2
  have hden : (a + u) ^ 2 ≤ (a + u) * (a + 2 * u) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (by linarith) h₁.le
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hden (mul_nonneg ha hu.le)



theorem d000286
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) :
    _root_.GD.N0230.N0638.d000278 a u ≤ 2 * _root_.GD.N0230.N0638.d000279 a u := by
  rw [_root_.GD.N0230.N0638.d000284 ha hu]
  unfold _root_.GD.N0230.N0638.d000278
  have h₁ : 0 < a + u := add_pos_of_nonneg_of_pos ha hu
  have h₂ : 0 < a + 2 * u := by positivity
  have hd₁ : 0 < (a + u) ^ 2 := sq_pos_of_pos h₁
  have hd₂ : 0 < (a + u) * (a + 2 * u) := mul_pos h₁ h₂
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hd₁ hd₂).2
  have hden : (a + u) * (a + 2 * u) ≤ 2 * (a + u) ^ 2 := by
    calc
      (a + u) * (a + 2 * u) ≤ (a + u) * (2 * (a + u)) :=
        mul_le_mul_of_nonneg_left (by linarith) h₁.le
      _ = 2 * (a + u) ^ 2 := by ring
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hden (mul_nonneg hu.le ha)



theorem d000287
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) :
    _root_.GD.N0230.N0638.d000279 a u ≤ _root_.GD.N0230.N0638.d000278 a u ∧
      _root_.GD.N0230.N0638.d000278 a u ≤ 2 * _root_.GD.N0230.N0638.d000279 a u :=
  ⟨_root_.GD.N0230.N0638.d000285 ha hu,
    _root_.GD.N0230.N0638.d000286 ha hu⟩



theorem d000288
    (a : ℝ) (n : ℕ) :
    _root_.GD.N0230.N0640.d000254 a (n + 1) =
      _root_.GD.N0230.N0638.d000279 a (_root_.GD.N0230.N0640.d000252 (n + 1)) := by
  have ht : 2 * _root_.GD.N0230.N0640.d000252 (n + 1) = _root_.GD.N0230.N0640.d000252 n := by
    rw [_root_.GD.N0230.N0640.d000257]
    ring
  unfold _root_.GD.N0230.N0640.d000254 _root_.GD.N0230.N0640.d000253 _root_.GD.N0230.N0638.d000279
  rw [ht]



theorem d000289
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    _root_.GD.N0230.N0640.d000254 a (n + 1) ≤
        _root_.GD.N0230.N0638.d000278 a (_root_.GD.N0230.N0640.d000252 (n + 1)) ∧
      _root_.GD.N0230.N0638.d000278 a (_root_.GD.N0230.N0640.d000252 (n + 1)) ≤
        2 * _root_.GD.N0230.N0640.d000254 a (n + 1) := by
  rw [_root_.GD.N0230.N0638.d000288]
  exact _root_.GD.N0230.N0638.d000287 ha (_root_.GD.N0230.N0640.d000256 (n + 1))

theorem d000290
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) :
    0 ≤ _root_.GD.N0230.N0638.d000280 a u := by
  unfold _root_.GD.N0230.N0638.d000280
  exact div_nonneg hu (add_nonneg ha hu)

theorem d000291
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) :
    _root_.GD.N0230.N0638.d000280 a u ≤ 1 := by
  unfold _root_.GD.N0230.N0638.d000280
  exact (div_le_one (add_pos_of_nonneg_of_pos ha hu)).2
    (le_add_of_nonneg_left ha)



theorem d000292
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 < u) (hau : a ≤ u) :
    1 / 2 ≤ _root_.GD.N0230.N0638.d000280 a u := by
  unfold _root_.GD.N0230.N0638.d000280
  apply (le_div_iff₀ (add_pos_of_nonneg_of_pos ha hu)).2
  nlinarith



theorem d000293
    {a u r : ℝ} (hu : 0 ≤ u) (hr : 0 < r) (har : r ≤ a) :
    _root_.GD.N0230.N0638.d000280 a u ≤ u / r := by
  have ha : 0 ≤ a := le_trans hr.le har
  have hsum : 0 < a + u := add_pos_of_pos_of_nonneg (lt_of_lt_of_le hr har) hu
  unfold _root_.GD.N0230.N0638.d000280
  apply (div_le_iff₀ hsum).2
  have hratio : 0 ≤ u / r := div_nonneg hu hr.le
  calc
    u = (u / r) * r := by field_simp [hr.ne']
    _ ≤ (u / r) * (a + u) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hratio




theorem d000294
    {a u : ℝ} (hu : 0 < u) (ha : Real.sqrt u ≤ a) :
    _root_.GD.N0230.N0638.d000280 a u ≤ Real.sqrt u := by
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hbound := _root_.GD.N0230.N0638.d000293 hu.le hsqrt ha
  have hquot : u / Real.sqrt u = Real.sqrt u := by
    apply (div_eq_iff hsqrt.ne').2
    nlinarith [Real.sq_sqrt hu.le]
  simpa [hquot] using hbound

end

end N0638
end N0230
end GD

#print axioms _root_.GD.N0230.N0638.d000282
#print axioms _root_.GD.N0230.N0638.d000283
#print axioms _root_.GD.N0230.N0638.d000289
#print axioms _root_.GD.N0230.N0638.d000292
#print axioms _root_.GD.N0230.N0638.d000294
