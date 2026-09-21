import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace GD.N0103
noncomputable section

variable {k : ℕ}

def d005208 (a : Fin k → ℝ) : ℝ := ∑ i, a i

def d005209 (a : Fin k → ℝ) : ℝ := ((k : ℝ) - 1) / _root_.GD.N0103.d005208 a

def d005210 (a : Fin k → ℝ) (i : Fin k) : ℝ := 1 - _root_.GD.N0103.d005209 a * a i

theorem d005211 (a : Fin k → ℝ) (hk : 0 < k) (ha : ∀ i, 0 < a i) :
    0 < _root_.GD.N0103.d005208 a :=
  Finset.sum_pos (fun i _ => ha i) ⟨⟨0, hk⟩, Finset.mem_univ _⟩

theorem d005212 (a : Fin k → ℝ) (hA : _root_.GD.N0103.d005208 a ≠ 0) :
    ∑ i, _root_.GD.N0103.d005210 a i = 1 := by
  unfold _root_.GD.N0103.d005210
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hones : (∑ _i : Fin k, (1 : ℝ)) = (k : ℝ) := by simp
  rw [hones]
  change (k : ℝ) - (((k : ℝ) - 1) / _root_.GD.N0103.d005208 a) * _root_.GD.N0103.d005208 a = 1
  rw [div_mul_cancel₀ _ hA]
  ring

theorem d005213 (a : Fin k → ℝ) (hA : 0 < _root_.GD.N0103.d005208 a) :
    _root_.GD.N0103.d005209 a < 1 ↔ (k : ℝ) - 1 < _root_.GD.N0103.d005208 a := by
  unfold _root_.GD.N0103.d005209
  rw [div_lt_iff₀ hA, one_mul]

theorem d005214 (a : Fin k → ℝ) (hA : 0 < _root_.GD.N0103.d005208 a) (i : Fin k) :
    0 < _root_.GD.N0103.d005210 a i ↔ ((k : ℝ) - 1) * a i < _root_.GD.N0103.d005208 a := by
  unfold _root_.GD.N0103.d005210 _root_.GD.N0103.d005209
  have heq : (((k : ℝ) - 1) / _root_.GD.N0103.d005208 a) * a i =
      (((k : ℝ) - 1) * a i) / _root_.GD.N0103.d005208 a := by ring
  rw [sub_pos, heq, div_lt_iff₀ hA, one_mul]

theorem d005215 (a : Fin k → ℝ) (ha : ∀ i, 1 ≤ a i) :
    (k : ℝ) ≤ _root_.GD.N0103.d005208 a := by
  unfold _root_.GD.N0103.d005208
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    using Finset.sum_le_sum (s := Finset.univ) (fun i _ => ha i)

theorem d005216 (a : Fin k → ℝ) (hk : 0 < k)
    (ha : ∀ i, 1 ≤ a i) : _root_.GD.N0103.d005209 a < 1 := by
  have hA := _root_.GD.N0103.d005211 a hk (fun i => zero_lt_one.trans_le (ha i))
  apply (_root_.GD.N0103.d005213 a hA).mpr
  have hsum := _root_.GD.N0103.d005215 a ha
  linarith

theorem d005217 (a : Fin k → ℝ) (ha : ∀ i, 1 ≤ a i) (i j : Fin k) :
    1 < a i + a j := by linarith [ha i, ha j]

theorem d005218 (hk : 0 < k) {a : ℝ} (ha : 0 < a) (i : Fin k) :
    _root_.GD.N0103.d005210 (fun _ : Fin k => a) i = 1 / (k : ℝ) := by
  have hA : _root_.GD.N0103.d005208 (fun _ : Fin k => a) = (k : ℝ) * a := by simp [_root_.GD.N0103.d005208]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  change 1 - (((k : ℝ) - 1) / _root_.GD.N0103.d005208 (fun _ : Fin k => a)) * a = 1 / (k : ℝ)
  rw [hA]
  field_simp [hkR, ha.ne']
  ring

theorem d005219 (hk : 0 < k) {a : ℝ} (ha : 1 ≤ a) :
    _root_.GD.N0103.d005209 (fun _ : Fin k => a) < 1 ∧
      (∀ i, 0 < _root_.GD.N0103.d005210 (fun _ : Fin k => a) i) ∧
      (∑ i, _root_.GD.N0103.d005210 (fun _ : Fin k => a) i) = 1 := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  refine ⟨_root_.GD.N0103.d005216 _ hk (fun _ => ha), ?_,
    _root_.GD.N0103.d005212 _ (_root_.GD.N0103.d005211 _ hk (fun _ => ha0)).ne'⟩
  intro i
  rw [_root_.GD.N0103.d005218 hk ha0 i]
  exact div_pos zero_lt_one (by exact_mod_cast hk)

theorem d005220 (hk : 2 ≤ k) {n : ℕ} (hn : 3 ≤ n) :
    let a : Fin k → ℝ := fun _ => ((n : ℝ) - 1) / 2
    _root_.GD.N0103.d005209 a < 1 ∧ (∀ i, 0 < _root_.GD.N0103.d005210 a i) ∧
      (∑ i, _root_.GD.N0103.d005210 a i) = 1 ∧ (∀ i, _root_.GD.N0103.d005210 a i = 1 / (k : ℝ)) := by
  have hk0 : 0 < k := by omega
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha : 1 ≤ ((n : ℝ) - 1) / 2 := by linarith
  obtain ⟨hρ, hα, hsum⟩ := _root_.GD.N0103.d005219 hk0 ha
  exact ⟨hρ, hα, hsum, fun i => _root_.GD.N0103.d005218 hk0 (zero_lt_one.trans_le ha) i⟩

#print axioms _root_.GD.N0103.d005211
#print axioms _root_.GD.N0103.d005212
#print axioms _root_.GD.N0103.d005213
#print axioms _root_.GD.N0103.d005214
#print axioms _root_.GD.N0103.d005215
#print axioms _root_.GD.N0103.d005216
#print axioms _root_.GD.N0103.d005217
#print axioms _root_.GD.N0103.d005218
#print axioms _root_.GD.N0103.d005219
#print axioms _root_.GD.N0103.d005220

end
end GD.N0103
