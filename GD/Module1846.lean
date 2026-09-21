import GD.Module1845

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0024.N0273

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1220
open _root_.GD.N0034.N0289 _root_.GD.N0024.N0274
open _root_.GD.N0046.N0305

local instance : DecidableEq _root_.GD.N0232.N0720.N1080.d014168 := Classical.decEq _

def d030355 (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (t : ℝ) : _root_.GD.N0232.N0720.N1080.d014168 → ℝ :=
  fun θ => (if θ = _root_.GD.N0232.N0720.N1080.d014169 then t - 1 else 0) +
    (if θ ∈ F then t * w θ else 0)

theorem d030356 (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (t : ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ) (ht : 1 ≤ t) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    0 ≤ _root_.GD.N0024.N0273.d030355 F w t θ := by
  unfold _root_.GD.N0024.N0273.d030355
  apply add_nonneg
  · split_ifs <;> linarith
  · split_ifs with h
    · exact mul_nonneg (by linarith) (hw θ h)
    · exact le_rfl

theorem d030357 (a : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (t : ℝ) :
    _root_.GD.N0024.N0274.d030344 a (insert _root_.GD.N0232.N0720.N1080.d014169 F) (_root_.GD.N0024.N0273.d030355 F w t) =
      t * _root_.GD.N0024.N0274.d030344 a F w := by
  classical
  have hsubset :
      (∑ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F, (if θ ∈ F then t * w θ else 0) * a θ) =
        ∑ θ ∈ F, t * w θ * a θ := by
    calc
      _ = ∑ θ ∈ F, (if θ ∈ F then t * w θ else 0) * a θ := by
        symm
        apply Finset.sum_subset (Finset.subset_insert _ _)
        intro θ _ hθ
        simp [hθ]
      _ = _ := Finset.sum_congr rfl (fun θ hθ => by simp [hθ])
  unfold _root_.GD.N0024.N0274.d030344 _root_.GD.N0024.N0273.d030355
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, hsubset]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_insert_self, if_true]
  simp_rw [mul_add, Finset.mul_sum, mul_assoc]
  ring

theorem d030358 (m n : ℕ)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (t : ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ) (ht : 1 ≤ t) :
    _root_.GD.N0232.N0720.N1220.d017301 m n (insert _root_.GD.N0232.N0720.N1080.d014169 F) (_root_.GD.N0024.N0273.d030355 F w t) =
      t * _root_.GD.N0232.N0720.N1220.d017301 m n F w := by
  classical
  have hw' : ∀ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F, 0 ≤ _root_.GD.N0024.N0273.d030355 F w t θ :=
    fun θ _ => _root_.GD.N0024.N0273.d030356 F w t hw ht θ
  have hid (p : _root_.GD.N0046.N0305.d030201 m n) :
      ‖p‖ ^ 2 + ∑ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F,
        _root_.GD.N0024.N0273.d030355 F w t θ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ p).toReal =
      t * (‖p‖ ^ 2 + ∑ θ ∈ F, w θ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ p).toReal) := by
    have h := _root_.GD.N0024.N0273.d030357 (fun θ => (_root_.GD.N0232.N0720.N1080.d014182 m n θ p).toReal) F w t
    have href : (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p).toReal = ‖p‖ ^ 2 := by
      rw [_root_.GD.N0232.N0720.N1080.d014190]
      simp [MeasureTheory.Lp.norm_def]
    simpa only [_root_.GD.N0024.N0274.d030344, href] using h
  obtain ⟨p, hp, heq⟩ := _root_.GD.N0232.N0720.N1220.d017303 m n F w hw
  obtain ⟨q, hq, heq'⟩ := _root_.GD.N0232.N0720.N1220.d017303
    m n (insert _root_.GD.N0232.N0720.N1080.d014169 F) (_root_.GD.N0024.N0273.d030355 F w t) hw'
  apply le_antisymm
  · exact (_root_.GD.N0232.N0720.N1220.d017302 m n _ _ hw' p hp).trans_eq
      ((hid p).trans (congrArg (fun x : ℝ => t * x) heq))
  · rw [← heq', hid q]
    exact mul_le_mul_of_nonneg_left (_root_.GD.N0232.N0720.N1220.d017302 m n F w hw q hq)
      (by linarith)

theorem d030359 (m n : ℕ) (c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (t : ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ) (ht : 1 ≤ t) :
    _root_.GD.N0232.N0720.N1220.d017301 m n (insert _root_.GD.N0232.N0720.N1080.d014169 F) (_root_.GD.N0024.N0273.d030355 F w t) -
      _root_.GD.N0024.N0274.d030344 c (insert _root_.GD.N0232.N0720.N1080.d014169 F) (_root_.GD.N0024.N0273.d030355 F w t) =
        t * (_root_.GD.N0232.N0720.N1220.d017301 m n F w - _root_.GD.N0024.N0274.d030344 c F w) := by
  rw [_root_.GD.N0024.N0273.d030358 m n F w t hw ht, _root_.GD.N0024.N0273.d030357]
  ring

theorem d030360 (m n : ℕ) (c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ)
    (hgap : 0 < _root_.GD.N0232.N0720.N1220.d017301 m n F w - _root_.GD.N0024.N0274.d030344 c F w) (L : ℝ) :
    ∃ (F' : Finset _root_.GD.N0232.N0720.N1080.d014168) (w' : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F', 0 ≤ w' θ) ∧
      L < _root_.GD.N0232.N0720.N1220.d017301 m n F' w' - _root_.GD.N0024.N0274.d030344 c F' w' := by
  classical
  let A := _root_.GD.N0232.N0720.N1220.d017301 m n F w - _root_.GD.N0024.N0274.d030344 c F w
  let t := 1 + max L 0 / A
  have ht : 1 ≤ t := by
    dsimp only [t]
    have h := div_nonneg (le_max_right L 0) hgap.le
    linarith
  refine ⟨insert _root_.GD.N0232.N0720.N1080.d014169 F, _root_.GD.N0024.N0273.d030355 F w t,
    fun θ _ => _root_.GD.N0024.N0273.d030356 F w t hw ht θ, ?_⟩
  rw [_root_.GD.N0024.N0273.d030359 m n c F w t hw ht]
  change L < t * A
  have heq : t * A = A + max L 0 := by
    dsimp only [t]
    have hA : A ≠ 0 := hgap.ne'
    field_simp [hA]
  rw [heq]
  linarith [le_max_left L 0]

end
end GD.N0024.N0273

#print axioms _root_.GD.N0024.N0273.d030356
#print axioms _root_.GD.N0024.N0273.d030357
#print axioms _root_.GD.N0024.N0273.d030358
#print axioms _root_.GD.N0024.N0273.d030359
#print axioms _root_.GD.N0024.N0273.d030360
