import GD.Module1845

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0024.N0283

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1459 _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0107
open _root_.GD.N0046.N0305
open _root_.GD.N0034.N0289 _root_.GD.N0034.N0294
open _root_.GD.N0024.N0274

def d030361 (m n : ℕ) (z : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  if 0 < _root_.GD.N0107.d009085 z.1 / (m : ℝ) + _root_.GD.N0107.d009085 z.2 / (n : ℝ) then
    ((_root_.GD.N0107.d009085 z.2 / (n : ℝ)) * _root_.GD.N0107.d009084 z.1 +
      (_root_.GD.N0107.d009085 z.1 / (m : ℝ)) * _root_.GD.N0107.d009084 z.2) /
        (_root_.GD.N0107.d009085 z.1 / (m : ℝ) + _root_.GD.N0107.d009085 z.2 / (n : ℝ))
  else (_root_.GD.N0107.d009084 z.1 + _root_.GD.N0107.d009084 z.2) / 2

theorem d030362 (m n : ℕ) : Measurable (_root_.GD.N0024.N0283.d030361 m n) := by
  unfold _root_.GD.N0024.N0283.d030361
  apply Measurable.ite
  · exact measurableSet_lt measurable_const (by fun_prop)
  · fun_prop
  · fun_prop

theorem d030363 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0024.N0283.d030361 m n =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] _root_.GD.N0232.N0720.N1080.d014175 m n := by
  apply (_root_.GD.N0232.N0720.N1080.d014173 m n θ).ae_le
  filter_upwards [_root_.GD.N0232.N0720.N1459.d018933 m n hm hn] with z hz
  have hpos : 0 < _root_.GD.N0107.d009085 z.1 / (m : ℝ) +
      _root_.GD.N0107.d009085 z.2 / (n : ℝ) := by
    simpa only [_root_.GD.N0232.N0720.N1467.d012547, _root_.GD.N0232.N0720.N1467.d012548] using hz
  rw [_root_.GD.N0024.N0283.d030361, if_pos hpos]
  exact (show _root_.GD.N0034.N0290.d021948 m n z = _ by
    rw [_root_.GD.N0034.N0290.d021948, if_pos hpos]).symm.trans
    (_root_.GD.N0034.N0290.d021950 m n z hpos)

def d030364 (m n : ℕ) : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :=
  {f | Measurable f ∧ ∀ θ,
    _root_.GD.N0232.N0720.N1080.d014197 m n θ f ≤ min (_root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0024.N0283.d030361 m n))
      (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ))}

theorem d030365 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0024.N0283.d030364 m n = _root_.GD.N0034.N0294.d030312 m n := by
  ext f
  have hrisk : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0024.N0283.d030361 m n) =
      _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) := fun θ =>
    _root_.GD.N0232.N0720.N1159.d014662 m n θ (_root_.GD.N0024.N0283.d030363 m n hm hn θ)
  simp only [_root_.GD.N0024.N0283.d030364, _root_.GD.N0034.N0294.d030312, mem_setOf_eq, hrisk, le_min_iff, and_comm]

theorem d030366 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (_root_.GD.N0024.N0283.d030364 m n).Nonempty ↔ (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty := by
  rw [_root_.GD.N0024.N0283.d030365 m n hm hn]
  exact _root_.GD.N0034.N0294.d030324 m n hm hn

theorem d030367 (m n : ℕ) (hm : 2 ≤ m) (_hn : 2 ≤ n)
    (htop : _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤) : (_root_.GD.N0024.N0283.d030364 m n).Nonempty := by
  refine ⟨_root_.GD.N0024.N0283.d030361 m n, _root_.GD.N0024.N0283.d030362 m n, fun θ => ?_⟩
  have hτ : ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (_root_.GD.N0232.N0720.N1257.d015510 m n (by omega) θ))
  rw [htop, ENNReal.top_mul hτ, min_eq_left le_top]

abbrev d030368 := {i : ℕ × ℕ // 2 ≤ i.1 ∧ 2 ≤ i.2}

def d030369 : Prop :=
  ∃ f : (i : _root_.GD.N0024.N0283.d030368) → _root_.GD.N0232.N0720.N1080.d014170 i.val.1 i.val.2 → ℝ,
    ∀ i, f i ∈ _root_.GD.N0024.N0283.d030364 i.val.1 i.val.2

theorem d030370 : _root_.GD.N0024.N0283.d030369 ↔ ∀ i : _root_.GD.N0024.N0283.d030368, (_root_.GD.N0024.N0283.d030364 i.val.1 i.val.2).Nonempty := by
  constructor
  · rintro ⟨f, hf⟩ i
    exact ⟨f i, hf i⟩
  · intro h
    exact ⟨fun i => Classical.choose (h i), fun i => Classical.choose_spec (h i)⟩

theorem d030371 : _root_.GD.N0024.N0283.d030369 ↔
    ∀ i : _root_.GD.N0024.N0283.d030368, _root_.GD.N0034.N0289.d030224 i.val.1 i.val.2 i.property.1 i.property.2 := by
  rw [_root_.GD.N0024.N0283.d030370]
  apply forall_congr'
  intro i
  exact (_root_.GD.N0024.N0283.d030366 _ _ i.property.1 i.property.2).trans
    (_root_.GD.N0034.N0289.d030225 _ _ i.property.1 i.property.2)

theorem d030372 : _root_.GD.N0024.N0283.d030369 ↔
    ∀ i : _root_.GD.N0024.N0283.d030368, _root_.GD.N0232.N0720.N1256.d015549 i.val.1 i.val.2 ≠ ⊤ →
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0024.N0274.d030345 i.val.1 i.val.2 i.property.1 i.property.2
          (_root_.GD.N0232.N0720.N1256.d015549 i.val.1 i.val.2).toReal F w ≤
        _root_.GD.N0024.N0274.d030346 i.val.1 i.val.2 (_root_.GD.N0232.N0720.N1256.d015549 i.val.1 i.val.2).toReal F w := by
  rw [_root_.GD.N0024.N0283.d030370]
  constructor
  · intro h i hfinite
    exact (_root_.GD.N0024.N0274.d030350 _ _ i.property.1 i.property.2 _
      ENNReal.toReal_nonneg (ENNReal.ofReal_toReal hfinite).symm).mp
      ((_root_.GD.N0024.N0283.d030366 _ _ i.property.1 i.property.2).mp (h i))
  · intro h i
    by_cases hfinite : _root_.GD.N0232.N0720.N1256.d015549 i.val.1 i.val.2 = ⊤
    · exact _root_.GD.N0024.N0283.d030367 _ _ i.property.1 i.property.2 hfinite
    · apply (_root_.GD.N0024.N0283.d030366 _ _ i.property.1 i.property.2).mpr
      exact (_root_.GD.N0024.N0274.d030350 _ _ i.property.1 i.property.2 _
        ENNReal.toReal_nonneg (ENNReal.ofReal_toReal hfinite).symm).mpr (h i hfinite)

theorem d030373 (i : _root_.GD.N0024.N0283.d030368) (hempty : _root_.GD.N0024.N0283.d030364 i.val.1 i.val.2 = ∅) :
    ¬ _root_.GD.N0024.N0283.d030369 := by
  intro h
  have hi := _root_.GD.N0024.N0283.d030370.mp h i
  simp [hempty] at hi

end
end GD.N0024.N0283

#print axioms _root_.GD.N0024.N0283.d030362
#print axioms _root_.GD.N0024.N0283.d030363
#print axioms _root_.GD.N0024.N0283.d030366
#print axioms _root_.GD.N0024.N0283.d030367
#print axioms _root_.GD.N0024.N0283.d030370
#print axioms _root_.GD.N0024.N0283.d030371
#print axioms _root_.GD.N0024.N0283.d030372
#print axioms _root_.GD.N0024.N0283.d030373
