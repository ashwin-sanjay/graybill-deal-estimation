import GD.Module0626
import GD.Module0677










namespace GD.N0232.N0719.N0922

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0901



def d009943 (y t : Fin 3 → ℝ) : _root_.GD.N0232.N0719.N0900.d009096 3 where
  mean := y
  meanVariance := t


theorem d009944
    (y t : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0922.d009943 y t) - y 0 =
      _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 1 * (y 1 - y 0) +
        _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 2 * (y 2 - y 0) := by
  have hsum := _root_.GD.N0232.N0719.N0900.d009131 (by norm_num : 0 < 3) (_root_.GD.N0232.N0719.N0922.d009943 y t)
  rw [Fin.sum_univ_three] at hsum
  unfold _root_.GD.N0232.N0719.N0900.d009110
  rw [Fin.sum_univ_three]
  change _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 0 * y 0 +
      _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 1 * y 1 +
        _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 2 * y 2 - y 0 =
    _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 1 * (y 1 - y 0) +
      _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 2 * (y 2 - y 0)
  linear_combination y 0 * hsum



theorem d009945
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t) :
    y 0 ≤ _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0922.d009943 y t) := by
  rcases hE with
    ⟨hε, hε1, ht0l, ht0u, ht1l, ht1u, ht2l, ht2u,
      hy1l, hy1u, hy2l, hy2u⟩
  rw [← sub_nonneg, _root_.GD.N0232.N0719.N0922.d009944]
  have hw1 : 0 ≤ _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 1 :=
    _root_.GD.N0232.N0719.N0900.d009132 (by norm_num) _ _
  have hw2 : 0 ≤ _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 2 :=
    _root_.GD.N0232.N0719.N0900.d009132 (by norm_num) _ _
  exact add_nonneg
    (mul_nonneg hw1 (by linarith))
    (mul_nonneg hw2 (by linarith))



theorem d009946
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t)
    (i : Fin 3) (hi : i = 1 ∨ i = 2) :
    _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) i ≤ 2 * ε := by
  rcases hE with
    ⟨hε, hε1, ht0l, ht0u, ht1l, ht1u, ht2l, ht2u,
      hy1l, hy1u, hy2l, hy2u⟩
  have ht0 : 0 < t 0 := hε.trans_le ht0l
  rcases hi with rfl | rfl
  · have ht1 : 0 < t 1 := lt_of_lt_of_le (by norm_num) ht1l
    refine (_root_.GD.N0232.N0719.N0901.d009161 (_root_.GD.N0232.N0719.N0922.d009943 y t) 1 0 ?_ ?_).trans ?_
    · simpa [_root_.GD.N0232.N0719.N0922.d009943] using ht1
    · simpa [_root_.GD.N0232.N0719.N0922.d009943] using ht0
    · simp only [_root_.GD.N0232.N0719.N0922.d009943]
      apply (div_le_iff₀ ht1).2
      nlinarith
  · have ht2 : 0 < t 2 := lt_of_lt_of_le (by norm_num) ht2l
    refine (_root_.GD.N0232.N0719.N0901.d009161 (_root_.GD.N0232.N0719.N0922.d009943 y t) 2 0 ?_ ?_).trans ?_
    · simpa [_root_.GD.N0232.N0719.N0922.d009943] using ht2
    · simpa [_root_.GD.N0232.N0719.N0922.d009943] using ht0
    · simp only [_root_.GD.N0232.N0719.N0922.d009943]
      apply (div_le_iff₀ ht2).2
      nlinarith



theorem d009947
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t) :
    _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0922.d009943 y t) - y 0 ≤ 8 * ε := by
  rcases hE with
    ⟨hε, hε1, ht0l, ht0u, ht1l, ht1u, ht2l, ht2u,
      hy1l, hy1u, hy2l, hy2u⟩
  have hE' : _root_.GD.N0232.N0719.N0922.d009928 ε y t :=
    ⟨hε, hε1, ht0l, ht0u, ht1l, ht1u, ht2l, ht2u,
      hy1l, hy1u, hy2l, hy2u⟩
  rw [_root_.GD.N0232.N0719.N0922.d009944]
  have hw1 : _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 1 ≤ 2 * ε :=
    _root_.GD.N0232.N0719.N0922.d009946 hE' 1 (Or.inl rfl)
  have hw2 : _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 2 ≤ 2 * ε :=
    _root_.GD.N0232.N0719.N0922.d009946 hE' 2 (Or.inr rfl)
  have hεnonneg : 0 ≤ 2 * ε := by positivity
  have h1nonneg : 0 ≤ y 1 - y 0 := by linarith
  have h2nonneg : 0 ≤ y 2 - y 0 := by linarith
  have hterm1 :
      _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 1 * (y 1 - y 0) ≤ 4 * ε := by
    calc
      _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 1 * (y 1 - y 0) ≤
          (2 * ε) * 2 :=
        mul_le_mul hw1 hy1u h1nonneg hεnonneg
      _ = 4 * ε := by ring
  have hterm2 :
      _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 2 * (y 2 - y 0) ≤ 4 * ε := by
    calc
      _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0922.d009943 y t) 2 * (y 2 - y 0) ≤
          (2 * ε) * 2 :=
        mul_le_mul hw2 hy2u h2nonneg hεnonneg
      _ = 4 * ε := by ring
  linarith

end

end GD.N0232.N0719.N0922

#print axioms _root_.GD.N0232.N0719.N0922.d009947
