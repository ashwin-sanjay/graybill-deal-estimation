import GD.Module1719
import GD.Module1673

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace GD.N0094
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0938 _root_.GD.N0232.N0719.N0877 _root_.GD.N0232.N0719.N0939
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0963
open _root_.GD.N0232.N0719.N0962
open _root_.GD.N0033 _root_.GD.N0093 _root_.GD.N0071

variable {k : ℕ}


theorem d028720
    (shape : Fin (k + 1) → ℝ) (hs : ∀ i, 0 < shape i)
    (i : Fin (k + 1)) (j : Fin k) (hi : shape i < 1)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, _root_.GD.N0232.N0719.N0938.d007530 (e n) (_root_.GD.N0232.N0719.N0877.d020693 (i.succAbove j) a) ∂_root_.GD.N0033.d028239 shape)
      atTop atTop := by
  apply tendsto_atTop_mono (fun n => ?_)
    (_root_.GD.N0093.d028719 shape hs i j hi e he he0)
  have hint : Integrable (fun a => _root_.GD.N0232.N0719.N0938.d007530 (e n) (_root_.GD.N0232.N0719.N0877.d020693 (i.succAbove j) a)) (_root_.GD.N0033.d028239 shape) :=
    (_root_.GD.N0033.d028244 shape hs (i.succAbove j) (he n).le).add
      (integrable_finsetSum _ fun l _ => _root_.GD.N0033.d028247 shape hs (i.succAbove j) l (he n))
  apply integral_mono (_root_.GD.N0033.d028247 shape hs (i.succAbove j) i (he n)) hint
  intro a
  have hsum := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun l => _root_.GD.N0232.N0719.N0938.d007528 (e n) (∑ m, _root_.GD.N0232.N0719.N0877.d020693 (i.succAbove j) a m)
      (_root_.GD.N0232.N0719.N0877.d020693 (i.succAbove j) a l))
    (fun l _ => by
      unfold _root_.GD.N0232.N0719.N0938.d007528
      exact div_nonneg (mul_nonneg (he n).le (sq_nonneg _)) (sq_nonneg _))
    (Finset.mem_univ i)
  exact hsum.trans (le_add_of_nonneg_left (sq_nonneg _))



theorem d028721
    (sizes : Fin (k + 1) → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (i h : Fin (k + 1)) (hi : sizes i = 2) (hih : i ≠ h)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0972.d012340 (k + 1) sizes
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)) / e n) atTop atTop := by
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hih)
  have hshape : _root_.GD.N0033.d028328 sizes i < 1 := by norm_num [_root_.GD.N0033.d028328, hi]
  have hlim := _root_.GD.N0094.d028720 (_root_.GD.N0033.d028328 sizes)
    (_root_.GD.N0033.d028330 sizes hn) i j hshape e he he0
  rw [hj] at hlim
  convert hlim using 1
  funext n
  rw [_root_.GD.N0232.N0719.N0939.d020708 sizes hn h (he n), mul_div_cancel_left₀ _ (he n).ne']
  rfl



theorem d028722
    (sizes : Fin (k + 1) → ℕ) (hk : 3 ≤ k + 1) (hn : ∀ i, 2 ≤ sizes i)
    (i h : Fin (k + 1)) (hi : sizes i = 2) (hih : i ≠ h)
    (e : ℕ → ℝ) (he : ∀ n, 0 < e n) (he0 : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => _root_.GD.N0232.N0719.N0962.d012186 (k + 1) sizes
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)) (_root_.GD.N0232.N0719.N0900.d009111 (k + 1) sizes))
      atTop (𝓝 ⊤) := by
  have hlim : Tendsto (fun n => _root_.GD.N0232.N0719.N0972.d012340 (k + 1) sizes
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)) /
      _root_.GD.N0232.N0719.N0963.d012141 (k + 1) sizes (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)))
      atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_)
      (_root_.GD.N0094.d028721 sizes hn i h hi hih e he he0)
    have hV : _root_.GD.N0232.N0719.N0963.d012141 (k + 1) sizes (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)) ≤ e n := by
      change (∑ l, (sizes l : ℝ) /
        (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)).scale l ^ 2)⁻¹ ≤ e n
      rw [_root_.GD.N0232.N0719.N0939.d020710 sizes hn h (he n)]
      apply div_le_self (he n).le
      simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) (he n).le)
    exact div_le_div_of_nonneg_left (_root_.GD.N0232.N0719.N0972.d012342 (k + 1) sizes hk hn _).le
      (_root_.GD.N0232.N0719.N0963.d012143 (k + 1) sizes (by omega) (fun l => by have := hn l; omega) _) hV
  convert ENNReal.tendsto_ofReal_nhds_top.mpr hlim using 1
  funext n
  have hraw : _root_.GD.N0232.N0719.N0859.d010840 (k + 1) sizes
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)) (_root_.GD.N0232.N0719.N0900.d009111 (k + 1) sizes) =
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0972.d012340 (k + 1) sizes (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n))) :=
    _root_.GD.N0232.N0719.N0972.d012341 (k + 1) sizes hk hn _
  rw [_root_.GD.N0232.N0719.N0962.d012186, hraw,
    ← ENNReal.ofReal_div_of_pos
      (_root_.GD.N0232.N0719.N0963.d012143 (k + 1) sizes (by omega) (fun l => by have := hn l; omega) _)]


theorem d028723
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (hsmall : ∃ i, sizes i = 2) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) = ⊤ := by
  cases k with
  | zero => omega
  | succ k =>
    obtain ⟨i, hi⟩ := hsmall
    let j : Fin k := ⟨0, by omega⟩
    let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have he : ∀ n, 0 < e n := fun n => by dsimp [e]; positivity
    have hlim := _root_.GD.N0094.d028722 sizes hk hn
      i (i.succAbove j) hi (Fin.succAbove_ne i j).symm e he
      tendsto_one_div_add_atTop_nhds_zero_nat
    apply top_unique
    apply le_of_tendsto hlim
    exact Eventually.of_forall fun n => le_iSup
      (fun θ => _root_.GD.N0232.N0719.N0962.d012186 (k + 1) sizes θ (_root_.GD.N0232.N0719.N0900.d009111 (k + 1) sizes))
      (_root_.GD.N0232.N0719.N0939.d020700 sizes hn (i.succAbove j) (e n) (he n))


theorem d028724
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≠ ⊤ ↔ ∀ i, 3 ≤ sizes i := by
  constructor
  · intro hfinite i
    by_contra hi
    have hi2 : sizes i = 2 := by have := hn i; omega
    exact hfinite (_root_.GD.N0094.d028723 sizes hk hn ⟨i, hi2⟩)
  · exact _root_.GD.N0071.d028308 sizes (by omega)


theorem d028725
    (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) = ⊤ ↔ ∃ i, sizes i = 2 := by
  constructor
  · intro htop
    by_contra hsmall
    have hn3 : ∀ i, 3 ≤ sizes i := by
      intro i
      have hh : sizes i ≠ 2 := fun hi => hsmall ⟨i, hi⟩
      have := hn i
      omega
    exact _root_.GD.N0071.d028308 sizes (by omega) hn3 htop
  · exact _root_.GD.N0094.d028723 sizes hk hn

end
end GD.N0094

#print axioms _root_.GD.N0094.d028720
#print axioms _root_.GD.N0094.d028721
#print axioms _root_.GD.N0094.d028722
#print axioms _root_.GD.N0094.d028723
#print axioms _root_.GD.N0094.d028724
#print axioms _root_.GD.N0094.d028725
