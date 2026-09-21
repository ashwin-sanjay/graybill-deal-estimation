import GD.Module1669
import GD.Module1672

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace GD.N0071
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0963
open _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0941 _root_.GD.N0232.N0719.N0939
open _root_.GD.N0033

variable {k : ℕ}

theorem d028335 (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0962.d012186 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) =
      ENNReal.ofReal ((_root_.GD.N0232.N0719.N0941.d020687 k sizes θ)⁻¹) := by
  have hraw : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
      (_root_.GD.N0232.N0719.N0900.d009111 k sizes) = ENNReal.ofReal (_root_.GD.N0232.N0719.N0972.d012340 k sizes θ) :=
    _root_.GD.N0232.N0719.N0972.d012341 k sizes hk hn θ
  rw [_root_.GD.N0232.N0719.N0962.d012186, hraw,
    ← ENNReal.ofReal_div_of_pos
      (_root_.GD.N0232.N0719.N0963.d012143 k sizes (by omega) (fun i => by have := hn i; omega) θ)]
  simp only [_root_.GD.N0232.N0719.N0941.d020687, inv_div, _root_.GD.N0232.N0719.N0963.d012141,
    _root_.GD.N0232.N0719.N0838.d012097,
    _root_.GD.N0232.N0719.N0838.d012096]



theorem d028336 (sizes : Fin (k + 1) → ℕ)
    (hk : 3 ≤ k + 1) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin (k + 1)) (hother : ∀ i, i ≠ h → 3 ≤ sizes i) :
    ENNReal.ofReal (1 + _root_.GD.N0033.d028329 sizes h) ≤
      _root_.GD.N0232.N0719.N0962.d012187 (k + 1) sizes (_root_.GD.N0232.N0719.N0900.d009111 (k + 1) sizes) := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he : ∀ n, 0 < e n := fun n => by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : 0 ≤ _root_.GD.N0033.d028329 sizes h := by
    unfold _root_.GD.N0033.d028329
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hlim := (_root_.GD.N0033.d028332
    sizes hn h hother e he he0).inv₀ (by positivity :
      1 / (1 + _root_.GD.N0033.d028329 sizes h) ≠ 0)
  simp only [one_div, inv_inv] at hlim
  have hlimE := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  apply le_of_tendsto hlimE
  apply Eventually.of_forall
  intro n
  change ENNReal.ofReal ((_root_.GD.N0232.N0719.N0941.d020687 (k + 1) sizes
    (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n)))⁻¹) ≤ _
  rw [← _root_.GD.N0071.d028335 sizes hk hn]
  exact le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 (k + 1) sizes θ
    (_root_.GD.N0232.N0719.N0900.d009111 (k + 1) sizes)) (_root_.GD.N0232.N0719.N0939.d020700 sizes hn h (e n) (he n))



theorem d028337 (hk : 3 ≤ k) :
    _root_.GD.N0232.N0719.N0962.d012187 k (fun _ => 3) (_root_.GD.N0232.N0719.N0900.d009111 k (fun _ => 3)) =
      ENNReal.ofReal (k : ℝ) := by
  apply le_antisymm (_root_.GD.N0071.d028309 (by omega))
  cases k with
  | zero => omega
  | succ k =>
    have hh := _root_.GD.N0071.d028336
      (fun _ : Fin (k + 1) => 3) hk (by norm_num) 0 (by norm_num)
    have hcount : _root_.GD.N0033.d028329 (fun _ : Fin (k + 1) => 3) 0 = k := by
      unfold _root_.GD.N0033.d028329
      rw [Fin.sum_univ_succ]
      simp
    simpa only [hcount, Nat.cast_add, Nat.cast_one, add_comm] using hh

end
end GD.N0071

#print axioms _root_.GD.N0071.d028336
#print axioms _root_.GD.N0071.d028337
