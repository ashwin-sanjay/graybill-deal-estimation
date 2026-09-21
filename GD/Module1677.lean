import GD.Module1676
import GD.Module1673

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0070
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0102.N0420
open _root_.GD.N0102.N0423
open _root_.GD.N0102.N0422
open _root_.GD.N0033 _root_.GD.N0071
open _root_.GD.N0072 _root_.GD.N0021

variable {k : ℕ}

theorem d028367
    (sizes : Fin (k + 1) → ℕ) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012187 (k + 1) sizes (_root_.GD.N0232.N0719.N0900.d009111 (k + 1) sizes) ≤
      ENNReal.ofReal (k + 1 : ℝ) := by
  have hn2 : ∀ i, 2 ≤ sizes i := fun i => by have := hn i; omega
  apply _root_.GD.N0102.N0423.d028280
    sizes (Nat.succ_pos _) hn2 (k + 1 : ℝ)
  intro θ
  have hn0 : ∀ i, 0 < sizes i := fun i => by have := hn i; omega
  have hv := _root_.GD.N0102.N0422.d028293 sizes hn0 θ
  have hs := _root_.GD.N0102.N0423.d028275 sizes hn2
  have heq : (∫⁻ q, ENNReal.ofReal (_root_.GD.N0072.d007621 (_root_.GD.N0102.N0422.d028292 sizes θ)
      (_root_.GD.N0021.d023313 (fun i => _root_.GD.N0102.N0422.d028292 sizes θ i * q i)) /
      _root_.GD.N0232.N0719.N0963.d012141 (k + 1) sizes θ) ∂_root_.GD.N0102.N0423.d028274 sizes) =
      ∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028256 (_root_.GD.N0102.N0422.d028282 (_root_.GD.N0102.N0422.d028292 sizes θ)) q)
        ∂_root_.GD.N0033.d028239 (_root_.GD.N0102.N0423.d028273 sizes) := by
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0033.d028240 (_root_.GD.N0102.N0423.d028273 sizes) hs] with q hq
    rw [_root_.GD.N0102.N0422.d028295 sizes hn0 θ q hq]
  change (∫⁻ q, ENNReal.ofReal (_root_.GD.N0072.d007621 (_root_.GD.N0102.N0422.d028292 sizes θ)
      (_root_.GD.N0021.d023313 (fun i => _root_.GD.N0102.N0422.d028292 sizes θ i * q i)) /
      _root_.GD.N0232.N0719.N0963.d012141 (k + 1) sizes θ) ∂_root_.GD.N0102.N0423.d028274 sizes) ≤ _
  rw [heq]
  exact _root_.GD.N0070.d028366 (_root_.GD.N0102.N0423.d028273 sizes)
    (_root_.GD.N0102.N0422.d028282 (_root_.GD.N0102.N0422.d028292 sizes θ)) (_root_.GD.N0071.d028306 sizes hn)
    (_root_.GD.N0102.N0422.d028284 (Nat.succ_pos _) _ hv)
    (_root_.GD.N0102.N0422.d028285 (Nat.succ_pos _) _ hv)




theorem d028368
    (hk : 0 < k) (sizes : Fin k → ℕ) (hn : ∀ i, 3 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≤ ENNReal.ofReal (k : ℝ) := by
  cases k with
  | zero => omega
  | succ k => simpa only [Nat.cast_add, Nat.cast_one] using
      _root_.GD.N0070.d028367 sizes hn




theorem d028369 (hk : 3 ≤ k) (C : ℝ≥0∞) :
    (∀ sizes : Fin k → ℕ, (∀ i, 3 ≤ sizes i) →
      _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≤ C) ↔
        ENNReal.ofReal (k : ℝ) ≤ C := by
  constructor
  · intro hC
    have hh := hC (fun _ => 3) (by norm_num)
    rwa [_root_.GD.N0071.d028337 hk] at hh
  · intro hC sizes hn
    exact (_root_.GD.N0070.d028368 (by omega) sizes hn).trans hC



theorem d028370
    (hk : 3 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 3 ≤ sizes i)
    (h : Fin k) (hother : ∀ i, i ≠ h → sizes i = 3) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) = ENNReal.ofReal (k : ℝ) := by
  apply le_antisymm (_root_.GD.N0070.d028368 (by omega) sizes hn)
  cases k with
  | zero => omega
  | succ k =>
    have hh := _root_.GD.N0071.d028336 sizes hk
      (fun i => by have := hn i; omega) h
      (fun i hi => by rw [hother i hi])
    have hcount : _root_.GD.N0033.d028329 sizes h = (k : ℝ) := by
      unfold _root_.GD.N0033.d028329
      rw [Fin.sum_univ_succAbove _ h]
      simp [hother, Fin.succAbove_ne]
    simpa only [hcount, Nat.cast_add, Nat.cast_one, add_comm] using hh

end
end GD.N0070

#print axioms _root_.GD.N0070.d028368
#print axioms _root_.GD.N0070.d028369
#print axioms _root_.GD.N0070.d028370
