import GD.Module1672
import GD.Module0813

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0101.N0353
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0973
open _root_.GD.N0232.N0719.N0962 (d012190 d012191)
open _root_.GD.N0033

variable {k : ℕ}



theorem d028338
    (sizes : Fin (k + 1) → ℕ) (hk : 3 ≤ k + 1) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin (k + 1)) (hother : ∀ i, i ≠ h → 3 ≤ sizes i) :
    1 / (1 + _root_.GD.N0033.d028329 sizes h) ≤
      (_root_.GD.N0232.N0719.N0973.d012377 (k + 1) sizes hk hn).toReal := by
  have hn0 : ∀ i, 0 < sizes i := fun i => by have := hn i; omega
  obtain ⟨d, _, hd, hv, _, _⟩ :=
    _root_.GD.N0232.N0719.N0972.d012350 (k + 1) sizes hk hn
  apply _root_.GD.N0033.d028334 sizes hk hn h hother d hd.1
    (_root_.GD.N0232.N0719.N0973.d012377 (k + 1) sizes hk hn).toReal ENNReal.toReal_nonneg
  intro θ
  apply (_root_.GD.N0232.N0719.N0844.d012250 (k + 1) sizes
    (_root_.GD.N0232.N0719.N0972.d012343 (k + 1) sizes hk hn) (by omega) hn0
    (_root_.GD.N0232.N0719.N0973.d012377 (k + 1) sizes hk hn).toReal ENNReal.toReal_nonneg θ d).mp
  rw [ENNReal.ofReal_toReal (_root_.GD.N0232.N0719.N0973.d012379 (k + 1) sizes hk hn)]
  exact (le_iSup (fun η => _root_.GD.N0232.N0719.N0844.d012246 (k + 1) sizes
    (_root_.GD.N0232.N0719.N0972.d012343 (k + 1) sizes hk hn) η d) θ).trans hv.le


theorem d028339
    (sizes : Fin (k + 1) → ℕ) (hk : 3 ≤ k + 1) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin (k + 1)) (hother : ∀ i, i ≠ h → 3 ≤ sizes i) :
    ENNReal.ofReal (1 / (1 + _root_.GD.N0033.d028329 sizes h)) ≤
      _root_.GD.N0232.N0719.N0973.d012377 (k + 1) sizes hk hn := by
  calc
    _ ≤ ENNReal.ofReal (_root_.GD.N0232.N0719.N0973.d012377 (k + 1) sizes hk hn).toReal :=
      ENNReal.ofReal_le_ofReal
        (_root_.GD.N0101.N0353.d028338 sizes hk hn h hother)
    _ = _ := ENNReal.ofReal_toReal (_root_.GD.N0232.N0719.N0973.d012379 (k + 1) sizes hk hn)




theorem d028340
    (sizes : Fin (k + 1) → ℕ) (hk : 3 ≤ k + 1) (hn : ∀ i, 2 ≤ sizes i)
    (h : Fin (k + 1)) (hother : ∀ i, i ≠ h → 3 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0973.d012376 (k + 1) sizes hk hn (_root_.GD.N0232.N0719.N0962.d012190 (k + 1) sizes) ≤
        ((_root_.GD.N0033.d028329 sizes h / (1 + _root_.GD.N0033.d028329 sizes h) : ℝ) : EReal) ∧
      _root_.GD.N0232.N0719.N0973.d012376 (k + 1) sizes hk hn
        (_root_.GD.N0232.N0719.N0962.d012191 (k + 1) sizes) ≤
        ((_root_.GD.N0033.d028329 sizes h / (1 + _root_.GD.N0033.d028329 sizes h) : ℝ) : EReal) := by
  have hC : 0 ≤ _root_.GD.N0033.d028329 sizes h := by
    unfold _root_.GD.N0033.d028329
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hden : 0 < 1 + _root_.GD.N0033.d028329 sizes h := by linarith
  have hlower := _root_.GD.N0101.N0353.d028338 sizes hk hn h hother
  have hreal : 1 - (_root_.GD.N0232.N0719.N0973.d012377 (k + 1) sizes hk hn).toReal ≤
      _root_.GD.N0033.d028329 sizes h / (1 + _root_.GD.N0033.d028329 sizes h) := by
    apply (le_div_iff₀ hden).mpr
    have hmul := (div_le_iff₀ hden).mp hlower
    nlinarith
  obtain ⟨_, _, _, hD, hE, _, _⟩ :=
    _root_.GD.N0232.N0719.N0973.d012380 (k + 1) sizes hk hn
  rw [hD, hE]
  exact ⟨EReal.coe_le_coe_iff.mpr hreal, EReal.coe_le_coe_iff.mpr hreal⟩



theorem d028341 :
    _root_.GD.N0232.N0719.N0973.d012376 3 (fun _ => 3) (by decide) (by decide)
        (_root_.GD.N0232.N0719.N0962.d012190 3 (fun _ => 3)) ≤ ((2 / 3 : ℝ) : EReal) ∧
      _root_.GD.N0232.N0719.N0973.d012376 3 (fun _ => 3) (by decide) (by decide)
        (_root_.GD.N0232.N0719.N0962.d012191 3 (fun _ => 3)) ≤ ((2 / 3 : ℝ) : EReal) := by
  have hb := _root_.GD.N0101.N0353.d028340 (k := 2)
    (fun _ => 3) (by decide) (by decide) 0 (by decide)
  have hcount : _root_.GD.N0033.d028329 (fun _ : Fin (2 + 1) => 3) 0 = 2 := by
    unfold _root_.GD.N0033.d028329
    rw [Fin.sum_univ_succ]
    simp
  rw [hcount] at hb
  norm_num at hb
  exact hb

end
end GD.N0101.N0353

#print axioms _root_.GD.N0101.N0353.d028338
#print axioms _root_.GD.N0101.N0353.d028339
#print axioms _root_.GD.N0101.N0353.d028340
#print axioms _root_.GD.N0101.N0353.d028341
