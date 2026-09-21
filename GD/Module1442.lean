import GD.Module1413
import GD.Module1441

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace GD.N0036
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0720.N1220
open _root_.GD.N0099

variable {k : ℕ}


theorem d022914
    (sizes : Fin (k + 2) → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 (k + 2) sizes θ)) :
    _root_.GD.N0232.N0720.N1256.d015549
      (sizes i) (sizes (i.succAbove j)) ≤ ENNReal.ofReal ((∏ l, _root_.GD.N0036.d022652 ε ^ _root_.GD.N0099.d022902 sizes i j l) * C) := by
  classical
  let m := sizes i
  let n := sizes (i.succAbove j)
  let cost := ∏ l, _root_.GD.N0036.d022652 ε ^ _root_.GD.N0099.d022902 sizes i j l
  have hc : 0 < cost := Finset.prod_pos fun _ _ => pow_pos (_root_.GD.N0036.d022653 ε hε) _
  apply (_root_.GD.N0232.N0720.N1220.d017309 m n (hn i) (hn (i.succAbove j)) (cost * C)
    (mul_nonneg hc.le hC)).mpr
  intro F w hw
  let B := 1 + ∑ θ ∈ F, |θ.location|
  have hB : 0 < B := by dsimp [B]; positivity
  have hloc (θ : _root_.GD.N0099.d022908) (hθ : θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F) :
      |θ.location| ≤ B := by
    rcases hθ with rfl | hθ
    · change |(0 : ℝ)| ≤ B
      simpa using hB.le
    · have hh := Finset.single_le_sum (fun θ _ => abs_nonneg θ.location) hθ
      dsimp [B]
      linarith
  let L := B / ε
  have hL : 0 < L := div_pos hB hε
  let H := (1 + ε) * L / 2
  have hH : 0 < H := by dsimp [H]; positivity
  have htwice : 2 * H = (1 + ε) * L := by dsimp [H]; ring
  let ν := _root_.GD.N0232.N0719.d009176 k (_root_.GD.N0099.d022902 sizes i j) 0 (fun _ => L)
  let η : _root_.GD.N0099.d022908 → Measure (_root_.GD.N0232.N0719.N0859.d010811 k (_root_.GD.N0099.d022902 sizes i j)) :=
    fun θ => _root_.GD.N0232.N0719.d009176 k (_root_.GD.N0099.d022902 sizes i j) θ.location (fun _ => 2 * H)
  let D := fun z => _root_.GD.N0099.d022746 B (d ((_root_.GD.N0099.d022903 sizes i j).symm z))
  have hD : Measurable D := (_root_.GD.N0099.d022749 B).comp (hd.comp (_root_.GD.N0099.d022903 sizes i j).symm.measurable)
  have hDb : ∀ z, |D z| ≤ B := fun z => _root_.GD.N0099.d022747 B hB.le _
  have hdom (θ : _root_.GD.N0099.d022908) (hθ : θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F) :
      ν ≤ ENNReal.ofReal cost • η θ := by
    have hh := _root_.GD.N0036.d022658 k (_root_.GD.N0099.d022902 sizes i j) ε L θ.location hε hL
      (show |θ.location| ≤ ε * L by simpa only [L, mul_div_cancel₀ _ hε.ne'] using hloc θ hθ)
    simpa only [ν, η, htwice] using hh
  have hupper (θ : _root_.GD.N0099.d022908) (hθ : θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F) :
      (∫ z, (D z - θ.location) ^ 2 ∂
        (_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod (η θ)) ≤
      C * _root_.GD.N0232.N0720.N1257.d015508 m n θ := by
    let θ' := _root_.GD.N0099.d022905 i j θ H hH
    let f := fun ω => _root_.GD.N0099.d022746 B (d ω)
    have hf : Measurable f := (_root_.GD.N0099.d022749 B).comp hd
    letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ') := by
      unfold _root_.GD.N0232.N0719.N0859.d010812
      infer_instance
    have hmem := _root_.GD.N0099.d022750 (_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ')
      f hf B (fun ω => _root_.GD.N0099.d022747 B hB.le (d ω)) θ.location
    have hraw : _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ' f =
        ENNReal.ofReal (∫ ω, (f ω - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ') :=
      (ofReal_integral_eq_lintegral_ofReal hmem.integrable_sq
        (ae_of_all _ fun _ => sq_nonneg _)).symm
    have hclip : _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ' f ≤
        _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ' d := by
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (_root_.GD.N0099.d022748 B θ.location (d ω) hB.le (hloc θ hθ))
    have hreal : (∫ ω, (f ω - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ') ≤
        C * _root_.GD.N0232.N0719.N0963.d012141 (k + 2) sizes θ' := by
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC
        (_root_.GD.N0232.N0719.N0963.d012143 (k + 2) sizes (by omega)
          (fun l => by have := hn l; omega) θ').le)).mp
      rw [← hraw]
      exact hclip.trans (hcap θ')
    have heq := (_root_.GD.N0099.d022906 sizes i j θ H hH).integral_comp' (fun z => (D z - θ.location) ^ 2)
    have heq' : (∫ ω, (f ω - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ') =
        ∫ z, (D z - θ.location) ^ 2 ∂
          (_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod (η θ) := by
      simpa only [D, f, MeasurableEquiv.symm_apply_apply] using heq
    rw [← heq']
    exact hreal.trans (mul_le_mul_of_nonneg_left (_root_.GD.N0099.d022907 sizes hn i j θ H hH) hC)
  have hh := _root_.GD.N0099.d022754 m n F w hw ν η D hD B hDb cost hc.le
    (fun θ => C * _root_.GD.N0232.N0720.N1257.d015508 m n θ) hdom hupper
  simpa only [_root_.GD.N0232.N0720.N1220.d017307, mul_add, Finset.mul_sum, mul_assoc, mul_left_comm] using hh

end
end GD.N0036

#print axioms _root_.GD.N0036.d022914
