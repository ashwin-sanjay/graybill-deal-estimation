import GD.Module1440
import GD.Module1424
import GD.Module0804

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter Set
open scoped ENNReal BigOperators

namespace GD.N0099
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0720.N1220

abbrev d022908 := _root_.GD.N0232.N0720.N1080.d014168

variable {k : ℕ}

def d022909 (sizes : Fin (k + 2) → ℕ) (i : Fin (k + 2)) (j : Fin (k + 1)) : ℝ :=
  ∏ l, _root_.GD.N0099.d022643 ^ _root_.GD.N0099.d022902 sizes i j l

theorem d022910 (sizes : Fin (k + 2) → ℕ) (i : Fin (k + 2)) (j : Fin (k + 1)) :
    0 < _root_.GD.N0099.d022909 sizes i j :=
  Finset.prod_pos fun _ _ => pow_pos _root_.GD.N0099.d022644 _



theorem d022911
    (sizes : Fin (k + 2) → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1))
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 (k + 2) sizes θ)) :
    _root_.GD.N0232.N0720.N1256.d015549
      (sizes i) (sizes (i.succAbove j)) ≤ ENNReal.ofReal (_root_.GD.N0099.d022909 sizes i j * C) := by
  classical
  let m := sizes i
  let n := sizes (i.succAbove j)
  let cost := _root_.GD.N0099.d022909 sizes i j
  have hc : 0 < cost := _root_.GD.N0099.d022910 sizes i j
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
  let ν := _root_.GD.N0232.N0719.d009176 k (_root_.GD.N0099.d022902 sizes i j) 0 (fun _ => B)
  let η : _root_.GD.N0099.d022908 → Measure (_root_.GD.N0232.N0719.N0859.d010811 k (_root_.GD.N0099.d022902 sizes i j)) :=
    fun θ => _root_.GD.N0232.N0719.d009176 k (_root_.GD.N0099.d022902 sizes i j) θ.location (fun _ => 2 * B)
  let D := fun z => _root_.GD.N0099.d022746 B (d ((_root_.GD.N0099.d022903 sizes i j).symm z))
  have hD : Measurable D := (_root_.GD.N0099.d022749 B).comp (hd.comp (_root_.GD.N0099.d022903 sizes i j).symm.measurable)
  have hDb : ∀ z, |D z| ≤ B := fun z => _root_.GD.N0099.d022747 B hB.le _
  have hdom (θ : _root_.GD.N0099.d022908) (hθ : θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F) :
      ν ≤ ENNReal.ofReal cost • η θ :=
    _root_.GD.N0099.d022651 k (_root_.GD.N0099.d022902 sizes i j) B θ.location hB (hloc θ hθ)
  have hupper (θ : _root_.GD.N0099.d022908) (hθ : θ = _root_.GD.N0232.N0720.N1080.d014169 ∨ θ ∈ F) :
      (∫ z, (D z - θ.location) ^ 2 ∂
        (_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod (η θ)) ≤
      C * _root_.GD.N0232.N0720.N1257.d015508 m n θ := by
    let θ' := _root_.GD.N0099.d022905 i j θ B hB
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
    have heq := (_root_.GD.N0099.d022906 sizes i j θ B hB).integral_comp' (fun z => (D z - θ.location) ^ 2)
    have heq' : (∫ ω, (f ω - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 (k + 2) sizes θ') =
        ∫ z, (D z - θ.location) ^ 2 ∂
          (_root_.GD.N0232.N0720.N1080.d014171 m n θ).prod (η θ) := by
      simpa only [D, f, MeasurableEquiv.symm_apply_apply] using heq
    rw [← heq']
    exact hreal.trans (mul_le_mul_of_nonneg_left (_root_.GD.N0099.d022907 sizes hn i j θ B hB) hC)
  have hh := _root_.GD.N0099.d022754 m n F w hw ν η D hD B hDb cost hc.le
    (fun θ => C * _root_.GD.N0232.N0720.N1257.d015508 m n θ) hdom hupper
  simpa only [_root_.GD.N0232.N0720.N1220.d017307, mul_add, Finset.mul_sum, mul_assoc, mul_left_comm] using hh


theorem d022912
    (sizes : Fin (k + 2) → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i : Fin (k + 2)) (j : Fin (k + 1)) (hi : sizes i = 2) (hj : sizes (i.succAbove j) = 2)
    (d : _root_.GD.N0232.N0719.N0859.d010811 (k + 2) sizes → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C) :
    ¬ (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (k + 2) sizes θ d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 (k + 2) sizes θ)) := by
  intro hcap
  have hh := _root_.GD.N0099.d022911 sizes hn i j d hd C hC hcap
  rw [hi, hj,
    _root_.GD.N0232.N0720.N1223.d019625
      _root_.GD.N0232.N0720.N1225.d020635] at hh
  exact (not_le_of_gt ENNReal.ofReal_lt_top) hh



theorem d022913
    {K : ℕ} (sizes : Fin K → ℕ) (hK : 3 ≤ K) (hn : ∀ l, 2 ≤ sizes l)
    (hsmall : ∃ i j, i ≠ j ∧ sizes i = 2 ∧ sizes j = 2) :
    _root_.GD.N0232.N0719.N0962.d012188 K sizes = ⊤ := by
  cases K with
  | zero => omega
  | succ K =>
    cases K with
    | zero => omega
    | succ k =>
      by_contra hfinite
      obtain ⟨i, h, hih, hi, hh⟩ := hsmall
      obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hih)
      obtain ⟨d, hd, hdv⟩ := _root_.GD.N0232.N0719.N0969.d012209
        (k + 2) sizes hK hn
      let C := (_root_.GD.N0232.N0719.N0962.d012188 (k + 2) sizes).toReal
      have hC : 0 ≤ C := ENNReal.toReal_nonneg
      apply _root_.GD.N0099.d022912 sizes hn i j hi (by simpa only [hj] using hh) d hd.1.1 C hC
      intro θ
      apply (_root_.GD.N0232.N0719.N0962.d012192 (k + 2) sizes
        (by omega) (fun l => by have := hn l; omega) C hC θ d).mp
      have hval : ENNReal.ofReal C = _root_.GD.N0232.N0719.N0962.d012187 (k + 2) sizes d :=
        (ENNReal.ofReal_toReal hfinite).trans hdv.symm
      rw [hval]
      exact le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 (k + 2) sizes θ d) θ

end
end GD.N0099

#print axioms _root_.GD.N0099.d022911
#print axioms _root_.GD.N0099.d022912
#print axioms _root_.GD.N0099.d022913
