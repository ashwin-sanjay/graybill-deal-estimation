import GD.Module1665
import GD.Module1486

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0102.N0420
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0033

variable {k : ℕ}

def d028264 (p : Fin (k + 1) → ℝ) (i : Fin (k + 1)) (b : Fin k → ℝ) : ℝ :=
  ∑ j, p (i.succAbove j) / b j

@[fun_prop] theorem d028265 (p : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    Measurable (_root_.GD.N0102.N0420.d028264 p i) := by
  unfold _root_.GD.N0102.N0420.d028264
  fun_prop

theorem d028266 (p : Fin (k + 1) → ℝ) (i : Fin (k + 1))
    (hp : ∀ j, 0 < p j) (b : Fin k → ℝ) (hb : ∀ j, 0 < b j) :
    0 ≤ _root_.GD.N0102.N0420.d028264 p i b := Finset.sum_nonneg fun j _ => (div_pos (hp _) (hb j)).le

theorem d028267 (p q : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    _root_.GD.N0102.N0420.d028253 p q = p i / q i + _root_.GD.N0102.N0420.d028264 p i (fun j => q (i.succAbove j)) := by
  exact Fin.sum_univ_succAbove _ i

theorem d028268 (p q : Fin (k + 1) → ℝ) (i : Fin (k + 1))
    (hp : ∀ j, 0 < p j) (hq : ∀ j, 0 < q j) :
    _root_.GD.N0102.N0420.d028255 p q i = p i /
      (p i + _root_.GD.N0102.N0420.d028264 p i (fun j => q (i.succAbove j)) * q i) ^ 2 := by
  have hB := _root_.GD.N0102.N0420.d028266 p i hp (fun j => q (i.succAbove j))
    (fun j => hq (i.succAbove j))
  have hd : p i + _root_.GD.N0102.N0420.d028264 p i (fun j => q (i.succAbove j)) * q i ≠ 0 :=
    (add_pos_of_pos_of_nonneg (hp i) (mul_nonneg hB (hq i).le)).ne'
  have hD : p i / q i + _root_.GD.N0102.N0420.d028264 p i (fun j => q (i.succAbove j)) ≠ 0 :=
    (add_pos_of_pos_of_nonneg (div_pos (hp i) (hq i)) hB).ne'
  unfold _root_.GD.N0102.N0420.d028255
  rw [_root_.GD.N0102.N0420.d028267]
  field_simp [(hq i).ne', hd, hD]

theorem d028269 (p q : Fin (k + 1) → ℝ) (i : Fin (k + 1))
    (hq : ∀ j, 0 < q j) :
    _root_.GD.N0102.N0420.d028254 p q = q i /
      (p i + _root_.GD.N0102.N0420.d028264 p i (fun j => q (i.succAbove j)) * q i) := by
  have hfrac : _root_.GD.N0102.N0420.d028253 p q =
      (p i + _root_.GD.N0102.N0420.d028264 p i (fun j => q (i.succAbove j)) * q i) / q i := by
    rw [_root_.GD.N0102.N0420.d028267]
    field_simp [(hq i).ne']
    rw [mul_add, mul_div_cancel₀ _ (hq i).ne']
  rw [_root_.GD.N0102.N0420.d028254, hfrac, inv_div]




theorem d028270
    (p q v w : Fin (k + 1) → ℝ) (P : ℝ)
    (hpv : ∀ i, P * v i * p i = 1)
    (hw : ∀ i, w i = (p i / q i) / _root_.GD.N0102.N0420.d028253 p q) :
    (∑ i, v i * w i ^ 2) * P = _root_.GD.N0102.N0420.d028256 p q := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hw]
  change v i * ((p i / q i) / _root_.GD.N0102.N0420.d028253 p q) ^ 2 * P =
    (p i / q i ^ 2) / _root_.GD.N0102.N0420.d028253 p q ^ 2
  calc
    _ = (P * v i * p i) * ((p i / q i ^ 2) / _root_.GD.N0102.N0420.d028253 p q ^ 2) := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [hpv, one_mul]



theorem d028271
    (shape p : Fin (k + 1) → ℝ) (hs : ∀ i, 0 < shape i) (hp : ∀ i, 0 < p i)
    (i : Fin (k + 1)) (hscalar : _root_.GD.N0102.N0420.d028262 (shape i)) :
    (∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028255 p q i) ∂_root_.GD.N0033.d028239 shape) ≤
      ENNReal.ofReal (shape i) * ∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028254 p q) ∂_root_.GD.N0033.d028239 shape := by
  have hB : ∀ᵐ b ∂_root_.GD.N0033.d028239 (fun j => shape (i.succAbove j)), 0 ≤ _root_.GD.N0102.N0420.d028264 p i b := by
    filter_upwards [_root_.GD.N0033.d028240 _ (fun j => hs (i.succAbove j))] with b hb
    exact _root_.GD.N0102.N0420.d028266 p i hp b hb
  have hc := _root_.GD.N0102.N0420.d028263 shape i hscalar (p i) (hp i)
    (_root_.GD.N0102.N0420.d028264 p i) (_root_.GD.N0102.N0420.d028265 p i) hB
  have heq : (∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028255 p q i) ∂_root_.GD.N0033.d028239 shape) =
      ∫⁻ q, ENNReal.ofReal (p i / (p i + _root_.GD.N0102.N0420.d028264 p i (fun j => q (i.succAbove j)) * q i) ^ 2)
        ∂_root_.GD.N0033.d028239 shape := by
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0033.d028240 shape hs] with q hq
    rw [_root_.GD.N0102.N0420.d028268 p q i hp hq]
  have heqH : (∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028254 p q) ∂_root_.GD.N0033.d028239 shape) =
      ∫⁻ q, ENNReal.ofReal (q i / (p i + _root_.GD.N0102.N0420.d028264 p i (fun j => q (i.succAbove j)) * q i))
        ∂_root_.GD.N0033.d028239 shape := by
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0033.d028240 shape hs] with q hq
    rw [_root_.GD.N0102.N0420.d028269 p q i hq]
  rwa [heq, heqH]



theorem d028272
    (shape p : Fin (k + 1) → ℝ) (hs : ∀ i, 0 < shape i)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1)
    (hscalar : ∀ i, _root_.GD.N0102.N0420.d028262 (shape i)) :
    (∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028256 p q) ∂_root_.GD.N0033.d028239 shape) ≤
      ENNReal.ofReal (∑ i, shape i) := by
  have heq : (∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028256 p q) ∂_root_.GD.N0033.d028239 shape) =
      ∑ i, ∫⁻ q, ENNReal.ofReal (_root_.GD.N0102.N0420.d028255 p q i) ∂_root_.GD.N0033.d028239 shape := by
    calc
      _ = ∫⁻ q, ∑ i, ENNReal.ofReal (_root_.GD.N0102.N0420.d028255 p q i) ∂_root_.GD.N0033.d028239 shape := by
        apply lintegral_congr
        intro q
        exact ENNReal.ofReal_sum_of_nonneg (fun i _ =>
          div_nonneg (div_nonneg (hp i).le (sq_nonneg _)) (sq_nonneg _))
      _ = _ := lintegral_finsetSum _ (fun i _ => ENNReal.measurable_ofReal.comp
        (_root_.GD.N0102.N0420.d028258 p i))
  rw [heq, ENNReal.ofReal_sum_of_nonneg (fun i _ => (hs i).le)]
  apply Finset.sum_le_sum
  intro i _
  exact (_root_.GD.N0102.N0420.d028271 shape p hs hp i (hscalar i)).trans
    (by
      simpa only [mul_one] using
        (mul_le_mul_right (_root_.GD.N0102.N0420.d028261 shape p hs hp hsum)
          (ENNReal.ofReal (shape i))))

end
end GD.N0102.N0420

#print axioms _root_.GD.N0102.N0420.d028268
#print axioms _root_.GD.N0102.N0420.d028269
#print axioms _root_.GD.N0102.N0420.d028270
#print axioms _root_.GD.N0102.N0420.d028271
#print axioms _root_.GD.N0102.N0420.d028272


set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0102.N0423
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0910 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0072 _root_.GD.N0021
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962

attribute [local fun_prop] _root_.GD.N0021.d023314

variable {k : ℕ}

def d028273 (sizes : Fin k → ℕ) (i : Fin k) : ℝ := (sizes i - 1 : ℕ) / 2
def d028274 (sizes : Fin k → ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi fun i => gammaMeasure (_root_.GD.N0102.N0423.d028273 sizes i) (_root_.GD.N0102.N0423.d028273 sizes i)

theorem d028275 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (i : Fin k) :
    0 < _root_.GD.N0102.N0423.d028273 sizes i := by
  have h : 0 < sizes i - 1 := by have := hn i; omega
  exact div_pos (Nat.cast_pos.mpr h) (by norm_num)



theorem d028276
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (scales : Fin k → ℝ) :
    MeasurePreserving (fun q : Fin k → ℝ => fun i =>
      (scales i ^ 2 / (sizes i : ℝ)) * q i)
      (_root_.GD.N0102.N0423.d028274 sizes) (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) := by
  letI (i : Fin k) : IsProbabilityMeasure
      (gammaMeasure (_root_.GD.N0102.N0423.d028273 sizes i) (_root_.GD.N0102.N0423.d028273 sizes i)) :=
    isProbabilityMeasure_gammaMeasure (_root_.GD.N0102.N0423.d028275 sizes hn i) (_root_.GD.N0102.N0423.d028275 sizes hn i)
  refine ⟨by fun_prop, ?_⟩
  change (Measure.pi fun i => gammaMeasure (_root_.GD.N0102.N0423.d028273 sizes i) (_root_.GD.N0102.N0423.d028273 sizes i)).map
    (fun q i => _root_.GD.N0232.N0719.N0933.d009287 (sizes i) (scales i) (q i)) = _
  rw [Measure.pi_map_pi]
  · rfl
  · intro i
    exact (_root_.GD.N0232.N0719.N0933.d009294 (sizes i) (scales i)).aemeasurable



theorem d028277
    (sizes : Fin k → ℕ) (hk : 0 < k) (hn : ∀ i, 2 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) =
      ∫⁻ q, ENNReal.ofReal (_root_.GD.N0072.d007621 (fun i => θ.scale i ^ 2 / (sizes i : ℝ))
        (_root_.GD.N0021.d023313 (fun i => (θ.scale i ^ 2 / (sizes i : ℝ)) * q i)))
        ∂_root_.GD.N0102.N0423.d028274 sizes := by
  have hm : Measurable (fun t : Fin k → ℝ =>
      ENNReal.ofReal (_root_.GD.N0072.d007621 (fun i => θ.scale i ^ 2 / (sizes i : ℝ)) (_root_.GD.N0021.d023313 t))) := by
    apply ENNReal.measurable_ofReal.comp
    unfold _root_.GD.N0072.d007621
    fun_prop
  rw [_root_.GD.N0021.d023315, _root_.GD.N0072.d023297 sizes hn _
    _root_.GD.N0021.d023314 (fun t => _root_.GD.N0232.N0719.N0900.d009131 hk (_root_.GD.N0232.N0719.N0933.d009305 k ((fun _ => 0), t)))]
  symm
  exact (_root_.GD.N0102.N0423.d028276 sizes hn θ.scale).lintegral_comp hm


theorem d028278 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (c : ℝ) (hc : 0 < c) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / ENNReal.ofReal c =
      ∫⁻ x, ENNReal.ofReal (f x / c) ∂μ := by
  simp_rw [ENNReal.ofReal_div_of_pos hc, div_eq_mul_inv]
  exact (lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hf)).symm



theorem d028279
    (sizes : Fin k → ℕ) (hk : 0 < k) (hn : ∀ i, 2 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0962.d012186 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) =
      ∫⁻ q, ENNReal.ofReal (_root_.GD.N0072.d007621 (fun i => θ.scale i ^ 2 / (sizes i : ℝ))
        (_root_.GD.N0021.d023313 (fun i => (θ.scale i ^ 2 / (sizes i : ℝ)) * q i)) /
        _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) ∂_root_.GD.N0102.N0423.d028274 sizes := by
  have ho : 0 < _root_.GD.N0232.N0719.N0963.d012141 k sizes θ :=
    _root_.GD.N0232.N0719.N0963.d012143 k sizes hk (fun i => by have := hn i; omega) θ
  let f : (Fin k → ℝ) → ℝ := fun q =>
    _root_.GD.N0072.d007621 (fun i => θ.scale i ^ 2 / (sizes i : ℝ))
      (_root_.GD.N0021.d023313 (fun i => (θ.scale i ^ 2 / (sizes i : ℝ)) * q i))
  have hm : Measurable f := by
    unfold f _root_.GD.N0072.d007621
    fun_prop
  calc
    _ = (∫⁻ q, ENNReal.ofReal (f q) ∂_root_.GD.N0102.N0423.d028274 sizes) /
        ENNReal.ofReal (_root_.GD.N0232.N0719.N0963.d012141 k sizes θ) :=
      congrArg (fun r : ℝ≥0∞ => r / ENNReal.ofReal (_root_.GD.N0232.N0719.N0963.d012141 k sizes θ))
        (_root_.GD.N0102.N0423.d028277 sizes hk hn θ)
    _ = _ := _root_.GD.N0102.N0423.d028278 (_root_.GD.N0102.N0423.d028274 sizes) f hm _ ho



theorem d028280
    (sizes : Fin k → ℕ) (hk : 0 < k) (hn : ∀ i, 2 ≤ sizes i) (C : ℝ)
    (hbound : ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k,
      (∫⁻ q, ENNReal.ofReal (_root_.GD.N0072.d007621 (fun i => θ.scale i ^ 2 / (sizes i : ℝ))
        (_root_.GD.N0021.d023313 (fun i => (θ.scale i ^ 2 / (sizes i : ℝ)) * q i)) /
        _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) ∂_root_.GD.N0102.N0423.d028274 sizes) ≤ ENNReal.ofReal C) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes) ≤ ENNReal.ofReal C := by
  apply iSup_le
  intro θ
  rw [_root_.GD.N0102.N0423.d028279 sizes hk hn θ]
  exact hbound θ

end
end GD.N0102.N0423

#print axioms _root_.GD.N0102.N0423.d028276
#print axioms _root_.GD.N0102.N0423.d028277
#print axioms _root_.GD.N0102.N0423.d028278
#print axioms _root_.GD.N0102.N0423.d028279
#print axioms _root_.GD.N0102.N0423.d028280
