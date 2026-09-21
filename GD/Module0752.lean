import GD.Module0749
import GD.Module0624






















open scoped BigOperators NNReal ENNReal
open ProbabilityTheory MeasureTheory

namespace GD
namespace N0232
namespace N0719
namespace N1011

noncomputable section

open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0137
open _root_.GD.N0107
open _root_.GD.N0232.N0719.N0865



theorem d011282
    (location scale x : ℝ) (hscale : scale ≠ 0) :
    _root_.GD.N0232.N0719.N0932.d009204 location scale x =
      (Real.sqrt (2 * Real.pi * scale ^ 2))⁻¹ /
          (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp
          (x ^ 2 / 2 - (x - location) ^ 2 / (2 * scale ^ 2)) := by
  have hpdf :
      _root_.GD.N0232.N0719.N0932.d009204 location scale x =
        gaussianPDFReal location (_root_.GD.N0232.N0719.N0932.d009193 scale) x /
          gaussianPDFReal 0 1 x := by
    simp [_root_.GD.N0232.N0719.N0932.d009204, _root_.GD.N0232.N0719.N0932.d009197]
  rw [hpdf]
  unfold gaussianPDFReal
  rw [_root_.GD.N0232.N0719.N0932.d009194]
  norm_num only [NNReal.coe_one, sub_zero, mul_one]
  change
    ((Real.sqrt (2 * Real.pi * scale ^ 2))⁻¹ *
        Real.exp (-((x - location) ^ 2) / (2 * scale ^ 2))) /
      ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)) = _
  rw [div_eq_mul_inv, mul_inv]
  calc
    (Real.sqrt (2 * Real.pi * scale ^ 2))⁻¹ *
          Real.exp (-((x - location) ^ 2) / (2 * scale ^ 2)) *
        (((Real.sqrt (2 * Real.pi))⁻¹)⁻¹ *
          (Real.exp (-(x ^ 2) / 2))⁻¹) =
        ((Real.sqrt (2 * Real.pi * scale ^ 2))⁻¹ /
            (Real.sqrt (2 * Real.pi))⁻¹) *
          (Real.exp (-((x - location) ^ 2) / (2 * scale ^ 2)) *
            (Real.exp (-(x ^ 2) / 2))⁻¹) := by ring
    _ = _ := by
      rw [← Real.exp_neg, ← Real.exp_add]
      congr 2
      field_simp [hscale]
      ring


def d011283 (n : ℕ) (meanVariance : ℝ) : ℝ :=
  (n : ℝ) * ((n - 1 : ℕ) : ℝ) * meanVariance


def d011284
    (n : ℕ) (location scale mean meanVariance : ℝ) : ℝ :=
  ((Real.sqrt (2 * Real.pi * scale ^ 2))⁻¹ /
      (Real.sqrt (2 * Real.pi))⁻¹) ^ n *
    Real.exp
      ((_root_.GD.N0232.N0719.N1011.d011283 n meanVariance + (n : ℝ) * mean ^ 2) / 2 -
        (_root_.GD.N0232.N0719.N1011.d011283 n meanVariance +
            (n : ℝ) * (mean - location) ^ 2) /
          (2 * scale ^ 2))

@[fun_prop]
theorem d011285
    (n : ℕ) (location scale : ℝ) :
    Measurable (fun z : ℝ × ℝ ↦
      _root_.GD.N0232.N0719.N1011.d011284 n location scale z.1 z.2) := by
  unfold _root_.GD.N0232.N0719.N1011.d011284 _root_.GD.N0232.N0719.N1011.d011283
  fun_prop



theorem d011286
    {n : ℕ} (hn : 2 ≤ n) (x : _root_.GD.N0137.d008894 n) :
    @_root_.GD.N0126.d006422 (Fin n) _ x =
      _root_.GD.N0232.N0719.N1011.d011283 n
        (_root_.GD.N0107.d009085 x / (n : ℝ)) := by
  unfold _root_.GD.N0232.N0719.N1011.d011283 _root_.GD.N0107.d009085
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hn1 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n - 1 ≠ 0)
  field_simp [hn0, hn1]



theorem d011287
    {n : ℕ} (hn : 2 ≤ n) (location scale : ℝ)
    (hscale : scale ≠ 0) (x : _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0719.N0932.d009213 n location scale x =
      _root_.GD.N0232.N0719.N1011.d011284 n location scale
        (_root_.GD.N0107.d009084 x) (_root_.GD.N0107.d009085 x / (n : ℝ)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  simp_rw [_root_.GD.N0232.N0719.N1011.d011282 location scale _ hscale]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum]
  unfold _root_.GD.N0232.N0719.N1011.d011284
  congr 1
  rw [Finset.sum_sub_distrib]
  simp only [← Finset.sum_div]
  rw [_root_.GD.N0126.d006428]
  rw [_root_.GD.N0126.d006427]
  rw [_root_.GD.N0232.N0719.N1011.d011286 hn x]
  simp only [_root_.GD.N0126.d006419, Fintype.card_fin,
    _root_.GD.N0107.d009084]


def d011288
    (k : ℕ) (sizes : Fin k → ℕ)
    (location : ℝ) (scale : Fin k → ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  ∏ i, _root_.GD.N0232.N0719.N1011.d011284
    (sizes i) location (scale i) (s.mean i) (s.meanVariance i)

@[fun_prop]
theorem d011289
    (k : ℕ) (sizes : Fin k → ℕ)
    (location : ℝ) (scale : Fin k → ℝ) :
    Measurable (_root_.GD.N0232.N0719.N1011.d011288 k sizes location scale) := by
  unfold _root_.GD.N0232.N0719.N1011.d011288
  apply Finset.measurable_prod
  intro i hi
  have hpair : Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 k ↦
      (s.mean i, s.meanVariance i)) :=
    (_root_.GD.N0232.N0719.N0900.d009099 i).prodMk (_root_.GD.N0232.N0719.N0900.d009100 i)
  exact (_root_.GD.N0232.N0719.N1011.d011285
    (sizes i) location (scale i)).comp hpair


theorem d011290
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scale : Fin k → ℝ)
    (hscale : ∀ i, scale i ≠ 0)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0932.d009219 k sizes location scale omega =
      _root_.GD.N0232.N0719.N1011.d011288 k sizes location scale
        (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega) := by
  unfold _root_.GD.N0232.N0719.N0932.d009219 _root_.GD.N0232.N0719.N0932.d009190
    _root_.GD.N0232.N0719.N1011.d011288
  apply Finset.prod_congr rfl
  intro i hi
  exact _root_.GD.N0232.N0719.N1011.d011287
    (hsizes i) location (scale i) (hscale i) (omega i)



def d011291
    (k : ℕ) (sizes : Fin k → ℕ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ :=
  _root_.GD.N0232.N0719.N1011.d011288 k sizes theta.location theta.scale

@[fun_prop]
theorem d011292
    (k : ℕ) (sizes : Fin k → ℕ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    Measurable (_root_.GD.N0232.N0719.N1011.d011291 k sizes theta) := by
  exact _root_.GD.N0232.N0719.N1011.d011289
    k sizes theta.location theta.scale


theorem d011293
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0865.d011217 k sizes theta =
      _root_.GD.N0232.N0719.N1011.d011291 k sizes theta ∘
        _root_.GD.N0232.N0719.N0900.d009104 k sizes := by
  funext omega
  exact _root_.GD.N0232.N0719.N1011.d011290
    k sizes hsizes theta.location theta.scale
      (fun i ↦ (theta.scale_pos i).ne') omega



theorem d011294
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    Measurable[(_root_.GD.N0232.N0719.N0900.d009098 k).comap (_root_.GD.N0232.N0719.N0900.d009104 k sizes)]
      (_root_.GD.N0232.N0719.N0865.d011217 k sizes theta) := by
  rw [_root_.GD.N0232.N0719.N1011.d011293 k sizes hsizes theta]
  exact (_root_.GD.N0232.N0719.N1011.d011292 k sizes theta).comp
    (comap_measurable (_root_.GD.N0232.N0719.N0900.d009104 k sizes))

end

end N1011
end N0719
end N0232
end GD
