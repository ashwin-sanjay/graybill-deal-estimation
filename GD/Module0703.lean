import GD.Module0702
import GD.Module0265














open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace GD.N0232.N0719.N0903

noncomputable section

local instance d010380 {k : ℕ} (p : Fin k → ℝ) :
    Decidable (_root_.GD.N0232.N0719.N0951.d003580 p) :=
  Classical.propDecidable _



theorem d010381
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
    let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
    (∫ y,
        _root_.GD.N0232.N0719.N1018.d010017 triangle
          (_root_.GD.N0232.N0719.N0902.d010367 t y)
      ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) =
      _root_.GD.N0232.N0719.N1019.d003792
        (q 0) (q 1) (q 2)
        (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0) : ℝ)
        (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1) : ℝ)
        (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2) : ℝ) := by
  dsimp only
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
  have hqsum :
      q 0 + q 1 + q 2 = 1 := by
    have :=
      _root_.GD.N0232.N0719.N0956.d010072
        hk triangle (fun _ => 0) t ht
    simpa only [q, Fin.sum_univ_three] using this
  rw [_root_.GD.N0232.N0719.N0902.d010373 sizes hsizes scales]
  have hmp :=
    _root_.GD.N0232.N0719.N1004.d009810
      triangle (_root_.GD.N0232.N0719.N0902.d010372 sizes scales)
  have hmeas :
      AEStronglyMeasurable
        (fun z : ℝ × (ℝ × ℝ) =>
          _root_.GD.N0232.N0719.N0881.d003572
            (q 0) (q 1) (q 2)
            z.1 z.2.1 z.2.2)
        (_root_.GD.N0232.N0719.N0886.d003649
          (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0))
          (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1))
          (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2))) := by
    unfold _root_.GD.N0232.N0719.N0881.d003572 _root_.GD.N0232.N0719.N0881.d003570
    fun_prop
  rw [show
    (fun y =>
      _root_.GD.N0232.N0719.N1018.d010017 triangle
        (_root_.GD.N0232.N0719.N0902.d010367 t y)) =
      (fun y =>
        _root_.GD.N0232.N0719.N0881.d003572
          (q 0) (q 1) (q 2)
          (_root_.GD.N0232.N0719.N1004.d009807 triangle y).1
          (_root_.GD.N0232.N0719.N1004.d009807 triangle y).2.1
          (_root_.GD.N0232.N0719.N1004.d009807 triangle y).2.2) by
        funext y
        exact
          _root_.GD.N0232.N0719.N0905.d010273
            hk triangle y t ht]
  have hmeas_map :
      AEStronglyMeasurable
        (fun z : ℝ × (ℝ × ℝ) =>
          _root_.GD.N0232.N0719.N0881.d003572
            (q 0) (q 1) (q 2)
            z.1 z.2.1 z.2.2)
        (Measure.map
          (_root_.GD.N0232.N0719.N1004.d009807 triangle)
          (Measure.pi fun i => gaussianReal 0
            (_root_.GD.N0232.N0719.N0902.d010372 sizes scales i))) := by
    rw [hmp.map_eq]
    exact hmeas
  rw [← MeasureTheory.integral_map hmp.measurable.aemeasurable hmeas_map,
    hmp.map_eq]
  exact
    _root_.GD.N0232.N0719.N0882.d003808
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0))
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1))
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2))
      hqsum



theorem d010382
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (y t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N1018.d010021 triangle ⟨y, t⟩ ^ 2 ≤
      (if _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0954.d009349 hk t) then 1 else 0) *
        250000 *
        _root_.GD.N0232.N0719.N0951.d003585 triangle
            (_root_.GD.N0232.N0719.N0954.d009349 hk t) ^ 2 *
        _root_.GD.N0232.N0719.N1018.d010017 triangle ⟨y, t⟩ := by
  by_cases hcell :
      _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0954.d009349 hk t)
  · rw [if_pos hcell]
    have hmain :=
      _root_.GD.N0232.N0719.N1020.d010267
        hk triangle (⟨y, t⟩ : _root_.GD.N0232.N0719.N0900.d009096 k) ht
    rw [_root_.GD.N0232.N0719.N0956.d010073
      hk triangle y t ht] at hmain
    simpa only [one_mul, mul_assoc] using hmain
  · have hloc :
      _root_.GD.N0232.N0719.N1018.d010020 (⟨y, t⟩ : _root_.GD.N0232.N0719.N0900.d009096 k) = 0 := by
      rw [_root_.GD.N0232.N0719.N0956.d010076
        hk y t ht, if_neg hcell]
    rw [if_neg hcell]
    simp [_root_.GD.N0232.N0719.N1018.d010021, hloc]





theorem d010383
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    {V : ℝ}
    (hv0V :
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0) : ℝ) ≤ V)
    (hv1V :
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1) : ℝ) ≤ V)
    (hv2V :
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2) : ℝ) ≤ V) :
    let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
    let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
    (∫ y,
        _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y) ^ 2
      ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) ≤
      (if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0) *
        250000 * r ^ 2 * V := by
  dsimp only
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
  let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
  have hqsum :
      q 0 + q 1 + q 2 = 1 := by
    have :=
      _root_.GD.N0232.N0719.N0956.d010072
        hk triangle (fun _ => 0) t ht
    simpa only [q, Fin.sum_univ_three] using this
  have hqpos : ∀ j, 0 < q j :=
    _root_.GD.N0232.N0719.N0956.d010071
      hk triangle (fun _ => 0) t ht
  have hdispInt :
      Integrable
        (fun y =>
          _root_.GD.N0232.N0719.N1018.d010017 triangle
            (_root_.GD.N0232.N0719.N0902.d010367 t y))
        (_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) := by
    rw [_root_.GD.N0232.N0719.N0902.d010373 sizes hsizes scales]
    have h :=
      _root_.GD.N0232.N0719.N0882.d003807
        (q 0) (q 1) (q 2)
        (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0))
        (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1))
        (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2))
    have hcomp :=
      (_root_.GD.N0232.N0719.N1004.d009810
        triangle (_root_.GD.N0232.N0719.N0902.d010372 sizes scales)).integrable_comp_of_integrable h
    apply hcomp.congr
    filter_upwards with y
    simp only [_root_.GD.N0232.N0719.N0902.d010367, Function.comp_apply]
    exact
      (_root_.GD.N0232.N0719.N0905.d010273
        hk triangle y t ht).symm
  have hright :=
    hdispInt.const_mul
      ((if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0) *
        250000 * r ^ 2)
  have hleft :=
    (_root_.GD.N0232.N0719.N0902.d010370
      hk sizes hsizes scales triangle t ht).integrable_sq
  have hpoint :
      ∀ y,
        _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y) ^ 2 ≤
          (if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0) *
            250000 * r ^ 2 *
            _root_.GD.N0232.N0719.N1018.d010017 triangle
              (_root_.GD.N0232.N0719.N0902.d010367 t y) := by
    intro y
    simpa [_root_.GD.N0232.N0719.N0902.d010367, p, r, mul_assoc] using
      _root_.GD.N0232.N0719.N0903.d010382
        hk triangle y t ht
  have hint :
      (∫ y,
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y) ^ 2
        ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) ≤
        (if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0) *
          250000 * r ^ 2 *
          ∫ y,
            _root_.GD.N0232.N0719.N1018.d010017 triangle
              (_root_.GD.N0232.N0719.N0902.d010367 t y)
            ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales := by
    rw [← integral_const_mul]
    exact integral_mono hleft hright hpoint
  rw [_root_.GD.N0232.N0719.N0903.d010381
    hk sizes hsizes scales triangle t ht] at hint
  have hmean :
      _root_.GD.N0232.N0719.N1019.d003792
          (q 0) (q 1) (q 2)
          (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0) : ℝ)
          (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1) : ℝ)
          (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2) : ℝ) ≤ V :=
    _root_.GD.N0232.N0719.N1019.d003794
      hqsum (hqpos 0).le (hqpos 1).le (hqpos 2).le
      (by positivity) (by positivity) (by positivity)
      hv0V hv1V hv2V
  have hcoef :
      0 ≤
        (if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0) *
          250000 * r ^ 2 := by
    split_ifs <;> positivity
  exact hint.trans
    (mul_le_mul_of_nonneg_left hmean hcoef)

end

end GD.N0232.N0719.N0903
