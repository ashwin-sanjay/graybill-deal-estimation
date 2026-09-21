import GD.Module0698
import GD.Module0699



















open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace GD.N0232.N0719.N0902

noncomputable section

local instance d010366 {k : ℕ} (p : Fin k → ℝ) :
    Decidable (_root_.GD.N0232.N0719.N0951.d003580 p) :=
  Classical.propDecidable _


def d010367 {k : ℕ}
    (t : Fin k → ℝ) (y : Fin k → ℝ) : _root_.GD.N0232.N0719.N0900.d009096 k :=
  ⟨y, t⟩

@[fun_prop]
theorem d010368
    {k : ℕ} (t : Fin k → ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0902.d010367 t) := by
  rw [measurable_comap_iff]
  exact measurable_id.prodMk measurable_const



theorem d010369
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ)
    (t : Fin k → ℝ) :
    MemLp
      (fun y =>
        _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y))
      2 (_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) := by
  have hmajorant :=
    _root_.GD.N0232.N0719.N0910.d010291
      sizes hsizes 0 scales
  apply hmajorant.mono'
  · exact
      (_root_.GD.N0232.N0719.N0900.d009121.comp
        (_root_.GD.N0232.N0719.N0902.d010368 t)).aestronglyMeasurable
  · filter_upwards with y
    simpa [_root_.GD.N0232.N0719.N0902.d010367, Real.norm_eq_abs] using
      _root_.GD.N0232.N0719.N0910.d010281
        hk 0 (_root_.GD.N0232.N0719.N0902.d010367 t y)



theorem d010370
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    MemLp
      (fun y =>
        _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y))
      2 (_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) := by
  have hmajorant :=
    (_root_.GD.N0232.N0719.N0910.d010291
      sizes hsizes 0 scales).const_mul 3000
  apply hmajorant.mono'
  · exact
      (_root_.GD.N0232.N0719.N1018.d010044 triangle).comp
        (_root_.GD.N0232.N0719.N0902.d010368 t) |>.aestronglyMeasurable
  · filter_upwards with y
    simpa [_root_.GD.N0232.N0719.N0902.d010367, Real.norm_eq_abs] using
      _root_.GD.N0232.N0719.N0910.d010283
        hk triangle 0 (_root_.GD.N0232.N0719.N0902.d010367 t y) ht



theorem d010371
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    Integrable
      (fun y =>
        _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y))
      (_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) :=
  (_root_.GD.N0232.N0719.N0902.d010369 hk sizes hsizes scales t).integrable_mul
    (_root_.GD.N0232.N0719.N0902.d010370
      hk sizes hsizes scales triangle t ht)


def d010372
    {k : ℕ} (sizes : Fin k → ℕ)
    (scales : Fin k → ℝ) (i : Fin k) : ℝ≥0 :=
  .mk (scales i ^ 2 / (sizes i : ℝ))
    (div_nonneg (sq_nonneg (scales i))
      (Nat.cast_nonneg (sizes i)))

theorem d010373
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales =
      Measure.pi (fun i => gaussianReal 0
        (_root_.GD.N0232.N0719.N0902.d010372 sizes scales i)) := by
  simpa [_root_.GD.N0232.N0719.N0902.d010372] using
    _root_.GD.N0232.N0719.N0933.d009302
      k sizes hsizes 0 scales




theorem d010374
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
    let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
    let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
    Integrable
      (fun y =>
        r *
            _root_.GD.N0232.N0719.N0886.d003653 (q 0) (q 1) (q 2)
              (_root_.GD.N0232.N0719.N1004.d009807 triangle y) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y))
      (_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) := by
  dsimp only
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
  let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
  let τ := _root_.GD.N0232.N0719.N0954.d009348 hk t / r
  have hp : ∀ j, 0 < q j :=
    _root_.GD.N0232.N0719.N0956.d010071 hk triangle (fun _ => 0) t ht
  have hτ : 0 < τ := div_pos
    (_root_.GD.N0232.N0719.N0956.d010063 hk t ht)
    (_root_.GD.N0232.N0719.N0956.d010070
      hk triangle (fun _ => 0) t ht)
  have hres :
      Integrable
        (_root_.GD.N0232.N0719.N0890.d003772
          (q 0) (q 1) (q 2) τ)
        (_root_.GD.N0232.N0719.N0886.d003649
          (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0))
          (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1))
          (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2))) :=
    _root_.GD.N0232.N0719.N0890.d003779
      (hp 0).le (hp 1).le (hp 2).le hτ
      (add_pos (hp 0) (hp 1)).ne'
      (add_pos (hp 0) (hp 2)).ne'
      (add_pos (hp 1) (hp 2)).ne'
  have hcomp :=
    (_root_.GD.N0232.N0719.N1004.d009810
      triangle (_root_.GD.N0232.N0719.N0902.d010372 sizes scales)).integrable_comp_of_integrable hres
  have hscaled :=
    hcomp.const_mul
      ((if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0) * r ^ 2)
  rw [_root_.GD.N0232.N0719.N0902.d010373 sizes hsizes scales]
  apply hscaled.congr
  filter_upwards with y
  simp only [_root_.GD.N0232.N0719.N0902.d010367, Function.comp_apply]
  rw [_root_.GD.N0232.N0719.N0905.d010274
      hk triangle y t ht,
    _root_.GD.N0232.N0719.N0905.d010277
      hk triangle y t ht]



theorem d010375
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    Integrable
      (fun y =>
        _root_.GD.N0232.N0719.N1004.d009812 triangle
            (_root_.GD.N0232.N0719.N0954.d009349 hk t)
            (_root_.GD.N0232.N0719.N1004.d009800 triangle y) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y))
      (_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) := by
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
  let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
  have htotal :=
    _root_.GD.N0232.N0719.N0902.d010371
      hk sizes hsizes scales triangle t ht
  have hselected :
      Integrable
        (fun y =>
          r *
              _root_.GD.N0232.N0719.N0886.d003653 (q 0) (q 1) (q 2)
                (_root_.GD.N0232.N0719.N1004.d009807 triangle y) *
            _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y))
        (_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) :=
    _root_.GD.N0232.N0719.N0902.d010374
      hk sizes hsizes scales triangle t ht
  have hdiff := htotal.sub hselected
  apply hdiff.congr
  filter_upwards with y
  simp only [Pi.sub_apply, _root_.GD.N0232.N0719.N0902.d010367]
  rw [_root_.GD.N0232.N0719.N0905.d010276
      hk triangle y t ht]
  dsimp [_root_.GD.N0232.N0719.N0902.d010367, p, r, q] at *
  ring



theorem d010376
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    (∫ y,
        _root_.GD.N0232.N0719.N1004.d009812 triangle
            (_root_.GD.N0232.N0719.N0954.d009349 hk t)
            (_root_.GD.N0232.N0719.N1004.d009800 triangle y) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)
      ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) = 0 := by
  rw [_root_.GD.N0232.N0719.N0902.d010373 sizes hsizes scales]
  let F : (Fin 3 → ℝ) → ℝ :=
    fun u =>
      _root_.GD.N0232.N0719.N0905.d010270 hk triangle t
        (_root_.GD.N0232.N0719.N1004.d009804 u)
  have hF : Measurable F :=
    (_root_.GD.N0232.N0719.N0905.d010271 hk triangle t).comp
      _root_.GD.N0232.N0719.N1004.d009805
  have hzero :=
    _root_.GD.N0232.N0719.N1004.d009815
      triangle (_root_.GD.N0232.N0719.N0902.d010372 sizes scales)
      (_root_.GD.N0232.N0719.N0954.d009349 hk t) F hF
  convert hzero using 1
  apply integral_congr_ae
  filter_upwards with y
  simp only [_root_.GD.N0232.N0719.N0902.d010367]
  rw [_root_.GD.N0232.N0719.N0905.d010274
      hk triangle y t ht]
  simp only [F, _root_.GD.N0232.N0719.N1004.d009807,
    Function.comp_apply]
  ring





theorem d010377
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
    let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
    let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
    let τ := _root_.GD.N0232.N0719.N0954.d009348 hk t / r
    (∫ y,
        _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)
      ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) =
      (if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0) * r ^ 2 *
        ∫ z,
          _root_.GD.N0232.N0719.N0890.d003772
            (q 0) (q 1) (q 2) τ z
          ∂_root_.GD.N0232.N0719.N0886.d003649
            (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0))
            (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1))
            (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2)) := by
  dsimp only
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
  let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
  let τ := _root_.GD.N0232.N0719.N0954.d009348 hk t / r
  have htotal :=
    _root_.GD.N0232.N0719.N0902.d010371
      hk sizes hsizes scales triangle t ht
  have hselected :
      Integrable
        (fun y =>
          r *
              _root_.GD.N0232.N0719.N0886.d003653 (q 0) (q 1) (q 2)
                (_root_.GD.N0232.N0719.N1004.d009807 triangle y) *
            _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y))
        (_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) :=
    _root_.GD.N0232.N0719.N0902.d010374
      hk sizes hsizes scales triangle t ht
  have hcomplement :
      Integrable
        (fun y =>
          _root_.GD.N0232.N0719.N1004.d009812 triangle p
              (_root_.GD.N0232.N0719.N1004.d009800 triangle y) *
            _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y))
        (_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) :=
    _root_.GD.N0232.N0719.N0902.d010375
      hk sizes hsizes scales triangle t ht
  rw [show
    (fun y =>
      _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
        _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)) =
      (fun y =>
        r *
            _root_.GD.N0232.N0719.N0886.d003653 (q 0) (q 1) (q 2)
              (_root_.GD.N0232.N0719.N1004.d009807 triangle y) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y) +
        _root_.GD.N0232.N0719.N1004.d009812 triangle p
            (_root_.GD.N0232.N0719.N1004.d009800 triangle y) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)) by
        funext y
        simp only [_root_.GD.N0232.N0719.N0902.d010367]
        rw [_root_.GD.N0232.N0719.N0905.d010276
          hk triangle y t ht]
        dsimp [p, r, q, _root_.GD.N0232.N0719.N0902.d010367]
        ring]
  rw [integral_add hselected hcomplement,
    _root_.GD.N0232.N0719.N0902.d010376
      hk sizes hsizes scales triangle t ht,
    add_zero]
  rw [_root_.GD.N0232.N0719.N0902.d010373 sizes hsizes scales]
  have hmp :=
    _root_.GD.N0232.N0719.N1004.d009810
      triangle (_root_.GD.N0232.N0719.N0902.d010372 sizes scales)
  have hmeas :
      AEStronglyMeasurable
        (fun z =>
          (if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0) * r ^ 2 *
            _root_.GD.N0232.N0719.N0890.d003772
              (q 0) (q 1) (q 2) τ z)
        (_root_.GD.N0232.N0719.N0886.d003649
          (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0))
          (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1))
          (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2))) :=
    (_root_.GD.N0232.N0719.N0890.d003774
      (fun z => by
        have hp : ∀ j, 0 < q j :=
          _root_.GD.N0232.N0719.N0956.d010071
            hk triangle (fun _ => 0) t ht
        have hτ : 0 < τ := div_pos
          (_root_.GD.N0232.N0719.N0956.d010063 hk t ht)
          (_root_.GD.N0232.N0719.N0956.d010070
            hk triangle (fun _ => 0) t ht)
        exact
          (_root_.GD.N0232.N0719.N0890.d003776
            (hp 0).le (hp 1).le (hp 2).le hτ z).ne')).const_mul _
      |>.aestronglyMeasurable
  have hmeas_map :
      AEStronglyMeasurable
        (fun z =>
          (if _root_.GD.N0232.N0719.N0951.d003580 p then 1 else 0) * r ^ 2 *
            _root_.GD.N0232.N0719.N0890.d003772
              (q 0) (q 1) (q 2) τ z)
        (Measure.map
          (_root_.GD.N0232.N0719.N1004.d009807 triangle)
          (Measure.pi fun i => gaussianReal 0 (_root_.GD.N0232.N0719.N0902.d010372 sizes scales i))) := by
    rw [hmp.map_eq]
    exact hmeas
  rw [← integral_const_mul]
  rw [← hmp.map_eq,
    MeasureTheory.integral_map hmp.measurable.aemeasurable hmeas_map]
  apply integral_congr_ae
  filter_upwards with y
  simp only [_root_.GD.N0232.N0719.N0902.d010367]
  rw [_root_.GD.N0232.N0719.N0905.d010274
      hk triangle y t ht,
    _root_.GD.N0232.N0719.N0905.d010277
      hk triangle y t ht]














theorem d010378
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
    let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
    (∫ y,
        _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)
      ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) = 0 ↔
      ¬_root_.GD.N0232.N0719.N0951.d003580 p ∨
        (_root_.GD.N0232.N0719.N0895.d003746
              (q 0) (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0)) =
            _root_.GD.N0232.N0719.N0895.d003746
              (q 1) (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1)) ∧
          _root_.GD.N0232.N0719.N0895.d003746
              (q 0) (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0)) =
            _root_.GD.N0232.N0719.N0895.d003746
              (q 2) (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2))) := by
  dsimp only
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
  let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
  let τ := _root_.GD.N0232.N0719.N0954.d009348 hk t / r
  let v₀ := _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0)
  let v₁ := _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1)
  let v₂ := _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2)
  let I :=
    ∫ z,
      _root_.GD.N0232.N0719.N0890.d003772
        (q 0) (q 1) (q 2) τ z
    ∂_root_.GD.N0232.N0719.N0886.d003649 v₀ v₁ v₂
  have hq : ∀ j, 0 < q j :=
    _root_.GD.N0232.N0719.N0956.d010071
      hk triangle (fun _ ↦ 0) t ht
  have hqsum : q 0 + q 1 + q 2 = 1 := by
    have hsum :=
      _root_.GD.N0232.N0719.N0956.d010072
        hk triangle (fun _ ↦ 0) t ht
    simpa only [q, Fin.sum_univ_three] using hsum
  have hr : 0 < r :=
    _root_.GD.N0232.N0719.N0956.d010070
      hk triangle (fun _ ↦ 0) t ht
  have hτ : 0 < τ := div_pos
    (_root_.GD.N0232.N0719.N0956.d010063 hk t ht) hr
  have hv : ∀ j : Fin 3, _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle j) ≠ 0 := by
    intro j
    have hpos : 0 < _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle j) := by
      apply NNReal.coe_pos.1
      simp only [_root_.GD.N0232.N0719.N0902.d010372, NNReal.coe_mk]
      have hsize : 0 < (sizes (triangle j) : ℝ) := by
        exact_mod_cast
          (lt_of_lt_of_le (by omega : 0 < 2) (hsizes (triangle j)))
      exact div_pos (sq_pos_of_pos (hscales (triangle j))) hsize
    exact hpos.ne'
  have hIzero :
      I = 0 ↔
        _root_.GD.N0232.N0719.N0895.d003746 (q 0) v₀ =
            _root_.GD.N0232.N0719.N0895.d003746 (q 1) v₁ ∧
          _root_.GD.N0232.N0719.N0895.d003746 (q 0) v₀ =
            _root_.GD.N0232.N0719.N0895.d003746 (q 2) v₂ := by
    exact
      _root_.GD.N0232.N0719.N0890.d003788
        (hq 0) (hq 1) (hq 2) hqsum (hv 0) (hv 1) (hv 2) hτ
  have hcross :=
    _root_.GD.N0232.N0719.N0902.d010377
      hk sizes hsizes scales triangle t ht
  change
    (∫ y,
        _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)
      ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) = 0 ↔
      ¬_root_.GD.N0232.N0719.N0951.d003580 p ∨
        (_root_.GD.N0232.N0719.N0895.d003746 (q 0) v₀ =
            _root_.GD.N0232.N0719.N0895.d003746 (q 1) v₁ ∧
          _root_.GD.N0232.N0719.N0895.d003746 (q 0) v₀ =
            _root_.GD.N0232.N0719.N0895.d003746 (q 2) v₂)
  by_cases hbalanced : _root_.GD.N0232.N0719.N0951.d003580 p
  · rw [hcross, if_pos hbalanced, one_mul]
    change r ^ 2 * I = 0 ↔ _
    rw [mul_eq_zero]
    simp only [sq_eq_zero_iff, ne_of_gt hr, or_false, hIzero,
      hbalanced, not_true, false_or]
  · rw [hcross, if_neg hbalanced]
    simp [hbalanced]







theorem d010379
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
    let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
    (∫ y,
        _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)
      ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) < 0 ↔
      _root_.GD.N0232.N0719.N0951.d003580 p ∧
        ¬(_root_.GD.N0232.N0719.N0895.d003746
              (q 0) (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0)) =
            _root_.GD.N0232.N0719.N0895.d003746
              (q 1) (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1)) ∧
          _root_.GD.N0232.N0719.N0895.d003746
              (q 0) (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0)) =
            _root_.GD.N0232.N0719.N0895.d003746
              (q 2) (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2))) := by
  dsimp only
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
  let q := _root_.GD.N0232.N0719.N0951.d003586 triangle p
  let τ := _root_.GD.N0232.N0719.N0954.d009348 hk t / r
  let v₀ := _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0)
  let v₁ := _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1)
  let v₂ := _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2)
  let I :=
    ∫ z,
      _root_.GD.N0232.N0719.N0890.d003772
        (q 0) (q 1) (q 2) τ z
    ∂_root_.GD.N0232.N0719.N0886.d003649 v₀ v₁ v₂
  have hq : ∀ j, 0 < q j :=
    _root_.GD.N0232.N0719.N0956.d010071
      hk triangle (fun _ ↦ 0) t ht
  have hqsum : q 0 + q 1 + q 2 = 1 := by
    have hsum :=
      _root_.GD.N0232.N0719.N0956.d010072
        hk triangle (fun _ ↦ 0) t ht
    simpa only [q, Fin.sum_univ_three] using hsum
  have hr : 0 < r :=
    _root_.GD.N0232.N0719.N0956.d010070
      hk triangle (fun _ ↦ 0) t ht
  have hτ : 0 < τ := div_pos
    (_root_.GD.N0232.N0719.N0956.d010063 hk t ht) hr
  have hv : ∀ j : Fin 3, _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle j) ≠ 0 := by
    intro j
    have hpos : 0 < _root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle j) := by
      apply NNReal.coe_pos.1
      simp only [_root_.GD.N0232.N0719.N0902.d010372, NNReal.coe_mk]
      have hsize : 0 < (sizes (triangle j) : ℝ) := by
        exact_mod_cast
          (lt_of_lt_of_le (by omega : 0 < 2) (hsizes (triangle j)))
      exact div_pos (sq_pos_of_pos (hscales (triangle j))) hsize
    exact hpos.ne'
  have hIstrict :
      I < 0 ↔
        ¬(_root_.GD.N0232.N0719.N0895.d003746 (q 0) v₀ =
            _root_.GD.N0232.N0719.N0895.d003746 (q 1) v₁ ∧
          _root_.GD.N0232.N0719.N0895.d003746 (q 0) v₀ =
            _root_.GD.N0232.N0719.N0895.d003746 (q 2) v₂) := by
    exact
      _root_.GD.N0232.N0719.N0890.d003787
        (hq 0) (hq 1) (hq 2) hqsum (hv 0) (hv 1) (hv 2) hτ
  have hcross :=
    _root_.GD.N0232.N0719.N0902.d010377
      hk sizes hsizes scales triangle t ht
  change
    (∫ y,
        _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)
      ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) < 0 ↔
      _root_.GD.N0232.N0719.N0951.d003580 p ∧
        ¬(_root_.GD.N0232.N0719.N0895.d003746 (q 0) v₀ =
            _root_.GD.N0232.N0719.N0895.d003746 (q 1) v₁ ∧
          _root_.GD.N0232.N0719.N0895.d003746 (q 0) v₀ =
            _root_.GD.N0232.N0719.N0895.d003746 (q 2) v₂)
  by_cases hbalanced : _root_.GD.N0232.N0719.N0951.d003580 p
  · rw [hcross, if_pos hbalanced, one_mul]
    constructor
    · intro hproduct
      have hI : I < 0 := by
        by_contra hnot
        have hInonneg : 0 ≤ I := not_lt.mp hnot
        exact (not_lt_of_ge (mul_nonneg (sq_nonneg r) hInonneg)) hproduct
      exact ⟨hbalanced, hIstrict.1 hI⟩
    · rintro ⟨_, hmismatch⟩
      exact mul_neg_of_pos_of_neg (sq_pos_of_pos hr) (hIstrict.2 hmismatch)
  · rw [hcross, if_neg hbalanced]
    simp [hbalanced]

end

end GD.N0232.N0719.N0902
