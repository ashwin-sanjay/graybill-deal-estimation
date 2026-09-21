import GD.Module0649
import GD.Module0697
import GD.Module0689























open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace GD.N0232.N0719.N0910

noncomputable section


def d010278 {k : ℕ} (target : ℝ) (y : Fin k → ℝ) : ℝ :=
  ∑ i, |y i - target|

theorem d010279 {k : ℕ} (target : ℝ) (y : Fin k → ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N0910.d010278 target y :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

@[fun_prop]
theorem d010280 {k : ℕ} (target : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0910.d010278 (k := k) target) := by
  unfold _root_.GD.N0232.N0719.N0910.d010278
  fun_prop






theorem d010281
    {k : ℕ} (hk : 0 < k) (target : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    |_root_.GD.N0232.N0719.N0900.d009110 s - target| ≤ _root_.GD.N0232.N0719.N0910.d010278 target s.mean := by
  have hidentity :
      _root_.GD.N0232.N0719.N0900.d009110 s - target =
        ∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i * (s.mean i - target) := by
    unfold _root_.GD.N0232.N0719.N0900.d009110
    calc
      (∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i * s.mean i) - target =
          (∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i * s.mean i) -
            (∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i) * target := by
              rw [_root_.GD.N0232.N0719.N0900.d009131 hk s]
              ring
      _ = ∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i * (s.mean i - target) := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring
  rw [hidentity]
  calc
    |∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i * (s.mean i - target)| ≤
        ∑ i, |_root_.GD.N0232.N0719.N0900.d009108 s i * (s.mean i - target)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i * |s.mean i - target| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (_root_.GD.N0232.N0719.N0900.d009132 hk s i)]
    _ ≤ ∑ i, |s.mean i - target| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_left
        (abs_nonneg _)
        (_root_.GD.N0232.N0719.N0900.d009133 hk s i)
    _ = _root_.GD.N0232.N0719.N0910.d010278 target s.mean := rfl





theorem d010282
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (target : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hvar : ∀ i, 0 < s.meanVariance i) :
    _root_.GD.N0232.N0719.N1018.d010017 triangle s ≤
      4 *
        (∑ j : Fin 3,
          |_root_.GD.N0232.N0719.N1018.d010014 triangle s j - target|) ^ 2 := by
  have hmass :
      0 < _root_.GD.N0232.N0719.N1018.d010012 triangle s := by
    have htotal :
        0 < _root_.GD.N0232.N0719.N0900.d009107 s := by
      unfold _root_.GD.N0232.N0719.N0900.d009107 _root_.GD.N0232.N0719.N0900.d009106
      exact Finset.sum_pos
        (fun i _ => by
          rw [_root_.GD.N0232.N0719.N0900.d009127 (hvar i)]
          exact inv_pos.mpr (hvar i))
        ⟨triangle 0, Finset.mem_univ _⟩
    unfold _root_.GD.N0232.N0719.N1018.d010012
    exact Finset.sum_pos
      (fun j _ => by
        unfold _root_.GD.N0232.N0719.N0900.d009108 _root_.GD.N0232.N0719.N0900.d009106
        rw [if_neg htotal.ne',
          _root_.GD.N0232.N0719.N0900.d009127 (hvar (triangle j))]
        exact div_pos (inv_pos.mpr (hvar (triangle j))) htotal)
      Finset.univ_nonempty
  have hsum :
      _root_.GD.N0232.N0719.N1018.d010013 triangle s 0 +
          _root_.GD.N0232.N0719.N1018.d010013 triangle s 1 +
          _root_.GD.N0232.N0719.N1018.d010013 triangle s 2 = 1 := by
    simpa only [Fin.sum_univ_three] using
      _root_.GD.N0232.N0719.N1018.d010024 triangle s hmass.ne'
  have hp :
      ∀ j : Fin 3,
        0 ≤ _root_.GD.N0232.N0719.N1018.d010013 triangle s j := by
    intro j
    exact div_nonneg
      (_root_.GD.N0232.N0719.N0900.d009132 hk s (triangle j))
      hmass.le
  have hp0 : _root_.GD.N0232.N0719.N1018.d010013 triangle s 0 ≤ 1 := by
    linarith [hp 1, hp 2]
  have hp1 : _root_.GD.N0232.N0719.N1018.d010013 triangle s 1 ≤ 1 := by
    linarith [hp 0, hp 2]
  have hp2 : _root_.GD.N0232.N0719.N1018.d010013 triangle s 2 ≤ 1 := by
    linarith [hp 0, hp 1]
  let x₀ := _root_.GD.N0232.N0719.N1018.d010014 triangle s 0 - target
  let x₁ := _root_.GD.N0232.N0719.N1018.d010014 triangle s 1 - target
  let x₂ := _root_.GD.N0232.N0719.N1018.d010014 triangle s 2 - target
  have h01 : (x₀ - x₁) ^ 2 ≤ 2 * (x₀ ^ 2 + x₁ ^ 2) := by
    nlinarith [sq_nonneg (x₀ + x₁)]
  have h02 : (x₀ - x₂) ^ 2 ≤ 2 * (x₀ ^ 2 + x₂ ^ 2) := by
    nlinarith [sq_nonneg (x₀ + x₂)]
  have h12 : (x₁ - x₂) ^ 2 ≤ 2 * (x₁ ^ 2 + x₂ ^ 2) := by
    nlinarith [sq_nonneg (x₁ + x₂)]
  have hp01 :
      _root_.GD.N0232.N0719.N1018.d010013 triangle s 0 *
          _root_.GD.N0232.N0719.N1018.d010013 triangle s 1 ≤ 1 := by
    nlinarith [hp 0, hp 1]
  have hp02 :
      _root_.GD.N0232.N0719.N1018.d010013 triangle s 0 *
          _root_.GD.N0232.N0719.N1018.d010013 triangle s 2 ≤ 1 := by
    nlinarith [hp 0, hp 2]
  have hp12 :
      _root_.GD.N0232.N0719.N1018.d010013 triangle s 1 *
          _root_.GD.N0232.N0719.N1018.d010013 triangle s 2 ≤ 1 := by
    nlinarith [hp 1, hp 2]
  have hpair :
      _root_.GD.N0232.N0719.N1018.d010017 triangle s ≤
        4 * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2) := by
    rw [_root_.GD.N0232.N0719.N1020.d010265,
      _root_.GD.N0232.N0719.N1019.d003795 hsum]
    dsimp [_root_.GD.N0232.N0719.N1018.d010014, x₀, x₁, x₂]
    have hterm01 :
        _root_.GD.N0232.N0719.N1018.d010013 triangle s 0 *
              _root_.GD.N0232.N0719.N1018.d010013 triangle s 1 *
              ((s.mean (triangle 0) - target) -
                (s.mean (triangle 1) - target)) ^ 2 ≤
            ((s.mean (triangle 0) - target) -
              (s.mean (triangle 1) - target)) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) hp01
    have hterm02 :
        _root_.GD.N0232.N0719.N1018.d010013 triangle s 0 *
              _root_.GD.N0232.N0719.N1018.d010013 triangle s 2 *
              ((s.mean (triangle 0) - target) -
                (s.mean (triangle 2) - target)) ^ 2 ≤
            ((s.mean (triangle 0) - target) -
              (s.mean (triangle 2) - target)) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) hp02
    have hterm12 :
        _root_.GD.N0232.N0719.N1018.d010013 triangle s 1 *
              _root_.GD.N0232.N0719.N1018.d010013 triangle s 2 *
              ((s.mean (triangle 1) - target) -
                (s.mean (triangle 2) - target)) ^ 2 ≤
            ((s.mean (triangle 1) - target) -
              (s.mean (triangle 2) - target)) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) hp12
    dsimp [x₀, x₁, x₂] at h01 h02 h12
    unfold _root_.GD.N0232.N0719.N1018.d010014 at h01 h02 h12
    have hdiff01 :
        s.mean (triangle 0) - s.mean (triangle 1) =
          (s.mean (triangle 0) - target) -
            (s.mean (triangle 1) - target) := by ring
    have hdiff02 :
        s.mean (triangle 0) - s.mean (triangle 2) =
          (s.mean (triangle 0) - target) -
            (s.mean (triangle 2) - target) := by ring
    have hdiff12 :
        s.mean (triangle 1) - s.mean (triangle 2) =
          (s.mean (triangle 1) - target) -
            (s.mean (triangle 2) - target) := by ring
    rw [hdiff01, hdiff02, hdiff12]
    linarith
  have hl1sq :
      x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 ≤
        (|x₀| + |x₁| + |x₂|) ^ 2 := by
    nlinarith [sq_abs x₀, sq_abs x₁, sq_abs x₂,
      abs_nonneg x₀, abs_nonneg x₁, abs_nonneg x₂]
  calc
    _root_.GD.N0232.N0719.N1018.d010017 triangle s ≤
        4 * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2) := hpair
    _ ≤ 4 * (|x₀| + |x₁| + |x₂|) ^ 2 :=
      mul_le_mul_of_nonneg_left hl1sq (by norm_num)
    _ =
        4 *
          (∑ j : Fin 3,
            |_root_.GD.N0232.N0719.N1018.d010014 triangle s j - target|) ^ 2 := by
      rw [Fin.sum_univ_three]






theorem d010283
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (target : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hvar : ∀ i, 0 < s.meanVariance i) :
    |_root_.GD.N0232.N0719.N1018.d010021 triangle s| ≤
      3000 * _root_.GD.N0232.N0719.N0910.d010278 target s.mean := by
  have hcorr :=
    _root_.GD.N0232.N0719.N1020.d010268 hk triangle s hvar
  have hdisp :=
    _root_.GD.N0232.N0719.N0910.d010282
      hk triangle target s hvar
  have hselected_le :
      (∑ j : Fin 3,
          |_root_.GD.N0232.N0719.N1018.d010014 triangle s j - target|) ≤
        _root_.GD.N0232.N0719.N0910.d010278 target s.mean := by
    unfold _root_.GD.N0232.N0719.N0910.d010278 _root_.GD.N0232.N0719.N1018.d010014
    calc
      (∑ j : Fin 3, |s.mean (triangle j) - target|) =
          ∑ i ∈ Finset.univ.image triangle, |s.mean i - target| := by
            rw [Finset.sum_image triangle.injective.injOn]
      _ ≤ ∑ i, |s.mean i - target| :=
        Finset.sum_le_univ_sum_of_nonneg (fun i => abs_nonneg _)
  have hselected_sq :
      (∑ j : Fin 3,
          |_root_.GD.N0232.N0719.N1018.d010014 triangle s j - target|) ^ 2 ≤
        _root_.GD.N0232.N0719.N0910.d010278 target s.mean ^ 2 := by
    have hselected_nonneg :
        0 ≤ ∑ j : Fin 3,
          |_root_.GD.N0232.N0719.N1018.d010014 triangle s j - target| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hfull_nonneg := _root_.GD.N0232.N0719.N0910.d010279 target s.mean
    nlinarith
  have hdisp' :
      _root_.GD.N0232.N0719.N1018.d010017 triangle s ≤
        4 * _root_.GD.N0232.N0719.N0910.d010278 target s.mean ^ 2 :=
    hdisp.trans (mul_le_mul_of_nonneg_left hselected_sq (by norm_num))
  have hsq :
      _root_.GD.N0232.N0719.N1018.d010021 triangle s ^ 2 ≤
        (3000 * _root_.GD.N0232.N0719.N0910.d010278 target s.mean) ^ 2 := by
    calc
      _root_.GD.N0232.N0719.N1018.d010021 triangle s ^ 2 ≤
          2250000 * _root_.GD.N0232.N0719.N1018.d010017 triangle s := hcorr
      _ ≤ 2250000 *
          (4 * _root_.GD.N0232.N0719.N0910.d010278 target s.mean ^ 2) :=
        mul_le_mul_of_nonneg_left hdisp' (by norm_num)
      _ = (3000 * _root_.GD.N0232.N0719.N0910.d010278 target s.mean) ^ 2 := by ring
  have hrhs :
      0 ≤ 3000 * _root_.GD.N0232.N0719.N0910.d010278 target s.mean :=
    mul_nonneg (by norm_num) (_root_.GD.N0232.N0719.N0910.d010279 target s.mean)
  nlinarith [sq_abs (_root_.GD.N0232.N0719.N1018.d010021 triangle s),
    sq_nonneg (|_root_.GD.N0232.N0719.N1018.d010021 triangle s| -
      3000 * _root_.GD.N0232.N0719.N0910.d010278 target s.mean)]



theorem d010284
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∀ᵐ x ∂gammaMeasure a r, 0 ≤ x := by
  rw [gammaMeasure]
  refine (ae_withDensity_iff
    ( μ := volume)
    ((measurable_gammaPDFReal a r).ennreal_ofReal)).2 ?_
  filter_upwards with x
  intro hpdf
  by_contra hx
  have hxneg : x < 0 := lt_of_not_ge hx
  exact hpdf (gammaPDF_of_neg hxneg)

theorem d010285
    (a r : ℝ) :
    ∀ᵐ x ∂gammaMeasure a r, x ≠ 0 := by
  rw [gammaMeasure]
  exact (withDensity_absolutelyContinuous volume (gammaPDF a r)).ae_le
    (MeasureTheory.volume.ae_ne 0)

theorem d010286
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  filter_upwards [_root_.GD.N0232.N0719.N0910.d010284 ha hr,
    _root_.GD.N0232.N0719.N0910.d010285 a r] with x hx hx0
  exact lt_of_le_of_ne hx (Ne.symm hx0)

theorem d010287
    {k : ℕ} {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i) :
    ∀ᵐ t ∂_root_.GD.N0232.N0719.N0954.d009342 shape rate,
      ∀ i, 0 < t i := by
  letI (i : Fin k) :
      IsProbabilityMeasure (gammaMeasure (shape i) (rate i)) :=
    isProbabilityMeasure_gammaMeasure (hshape i) (hrate i)
  apply ae_all_iff.2
  intro i
  exact
    (measurePreserving_eval
      (fun i => gammaMeasure (shape i) (rate i)) i).quasiMeasurePreserving.ae
      (_root_.GD.N0232.N0719.N0910.d010286 (hshape i) (hrate i))

theorem d010288
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    {scales : Fin k → ℝ}
    (hscales : ∀ i, 0 < scales i) :
    ∀ᵐ t ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes scales,
      ∀ i, 0 < t i := by
  rw [_root_.GD.N0232.N0719.N0954.d009362
    sizes hsizes scales hscales]
  exact _root_.GD.N0232.N0719.N0910.d010287
    (fun i => _root_.GD.N0232.N0719.N0954.d009358 hsizes i)
    (fun i => _root_.GD.N0232.N0719.N0954.d009360 hsizes hscales i)





theorem d010289
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) :
    IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) := by
  unfold _root_.GD.N0232.N0719.N0933.d009301
  letI (i : Fin k) :
      IsProbabilityMeasure
        (_root_.GD.N0232.N0719.N0933.d009289 (sizes i) (scales i)) := by
    have hshapeNat : 0 < sizes i - 1 := by
      have := hsizes i
      omega
    have hshapeReal :
        0 < (((sizes i - 1 : ℕ) : ℝ) / 2) := by
      have : 0 < ((sizes i - 1 : ℕ) : ℝ) := by
        exact_mod_cast hshapeNat
      positivity
    unfold _root_.GD.N0232.N0719.N0933.d009289
    letI :
        IsProbabilityMeasure
          (gammaMeasure (((sizes i - 1 : ℕ) : ℝ) / 2)
            (((sizes i - 1 : ℕ) : ℝ) / 2)) :=
      isProbabilityMeasure_gammaMeasure hshapeReal hshapeReal
    exact Measure.isProbabilityMeasure_map
      (_root_.GD.N0232.N0719.N0933.d009294
        (sizes i) (scales i)).aemeasurable
  infer_instance



theorem d010290
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ)
    (i : Fin k) :
    MemLp
      (fun y : Fin k → ℝ => y i - location)
      2 (_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales) := by
  rw [_root_.GD.N0232.N0719.N0933.d009302
    k sizes hsizes location scales]
  let variance : Fin k → ℝ≥0 :=
    fun j =>
      .mk (scales j ^ 2 / (sizes j : ℝ))
        (div_nonneg (sq_nonneg (scales j))
          (Nat.cast_nonneg (sizes j)))
  have hi :
      MemLp (fun x : ℝ => x - location) 2
        (gaussianReal location (variance i)) := by
    exact
      (memLp_id_gaussianReal
        (μ := location) (v := variance i) 2).sub
          (memLp_const location)
  simpa [variance, Function.comp_def] using
    hi.comp_measurePreserving
      (measurePreserving_eval
        (fun j => gaussianReal location (variance j)) i)

theorem d010291
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    MemLp
      (_root_.GD.N0232.N0719.N0910.d010278 (k := k) location)
      2 (_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales) := by
  unfold _root_.GD.N0232.N0719.N0910.d010278
  exact
    memLp_finsetSum Finset.univ fun i _ =>
      (_root_.GD.N0232.N0719.N0910.d010290
        sizes hsizes location scales i).norm

theorem d010292
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    MemLp
      (fun z : (Fin k → ℝ) × (Fin k → ℝ) =>
        _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0933.d009305 k z) - location)
      2
      ((_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales).prod
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales)) := by
  letI :
      IsProbabilityMeasure
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hsizes scales
  have hmajorant :=
    (_root_.GD.N0232.N0719.N0910.d010291
      sizes hsizes location scales).comp_fst
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales)
  apply hmajorant.mono'
  · exact
      ((_root_.GD.N0232.N0719.N0900.d009121.comp
        (_root_.GD.N0232.N0719.N0933.d009306 k)).sub
          measurable_const).aestronglyMeasurable
  · filter_upwards with z
    simpa [_root_.GD.N0232.N0719.N0933.d009305, Real.norm_eq_abs] using
      _root_.GD.N0232.N0719.N0910.d010281
        hk location (_root_.GD.N0232.N0719.N0933.d009305 k z)

theorem d010293
    {k : ℕ} (hk : 0 < k)
    (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ)
    (hscales : ∀ i, 0 < scales i)
    (triangle : Fin 3 ↪ Fin k) :
    MemLp
      (fun z : (Fin k → ℝ) × (Fin k → ℝ) =>
        _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0933.d009305 k z))
      2
      ((_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales).prod
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales)) := by
  letI :
      IsProbabilityMeasure
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hsizes scales
  have hmajorant :=
    ((_root_.GD.N0232.N0719.N0910.d010291
      sizes hsizes location scales).const_mul 3000).comp_fst
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales)
  apply hmajorant.mono'
  · exact
      (_root_.GD.N0232.N0719.N1018.d010044 triangle).comp
        (_root_.GD.N0232.N0719.N0933.d009306 k) |>.aestronglyMeasurable
  · have hpos :=
      (Measure.quasiMeasurePreserving_snd
        (μ := _root_.GD.N0232.N0719.N0933.d009300 k sizes location scales)
        (ν := _root_.GD.N0232.N0719.N0933.d009301 k sizes scales)).ae
        (_root_.GD.N0232.N0719.N0910.d010288 hsizes hscales)
    filter_upwards [hpos] with z hz
    simpa [_root_.GD.N0232.N0719.N0933.d009305, Real.norm_eq_abs] using
      _root_.GD.N0232.N0719.N0910.d010283
        hk triangle location (_root_.GD.N0232.N0719.N0933.d009305 k z) hz



theorem d010294
    {k : ℕ} (sizes : Fin k → ℕ)
    (hk : 0 < k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    MemLp
      (fun x =>
        _root_.GD.N0232.N0719.N0900.d009111 k sizes x - location)
      2 (_root_.GD.N0232.N0719.d009176 k sizes location scales) := by
  let split := _root_.GD.N0232.N0719.N0933.d009304 k sizes
  let productLaw :=
    (_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales).prod
      (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales)
  have hmp :
      MeasurePreserving split
        (_root_.GD.N0232.N0719.d009176 k sizes location scales)
        productLaw := by
    refine ⟨_root_.GD.N0232.N0719.N0933.d009308 k sizes, ?_⟩
    exact _root_.GD.N0232.N0719.N0933.d009309
      k sizes hsizes location scales
  have h :=
    (_root_.GD.N0232.N0719.N0910.d010292
      hk sizes hsizes location scales).comp_measurePreserving hmp
  simpa [split, productLaw, _root_.GD.N0232.N0719.N0900.d009111, Function.comp_def,
    _root_.GD.N0232.N0719.N0933.d009307] using h



theorem d010295
    {k : ℕ} (sizes : Fin k → ℕ)
    (hk : 0 < k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ)
    (hscales : ∀ i, 0 < scales i)
    (triangle : Fin 3 ↪ Fin k) :
    MemLp
      (_root_.GD.N0232.N0719.N1015.d010079 triangle)
      2 (_root_.GD.N0232.N0719.d009176 k sizes location scales) := by
  let split := _root_.GD.N0232.N0719.N0933.d009304 k sizes
  let productLaw :=
    (_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales).prod
      (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales)
  have hmp :
      MeasurePreserving split
        (_root_.GD.N0232.N0719.d009176 k sizes location scales)
        productLaw := by
    refine ⟨_root_.GD.N0232.N0719.N0933.d009308 k sizes, ?_⟩
    exact _root_.GD.N0232.N0719.N0933.d009309
      k sizes hsizes location scales
  have h :=
    (_root_.GD.N0232.N0719.N0910.d010293
      hk sizes hsizes location scales hscales triangle).comp_measurePreserving hmp
  change MemLp
    (fun x : _root_.GD.N0232.N0719.N0900.d009094 k sizes =>
      _root_.GD.N0232.N0719.N1018.d010021 triangle
        (_root_.GD.N0232.N0719.N0900.d009104 k sizes x))
    2 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
  simpa [split, productLaw, Function.comp_def,
    _root_.GD.N0232.N0719.N0933.d009307] using h



theorem d010296
    {k : ℕ} (sizes : Fin k → ℕ)
    (hk : 0 < k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ)
    (hscales : ∀ i, 0 < scales i)
    (triangle : Fin 3 ↪ Fin k) :
    Integrable
      (fun x =>
        _root_.GD.N0232.N0719.N1015.d010078 location x *
          _root_.GD.N0232.N0719.N1015.d010079 triangle x)
      (_root_.GD.N0232.N0719.d009176 k sizes location scales) := by
  exact
    (_root_.GD.N0232.N0719.N0910.d010294
      sizes hk hsizes location scales).integrable_mul
      (_root_.GD.N0232.N0719.N0910.d010295
        sizes hk hsizes location scales hscales triangle)



theorem d010297
    {k : ℕ} (sizes : Fin k → ℕ)
    (hk : 0 < k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ)
    (hscales : ∀ i, 0 < scales i)
    (triangle : Fin 3 ↪ Fin k) (ε : ℝ) :
    MemLp
      (fun x =>
        _root_.GD.N0232.N0719.N1018.d010023 k sizes triangle ε x - location)
      2 (_root_.GD.N0232.N0719.d009176 k sizes location scales) := by
  have hbase :=
    _root_.GD.N0232.N0719.N0910.d010294 sizes hk hsizes location scales
  have hcorr :=
    (_root_.GD.N0232.N0719.N0910.d010295
      sizes hk hsizes location scales hscales triangle).const_mul ε
  apply (memLp_congr_ae ?_).2 (hbase.add hcorr)
  filter_upwards with x
  unfold _root_.GD.N0232.N0719.N1018.d010023 _root_.GD.N0232.N0719.N1018.d010022
    _root_.GD.N0232.N0719.N1015.d010079 _root_.GD.N0232.N0719.N0900.d009111
  change
    _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0900.d009104 k sizes x) +
          ε * _root_.GD.N0232.N0719.N1018.d010021 triangle
            (_root_.GD.N0232.N0719.N0900.d009104 k sizes x) - location =
      (_root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0900.d009104 k sizes x) - location) +
        ε * _root_.GD.N0232.N0719.N1018.d010021 triangle
          (_root_.GD.N0232.N0719.N0900.d009104 k sizes x)
  ring

end

end GD.N0232.N0719.N0910
