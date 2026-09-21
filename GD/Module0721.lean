import GD.Module0704
import GD.Module0652
import GD.Module0715
import GD.Module0716
import GD.Module0719






















open MeasureTheory Set
open scoped BigOperators NNReal

namespace GD.N0232.N0719.N0912

noncomputable section





local instance (p : Prop) : Decidable p := Classical.propDecidable p




def d010745
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (variance : Fin k → ℝ) : ℝ :=
  max (variance (triangle 0))
    (max (variance (triangle 1)) (variance (triangle 2)))


def d010746
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (variance : Fin k → ℝ) (j : Fin 3) : ℝ :=
  variance (triangle j) / _root_.GD.N0232.N0719.N0912.d010745 triangle variance

theorem d010747
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    {variance : Fin k → ℝ}
    (hvariance : ∀ i, 0 < variance i) :
    0 < _root_.GD.N0232.N0719.N0912.d010745 triangle variance := by
  unfold _root_.GD.N0232.N0719.N0912.d010745
  exact lt_of_lt_of_le (hvariance (triangle 0)) (le_max_left _ _)

theorem d010748
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (variance : Fin k → ℝ) (j : Fin 3) :
    variance (triangle j) ≤ _root_.GD.N0232.N0719.N0912.d010745 triangle variance := by
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_right _ _)

theorem d010749
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    {variance : Fin k → ℝ}
    (hvariance : ∀ i, 0 < variance i) :
    _root_.GD.N0232.N0719.N0912.d010746 triangle variance ∈
      _root_.GD.N0232.N0719.N0856.d009532 := by
  let V₀ := _root_.GD.N0232.N0719.N0912.d010745 triangle variance
  have hV₀ : 0 < V₀ := _root_.GD.N0232.N0719.N0912.d010747 triangle hvariance
  constructor
  · intro j
    constructor
    · exact div_nonneg (hvariance (triangle j)).le hV₀.le
    · exact (div_le_one hV₀).2
        (_root_.GD.N0232.N0719.N0912.d010748 triangle variance j)
  · dsimp [_root_.GD.N0232.N0719.N0912.d010746, V₀]
    unfold _root_.GD.N0232.N0719.N0912.d010745 at hV₀ ⊢
    rcases le_total
        (variance (triangle 1)) (variance (triangle 2)) with h12 | h21
    · have hm12 :
          max (variance (triangle 1)) (variance (triangle 2)) =
            variance (triangle 2) :=
        max_eq_right h12
      rw [hm12]
      rcases le_total
          (variance (triangle 0)) (variance (triangle 2)) with h02 | h20
      · exact Or.inr (Or.inr
          (by rw [max_eq_right h02, div_self
            (hvariance (triangle 2)).ne']))
      · exact Or.inl
          (by rw [max_eq_left h20, div_self
            (hvariance (triangle 0)).ne'])
    · have hm21 :
          max (variance (triangle 1)) (variance (triangle 2)) =
            variance (triangle 1) :=
        max_eq_left h21
      rw [hm21]
      rcases le_total
          (variance (triangle 0)) (variance (triangle 1)) with h01 | h10
      · exact Or.inr (Or.inl
          (by rw [max_eq_right h01, div_self
            (hvariance (triangle 1)).ne']))
      · exact Or.inl
          (by rw [max_eq_left h10, div_self
            (hvariance (triangle 0)).ne'])

theorem d010750
    {k : ℕ} (sizes : Fin k → ℕ)
    (scales : Fin k → ℝ) (i : Fin k) :
    _root_.GD.N0232.N0719.N0954.d009356 sizes scales i =
      (_root_.GD.N0232.N0719.N0902.d010372 sizes scales i : ℝ) := by
  rfl

theorem d010751
    {k : ℕ} (sizes : Fin k → ℕ)
    (scales : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0954.d009357 sizes scales =
      _root_.GD.N0232.N0719.N0960.d009692
        (_root_.GD.N0232.N0719.N0954.d009355 sizes)
        (_root_.GD.N0232.N0719.N0954.d009356 sizes scales) := by
  rfl




theorem d010752
    {k : ℕ} (hk : 0 < k)
    (t : Fin k → ℝ) :
    ∑ i, _root_.GD.N0232.N0719.N0954.d009349 hk t i = 1 := by
  let e := _root_.GD.N0232.N0719.N0954.d009344 k hk
  rw [show
      (∑ i : Fin k, _root_.GD.N0232.N0719.N0954.d009349 hk t i) =
        ∑ j : _root_.GD.N0232.N0719.N0953.d003305 (k - 1),
          _root_.GD.N0232.N0719.N0954.d009349 hk t (e j) by
    symm
    exact Fintype.sum_equiv e _ _ fun _ => rfl]
  simpa [_root_.GD.N0232.N0719.N0954.d009349, e] using
    _root_.GD.N0232.N0719.N0953.d003335 (_root_.GD.N0232.N0719.N0954.d009347 hk t)



theorem d010753
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0954.d009349 hk t) ≤ 1 := by
  exact _root_.GD.N0232.N0719.N0904.d010387 hk triangle t ht





theorem d010754
    {k : ℕ} (hk3 : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.N1024.d010713 k sizes hk3 scales =
      ∫ t,
        ∫ y,
          _root_.GD.N0232.N0719.N1018.d010021 (_root_.GD.N0232.N0719.N1024.d010710 hk3)
              (_root_.GD.N0232.N0719.N0902.d010367 t y) ^ 2
            ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales
        ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes scales := by
  let triangle := _root_.GD.N0232.N0719.N1024.d010710 hk3
  have hk : 0 < k := by omega
  have hprod :=
    (_root_.GD.N0232.N0719.N0910.d010293
      hk sizes hsizes 0 scales hscales triangle).integrable_sq
  letI :
      ∀ i : Fin k,
        IsProbabilityMeasure
          (ProbabilityTheory.gammaMeasure
            (_root_.GD.N0232.N0719.N0954.d009355 sizes i)
            (_root_.GD.N0232.N0719.N0954.d009357 sizes scales i)) :=
    fun i =>
      ProbabilityTheory.isProbabilityMeasure_gammaMeasure
        (_root_.GD.N0232.N0719.N0954.d009358 hsizes i)
        (_root_.GD.N0232.N0719.N0954.d009360 hsizes hscales i)
  letI :
      IsProbabilityMeasure
        (_root_.GD.N0232.N0719.N0954.d009342
          (_root_.GD.N0232.N0719.N0954.d009355 sizes)
          (_root_.GD.N0232.N0719.N0954.d009357 sizes scales)) := by
    unfold _root_.GD.N0232.N0719.N0954.d009342
    infer_instance
  letI :
      IsProbabilityMeasure
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) := by
    rw [_root_.GD.N0232.N0719.N0954.d009362
      sizes hsizes scales hscales]
    infer_instance
  letI :
      IsProbabilityMeasure
        (_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) := by
    unfold _root_.GD.N0232.N0719.N0933.d009300
    infer_instance
  unfold _root_.GD.N0232.N0719.N1024.d010713 _root_.GD.N0232.N0719.N1024.d010711
    _root_.GD.N0232.N0719.N1015.d010081
    _root_.GD.N0232.N0719.N1015.d010079
  rw [_root_.GD.N0232.N0719.N0933.d009310
    k sizes hsizes 0 scales
    (fun s => _root_.GD.N0232.N0719.N1018.d010021 triangle s ^ 2)
    ((_root_.GD.N0232.N0719.N1018.d010044 triangle).pow_const 2)]
  change
    (∫ z,
        _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0933.d009305 k z) ^ 2
      ∂((_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales).prod
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales))) =
      _
  exact integral_prod_symm _ hprod



theorem d010755
    {k : ℕ} (hk3 : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.N1024.d010712 k sizes hk3 scales =
      ∫ t,
        ∫ y,
          _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
            _root_.GD.N0232.N0719.N1018.d010021 (_root_.GD.N0232.N0719.N1024.d010710 hk3)
              (_root_.GD.N0232.N0719.N0902.d010367 t y)
            ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales
        ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes scales := by
  let triangle := _root_.GD.N0232.N0719.N1024.d010710 hk3
  have hk : 0 < k := by omega
  have hprod :=
    (_root_.GD.N0232.N0719.N0910.d010292
      hk sizes hsizes 0 scales).integrable_mul
      (_root_.GD.N0232.N0719.N0910.d010293
        hk sizes hsizes 0 scales hscales triangle)
  letI :
      ∀ i : Fin k,
        IsProbabilityMeasure
          (ProbabilityTheory.gammaMeasure
            (_root_.GD.N0232.N0719.N0954.d009355 sizes i)
            (_root_.GD.N0232.N0719.N0954.d009357 sizes scales i)) :=
    fun i =>
      ProbabilityTheory.isProbabilityMeasure_gammaMeasure
        (_root_.GD.N0232.N0719.N0954.d009358 hsizes i)
        (_root_.GD.N0232.N0719.N0954.d009360 hsizes hscales i)
  letI :
      IsProbabilityMeasure
        (_root_.GD.N0232.N0719.N0954.d009342
          (_root_.GD.N0232.N0719.N0954.d009355 sizes)
          (_root_.GD.N0232.N0719.N0954.d009357 sizes scales)) := by
    unfold _root_.GD.N0232.N0719.N0954.d009342
    infer_instance
  letI :
      IsProbabilityMeasure
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) := by
    rw [_root_.GD.N0232.N0719.N0954.d009362
      sizes hsizes scales hscales]
    infer_instance
  letI :
      IsProbabilityMeasure
        (_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) := by
    unfold _root_.GD.N0232.N0719.N0933.d009300
    infer_instance
  unfold _root_.GD.N0232.N0719.N1024.d010712 _root_.GD.N0232.N0719.N1024.d010711
    _root_.GD.N0232.N0719.N1015.d010080
    _root_.GD.N0232.N0719.N1015.d010078
    _root_.GD.N0232.N0719.N1015.d010079
    _root_.GD.N0232.N0719.N0900.d009111
  rw [_root_.GD.N0232.N0719.N0933.d009310
    k sizes hsizes 0 scales
    (fun s => (_root_.GD.N0232.N0719.N0900.d009110 s - 0) * _root_.GD.N0232.N0719.N1018.d010021 triangle s)
    (((_root_.GD.N0232.N0719.N0900.d009121.sub measurable_const).mul
      (_root_.GD.N0232.N0719.N1018.d010044 triangle)))]
  simp only [sub_zero]
  change
    (∫ z,
        _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0933.d009305 k z) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0933.d009305 k z)
      ∂((_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales).prod
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales))) =
      _
  have hfun :
      ((fun z =>
          _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0933.d009305 k z) - 0) *
        fun z => _root_.GD.N0232.N0719.N1018.d010021 triangle
          (_root_.GD.N0232.N0719.N0933.d009305 k z)) =
        (fun z =>
          _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0933.d009305 k z) *
            _root_.GD.N0232.N0719.N1018.d010021 triangle
              (_root_.GD.N0232.N0719.N0933.d009305 k z)) := by
    funext z
    simp
  rw [hfun] at hprod
  exact integral_prod_symm _ hprod




def d010756
    {k : ℕ} (hk : 0 < k)
    (x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1)) (i : Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N0953.d003334 x ((_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i)



def d010757
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (V₀ : ℝ)
    (x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1)) : ℝ :=
  (if _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0912.d010756 hk x) then 1 else 0) *
    250000 *
    _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) ^ 2 * V₀



def d010758
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) (V₀ : ℝ)
    (x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1)) : ℝ :=
  (if _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0912.d010756 hk x) then 1 else 0) *
    (_root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) ^ 2 *
      _root_.GD.N0232.N0719.N0856.d009528 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) w /
      (_root_.GD.N0232.N0719.N0953.d003308 x + V₀))

theorem d010759
    {k : ℕ} (hk : 0 < k)
    (t : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0912.d010756 hk (_root_.GD.N0232.N0719.N0954.d009347 hk t) =
      _root_.GD.N0232.N0719.N0954.d009349 hk t := by
  rfl

theorem d010760
    {k : ℕ} (hk : 0 < k)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k)
    (ω : ℝ) :
    _root_.GD.N0232.N0719.N0912.d010756 hk (_root_.GD.N0232.N0719.N0955.d009612 q ω) =
      _root_.GD.N0232.N0719.N0853.d009567 hk q := by
  funext i
  exact _root_.GD.N0232.N0719.N0955.d009616 hk q ω i

@[fun_prop]
theorem d010761
    {k : ℕ} (hk : 0 < k) (i : Fin k) :
    Measurable (fun x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) =>
      _root_.GD.N0232.N0719.N0912.d010756 hk x i) := by
  unfold _root_.GD.N0232.N0719.N0912.d010756
  generalize hindex : (_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i = j
  cases j with
  | inl j =>
      simp [_root_.GD.N0232.N0719.N0953.d003334,
        _root_.GD.N0232.N0719.N0953.d003307]
      fun_prop
  | inr j =>
      simp [_root_.GD.N0232.N0719.N0953.d003334,
        _root_.GD.N0232.N0719.N0953.d003309,
        _root_.GD.N0232.N0719.N0953.d003307]
      fun_prop

@[fun_prop]
theorem d010762
    {k : ℕ} (hk : 0 < k) (triangle : Fin 3 ↪ Fin k) :
    Measurable (fun x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) =>
      _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x)) := by
  unfold _root_.GD.N0232.N0719.N0951.d003585
  fun_prop

@[fun_prop]
theorem d010763
    {k : ℕ} (hk : 0 < k) (triangle : Fin 3 ↪ Fin k) (j : Fin 3) :
    Measurable (fun x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) =>
      _root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) j) := by
  unfold _root_.GD.N0232.N0719.N0951.d003586
  fun_prop

@[fun_prop]
theorem d010764
    {k : ℕ} (hk : 0 < k) (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) :
    Measurable (fun x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) =>
      _root_.GD.N0232.N0719.N0856.d009528 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) w) := by
  unfold _root_.GD.N0232.N0719.N0856.d009528 _root_.GD.N0232.N0719.N1016.d003608
  fun_prop

@[fun_prop]
theorem d010765
    {k : ℕ} (hk : 0 < k) :
    Measurable (_root_.GD.N0232.N0719.N0954.d009347 hk) := by
  apply measurable_pi_lambda
  intro i
  cases i with
  | inl i =>
      simp [_root_.GD.N0232.N0719.N0954.d009347,
        _root_.GD.N0232.N0719.N0953.d003314,
        _root_.GD.N0232.N0719.N0953.d003313,
        _root_.GD.N0232.N0719.N0953.d003312,
        _root_.GD.N0232.N0719.N0956.d010060]
      fun_prop
  | inr i =>
      simp [_root_.GD.N0232.N0719.N0954.d009347,
        _root_.GD.N0232.N0719.N0953.d003314,
        _root_.GD.N0232.N0719.N0953.d003313,
        _root_.GD.N0232.N0719.N0953.d003312,
        _root_.GD.N0232.N0719.N0956.d010060]
      fun_prop

theorem d010766
    {k : ℕ} (hk : 0 < k) :
    MeasurableSet
      {x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) |
        _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0912.d010756 hk x)} := by
  rw [show
      {x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) |
          _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0912.d010756 hk x)} =
        ⋂ i : Fin k,
          {x | _root_.GD.N0232.N0719.N0951.d003578 k ≤ _root_.GD.N0232.N0719.N0912.d010756 hk x i} ∩
          {x | _root_.GD.N0232.N0719.N0912.d010756 hk x i ≤ _root_.GD.N0232.N0719.N0951.d003579 k} by
    ext x
    simp [_root_.GD.N0232.N0719.N0951.d003580]]
  exact MeasurableSet.iInter fun i => by
    have hi : Measurable (fun x => _root_.GD.N0232.N0719.N0912.d010756 hk x i) :=
      _root_.GD.N0232.N0719.N0912.d010761 hk i
    exact
      (measurableSet_le measurable_const hi).inter
        (measurableSet_le hi measurable_const)

@[fun_prop]
theorem d010767
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (V₀ : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀) := by
  unfold _root_.GD.N0232.N0719.N0912.d010757
  have hindicator :
      Measurable (fun x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) =>
        if _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0912.d010756 hk x) then
          (1 : ℝ)
        else 0) :=
    Measurable.ite (_root_.GD.N0232.N0719.N0912.d010766 hk)
      measurable_const measurable_const
  exact (((hindicator.mul measurable_const).mul
    ((_root_.GD.N0232.N0719.N0912.d010762 hk triangle).pow_const 2)).mul measurable_const)

@[fun_prop]
theorem d010768
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) (V₀ : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀) := by
  unfold _root_.GD.N0232.N0719.N0912.d010758
  have hindicator :
      Measurable (fun x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) =>
        if _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0912.d010756 hk x) then
          (1 : ℝ)
        else 0) :=
    Measurable.ite (_root_.GD.N0232.N0719.N0912.d010766 hk)
      measurable_const measurable_const
  have hden :
      Measurable (fun x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) =>
        _root_.GD.N0232.N0719.N0953.d003308 x + V₀) := by
    unfold _root_.GD.N0232.N0719.N0953.d003308
    fun_prop
  exact hindicator.mul
    (((_root_.GD.N0232.N0719.N0912.d010762 hk triangle).pow_const 2 |>.mul
      (_root_.GD.N0232.N0719.N0912.d010764 hk triangle w)).div hden)

theorem d010769
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (V₀ : ℝ)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k)
    (ω : ℝ) :
    _root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀ (_root_.GD.N0232.N0719.N0955.d009612 q ω) =
      (if q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk then
        _root_.GD.N0232.N0719.N0914.d010624 hk triangle V₀ q
      else 0) := by
  rw [_root_.GD.N0232.N0719.N0912.d010757, _root_.GD.N0232.N0719.N0912.d010760]
  simp only [_root_.GD.N0232.N0719.N0853.d009581, Set.mem_setOf_eq]
  split_ifs <;> simp [_root_.GD.N0232.N0719.N0914.d010624, _root_.GD.N0232.N0719.N0855.d010601]

theorem d010770
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) (V₀ : ℝ)
    (q : _root_.GD.N0232.N0719.N0857.d009377 k)
    (ω : ℝ) :
    _root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀ (_root_.GD.N0232.N0719.N0955.d009612 q ω) =
      (if q ∈ _root_.GD.N0232.N0719.N0853.d009581 hk then
        _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w / (ω + V₀)
      else 0) := by
  rw [_root_.GD.N0232.N0719.N0912.d010758, _root_.GD.N0232.N0719.N0912.d010760,
    _root_.GD.N0232.N0719.N0955.d009614]
  simp only [_root_.GD.N0232.N0719.N0853.d009581, Set.mem_setOf_eq]
  split_ifs <;>
    simp [_root_.GD.N0232.N0719.N0855.d010602, _root_.GD.N0232.N0719.N0855.d010601,
      _root_.GD.N0232.N0719.N0853.d009591]



theorem d010771
    {k : ℕ} (hk3 : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    let hk : 0 < k := by omega
    let triangle := _root_.GD.N0232.N0719.N1024.d010710 hk3
    let variance := _root_.GD.N0232.N0719.N0954.d009356 sizes scales
    let V₀ := _root_.GD.N0232.N0719.N0912.d010745 triangle variance
    let w := _root_.GD.N0232.N0719.N0912.d010746 triangle variance
    (3 / 128 : ℝ) * _root_.GD.N0232.N0719.N0950.d010587 k * V₀ ^ 2 *
          _root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀
            (_root_.GD.N0232.N0719.N0954.d009347 hk t) ≤
      -(∫ y,
          _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
            _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y)
        ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales) := by
  dsimp only
  let hk : 0 < k := by omega
  let triangle := _root_.GD.N0232.N0719.N1024.d010710 hk3
  let variance := _root_.GD.N0232.N0719.N0954.d009356 sizes scales
  let V₀ := _root_.GD.N0232.N0719.N0912.d010745 triangle variance
  let w := _root_.GD.N0232.N0719.N0912.d010746 triangle variance
  let p := _root_.GD.N0232.N0719.N0954.d009349 hk t
  let r := _root_.GD.N0232.N0719.N0951.d003585 triangle p
  let ω := _root_.GD.N0232.N0719.N0954.d009348 hk t
  have hvariance : ∀ i, 0 < variance i :=
    fun i => _root_.GD.N0232.N0719.N0954.d009359 hsizes hscales i
  have hV₀ : 0 < V₀ :=
    _root_.GD.N0232.N0719.N0912.d010747 triangle hvariance
  have hv :
      ∀ j : Fin 3,
        (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle j) : ℝ) =
          V₀ * w j := by
    intro j
    change variance (triangle j) =
      V₀ * (variance (triangle j) / V₀)
    field_simp [hV₀.ne']
  have hw := _root_.GD.N0232.N0719.N0912.d010749 triangle hvariance
  by_cases hbal : _root_.GD.N0232.N0719.N0951.d003580 p
  · have hfloor :
        _root_.GD.N0232.N0719.N0950.d010587 k ≤ r := by
      simpa [_root_.GD.N0232.N0719.N0950.d010587, r, p] using
        _root_.GD.N0232.N0719.N0951.d003591 hk triangle hbal
    have hmain :=
      _root_.GD.N0232.N0719.N0904.d010389
        hk sizes hsizes scales hscales triangle t ht
        hV₀ (_root_.GD.N0232.N0719.N0950.d010589 hk).le
        hbal hfloor w
        (hv 0) (hv 1) (hv 2)
        (hw.1 0).2 (hw.1 1).2 (hw.1 2).2
    dsimp only at hmain
    rw [_root_.GD.N0232.N0719.N0912.d010758, _root_.GD.N0232.N0719.N0912.d010759,
      if_pos hbal]
    simp only [one_mul]
    change
      (3 / 128 : ℝ) * _root_.GD.N0232.N0719.N0950.d010587 k * V₀ ^ 2 *
          (r ^ 2 *
              _root_.GD.N0232.N0719.N0856.d009528 triangle p w /
            (ω + V₀)) ≤
        -(∫ y,
            _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
              _root_.GD.N0232.N0719.N1018.d010021 triangle
                (_root_.GD.N0232.N0719.N0902.d010367 t y)
          ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales)
    convert hmain using 1 <;> ring
  · have hcross :=
      _root_.GD.N0232.N0719.N0902.d010377
        hk sizes hsizes scales triangle t ht
    dsimp only at hcross
    rw [_root_.GD.N0232.N0719.N0912.d010758, _root_.GD.N0232.N0719.N0912.d010759,
      if_neg hbal]
    rw [hcross, if_neg hbal]
    simp

theorem d010772
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {V₀ : ℝ} (hV₀ : 0 ≤ V₀)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    0 ≤
        _root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀
          (_root_.GD.N0232.N0719.N0954.d009347 hk t) ∧
      _root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀
          (_root_.GD.N0232.N0719.N0954.d009347 hk t) ≤ 250000 * V₀ := by
  have hr :
      _root_.GD.N0232.N0719.N0951.d003585 triangle
          (_root_.GD.N0232.N0719.N0954.d009349 hk t) ≤ 1 :=
    _root_.GD.N0232.N0719.N0912.d010753 hk triangle t ht
  have hr0 :
      0 ≤ _root_.GD.N0232.N0719.N0951.d003585 triangle
          (_root_.GD.N0232.N0719.N0954.d009349 hk t) :=
    (_root_.GD.N0232.N0719.N0956.d010070
      hk triangle (fun _ => 0) t ht).le
  rw [_root_.GD.N0232.N0719.N0912.d010757, _root_.GD.N0232.N0719.N0912.d010759]
  split_ifs with hbal
  · constructor
    · positivity
    · have hrsq :
          _root_.GD.N0232.N0719.N0951.d003585 triangle
                (_root_.GD.N0232.N0719.N0954.d009349 hk t) ^ 2 ≤ 1 := by
        nlinarith [sq_nonneg
          (_root_.GD.N0232.N0719.N0951.d003585 triangle
            (_root_.GD.N0232.N0719.N0954.d009349 hk t))]
      calc
        1 * 250000 *
              _root_.GD.N0232.N0719.N0951.d003585 triangle
                  (_root_.GD.N0232.N0719.N0954.d009349 hk t) ^ 2 * V₀ =
            (250000 * V₀) *
              _root_.GD.N0232.N0719.N0951.d003585 triangle
                  (_root_.GD.N0232.N0719.N0954.d009349 hk t) ^ 2 := by ring
        _ ≤ (250000 * V₀) * 1 :=
          mul_le_mul_of_nonneg_left hrsq (mul_nonneg (by norm_num) hV₀)
        _ = 250000 * V₀ := by ring
  · constructor <;> simp [hV₀]

theorem d010773
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ)
    {V₀ : ℝ} (hV₀ : 0 < V₀)
    (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    0 ≤
      _root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀
        (_root_.GD.N0232.N0719.N0954.d009347 hk t) := by
  unfold _root_.GD.N0232.N0719.N0912.d010758
  rw [_root_.GD.N0232.N0719.N0912.d010759]
  by_cases hbal :
      _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0954.d009349 hk t)
  · rw [if_pos hbal, one_mul]
    exact div_nonneg
      (mul_nonneg (sq_nonneg _)
        (_root_.GD.N0232.N0719.N0856.d009544
          hk triangle hbal w))
      (add_nonneg
        (_root_.GD.N0232.N0719.N0956.d010063 hk t ht).le
        hV₀.le)
  · rw [if_neg hbal]
    simp



theorem d010774
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (triangle : Fin 3 ↪ Fin k) (V₀ : ℝ)
    (hchart :
      IntegrableOn
        (fun x =>
          _root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀ x *
            _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
              (_root_.GD.N0232.N0719.N0954.d009350 hk rate) x)
        (_root_.GD.N0232.N0719.N0953.d003311 (k - 1))) :
    (∫ t,
        _root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀
          (_root_.GD.N0232.N0719.N0954.d009347 hk t)
        ∂_root_.GD.N0232.N0719.N0954.d009342 shape rate) =
      _root_.GD.N0232.N0719.N0954.d009509 shape rate *
        ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
          _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
            _root_.GD.N0232.N0719.N0914.d010624 hk triangle V₀ q := by
  rw [_root_.GD.N0232.N0719.N0955.d009630
    hk hshape hrate _ hchart]
  calc
    (∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
        ∫ ω in Ioi 0,
          _root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀
                (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
            _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
              (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
              (_root_.GD.N0232.N0719.N0955.d009612 q ω)) =
        ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
          ∫ ω in Ioi 0,
            _root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀
                  (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
              _root_.GD.N0232.N0719.N0954.d009483
                (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
                (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
                (_root_.GD.N0232.N0719.N0955.d009612 q ω) := by
      exact setIntegral_eq_of_subset_of_forall_diff_eq_zero
        (_root_.GD.N0232.N0719.N0955.d009608 k)
        (_root_.GD.N0232.N0719.N0955.d009622 hk)
        (fun q hq => by
          have hnot : q ∉ _root_.GD.N0232.N0719.N0853.d009581 hk := hq.2
          apply setIntegral_eq_zero_of_forall_eq_zero
          intro ω hω
          rw [_root_.GD.N0232.N0719.N0912.d010769]
          simp [hnot])
    _ =
        ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
          _root_.GD.N0232.N0719.N0954.d009508
              shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
            _root_.GD.N0232.N0719.N0914.d010624 hk triangle V₀ q := by
      apply setIntegral_congr_fun
        (_root_.GD.N0232.N0719.N0853.d009583 hk).measurableSet
      intro q hq
      change
        (∫ ω in Ioi 0,
            _root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀
                  (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
              _root_.GD.N0232.N0719.N0954.d009483
                (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
                (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
                (_root_.GD.N0232.N0719.N0955.d009612 q ω)) =
          _root_.GD.N0232.N0719.N0954.d009508
              shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
            _root_.GD.N0232.N0719.N0914.d010624 hk triangle V₀ q
      rw [show
          (fun ω =>
            _root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀
                  (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
              _root_.GD.N0232.N0719.N0954.d009483
                (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
                (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
                (_root_.GD.N0232.N0719.N0955.d009612 q ω)) =
            (fun ω =>
              _root_.GD.N0232.N0719.N0954.d009483
                  (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
                  (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
                  (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
                _root_.GD.N0232.N0719.N0914.d010624 hk triangle V₀ q) by
        funext ω
        rw [_root_.GD.N0232.N0719.N0912.d010769]
        simp [hq]
        ring]
      exact
        _root_.GD.N0232.N0719.N0914.d010622
          hk hshape hrate hq
            (_root_.GD.N0232.N0719.N0914.d010624 hk triangle V₀ q)
    _ =
        _root_.GD.N0232.N0719.N0954.d009509 shape rate *
          ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
            _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
              _root_.GD.N0232.N0719.N0914.d010624 hk triangle V₀ q := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun
        (_root_.GD.N0232.N0719.N0853.d009583 hk).measurableSet
      intro q hq
      have hp :
          ∀ i, 0 < _root_.GD.N0232.N0719.N0853.d009567 hk q i :=
        fun i => _root_.GD.N0232.N0719.N0951.d003590 hk hq i
      change
        _root_.GD.N0232.N0719.N0954.d009508
              shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
            _root_.GD.N0232.N0719.N0914.d010624 hk triangle V₀ q =
          _root_.GD.N0232.N0719.N0954.d009509 shape rate *
            (_root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
              _root_.GD.N0232.N0719.N0914.d010624 hk triangle V₀ q)
      rw [_root_.GD.N0232.N0719.N0954.d009515
        hk hshape hrate hp]
      simp [_root_.GD.N0232.N0719.N0855.d010603]
      ring

theorem d010775
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {V₀ : ℝ} (hV₀ : 0 ≤ V₀)
    {x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1)}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 (k - 1)) :
    0 ≤ _root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀ x := by
  unfold _root_.GD.N0232.N0719.N0912.d010757
  split_ifs <;> positivity

theorem d010776
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ)
    {V₀ : ℝ} (hV₀ : 0 < V₀)
    {x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1)}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 (k - 1)) :
    0 ≤ _root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀ x := by
  unfold _root_.GD.N0232.N0719.N0912.d010758
  by_cases hbal : _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0912.d010756 hk x)
  · rw [if_pos hbal, one_mul]
    exact div_nonneg
      (mul_nonneg (sq_nonneg _)
        (_root_.GD.N0232.N0719.N0856.d009544
          hk triangle hbal w))
      (add_nonneg hx.1.le hV₀.le)
  · rw [if_neg hbal]
    simp

theorem d010777
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {p : Fin k → ℝ} (hp : _root_.GD.N0232.N0719.N0951.d003580 p)
    {w : Fin 3 → ℝ}
    (hw : w ∈ _root_.GD.N0232.N0719.N0856.d009532) :
    _root_.GD.N0232.N0719.N0856.d009528 triangle p w ≤ 3 := by
  let q : Fin 3 → ℝ := _root_.GD.N0232.N0719.N0951.d003586 triangle p
  let z : Fin 3 → ℝ := fun j => q j * w j
  have hq0 : ∀ j, 0 ≤ q j :=
    fun j => (_root_.GD.N0232.N0719.N0951.d003596 hk triangle hp j).le
  have hqU : ∀ j, q j ≤ 5 / 9 :=
    fun j => _root_.GD.N0232.N0719.N0951.d003595 hk triangle hp j
  have hz0 : ∀ j, 0 ≤ z j :=
    fun j => mul_nonneg (hq0 j) (hw.1 j).1
  have hzU : ∀ j, z j ≤ 5 / 9 := by
    intro j
    exact (mul_le_of_le_one_right (hq0 j) (hw.1 j).2).trans
      (hqU j)
  have hterm :
      ∀ i j : Fin 3,
        (z i - z j) ^ 2 / (q i + q j) ≤ 1 := by
    intro i j
    have habs :
        |z i - z j| ≤ 5 / 9 := by
      rw [abs_le]
      constructor <;> nlinarith [hz0 i, hz0 j, hzU i, hzU j]
    have hsq :
        (z i - z j) ^ 2 ≤ (5 / 9 : ℝ) ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 habs
    have hden :
        0 < q i + q j :=
      add_pos
        (_root_.GD.N0232.N0719.N0951.d003596 hk triangle hp i)
        (_root_.GD.N0232.N0719.N0951.d003596 hk triangle hp j)
    apply (div_le_one hden).2
    have hqi := _root_.GD.N0232.N0719.N0951.d003594 hk triangle hp i
    have hqj := _root_.GD.N0232.N0719.N0951.d003594 hk triangle hp j
    nlinarith
  unfold _root_.GD.N0232.N0719.N0856.d009528 _root_.GD.N0232.N0719.N1016.d003608
  dsimp [q, z] at hterm ⊢
  nlinarith [hterm 0 1, hterm 0 2, hterm 1 2]

theorem d010778
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {V₀ : ℝ} (hV₀ : 0 ≤ V₀)
    {x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1)}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 (k - 1)) :
    ‖_root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀ x‖ ≤
      250000 * _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V₀ := by
  by_cases hbal : _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0912.d010756 hk x)
  · have hr :=
      _root_.GD.N0232.N0719.N0951.d003592 hk triangle hbal
    have hr0 :=
      _root_.GD.N0232.N0719.N0951.d003593 hk triangle hbal
    have hceil :=
      _root_.GD.N0232.N0719.N0950.d010590 hk
    rw [_root_.GD.N0232.N0719.N0912.d010757, if_pos hbal,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hrsq :
        _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) ^ 2 ≤
          _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 :=
      (sq_le_sq₀ hr0.le hceil.le).2
        (by simpa [_root_.GD.N0232.N0719.N0950.d010588] using hr)
    calc
      1 * 250000 *
            _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) ^ 2 * V₀ =
          (250000 * V₀) *
            _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) ^ 2 := by ring
      _ ≤ (250000 * V₀) *
            _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 :=
        mul_le_mul_of_nonneg_left hrsq (mul_nonneg (by norm_num) hV₀)
      _ = 250000 * _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V₀ := by
        ring
  · rw [_root_.GD.N0232.N0719.N0912.d010757, if_neg hbal]
    simp [hV₀, _root_.GD.N0232.N0719.N0950.d010590 hk]

theorem d010779
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    {w : Fin 3 → ℝ}
    (hw : w ∈ _root_.GD.N0232.N0719.N0856.d009532)
    {V₀ : ℝ} (hV₀ : 0 < V₀)
    {x : _root_.GD.N0232.N0719.N0953.d003306 (k - 1)}
    (hx : x ∈ _root_.GD.N0232.N0719.N0953.d003311 (k - 1)) :
    ‖_root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀ x‖ ≤
      _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * 3 / V₀ := by
  by_cases hbal : _root_.GD.N0232.N0719.N0951.d003580 (_root_.GD.N0232.N0719.N0912.d010756 hk x)
  · have hr :=
      _root_.GD.N0232.N0719.N0951.d003592 hk triangle hbal
    have hr0 :=
      _root_.GD.N0232.N0719.N0951.d003593 hk triangle hbal
    have hceil :=
      _root_.GD.N0232.N0719.N0950.d010590 hk
    have hmismatch :=
      _root_.GD.N0232.N0719.N0912.d010777 hk triangle hbal hw
    have hmismatch0 :=
      _root_.GD.N0232.N0719.N0856.d009544 hk triangle hbal w
    have hden : V₀ ≤ _root_.GD.N0232.N0719.N0953.d003308 x + V₀ := by
      linarith [hx.1]
    rw [_root_.GD.N0232.N0719.N0912.d010758, if_pos hbal, one_mul,
      Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (mul_nonneg (sq_nonneg _) hmismatch0)
          (add_nonneg hx.1.le hV₀.le))]
    have hrsq :
        _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) ^ 2 ≤
          _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 :=
      (sq_le_sq₀ hr0.le hceil.le).2
        (by simpa [_root_.GD.N0232.N0719.N0950.d010588] using hr)
    have hnum :
        _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) ^ 2 *
              _root_.GD.N0232.N0719.N0856.d009528 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) w ≤
            _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * 3 :=
      mul_le_mul hrsq hmismatch hmismatch0
        (sq_nonneg (_root_.GD.N0232.N0719.N0950.d010588 k))
    calc
      _root_.GD.N0232.N0719.N0951.d003585 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) ^ 2 *
              _root_.GD.N0232.N0719.N0856.d009528 triangle (_root_.GD.N0232.N0719.N0912.d010756 hk x) w /
            (_root_.GD.N0232.N0719.N0953.d003308 x + V₀) ≤
          (_root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * 3) /
            (_root_.GD.N0232.N0719.N0953.d003308 x + V₀) :=
        div_le_div_of_nonneg_right hnum
          (add_nonneg hx.1.le hV₀.le)
      _ ≤ (_root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * 3) / V₀ :=
        div_le_div_of_nonneg_left
          (mul_nonneg (sq_nonneg _) (by norm_num))
          hV₀ hden
  · rw [_root_.GD.N0232.N0719.N0912.d010758, if_neg hbal]
    simp only [zero_mul, norm_zero]
    exact div_nonneg
      (mul_nonneg (sq_nonneg _) (by norm_num)) hV₀.le

theorem d010780
    {k : ℕ} (hk : 0 < k)
    {shape variance : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hvariance : ∀ i, 0 < variance i)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) (V₀ : ℝ)
    (hchart :
      IntegrableOn
        (fun x =>
          _root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀ x *
            _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
              (_root_.GD.N0232.N0719.N0954.d009350 hk
                (_root_.GD.N0232.N0719.N0960.d009692 shape variance)) x)
        (_root_.GD.N0232.N0719.N0953.d003311 (k - 1))) :
    (∫ t,
        _root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀
          (_root_.GD.N0232.N0719.N0954.d009347 hk t)
        ∂_root_.GD.N0232.N0719.N0954.d009342 shape
          (_root_.GD.N0232.N0719.N0960.d009692 shape variance)) =
      _root_.GD.N0232.N0719.N0914.d010623
        hk shape variance triangle w V₀ := by
  have hrate :
      ∀ i, 0 < _root_.GD.N0232.N0719.N0960.d009692 shape variance i :=
    _root_.GD.N0232.N0719.N0914.d010619 hshape hvariance
  rw [_root_.GD.N0232.N0719.N0955.d009630
    hk hshape hrate _ hchart]
  unfold _root_.GD.N0232.N0719.N0914.d010623
  calc
    (∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
        ∫ ω in Ioi 0,
          _root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀
                (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
            _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
              (_root_.GD.N0232.N0719.N0954.d009350 hk
                (_root_.GD.N0232.N0719.N0960.d009692 shape variance))
              (_root_.GD.N0232.N0719.N0955.d009612 q ω)) =
        ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
          ∫ ω in Ioi 0,
            _root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀
                  (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
              _root_.GD.N0232.N0719.N0954.d009483
                (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
                (_root_.GD.N0232.N0719.N0954.d009350 hk
                  (_root_.GD.N0232.N0719.N0960.d009692 shape variance))
                (_root_.GD.N0232.N0719.N0955.d009612 q ω) :=
      setIntegral_eq_of_subset_of_forall_diff_eq_zero
        (_root_.GD.N0232.N0719.N0955.d009608 k)
        (_root_.GD.N0232.N0719.N0955.d009622 hk)
        (fun q hq => by
          have hnot : q ∉ _root_.GD.N0232.N0719.N0853.d009581 hk := hq.2
          apply setIntegral_eq_zero_of_forall_eq_zero
          intro ω hω
          rw [_root_.GD.N0232.N0719.N0912.d010770]
          simp [hnot])
    _ =
        ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
          ∫ ω in Ioi 0,
            _root_.GD.N0232.N0719.N0954.d009483
                (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
                (_root_.GD.N0232.N0719.N0954.d009350 hk
                  (_root_.GD.N0232.N0719.N0960.d009692 shape variance))
                (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
              (_root_.GD.N0232.N0719.N0855.d010602 hk triangle q w /
                (ω + V₀)) := by
      apply setIntegral_congr_fun
        (_root_.GD.N0232.N0719.N0853.d009583 hk).measurableSet
      intro q hq
      apply setIntegral_congr_fun measurableSet_Ioi
      intro ω hω
      change
        _root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀
              (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
            _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
              (_root_.GD.N0232.N0719.N0954.d009350 hk
                (_root_.GD.N0232.N0719.N0960.d009692 shape variance))
              (_root_.GD.N0232.N0719.N0955.d009612 q ω) =
          _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
              (_root_.GD.N0232.N0719.N0954.d009350 hk
                (_root_.GD.N0232.N0719.N0960.d009692 shape variance))
              (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
            (_root_.GD.N0232.N0719.N0855.d010602 hk triangle q w /
              (ω + V₀))
      rw [_root_.GD.N0232.N0719.N0912.d010770]
      simp [hq]
      ring












theorem d010781
    {k : ℕ} (hk3 : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (hchartEnergy :
      IntegrableOn
        (fun x =>
          _root_.GD.N0232.N0719.N0912.d010757 (by omega)
              (_root_.GD.N0232.N0719.N1024.d010710 hk3)
              (_root_.GD.N0232.N0719.N0912.d010745 (_root_.GD.N0232.N0719.N1024.d010710 hk3)
                (_root_.GD.N0232.N0719.N0954.d009356 sizes scales)) x *
            _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 (by omega)
                (_root_.GD.N0232.N0719.N0954.d009355 sizes))
              (_root_.GD.N0232.N0719.N0954.d009350 (by omega)
                (_root_.GD.N0232.N0719.N0954.d009357 sizes scales)) x)
        (_root_.GD.N0232.N0719.N0953.d003311 (k - 1)))
    (hchartGain :
      IntegrableOn
        (fun x =>
          _root_.GD.N0232.N0719.N0912.d010758 (by omega)
              (_root_.GD.N0232.N0719.N1024.d010710 hk3)
              (_root_.GD.N0232.N0719.N0912.d010746
                (_root_.GD.N0232.N0719.N1024.d010710 hk3)
                (_root_.GD.N0232.N0719.N0954.d009356 sizes scales))
              (_root_.GD.N0232.N0719.N0912.d010745 (_root_.GD.N0232.N0719.N1024.d010710 hk3)
                (_root_.GD.N0232.N0719.N0954.d009356 sizes scales)) x *
            _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 (by omega)
                (_root_.GD.N0232.N0719.N0954.d009355 sizes))
              (_root_.GD.N0232.N0719.N0954.d009350 (by omega)
                (_root_.GD.N0232.N0719.N0954.d009357 sizes scales)) x)
        (_root_.GD.N0232.N0719.N0953.d003311 (k - 1)))
    (hprojectiveGain :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0855.d010603 (by omega)
              (_root_.GD.N0232.N0719.N0954.d009355 sizes)
              (_root_.GD.N0232.N0719.N0954.d009357 sizes scales) q *
            _root_.GD.N0232.N0719.N0855.d010602 (by omega)
              (_root_.GD.N0232.N0719.N1024.d010710 hk3) q
              (_root_.GD.N0232.N0719.N0912.d010746
                (_root_.GD.N0232.N0719.N1024.d010710 hk3)
                (_root_.GD.N0232.N0719.N0954.d009356 sizes scales)))
        (_root_.GD.N0232.N0719.N0853.d009581 (by omega)))
    (hleft :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0954.d009508
              (_root_.GD.N0232.N0719.N0954.d009355 sizes)
              (_root_.GD.N0232.N0719.N0954.d009357 sizes scales)
              (_root_.GD.N0232.N0719.N0853.d009567 (by omega) q) *
            (_root_.GD.N0232.N0719.N0950.d010591
                (_root_.GD.N0232.N0719.N0954.d009355 sizes)
                (_root_.GD.N0232.N0719.N1024.d010710 hk3) /
              _root_.GD.N0232.N0719.N0912.d010745 (_root_.GD.N0232.N0719.N1024.d010710 hk3)
                (_root_.GD.N0232.N0719.N0954.d009356 sizes scales)) *
            _root_.GD.N0232.N0719.N0855.d010602 (by omega)
              (_root_.GD.N0232.N0719.N1024.d010710 hk3) q
              (_root_.GD.N0232.N0719.N0912.d010746
                (_root_.GD.N0232.N0719.N1024.d010710 hk3)
                (_root_.GD.N0232.N0719.N0954.d009356 sizes scales)))
        (_root_.GD.N0232.N0719.N0853.d009581 (by omega)))
    (hright :
      IntegrableOn
        (fun q =>
          ∫ ω in Ioi 0,
            _root_.GD.N0232.N0719.N0954.d009483
                (_root_.GD.N0232.N0719.N0954.d009350 (by omega)
                  (_root_.GD.N0232.N0719.N0954.d009355 sizes))
                (_root_.GD.N0232.N0719.N0954.d009350 (by omega)
                  (_root_.GD.N0232.N0719.N0954.d009357 sizes scales))
                (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
              (_root_.GD.N0232.N0719.N0855.d010602 (by omega)
                  (_root_.GD.N0232.N0719.N1024.d010710 hk3) q
                  (_root_.GD.N0232.N0719.N0912.d010746
                    (_root_.GD.N0232.N0719.N1024.d010710 hk3)
                    (_root_.GD.N0232.N0719.N0954.d009356 sizes scales)) /
                (ω +
                  _root_.GD.N0232.N0719.N0912.d010745 (_root_.GD.N0232.N0719.N1024.d010710 hk3)
                    (_root_.GD.N0232.N0719.N0954.d009356 sizes scales))))
        (_root_.GD.N0232.N0719.N0853.d009581 (by omega)))
    (hprojectiveEnergy :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0855.d010603 (by omega)
              (_root_.GD.N0232.N0719.N0954.d009355 sizes)
              (_root_.GD.N0232.N0719.N0954.d009357 sizes scales) q *
            _root_.GD.N0232.N0719.N0914.d010624 (by omega)
              (_root_.GD.N0232.N0719.N1024.d010710 hk3)
              (_root_.GD.N0232.N0719.N0912.d010745 (_root_.GD.N0232.N0719.N1024.d010710 hk3)
                (_root_.GD.N0232.N0719.N0954.d009356 sizes scales)) q)
        (_root_.GD.N0232.N0719.N0853.d009581 (by omega))) :
    _root_.GD.N0232.N0719.N1024.d010712 k sizes hk3 scales < 0 ∧
      _root_.GD.N0232.N0719.N1024.d010713 k sizes hk3 scales ≤
        _root_.GD.N0232.N0719.N0950.d010597 (by omega)
            (_root_.GD.N0232.N0719.N0954.d009355 sizes) (_root_.GD.N0232.N0719.N1024.d010710 hk3) *
          (-_root_.GD.N0232.N0719.N1024.d010712 k sizes hk3 scales) := by
  let hk : 0 < k := by omega
  let triangle : Fin 3 ↪ Fin k := _root_.GD.N0232.N0719.N1024.d010710 hk3
  let shape : Fin k → ℝ := _root_.GD.N0232.N0719.N0954.d009355 sizes
  let variance : Fin k → ℝ :=
    _root_.GD.N0232.N0719.N0954.d009356 sizes scales
  let rate : Fin k → ℝ :=
    _root_.GD.N0232.N0719.N0954.d009357 sizes scales
  let V₀ : ℝ := _root_.GD.N0232.N0719.N0912.d010745 triangle variance
  let w : Fin 3 → ℝ :=
    _root_.GD.N0232.N0719.N0912.d010746 triangle variance
  let μY := _root_.GD.N0232.N0719.N0933.d009300 k sizes 0 scales
  let μT := _root_.GD.N0232.N0719.N0933.d009301 k sizes scales
  let conditionalEnergy : (Fin k → ℝ) → ℝ :=
    fun t =>
      ∫ y,
        _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y) ^ 2 ∂μY
  let conditionalCross : (Fin k → ℝ) → ℝ :=
    fun t =>
      ∫ y,
        _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0902.d010367 t y) *
          _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0902.d010367 t y) ∂μY
  let energyEnvelope : (Fin k → ℝ) → ℝ :=
    fun t =>
      _root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀
        (_root_.GD.N0232.N0719.N0954.d009347 hk t)
  let gainEnvelope : (Fin k → ℝ) → ℝ :=
    fun t =>
      (3 / 128 : ℝ) * _root_.GD.N0232.N0719.N0950.d010587 k * V₀ ^ 2 *
        _root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀
          (_root_.GD.N0232.N0719.N0954.d009347 hk t)
  have hshape : ∀ i, 0 < shape i :=
    fun i => _root_.GD.N0232.N0719.N0954.d009358 hsizes i
  have hvariance : ∀ i, 0 < variance i :=
    fun i => _root_.GD.N0232.N0719.N0954.d009359 hsizes hscales i
  have hrate : ∀ i, 0 < rate i :=
    fun i => _root_.GD.N0232.N0719.N0954.d009360 hsizes hscales i
  have hV₀ : 0 < V₀ :=
    _root_.GD.N0232.N0719.N0912.d010747 triangle hvariance
  have hw : w ∈ _root_.GD.N0232.N0719.N0856.d009532 :=
    _root_.GD.N0232.N0719.N0912.d010749 triangle hvariance
  letI :
      ∀ i : Fin k,
        IsProbabilityMeasure
          (ProbabilityTheory.gammaMeasure (shape i) (rate i)) :=
    fun i =>
      ProbabilityTheory.isProbabilityMeasure_gammaMeasure
        (hshape i) (hrate i)
  letI :
      IsProbabilityMeasure (_root_.GD.N0232.N0719.N0954.d009342 shape rate) :=
    by
      unfold _root_.GD.N0232.N0719.N0954.d009342
      infer_instance
  letI : IsProbabilityMeasure μT := by
    rw [show μT = _root_.GD.N0232.N0719.N0954.d009342 shape rate by
      simpa [μT, shape, rate] using
        _root_.GD.N0232.N0719.N0954.d009362
          sizes hsizes scales hscales]
    infer_instance
  letI : IsProbabilityMeasure μY := by
    dsimp [μY]
    unfold _root_.GD.N0232.N0719.N0933.d009300
    infer_instance
  have hTpos :
      ∀ᵐ t ∂μT, ∀ i, 0 < t i :=
    _root_.GD.N0232.N0719.N0910.d010288 hsizes hscales
  have hrawEnergy :
      _root_.GD.N0232.N0719.N1024.d010713 k sizes hk3 scales =
        ∫ t, conditionalEnergy t ∂μT := by
    simpa [conditionalEnergy, μY, μT, triangle] using
      _root_.GD.N0232.N0719.N0912.d010754
        hk3 sizes hsizes scales hscales
  have hrawCross :
      _root_.GD.N0232.N0719.N1024.d010712 k sizes hk3 scales =
        ∫ t, conditionalCross t ∂μT := by
    simpa [conditionalCross, μY, μT, triangle] using
      _root_.GD.N0232.N0719.N0912.d010755
        hk3 sizes hsizes scales hscales
  have henergyProduct :=
    (_root_.GD.N0232.N0719.N0910.d010293
      hk sizes hsizes 0 scales hscales triangle).integrable_sq
  have hcrossProduct :=
    (_root_.GD.N0232.N0719.N0910.d010292
      hk sizes hsizes 0 scales).integrable_mul
      (_root_.GD.N0232.N0719.N0910.d010293
        hk sizes hsizes 0 scales hscales triangle)
  have hconditionalEnergy :
      Integrable conditionalEnergy μT := by
    simpa [conditionalEnergy, μY, μT, _root_.GD.N0232.N0719.N0902.d010367,
      _root_.GD.N0232.N0719.N0933.d009305] using henergyProduct.integral_prod_right
  have hconditionalCross :
      Integrable conditionalCross μT := by
    simpa [conditionalCross, μY, μT, _root_.GD.N0232.N0719.N0902.d010367,
      _root_.GD.N0232.N0719.N0933.d009305] using hcrossProduct.integral_prod_right
  have henergyEnvelopeMeas :
      AEStronglyMeasurable energyEnvelope μT :=
    ((_root_.GD.N0232.N0719.N0912.d010767 hk triangle V₀).comp
      (_root_.GD.N0232.N0719.N0912.d010765 hk)).aestronglyMeasurable
  have henergyEnvelope :
      Integrable energyEnvelope μT := by
    apply (integrable_const
      (μ := μT) (250000 * V₀)).mono'
        henergyEnvelopeMeas
    filter_upwards [hTpos] with t ht
    have hb :=
      _root_.GD.N0232.N0719.N0912.d010772
        hk triangle hV₀.le t ht
    change
      |_root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀
          (_root_.GD.N0232.N0719.N0954.d009347 hk t)| ≤ 250000 * V₀
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have henergyPoint :
      ∀ᵐ t ∂μT,
        conditionalEnergy t ≤ energyEnvelope t := by
    filter_upwards [hTpos] with t ht
    have hv0 :
        (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 0) : ℝ) ≤ V₀ := by
      rw [← _root_.GD.N0232.N0719.N0912.d010750]
      exact _root_.GD.N0232.N0719.N0912.d010748 triangle variance 0
    have hv1 :
        (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 1) : ℝ) ≤ V₀ := by
      rw [← _root_.GD.N0232.N0719.N0912.d010750]
      exact _root_.GD.N0232.N0719.N0912.d010748 triangle variance 1
    have hv2 :
        (_root_.GD.N0232.N0719.N0902.d010372 sizes scales (triangle 2) : ℝ) ≤ V₀ := by
      rw [← _root_.GD.N0232.N0719.N0912.d010750]
      exact _root_.GD.N0232.N0719.N0912.d010748 triangle variance 2
    simpa [conditionalEnergy, energyEnvelope, μY, triangle,
      _root_.GD.N0232.N0719.N0912.d010757, _root_.GD.N0232.N0719.N0912.d010759,
      mul_assoc] using
      _root_.GD.N0232.N0719.N0903.d010383
        hk sizes hsizes scales triangle t ht hv0 hv1 hv2
  have henergyToChart :
      _root_.GD.N0232.N0719.N1024.d010713 k sizes hk3 scales ≤
        ∫ t, energyEnvelope t ∂μT := by
    rw [hrawEnergy]
    exact integral_mono_ae
      hconditionalEnergy henergyEnvelope henergyPoint
  have henergyChart :
      (∫ t, energyEnvelope t ∂μT) =
        _root_.GD.N0232.N0719.N0954.d009509 shape rate *
          ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
            _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
              _root_.GD.N0232.N0719.N0914.d010624 hk triangle V₀ q := by
    change
      (∫ t, energyEnvelope t
          ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) = _
    rw [_root_.GD.N0232.N0719.N0954.d009362
      sizes hsizes scales hscales]
    simpa [energyEnvelope, shape, rate, triangle, variance, V₀] using
      _root_.GD.N0232.N0719.N0912.d010774
        hk hshape hrate triangle V₀ hchartEnergy
  have henergyBridge :
      _root_.GD.N0232.N0719.N1024.d010713 k sizes hk3 scales ≤
        _root_.GD.N0232.N0719.N0954.d009509 shape rate *
          ∫ q in _root_.GD.N0232.N0719.N0853.d009581 hk,
            _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
              _root_.GD.N0232.N0719.N0914.d010624 hk triangle V₀ q :=
    henergyToChart.trans_eq henergyChart
  have hgainMeas :
      AEStronglyMeasurable gainEnvelope μT := by
    exact
      (((_root_.GD.N0232.N0719.N0912.d010768 hk triangle w V₀).comp
        (_root_.GD.N0232.N0719.N0912.d010765 hk)).const_mul
        ((3 / 128 : ℝ) * _root_.GD.N0232.N0719.N0950.d010587 k * V₀ ^ 2))
        |>.aestronglyMeasurable
  have hgainPoint :
      ∀ᵐ t ∂μT,
        gainEnvelope t ≤ -conditionalCross t := by
    filter_upwards [hTpos] with t ht
    simpa [gainEnvelope, conditionalCross, μY, triangle,
      variance, V₀, w] using
      _root_.GD.N0232.N0719.N0912.d010771
        hk3 sizes hsizes scales hscales t ht
  have hgainNonneg :
      ∀ᵐ t ∂μT, 0 ≤ gainEnvelope t := by
    filter_upwards [hTpos] with t ht
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num)
          (_root_.GD.N0232.N0719.N0950.d010589 hk).le)
        (sq_nonneg V₀))
      (_root_.GD.N0232.N0719.N0912.d010773
        hk triangle w hV₀ t ht)
  have hgain :
      Integrable gainEnvelope μT := by
    apply hconditionalCross.neg.mono' hgainMeas
    filter_upwards [hgainPoint, hgainNonneg] with t hle hnonneg
    have hcrossNonneg : 0 ≤ -conditionalCross t := hnonneg.trans hle
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg,
      abs_of_nonneg hcrossNonneg] using hle
  have hcrossToChart :
      (∫ t, gainEnvelope t ∂μT) ≤
        -_root_.GD.N0232.N0719.N1024.d010712 k sizes hk3 scales := by
    calc
      (∫ t, gainEnvelope t ∂μT) ≤
          ∫ t, -conditionalCross t ∂μT :=
        integral_mono_ae hgain hconditionalCross.neg hgainPoint
      _ = -(∫ t, conditionalCross t ∂μT) :=
        by simpa only [Pi.neg_apply] using
          (integral_neg conditionalCross :
            (∫ t, -conditionalCross t ∂μT) = -(∫ t, conditionalCross t ∂μT))
      _ = -_root_.GD.N0232.N0719.N1024.d010712 k sizes hk3 scales := by
        rw [hrawCross]
  have hgainChart :
      (∫ t, gainEnvelope t ∂μT) =
        (3 / 128 : ℝ) * _root_.GD.N0232.N0719.N0950.d010587 k * V₀ ^ 2 *
          _root_.GD.N0232.N0719.N0914.d010623
            hk shape variance triangle w V₀ := by
    change
      (∫ t, gainEnvelope t
          ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) = _
    rw [_root_.GD.N0232.N0719.N0954.d009362
      sizes hsizes scales hscales]
    rw [_root_.GD.N0232.N0719.N0912.d010751 sizes scales]
    simp only [gainEnvelope]
    rw [integral_const_mul]
    congr 1
    simpa [gainEnvelope, shape, variance, triangle, V₀, w] using
      _root_.GD.N0232.N0719.N0912.d010780
        hk hshape hvariance triangle w V₀ hchartGain
  have hcrossBridge :
      (3 / 128 : ℝ) * _root_.GD.N0232.N0719.N0950.d010587 k * V₀ ^ 2 *
          _root_.GD.N0232.N0719.N0914.d010623
            hk shape variance triangle w V₀ ≤
        -_root_.GD.N0232.N0719.N1024.d010712 k sizes hk3 scales := by
    rw [← hgainChart]
    exact hcrossToChart
  have hresult :=
    _root_.GD.N0232.N0719.N0914.d010628
      hk3 hshape hvariance hV₀
      (_root_.GD.N0232.N0719.N0912.d010748 triangle variance 0)
      hw
      (by simpa [shape, rate, variance, triangle, w,
          _root_.GD.N0232.N0719.N0912.d010751,
          _root_.GD.N0232.N0719.N1024.d010710] using
        hprojectiveGain)
      (by simpa [shape, rate, variance, triangle, V₀, w,
          _root_.GD.N0232.N0719.N0912.d010751,
          _root_.GD.N0232.N0719.N1024.d010710] using
        hleft)
      (by simpa [shape, rate, variance, triangle, V₀, w,
          _root_.GD.N0232.N0719.N0912.d010751,
          _root_.GD.N0232.N0719.N1024.d010710] using
        hright)
      (by simpa [shape, rate, variance, triangle, V₀,
          _root_.GD.N0232.N0719.N0912.d010751,
          _root_.GD.N0232.N0719.N1024.d010710] using
        hprojectiveEnergy)
      henergyBridge hcrossBridge
  simpa [shape, triangle, _root_.GD.N0232.N0719.N1024.d010710] using hresult










theorem d010782
    {k : ℕ} (hk3 : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.N1024.d010712 k sizes hk3 scales < 0 ∧
      _root_.GD.N0232.N0719.N1024.d010713 k sizes hk3 scales ≤
        _root_.GD.N0232.N0719.N0950.d010597 (by omega)
            (_root_.GD.N0232.N0719.N0954.d009355 sizes) (_root_.GD.N0232.N0719.N1024.d010710 hk3) *
          (-_root_.GD.N0232.N0719.N1024.d010712 k sizes hk3 scales) := by
  let hk : 0 < k := by omega
  let triangle : Fin 3 ↪ Fin k := _root_.GD.N0232.N0719.N1024.d010710 hk3
  let shape : Fin k → ℝ := _root_.GD.N0232.N0719.N0954.d009355 sizes
  let variance : Fin k → ℝ :=
    _root_.GD.N0232.N0719.N0954.d009356 sizes scales
  let rate : Fin k → ℝ :=
    _root_.GD.N0232.N0719.N0954.d009357 sizes scales
  let V₀ : ℝ := _root_.GD.N0232.N0719.N0912.d010745 triangle variance
  let w : Fin 3 → ℝ :=
    _root_.GD.N0232.N0719.N0912.d010746 triangle variance
  have hshape : ∀ i, 0 < shape i :=
    fun i => _root_.GD.N0232.N0719.N0954.d009358 hsizes i
  have hvariance : ∀ i, 0 < variance i :=
    fun i => _root_.GD.N0232.N0719.N0954.d009359 hsizes hscales i
  have hrate : ∀ i, 0 < rate i :=
    fun i => _root_.GD.N0232.N0719.N0954.d009360 hsizes hscales i
  have hV₀ : 0 < V₀ :=
    _root_.GD.N0232.N0719.N0912.d010747 triangle hvariance
  have hw : w ∈ _root_.GD.N0232.N0719.N0856.d009532 :=
    _root_.GD.N0232.N0719.N0912.d010749 triangle hvariance
  have hchartEnergy :
      IntegrableOn
        (fun x =>
          _root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀ x *
            _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
              (_root_.GD.N0232.N0719.N0954.d009350 hk rate) x)
        (_root_.GD.N0232.N0719.N0953.d003311 (k - 1)) := by
    apply
      _root_.GD.N0232.N0719.N0913.d010639
        hk hshape hrate (_root_.GD.N0232.N0719.N0912.d010757 hk triangle V₀)
        (_root_.GD.N0232.N0719.N0912.d010767 hk triangle V₀).aestronglyMeasurable
        (C := 250000 * _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * V₀)
    · positivity
    · intro x hx
      exact _root_.GD.N0232.N0719.N0912.d010778
        hk triangle hV₀.le hx
  have hchartGain :
      IntegrableOn
        (fun x =>
          _root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀ x *
            _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
              (_root_.GD.N0232.N0719.N0954.d009350 hk rate) x)
        (_root_.GD.N0232.N0719.N0953.d003311 (k - 1)) := by
    apply
      _root_.GD.N0232.N0719.N0913.d010639
        hk hshape hrate (_root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀)
        (_root_.GD.N0232.N0719.N0912.d010768 hk triangle w V₀).aestronglyMeasurable
        (C := _root_.GD.N0232.N0719.N0950.d010588 k ^ 2 * 3 / V₀)
    · positivity
    · intro x hx
      exact _root_.GD.N0232.N0719.N0912.d010779
        hk triangle hw hV₀ hx
  have hprojectiveGain :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
            _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w)
        (_root_.GD.N0232.N0719.N0853.d009581 hk) :=
    _root_.GD.N0232.N0719.N0913.d010635
      hk hk3 hshape hrate triangle w
  have hleft :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0954.d009508
              shape rate (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
            (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V₀) *
            _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w)
        (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
    have h :=
      _root_.GD.N0232.N0719.N0913.d010637
        hk hk3 hshape hvariance triangle hV₀ w
    simpa [rate, variance, shape,
      _root_.GD.N0232.N0719.N0912.d010751] using h
  have hright :
      IntegrableOn
        (fun q =>
          ∫ ω in Ioi 0,
            _root_.GD.N0232.N0719.N0954.d009483
                (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
                (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
                (_root_.GD.N0232.N0719.N0955.d009612 q ω) *
              (_root_.GD.N0232.N0719.N0855.d010602 hk triangle q w /
                (ω + V₀)))
        (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
    let Hchart : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) → ℝ :=
      fun x =>
        _root_.GD.N0232.N0719.N0912.d010758 hk triangle w V₀ x *
          _root_.GD.N0232.N0719.N0954.d009483
            (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
            (_root_.GD.N0232.N0719.N0954.d009350 hk rate) x
    have hsection :
        IntegrableOn
          (fun q =>
            ∫ ω in Ioi 0, Hchart (_root_.GD.N0232.N0719.N0955.d009612 q ω))
          (_root_.GD.N0232.N0719.N0853.d009581 hk) :=
      _root_.GD.N0232.N0719.N0913.d010641
        hk Hchart (by simpa [Hchart] using hchartGain)
    apply hsection.congr_fun
    · intro q hq
      apply setIntegral_congr_fun measurableSet_Ioi
      intro ω hω
      dsimp [Hchart]
      rw [_root_.GD.N0232.N0719.N0912.d010770]
      simp only [if_pos hq]
      ring
    · exact (_root_.GD.N0232.N0719.N0853.d009583 hk).measurableSet
  have hprojectiveEnergy :
      IntegrableOn
        (fun q =>
          _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
            _root_.GD.N0232.N0719.N0914.d010624 hk triangle V₀ q)
        (_root_.GD.N0232.N0719.N0853.d009581 hk) :=
    _root_.GD.N0232.N0719.N0913.d010636
      hk hk3 hshape hrate triangle V₀
  exact
    _root_.GD.N0232.N0719.N0912.d010781
      hk3 sizes hsizes scales hscales
      (by simpa [hk, triangle, shape, variance, rate, V₀] using hchartEnergy)
      (by simpa [hk, triangle, shape, variance, rate, V₀, w] using hchartGain)
      (by simpa [hk, triangle, shape, variance, rate, w] using hprojectiveGain)
      (by simpa [hk, triangle, shape, variance, rate, V₀, w] using hleft)
      (by simpa [hk, triangle, shape, variance, rate, V₀, w] using hright)
      (by simpa [hk, triangle, shape, variance, rate, V₀] using hprojectiveEnergy)

end

end GD.N0232.N0719.N0912
