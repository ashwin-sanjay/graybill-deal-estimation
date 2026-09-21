import GD.Module0623





















open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0900

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0107


abbrev d009094 (k : ℕ) (sizes : Fin k → ℕ) :=
  ∀ i, _root_.GD.N0137.d008894 (sizes i)


def d009095
    (k : ℕ) (sizes : Fin k → ℕ) (location scale : ℝ)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) : _root_.GD.N0232.N0719.N0900.d009094 k sizes :=
  fun i => _root_.GD.N0107.d009018 (sizes i) location scale (ω i)


@[ext]
structure d009096 (k : ℕ) where
  mean : Fin k → ℝ
  meanVariance : Fin k → ℝ



def d009097 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    (Fin k → ℝ) × (Fin k → ℝ) :=
  (s.mean, s.meanVariance)

instance d009098 (k : ℕ) : MeasurableSpace (_root_.GD.N0232.N0719.N0900.d009096 k) :=
  MeasurableSpace.comap _root_.GD.N0232.N0719.N0900.d009097 inferInstance

@[fun_prop]
theorem d009099 {k : ℕ} (i : Fin k) :
    Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 k => s.mean i) := by
  have hcoordinates :
      Measurable (_root_.GD.N0232.N0719.N0900.d009097 : _root_.GD.N0232.N0719.N0900.d009096 k →
        (Fin k → ℝ) × (Fin k → ℝ)) :=
    comap_measurable _
  exact (measurable_pi_apply i).comp hcoordinates.fst

@[fun_prop]
theorem d009100 {k : ℕ} (i : Fin k) :
    Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 k => s.meanVariance i) := by
  have hcoordinates :
      Measurable (_root_.GD.N0232.N0719.N0900.d009097 : _root_.GD.N0232.N0719.N0900.d009096 k →
        (Fin k → ℝ) × (Fin k → ℝ)) :=
    comap_measurable _
  exact (measurable_pi_apply i).comp hcoordinates.snd


def d009101 {k : ℕ} (location scale : ℝ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) : _root_.GD.N0232.N0719.N0900.d009096 k where
  mean i := location + scale * s.mean i
  meanVariance i := scale ^ 2 * s.meanVariance i


def d009102
    (k : ℕ) (sizes : Fin k → ℕ)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) (i : Fin k) : ℝ :=
  _root_.GD.N0107.d009084 (ω i)


def d009103
    (k : ℕ) (sizes : Fin k → ℕ)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) (i : Fin k) : ℝ :=
  _root_.GD.N0107.d009085 (ω i) / (sizes i : ℝ)


def d009104
    (k : ℕ) (sizes : Fin k → ℕ)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) : _root_.GD.N0232.N0719.N0900.d009096 k where
  mean := _root_.GD.N0232.N0719.N0900.d009102 k sizes ω
  meanVariance := _root_.GD.N0232.N0719.N0900.d009103 k sizes ω






def d009105 (t : ℝ) : ℝ :=
  if 0 < t then t⁻¹ else 0


def d009106 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i : Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N0900.d009105 (s.meanVariance i)


def d009107 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  ∑ i, _root_.GD.N0232.N0719.N0900.d009106 s i




def d009108 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i : Fin k) : ℝ :=
  if _root_.GD.N0232.N0719.N0900.d009107 s = 0 then (k : ℝ)⁻¹
  else _root_.GD.N0232.N0719.N0900.d009106 s i / _root_.GD.N0232.N0719.N0900.d009107 s


def d009109 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) : Fin k → ℝ :=
  fun i => _root_.GD.N0232.N0719.N0900.d009108 s i


def d009110 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  ∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i * s.mean i


def d009111
    (k : ℕ) (sizes : Fin k → ℕ)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)

@[fun_prop]
theorem d009112
    (k : ℕ) (sizes : Fin k → ℕ) (location scale : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale) := by
  unfold _root_.GD.N0232.N0719.N0900.d009095
  fun_prop

@[fun_prop]
theorem d009113
    (k : ℕ) (sizes : Fin k → ℕ) (i : Fin k) :
    Measurable (fun ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes => _root_.GD.N0232.N0719.N0900.d009102 k sizes ω i) := by
  unfold _root_.GD.N0232.N0719.N0900.d009102 _root_.GD.N0107.d009084 _root_.GD.N0126.d006420
    _root_.GD.N0126.d006419
  fun_prop

@[fun_prop]
theorem d009114
    (k : ℕ) (sizes : Fin k → ℕ) (i : Fin k) :
    Measurable
      (fun ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes =>
        _root_.GD.N0232.N0719.N0900.d009103 k sizes ω i) := by
  unfold _root_.GD.N0232.N0719.N0900.d009103 _root_.GD.N0107.d009085
    _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
    _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
  fun_prop

@[fun_prop]
theorem d009115
    (k : ℕ) (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0232.N0719.N0900.d009104 k sizes) := by
  rw [measurable_comap_iff]
  change Measurable
    (fun ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes =>
      (_root_.GD.N0232.N0719.N0900.d009102 k sizes ω, _root_.GD.N0232.N0719.N0900.d009103 k sizes ω))
  fun_prop

@[fun_prop]
theorem d009116 :
    Measurable _root_.GD.N0232.N0719.N0900.d009105 := by
  unfold _root_.GD.N0232.N0719.N0900.d009105
  exact Measurable.ite
    (measurableSet_lt measurable_const measurable_id)
    measurable_inv measurable_const

@[fun_prop]
theorem d009117 {k : ℕ} (i : Fin k) :
    Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 k => _root_.GD.N0232.N0719.N0900.d009106 s i) := by
  unfold _root_.GD.N0232.N0719.N0900.d009106
  fun_prop

@[fun_prop]
theorem d009118 {k : ℕ} :
    Measurable (_root_.GD.N0232.N0719.N0900.d009107 : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N0900.d009107
  fun_prop

@[fun_prop]
theorem d009119 {k : ℕ} (i : Fin k) :
    Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 k => _root_.GD.N0232.N0719.N0900.d009108 s i) := by
  unfold _root_.GD.N0232.N0719.N0900.d009108
  exact Measurable.ite
    (measurableSet_eq_fun _root_.GD.N0232.N0719.N0900.d009118 measurable_const)
    measurable_const
    ((_root_.GD.N0232.N0719.N0900.d009117 i).div _root_.GD.N0232.N0719.N0900.d009118)

@[fun_prop]
theorem d009120 {k : ℕ} :
    Measurable (_root_.GD.N0232.N0719.N0900.d009109 : _root_.GD.N0232.N0719.N0900.d009096 k → Fin k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N0900.d009109
  fun_prop

@[fun_prop]
theorem d009121 {k : ℕ} :
    Measurable (_root_.GD.N0232.N0719.N0900.d009110 : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N0900.d009110
  fun_prop

@[fun_prop]
theorem d009122
    (k : ℕ) (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0232.N0719.N0900.d009111 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0900.d009111
  fun_prop

theorem d009123
    {n : ℕ} (hn : 0 < n) (x : _root_.GD.N0137.d008894 n) :
    0 ≤ @_root_.GD.N0126.d006422 (Fin n) _ x := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold _root_.GD.N0126.d006422
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem d009124
    {n : ℕ} (hn : 2 ≤ n) (x : _root_.GD.N0137.d008894 n) :
    0 ≤ _root_.GD.N0107.d009085 x := by
  unfold _root_.GD.N0107.d009085
  exact div_nonneg
    (_root_.GD.N0232.N0719.N0900.d009123 (by omega) x)
    (by positivity)

theorem d009125
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) (i : Fin k) :
    0 ≤ _root_.GD.N0232.N0719.N0900.d009103 k sizes ω i := by
  unfold _root_.GD.N0232.N0719.N0900.d009103
  exact div_nonneg
    (_root_.GD.N0232.N0719.N0900.d009124 (hsizes i) (ω i))
    (by positivity)

theorem d009126 (t : ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N0900.d009105 t := by
  by_cases ht : 0 < t
  · simp [_root_.GD.N0232.N0719.N0900.d009105, ht, (inv_pos.mpr ht).le]
  · simp [_root_.GD.N0232.N0719.N0900.d009105, ht]

theorem d009127 {t : ℝ} (ht : 0 < t) :
    _root_.GD.N0232.N0719.N0900.d009105 t = t⁻¹ := by
  simp [_root_.GD.N0232.N0719.N0900.d009105, ht]

theorem d009128 {t : ℝ} (ht : t ≤ 0) :
    _root_.GD.N0232.N0719.N0900.d009105 t = 0 := by
  simp [_root_.GD.N0232.N0719.N0900.d009105, not_lt.mpr ht]

theorem d009129 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i : Fin k) :
    0 ≤ _root_.GD.N0232.N0719.N0900.d009106 s i :=
  _root_.GD.N0232.N0719.N0900.d009126 _

theorem d009130 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    0 ≤ _root_.GD.N0232.N0719.N0900.d009107 s :=
  Finset.sum_nonneg fun i _ => _root_.GD.N0232.N0719.N0900.d009129 s i

theorem d009131 {k : ℕ} (hk : 0 < k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    ∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i = 1 := by
  by_cases hzero : _root_.GD.N0232.N0719.N0900.d009107 s = 0
  · simp [_root_.GD.N0232.N0719.N0900.d009108, hzero, hk.ne']
  · simp only [_root_.GD.N0232.N0719.N0900.d009108, hzero, ↓reduceIte]
    rw [← Finset.sum_div]
    exact div_self hzero

theorem d009132 {k : ℕ} (hk : 0 < k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i : Fin k) :
    0 ≤ _root_.GD.N0232.N0719.N0900.d009108 s i := by
  by_cases hzero : _root_.GD.N0232.N0719.N0900.d009107 s = 0
  · simp [_root_.GD.N0232.N0719.N0900.d009108, hzero]
  · rw [_root_.GD.N0232.N0719.N0900.d009108, if_neg hzero]
    exact div_nonneg
      (_root_.GD.N0232.N0719.N0900.d009129 s i)
      (_root_.GD.N0232.N0719.N0900.d009130 s)

theorem d009133 {k : ℕ} (hk : 0 < k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009108 s i ≤ 1 := by
  have hnonneg := _root_.GD.N0232.N0719.N0900.d009132 hk s
  calc
    _root_.GD.N0232.N0719.N0900.d009108 s i ≤ ∑ j, _root_.GD.N0232.N0719.N0900.d009108 s j := by
      exact Finset.single_le_sum
        (fun j _ => hnonneg j) (Finset.mem_univ i)
    _ = 1 := _root_.GD.N0232.N0719.N0900.d009131 hk s

theorem d009134 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0900.d009110 s = ∑ i, _root_.GD.N0232.N0719.N0900.d009109 s i * s.mean i := by
  rfl

theorem d009135
    {n : ℕ} (hn : 0 < n) (location scale : ℝ)
    (x : _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009084 (_root_.GD.N0107.d009018 n location scale x) =
      location + scale * _root_.GD.N0107.d009084 x := by
  exact _root_.GD.N0107.d009086 hn location scale x

theorem d009136
    {n : ℕ} (hn : 0 < n) (location scale : ℝ)
    (x : _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009085 (_root_.GD.N0107.d009018 n location scale x) =
      scale ^ 2 * _root_.GD.N0107.d009085 x := by
  unfold _root_.GD.N0107.d009085
  rw [_root_.GD.N0107.d009088 hn location scale x]
  ring

theorem d009137
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 0 < sizes i)
    (location scale : ℝ) (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) (i : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009102 k sizes
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) i =
      location + scale * _root_.GD.N0232.N0719.N0900.d009102 k sizes ω i := by
  exact _root_.GD.N0232.N0719.N0900.d009135
    (hsizes i) location scale (ω i)

theorem d009138
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 0 < sizes i)
    (location scale : ℝ) (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) (i : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009103 k sizes
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) i =
      scale ^ 2 * _root_.GD.N0232.N0719.N0900.d009103 k sizes ω i := by
  unfold _root_.GD.N0232.N0719.N0900.d009103 _root_.GD.N0232.N0719.N0900.d009095
  rw [_root_.GD.N0232.N0719.N0900.d009136
    (hsizes i) location scale (ω i)]
  ring

theorem d009139
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 0 < sizes i)
    (location scale : ℝ) (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0232.N0719.N0900.d009104 k sizes
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) =
      _root_.GD.N0232.N0719.N0900.d009101 location scale (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) := by
  ext i
  · exact _root_.GD.N0232.N0719.N0900.d009137
      hsizes location scale ω i
  · exact _root_.GD.N0232.N0719.N0900.d009138
      hsizes location scale ω i

theorem d009140
    {a : ℝ} (ha : 0 < a) (t : ℝ) :
    _root_.GD.N0232.N0719.N0900.d009105 (a * t) = a⁻¹ * _root_.GD.N0232.N0719.N0900.d009105 t := by
  by_cases ht : 0 < t
  · have hat : 0 < a * t := mul_pos ha ht
    simp only [_root_.GD.N0232.N0719.N0900.d009105, ht, hat, ↓reduceIte]
    rw [mul_inv_rev]
    ring
  · have ht' : t ≤ 0 := not_lt.mp ht
    have hat : ¬ 0 < a * t := by
      exact not_lt.mpr
        (mul_nonpos_of_nonneg_of_nonpos ha.le ht')
    simp [_root_.GD.N0232.N0719.N0900.d009105, ht, hat]

theorem d009141
    {k : ℕ} (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009106 (_root_.GD.N0232.N0719.N0900.d009101 location scale s) i =
      (scale ^ 2)⁻¹ * _root_.GD.N0232.N0719.N0900.d009106 s i := by
  exact _root_.GD.N0232.N0719.N0900.d009140
    (sq_pos_of_ne_zero hscale) (s.meanVariance i)

theorem d009142
    {k : ℕ} (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0900.d009107 (_root_.GD.N0232.N0719.N0900.d009101 location scale s) =
      (scale ^ 2)⁻¹ * _root_.GD.N0232.N0719.N0900.d009107 s := by
  unfold _root_.GD.N0232.N0719.N0900.d009107
  simp_rw [_root_.GD.N0232.N0719.N0900.d009141 location hscale s]
  exact (Finset.mul_sum _ _ _).symm

theorem d009143
    {k : ℕ} (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0900.d009101 location scale s) i = _root_.GD.N0232.N0719.N0900.d009108 s i := by
  have hfactor : (scale ^ 2)⁻¹ ≠ 0 :=
    inv_ne_zero (pow_ne_zero 2 hscale)
  unfold _root_.GD.N0232.N0719.N0900.d009108
  rw [_root_.GD.N0232.N0719.N0900.d009142 location hscale s,
    _root_.GD.N0232.N0719.N0900.d009141 location hscale s]
  by_cases hzero : _root_.GD.N0232.N0719.N0900.d009107 s = 0
  · have hscaled :
        (scale ^ 2)⁻¹ * _root_.GD.N0232.N0719.N0900.d009107 s = 0 := by
      rw [hzero, mul_zero]
    rw [if_pos hscaled, if_pos hzero]
  · have hscaled :
        (scale ^ 2)⁻¹ * _root_.GD.N0232.N0719.N0900.d009107 s ≠ 0 :=
      mul_ne_zero hfactor hzero
    rw [if_neg hscaled, if_neg hzero]
    exact mul_div_mul_left _ _ hfactor

theorem d009144
    {k : ℕ} (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0900.d009109 (_root_.GD.N0232.N0719.N0900.d009101 location scale s) = _root_.GD.N0232.N0719.N0900.d009109 s := by
  funext i
  exact _root_.GD.N0232.N0719.N0900.d009143 location hscale s i

theorem d009145
    {k : ℕ} (hk : 0 < k)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0900.d009101 location scale s) =
      location + scale * _root_.GD.N0232.N0719.N0900.d009110 s := by
  unfold _root_.GD.N0232.N0719.N0900.d009110
  simp_rw [_root_.GD.N0232.N0719.N0900.d009143 location hscale s]
  change
    (∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i * (location + scale * s.mean i)) =
      location + scale * ∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i * s.mean i
  calc
    (∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i * (location + scale * s.mean i)) =
        (∑ i, location * _root_.GD.N0232.N0719.N0900.d009108 s i) +
          ∑ i, scale * (_root_.GD.N0232.N0719.N0900.d009108 s i * s.mean i) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = location * (∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i) +
          scale * (∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i * s.mean i) := by
            rw [Finset.mul_sum, Finset.mul_sum]
    _ = location + scale * (∑ i, _root_.GD.N0232.N0719.N0900.d009108 s i * s.mean i) := by
            rw [_root_.GD.N0232.N0719.N0900.d009131 hk s]
            ring






theorem d009146
    {k : ℕ} (hk : 0 < k)
    {sizes : Fin k → ℕ} (hsizes : ∀ i, 0 < sizes i)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0232.N0719.N0900.d009111 k sizes
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) =
      location + scale * _root_.GD.N0232.N0719.N0900.d009111 k sizes ω := by
  unfold _root_.GD.N0232.N0719.N0900.d009111
  rw [_root_.GD.N0232.N0719.N0900.d009139
    hsizes location scale ω]
  exact _root_.GD.N0232.N0719.N0900.d009145 hk location hscale _

theorem d009147
    {k : ℕ} (hk : 0 < k)
    {sizes : Fin k → ℕ} (hsizes : ∀ i, 0 < sizes i)
    (location : ℝ) {scale : ℝ} (hscale : 0 < scale)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0232.N0719.N0900.d009111 k sizes
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) =
      location + scale * _root_.GD.N0232.N0719.N0900.d009111 k sizes ω :=
  _root_.GD.N0232.N0719.N0900.d009146
    hk hsizes location hscale.ne' ω

end

end GD.N0232.N0719.N0900
