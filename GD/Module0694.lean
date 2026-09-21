import GD.Module0689
import GD.Module0693
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul




































open MeasureTheory
open scoped BigOperators

namespace GD.N0232.N0719.N0874

noncomputable section

variable {ι Ω : Type*} [Fintype ι]
variable [MeasurableSpace Ω]


def d010190
    (weight : ι → ℝ) (correction : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, weight i * correction i ω


def d010191
    (μ : Measure Ω) (residual : Ω → ℝ)
    (correction : ι → Ω → ℝ) (i : ι) : ℝ :=
  ∫ ω, residual ω * correction i ω ∂μ


def d010192
    (μ : Measure Ω) (correction : ι → Ω → ℝ) (i : ι) : ℝ :=
  ∫ ω, (correction i ω) ^ 2 ∂μ


def d010193
    (μ : Measure Ω) (residual : Ω → ℝ)
    (weight : ι → ℝ) (correction : ι → Ω → ℝ) : ℝ :=
  ∫ ω, residual ω * _root_.GD.N0232.N0719.N0874.d010190 weight correction ω ∂μ


def d010194
    (μ : Measure Ω) (weight : ι → ℝ)
    (correction : ι → Ω → ℝ) : ℝ :=
  ∫ ω, (_root_.GD.N0232.N0719.N0874.d010190 weight correction ω) ^ 2 ∂μ



theorem d010195
    (weight : ι → ℝ) (correction : ι → Ω → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hsum : ∑ i, weight i = 1) (ω : Ω) :
    (_root_.GD.N0232.N0719.N0874.d010190 weight correction ω) ^ 2 ≤
      ∑ i, weight i * (correction i ω) ^ 2 := by
  have hconvex :
      ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    even_two.convexOn_pow
  have h := hconvex.map_sum_le
    (t := (Finset.univ : Finset ι))
    (w := weight)
    (p := fun i => correction i ω)
    (fun i _ => hweight i)
    (by simpa using hsum)
    (fun _ _ => Set.mem_univ _)
  simpa [_root_.GD.N0232.N0719.N0874.d010190, smul_eq_mul] using h



theorem d010196
    (μ : Measure Ω) (residual : Ω → ℝ)
    (weight : ι → ℝ) (correction : ι → Ω → ℝ)
    (hintegrable : ∀ i,
      Integrable (fun ω => residual ω * correction i ω) μ) :
    _root_.GD.N0232.N0719.N0874.d010193 μ residual weight correction =
      ∑ i, weight i * _root_.GD.N0232.N0719.N0874.d010191 μ residual correction i := by
  have hfun :
      (fun ω => residual ω * _root_.GD.N0232.N0719.N0874.d010190 weight correction ω) =
        (fun ω => ∑ i, weight i * (residual ω * correction i ω)) := by
    funext ω
    simp only [_root_.GD.N0232.N0719.N0874.d010190]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [_root_.GD.N0232.N0719.N0874.d010193, hfun]
  rw [integral_finset_sum _ (fun i _ => (hintegrable i).const_mul (weight i))]
  unfold _root_.GD.N0232.N0719.N0874.d010191
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul]



theorem d010197
    (weight : ι → ℝ) (correction : ι → Ω → ℝ)
    (hmeasurable : ∀ i, Measurable (correction i)) :
    Measurable (_root_.GD.N0232.N0719.N0874.d010190 weight correction) := by
  unfold _root_.GD.N0232.N0719.N0874.d010190
  fun_prop



theorem d010198
    (μ : Measure Ω) (weight : ι → ℝ)
    (correction : ι → Ω → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hsum : ∑ i, weight i = 1)
    (hmeasurable : ∀ i, Measurable (correction i))
    (hintegrable : ∀ i,
      Integrable (fun ω => (correction i ω) ^ 2) μ) :
    Integrable (fun ω => (_root_.GD.N0232.N0719.N0874.d010190 weight correction ω) ^ 2) μ := by
  let bound : Ω → ℝ := fun ω =>
    ∑ i, weight i * (correction i ω) ^ 2
  have hbound_integrable : Integrable bound μ := by
    unfold bound
    exact integrable_finset_sum _ fun i _ =>
      (hintegrable i).const_mul (weight i)
  apply Integrable.mono' hbound_integrable
    ((_root_.GD.N0232.N0719.N0874.d010197 weight correction hmeasurable).pow_const 2).aestronglyMeasurable
  filter_upwards with ω
  have hpoint :=
    _root_.GD.N0232.N0719.N0874.d010195
      weight correction hweight hsum ω
  have hleft : 0 ≤ (_root_.GD.N0232.N0719.N0874.d010190 weight correction ω) ^ 2 :=
    sq_nonneg _
  have hright : 0 ≤ bound ω := by
    unfold bound
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hweight i) (sq_nonneg _)
  simpa [Real.norm_eq_abs, abs_of_nonneg hleft,
    abs_of_nonneg hright, bound] using hpoint



theorem d010199
    (μ : Measure Ω) (residual : Ω → ℝ)
    (weight : ι → ℝ) (correction : ι → Ω → ℝ)
    (hintegrable : ∀ i,
      Integrable (fun ω => residual ω * correction i ω) μ) :
    Integrable
      (fun ω => residual ω * _root_.GD.N0232.N0719.N0874.d010190 weight correction ω) μ := by
  have hfun :
      (fun ω => residual ω * _root_.GD.N0232.N0719.N0874.d010190 weight correction ω) =
        (fun ω => ∑ i, weight i * (residual ω * correction i ω)) := by
    funext ω
    simp only [_root_.GD.N0232.N0719.N0874.d010190]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfun]
  exact integrable_finset_sum _ fun i _ =>
    (hintegrable i).const_mul (weight i)



theorem d010200
    (μ : Measure Ω) (weight : ι → ℝ)
    (correction : ι → Ω → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hsum : ∑ i, weight i = 1)
    (hmeasurable : ∀ i, Measurable (correction i))
    (hintegrable : ∀ i,
      Integrable (fun ω => (correction i ω) ^ 2) μ) :
    _root_.GD.N0232.N0719.N0874.d010194 μ weight correction ≤
      ∑ i, weight i * _root_.GD.N0232.N0719.N0874.d010192 μ correction i := by
  let bound : Ω → ℝ := fun ω =>
    ∑ i, weight i * (correction i ω) ^ 2
  have hbound_integrable : Integrable bound μ := by
    unfold bound
    exact integrable_finset_sum _ fun i _ =>
      (hintegrable i).const_mul (weight i)
  have havg_integrable :=
    _root_.GD.N0232.N0719.N0874.d010198
      μ weight correction hweight hsum hmeasurable hintegrable
  have hmono :
      (∫ ω, (_root_.GD.N0232.N0719.N0874.d010190 weight correction ω) ^ 2 ∂μ) ≤
        ∫ ω, bound ω ∂μ := by
    exact integral_mono havg_integrable hbound_integrable fun ω =>
      _root_.GD.N0232.N0719.N0874.d010195
        weight correction hweight hsum ω
  calc
    _root_.GD.N0232.N0719.N0874.d010194 μ weight correction =
        ∫ ω, (_root_.GD.N0232.N0719.N0874.d010190 weight correction ω) ^ 2 ∂μ := rfl
    _ ≤ ∫ ω, bound ω ∂μ := hmono
    _ = ∑ i, weight i * _root_.GD.N0232.N0719.N0874.d010192 μ correction i := by
      unfold bound _root_.GD.N0232.N0719.N0874.d010192
      rw [integral_finset_sum _ (fun i _ =>
        (hintegrable i).const_mul (weight i))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_const_mul]


theorem d010201
    [Nonempty ι]
    (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hsum : ∑ i, weight i = 1) :
    ∃ i, 0 < weight i := by
  by_contra hnone
  push Not at hnone
  have hzero : ∀ i, weight i = 0 := fun i =>
    le_antisymm (hnone i) (hweight i)
  have : (∑ i, weight i) = 0 := by simp [hzero]
  linarith



theorem d010202
    [Nonempty ι]
    (weight cross : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hsum : ∑ i, weight i = 1)
    (hcross : ∀ i, cross i < 0) :
    (∑ i, weight i * cross i) < 0 := by
  obtain ⟨i₀, hi₀⟩ := _root_.GD.N0232.N0719.N0874.d010201 weight hweight hsum
  have hle : ∀ i ∈ (Finset.univ : Finset ι),
      weight i * cross i ≤ 0 := fun i _ =>
    mul_nonpos_of_nonneg_of_nonpos (hweight i) (hcross i).le
  have hlt : ∃ i ∈ (Finset.univ : Finset ι),
      weight i * cross i < 0 :=
    ⟨i₀, Finset.mem_univ i₀, mul_neg_of_pos_of_neg hi₀ (hcross i₀)⟩
  simpa using
    (Finset.sum_lt_sum (s := (Finset.univ : Finset ι))
      (f := fun i => weight i * cross i)
      (g := fun _ => (0 : ℝ)) hle hlt)



theorem d010203
    [Nonempty ι]
    (μ : Measure Ω) (residual : Ω → ℝ)
    (weight : ι → ℝ) (correction : ι → Ω → ℝ)
    (gamma : ℝ)
    (_hgamma : 0 ≤ gamma)
    (hweight : ∀ i, 0 ≤ weight i)
    (hsum : ∑ i, weight i = 1)
    (hmeasurable : ∀ i, Measurable (correction i))
    (hcross_integrable : ∀ i,
      Integrable (fun ω => residual ω * correction i ω) μ)
    (henergy_integrable : ∀ i,
      Integrable (fun ω => (correction i ω) ^ 2) μ)
    (hcross_negative : ∀ i,
      _root_.GD.N0232.N0719.N0874.d010191 μ residual correction i < 0)
    (hcapacity : ∀ i,
      _root_.GD.N0232.N0719.N0874.d010192 μ correction i ≤
        gamma * (-_root_.GD.N0232.N0719.N0874.d010191 μ residual correction i)) :
    _root_.GD.N0232.N0719.N0874.d010193 μ residual weight correction < 0 ∧
      _root_.GD.N0232.N0719.N0874.d010194 μ weight correction ≤
        gamma * (-_root_.GD.N0232.N0719.N0874.d010193 μ residual weight correction) := by
  have hcross_eq :=
    _root_.GD.N0232.N0719.N0874.d010196
      μ residual weight correction hcross_integrable
  have hcross_neg :
      (∑ i, weight i * _root_.GD.N0232.N0719.N0874.d010191 μ residual correction i) < 0 :=
    _root_.GD.N0232.N0719.N0874.d010202 weight
      (fun i => _root_.GD.N0232.N0719.N0874.d010191 μ residual correction i)
      hweight hsum hcross_negative
  refine ⟨?_, ?_⟩
  · rw [hcross_eq]
    exact hcross_neg
  · calc
      _root_.GD.N0232.N0719.N0874.d010194 μ weight correction ≤
          ∑ i, weight i * _root_.GD.N0232.N0719.N0874.d010192 μ correction i :=
        _root_.GD.N0232.N0719.N0874.d010200
          μ weight correction hweight hsum hmeasurable henergy_integrable
      _ ≤ ∑ i, weight i *
          (gamma * (-_root_.GD.N0232.N0719.N0874.d010191 μ residual correction i)) := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hcapacity i) (hweight i)
      _ = gamma *
          (-(∑ i, weight i * _root_.GD.N0232.N0719.N0874.d010191 μ residual correction i)) := by
        calc
          ∑ i, weight i *
                (gamma * (-_root_.GD.N0232.N0719.N0874.d010191 μ residual correction i)) =
              gamma *
                (∑ i, -(weight i * _root_.GD.N0232.N0719.N0874.d010191 μ residual correction i)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = gamma *
                (-(∑ i, weight i * _root_.GD.N0232.N0719.N0874.d010191 μ residual correction i)) := by
            rw [Finset.sum_neg_distrib]
      _ = gamma * (-_root_.GD.N0232.N0719.N0874.d010193 μ residual weight correction) := by
        rw [hcross_eq]



open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1015
open _root_.GD.N0232.N0719.N0852
open _root_.GD.N0237.N0746


def d010204
    {k : ℕ} {sizes : Fin k → ℕ}
    (μ : Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)) (target : ℝ) : ℝ :=
  ∫ ω,
    _root_.GD.N0232.N0719.N1015.d010078 target ω *
      _root_.GD.N0232.N0719.N0852.d010177 (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) ∂μ


def d010205
    {k : ℕ} {sizes : Fin k → ℕ}
    (μ : Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)) : ℝ :=
  ∫ ω,
    (_root_.GD.N0232.N0719.N0852.d010177 (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)) ^ 2 ∂μ



theorem d010206
    {k : ℕ} {sizes : Fin k → ℕ}
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0232.N0719.N0874.d010190
        (fun _triangle : Fin 3 ↪ Fin k => _root_.GD.N0232.N0719.N0852.d010176 k)
        (fun triangle => _root_.GD.N0232.N0719.N1015.d010079 triangle) ω =
      _root_.GD.N0232.N0719.N0852.d010177 (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) := by
  unfold _root_.GD.N0232.N0719.N0874.d010190 _root_.GD.N0232.N0719.N0852.d010177
    _root_.GD.N0232.N0719.N1015.d010079
  rw [Finset.mul_sum]



theorem d010207
    {k : ℕ} {sizes : Fin k → ℕ}
    (μ : Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)) (target : ℝ)
    (hintegrable : ∀ triangle : Fin 3 ↪ Fin k,
      Integrable
        (fun ω => _root_.GD.N0232.N0719.N1015.d010078 target ω * _root_.GD.N0232.N0719.N1015.d010079 triangle ω) μ) :
    _root_.GD.N0232.N0719.N0874.d010204 μ target =
      ∑ triangle : Fin 3 ↪ Fin k,
        _root_.GD.N0232.N0719.N0852.d010176 k * _root_.GD.N0232.N0719.N1015.d010080 μ target triangle := by
  have h := _root_.GD.N0232.N0719.N0874.d010196
    μ (_root_.GD.N0232.N0719.N1015.d010078 target)
    (fun _triangle : Fin 3 ↪ Fin k => _root_.GD.N0232.N0719.N0852.d010176 k)
    (fun triangle => _root_.GD.N0232.N0719.N1015.d010079 triangle) hintegrable
  rw [_root_.GD.N0232.N0719.N0874.d010193] at h
  simp_rw [_root_.GD.N0232.N0719.N0874.d010206] at h
  simpa only [_root_.GD.N0232.N0719.N0874.d010204, _root_.GD.N0232.N0719.N0874.d010191, _root_.GD.N0232.N0719.N1015.d010080] using h



theorem d010208
    {k : ℕ} {sizes : Fin k → ℕ}
    (hk : 3 ≤ k)
    (μ : Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes))
    (hintegrable : ∀ triangle : Fin 3 ↪ Fin k,
      Integrable (fun ω => (_root_.GD.N0232.N0719.N1015.d010079 triangle ω) ^ 2) μ) :
    _root_.GD.N0232.N0719.N0874.d010205 μ ≤
      ∑ triangle : Fin 3 ↪ Fin k,
        _root_.GD.N0232.N0719.N0852.d010176 k * _root_.GD.N0232.N0719.N1015.d010081 μ triangle := by
  have h := _root_.GD.N0232.N0719.N0874.d010200
    μ
    (fun _triangle : Fin 3 ↪ Fin k => _root_.GD.N0232.N0719.N0852.d010176 k)
    (fun triangle => _root_.GD.N0232.N0719.N1015.d010079 triangle)
    (fun _ => (_root_.GD.N0232.N0719.N0852.d010180 hk).le)
    (_root_.GD.N0232.N0719.N0852.d010181 hk)
    (fun triangle =>
      (_root_.GD.N0232.N0719.N1018.d010044 triangle).comp
        (_root_.GD.N0232.N0719.N0900.d009115 k sizes))
    hintegrable
  rw [_root_.GD.N0232.N0719.N0874.d010194] at h
  simp_rw [_root_.GD.N0232.N0719.N0874.d010206] at h
  simpa only [_root_.GD.N0232.N0719.N0874.d010205, _root_.GD.N0232.N0719.N0874.d010192,
    _root_.GD.N0232.N0719.N1015.d010081] using h




theorem d010209
    {k : ℕ} {sizes : Fin k → ℕ}
    (hk : 3 ≤ k)
    (μ : Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)) (target gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (hcross_integrable : ∀ triangle : Fin 3 ↪ Fin k,
      Integrable
        (fun ω => _root_.GD.N0232.N0719.N1015.d010078 target ω * _root_.GD.N0232.N0719.N1015.d010079 triangle ω) μ)
    (henergy_integrable : ∀ triangle : Fin 3 ↪ Fin k,
      Integrable (fun ω => (_root_.GD.N0232.N0719.N1015.d010079 triangle ω) ^ 2) μ)
    (hcross_negative : ∀ triangle : Fin 3 ↪ Fin k,
      _root_.GD.N0232.N0719.N1015.d010080 μ target triangle < 0)
    (hcapacity : ∀ triangle : Fin 3 ↪ Fin k,
      _root_.GD.N0232.N0719.N1015.d010081 μ triangle ≤
        gamma * (-_root_.GD.N0232.N0719.N1015.d010080 μ target triangle)) :
    _root_.GD.N0232.N0719.N0874.d010204 μ target < 0 ∧
      _root_.GD.N0232.N0719.N0874.d010205 μ ≤
        gamma * (-_root_.GD.N0232.N0719.N0874.d010204 μ target) := by
  letI : Nonempty (Fin 3 ↪ Fin k) := ⟨Fin.castLEEmb hk⟩
  have h := _root_.GD.N0232.N0719.N0874.d010203
    μ (_root_.GD.N0232.N0719.N1015.d010078 target)
    (fun _triangle : Fin 3 ↪ Fin k => _root_.GD.N0232.N0719.N0852.d010176 k)
    (fun triangle => _root_.GD.N0232.N0719.N1015.d010079 triangle)
    gamma hgamma
    (fun _ => (_root_.GD.N0232.N0719.N0852.d010180 hk).le)
    (_root_.GD.N0232.N0719.N0852.d010181 hk)
    (fun triangle =>
      (_root_.GD.N0232.N0719.N1018.d010044 triangle).comp
        (_root_.GD.N0232.N0719.N0900.d009115 k sizes))
    hcross_integrable henergy_integrable
    (by
      intro triangle
      change _root_.GD.N0232.N0719.N1015.d010080 μ target triangle < 0
      exact hcross_negative triangle)
    (by
      intro triangle
      change _root_.GD.N0232.N0719.N1015.d010081 μ triangle ≤
        gamma * (-_root_.GD.N0232.N0719.N1015.d010080 μ target triangle)
      exact hcapacity triangle)
  rw [_root_.GD.N0232.N0719.N0874.d010193, _root_.GD.N0232.N0719.N0874.d010194] at h
  simp_rw [_root_.GD.N0232.N0719.N0874.d010206] at h
  simpa only [_root_.GD.N0232.N0719.N0874.d010204, _root_.GD.N0232.N0719.N0874.d010205] using h



theorem d010210
    {k : ℕ} {sizes : Fin k → ℕ}
    (hk : 3 ≤ k)
    (μ : Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes))
    (hintegrable : ∀ triangle : Fin 3 ↪ Fin k,
      Integrable (fun ω => (_root_.GD.N0232.N0719.N1015.d010079 triangle ω) ^ 2) μ) :
    Integrable
      (fun ω =>
        (_root_.GD.N0232.N0719.N0852.d010177 (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)) ^ 2) μ := by
  have h := _root_.GD.N0232.N0719.N0874.d010198
    μ
    (fun _triangle : Fin 3 ↪ Fin k => _root_.GD.N0232.N0719.N0852.d010176 k)
    (fun triangle => _root_.GD.N0232.N0719.N1015.d010079 triangle)
    (fun _ => (_root_.GD.N0232.N0719.N0852.d010180 hk).le)
    (_root_.GD.N0232.N0719.N0852.d010181 hk)
    (fun triangle =>
      (_root_.GD.N0232.N0719.N1018.d010044 triangle).comp
        (_root_.GD.N0232.N0719.N0900.d009115 k sizes))
    hintegrable
  simpa [_root_.GD.N0232.N0719.N0874.d010206] using h



theorem d010211
    {k : ℕ} {sizes : Fin k → ℕ}
    (μ : Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)) (target : ℝ)
    (hintegrable : ∀ triangle : Fin 3 ↪ Fin k,
      Integrable
        (fun ω => _root_.GD.N0232.N0719.N1015.d010078 target ω * _root_.GD.N0232.N0719.N1015.d010079 triangle ω) μ) :
    Integrable
      (fun ω =>
        _root_.GD.N0232.N0719.N1015.d010078 target ω *
          _root_.GD.N0232.N0719.N0852.d010177 (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)) μ := by
  have h := _root_.GD.N0232.N0719.N0874.d010199
    μ (_root_.GD.N0232.N0719.N1015.d010078 target)
    (fun _triangle : Fin 3 ↪ Fin k => _root_.GD.N0232.N0719.N0852.d010176 k)
    (fun triangle => _root_.GD.N0232.N0719.N1015.d010079 triangle)
    hintegrable
  simpa [_root_.GD.N0232.N0719.N0874.d010206] using h







theorem d010212
    {k : ℕ} {sizes : Fin k → ℕ}
    (hk : 3 ≤ k)
    (μ : Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)) (target gamma epsilon : ℝ)
    (hgamma : 0 ≤ gamma)
    (hepsilon : 0 < epsilon)
    (hstep : epsilon * gamma < 2)
    (hresidual :
      Integrable (fun ω => (_root_.GD.N0232.N0719.N1015.d010078 target ω) ^ 2) μ)
    (hcross_integrable : ∀ triangle : Fin 3 ↪ Fin k,
      Integrable
        (fun ω => _root_.GD.N0232.N0719.N1015.d010078 target ω * _root_.GD.N0232.N0719.N1015.d010079 triangle ω) μ)
    (henergy_integrable : ∀ triangle : Fin 3 ↪ Fin k,
      Integrable (fun ω => (_root_.GD.N0232.N0719.N1015.d010079 triangle ω) ^ 2) μ)
    (hcross_negative : ∀ triangle : Fin 3 ↪ Fin k,
      _root_.GD.N0232.N0719.N1015.d010080 μ target triangle < 0)
    (hcapacity : ∀ triangle : Fin 3 ↪ Fin k,
      _root_.GD.N0232.N0719.N1015.d010081 μ triangle ≤
        gamma * (-_root_.GD.N0232.N0719.N1015.d010080 μ target triangle)) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N0852.d010179 k sizes epsilon ω -
          target) ^ 2 ∂μ) <
      ∫ ω, (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - target) ^ 2 ∂μ := by
  let r : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ := _root_.GD.N0232.N0719.N1015.d010078 target
  let u : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ := fun ω =>
    _root_.GD.N0232.N0719.N0852.d010177 (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)
  let h : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ := -u
  have hcap := _root_.GD.N0232.N0719.N0874.d010209
    hk μ target gamma hgamma hcross_integrable henergy_integrable
      hcross_negative hcapacity
  have hu_sq : Integrable (fun ω => (u ω) ^ 2) μ := by
    simpa [u] using
      _root_.GD.N0232.N0719.N0874.d010210 hk μ henergy_integrable
  have hh_sq : Integrable (fun ω => (h ω) ^ 2) μ := by
    simpa [h] using hu_sq
  have hru : Integrable (fun ω => r ω * u ω) μ := by
    simpa [r, u] using
      _root_.GD.N0232.N0719.N0874.d010211
        μ target hcross_integrable
  have hrh : Integrable (fun ω => r ω * h ω) μ := by
    simpa [h, mul_neg] using hru.neg
  have hid := _root_.GD.N0237.N0746.d004286 μ epsilon r h
    hresidual hh_sq hrh
  have henergy :
      _root_.GD.N0237.N0746.d004281 μ h =
        _root_.GD.N0232.N0719.N0874.d010205 μ := by
    unfold _root_.GD.N0237.N0746.d004281
      _root_.GD.N0232.N0719.N0874.d010205 h u
    apply integral_congr_ae
    filter_upwards with ω
    change (-u ω) ^ 2 = (u ω) ^ 2
    ring
  have hcross :
      _root_.GD.N0237.N0746.d004280 μ r h =
        -_root_.GD.N0232.N0719.N0874.d010204 μ target := by
    unfold _root_.GD.N0237.N0746.d004280
      _root_.GD.N0232.N0719.N0874.d010204 r h u
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with ω
    change r ω * (-u ω) = -(r ω * u ω)
    ring
  rw [henergy, hcross] at hid
  let C := _root_.GD.N0232.N0719.N0874.d010204 μ target
  let B := _root_.GD.N0232.N0719.N0874.d010205 μ
  have hC : C < 0 := hcap.1
  have hB : B ≤ gamma * (-C) := hcap.2
  have hinc : epsilon ^ 2 * B + 2 * epsilon * C < 0 := by
    have hscaled : epsilon ^ 2 * B ≤
        epsilon ^ 2 * (gamma * (-C)) :=
      mul_le_mul_of_nonneg_left hB (sq_nonneg epsilon)
    have hleft : 0 < epsilon * (-C) :=
      mul_pos hepsilon (neg_pos.mpr hC)
    have hright : epsilon * gamma - 2 < 0 := sub_neg.mpr hstep
    have hneg : epsilon * (-C) * (epsilon * gamma - 2) < 0 :=
      mul_neg_of_pos_of_neg hleft hright
    nlinarith
  have herror :
      (fun ω =>
        _root_.GD.N0232.N0719.N0852.d010179 k sizes epsilon ω - target) =
        (fun ω => r ω - epsilon * h ω) := by
    funext ω
    unfold _root_.GD.N0232.N0719.N0852.d010179 _root_.GD.N0232.N0719.N0852.d010178 r h u
      _root_.GD.N0232.N0719.N1015.d010078 _root_.GD.N0232.N0719.N0900.d009111
    simp only [Pi.neg_apply]
    ring
  have hdiff :
      (∫ ω, (r ω - epsilon * h ω) ^ 2 ∂μ) -
        ∫ ω, (r ω) ^ 2 ∂μ < 0 := by
    rw [hid]
    simpa [C, B, add_comm] using hinc
  change
    (∫ ω,
        ((fun ω =>
          _root_.GD.N0232.N0719.N0852.d010179 k sizes epsilon ω - target) ω) ^ 2 ∂μ) <
      ∫ ω, (r ω) ^ 2 ∂μ
  rw [herror]
  change (∫ ω, (r ω - epsilon * h ω) ^ 2 ∂μ) <
    ∫ ω, (r ω) ^ 2 ∂μ
  linarith



theorem d010213
    {k : ℕ} {sizes : Fin k → ℕ}
    (hk : 3 ≤ k)
    (μ : Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)) (target gamma : ℝ)
    (hgamma : 0 ≤ gamma)
    (hresidual :
      Integrable (fun ω => (_root_.GD.N0232.N0719.N1015.d010078 target ω) ^ 2) μ)
    (hcross_integrable : ∀ triangle : Fin 3 ↪ Fin k,
      Integrable
        (fun ω => _root_.GD.N0232.N0719.N1015.d010078 target ω * _root_.GD.N0232.N0719.N1015.d010079 triangle ω) μ)
    (henergy_integrable : ∀ triangle : Fin 3 ↪ Fin k,
      Integrable (fun ω => (_root_.GD.N0232.N0719.N1015.d010079 triangle ω) ^ 2) μ)
    (hcross_negative : ∀ triangle : Fin 3 ↪ Fin k,
      _root_.GD.N0232.N0719.N1015.d010080 μ target triangle < 0)
    (hcapacity : ∀ triangle : Fin 3 ↪ Fin k,
      _root_.GD.N0232.N0719.N1015.d010081 μ triangle ≤
        gamma * (-_root_.GD.N0232.N0719.N1015.d010080 μ target triangle)) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N0852.d010179 k sizes (1 / (1 + gamma)) ω -
          target) ^ 2 ∂μ) <
      ∫ ω, (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - target) ^ 2 ∂μ := by
  have hden : 0 < 1 + gamma := by linarith
  apply _root_.GD.N0232.N0719.N0874.d010212
    hk μ target gamma (1 / (1 + gamma)) hgamma
  · exact one_div_pos.mpr hden
  · have hfrac : gamma / (1 + gamma) < 1 :=
      (div_lt_one hden).2 (by linarith)
    calc
      (1 / (1 + gamma)) * gamma = gamma / (1 + gamma) := by ring
      _ < 1 := hfrac
      _ < 2 := by norm_num
  · exact hresidual
  · exact hcross_integrable
  · exact henergy_integrable
  · exact hcross_negative
  · exact hcapacity

end

end GD.N0232.N0719.N0874
