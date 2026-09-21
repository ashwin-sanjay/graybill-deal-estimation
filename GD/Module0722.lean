import GD.Module0694
import GD.Module0721
import Mathlib.MeasureTheory.Constructions.Pi




















open MeasureTheory
open scoped BigOperators

namespace GD.N0232.N0719.N0851

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1015
open _root_.GD.N0232.N0719.N1018
open _root_.GD.N0232.N0719.N0852
open _root_.GD.N0232.N0719.N0874
open _root_.GD.N0232.N0719.N1024
open _root_.GD.N0137



def d010783
    {k : ℕ} (sizes : Fin k → ℕ) (σ : Equiv.Perm (Fin k)) :
    _root_.GD.N0232.N0719.d009173 k sizes ≃ᵐ _root_.GD.N0232.N0719.d009173 k (sizes ∘ σ) :=
  (MeasurableEquiv.piCongrLeft
    (fun i : Fin k => _root_.GD.N0137.d008894 (sizes i)) σ).symm

@[simp]
theorem d010784
    {k : ℕ} (sizes : Fin k → ℕ) (σ : Equiv.Perm (Fin k))
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) (i : Fin k) :
    _root_.GD.N0232.N0719.N0851.d010783 sizes σ ω i = ω (σ i) := by
  rfl


theorem d010785
    {k : ℕ} (sizes : Fin k → ℕ) (σ : Equiv.Perm (Fin k))
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0900.d009104 k (sizes ∘ σ) (_root_.GD.N0232.N0719.N0851.d010783 sizes σ ω) =
      _root_.GD.N0232.N0719.N0852.d010153 σ (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) := by
  ext i
  · rfl
  · rfl


theorem d010786
    {k : ℕ} (sizes : Fin k → ℕ) (σ : Equiv.Perm (Fin k))
    (location : ℝ) (scales : Fin k → ℝ) :
    (_root_.GD.N0232.N0719.d009176 k sizes location scales).map
        (_root_.GD.N0232.N0719.N0851.d010783 sizes σ) =
      _root_.GD.N0232.N0719.d009176 k (sizes ∘ σ) location (scales ∘ σ) := by
  let block : (i : Fin k) → Measure (_root_.GD.N0137.d008894 (sizes i)) :=
    fun i => _root_.GD.N0232.N0719.d009174 (sizes i) location (scales i)
  have hforward :=
    measurePreserving_piCongrLeft block σ
  have hbackward :=
    MeasurePreserving.symm
      (MeasurableEquiv.piCongrLeft
        (fun i : Fin k => _root_.GD.N0137.d008894 (sizes i)) σ)
      hforward
  change
    Measure.map
        (MeasurableEquiv.piCongrLeft
          (fun i : Fin k => _root_.GD.N0137.d008894 (sizes i)) σ).symm
        (Measure.pi block) =
      Measure.pi
        (fun i : Fin k =>
          _root_.GD.N0232.N0719.d009174 (sizes (σ i)) location (scales (σ i)))
  exact hbackward.map_eq


theorem d010787
    {k : ℕ} (sizes : Fin k → ℕ) (σ : Equiv.Perm (Fin k))
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0900.d009111 k (sizes ∘ σ) (_root_.GD.N0232.N0719.N0851.d010783 sizes σ ω) =
      _root_.GD.N0232.N0719.N0900.d009111 k sizes ω := by
  unfold _root_.GD.N0232.N0719.N0900.d009111
  rw [_root_.GD.N0232.N0719.N0851.d010785, _root_.GD.N0232.N0719.N0852.d010165]



theorem d010788
    {k : ℕ} (sizes : Fin k → ℕ) (σ : Equiv.Perm (Fin k))
    (triangle : Fin 3 ↪ Fin k) (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N1015.d010079 triangle (_root_.GD.N0232.N0719.N0851.d010783 sizes σ ω) =
      _root_.GD.N0232.N0719.N1015.d010079 (_root_.GD.N0232.N0719.N0852.d010159 σ triangle) ω := by
  unfold _root_.GD.N0232.N0719.N1015.d010079
  rw [_root_.GD.N0232.N0719.N0851.d010785, _root_.GD.N0232.N0719.N0852.d010175]



theorem d010789
    {k : ℕ} (hk : 3 ≤ k) (triangle : Fin 3 ↪ Fin k) :
    ∃ σ : Equiv.Perm (Fin k),
      _root_.GD.N0232.N0719.N0852.d010159 σ (_root_.GD.N0232.N0719.N1024.d010710 hk) = triangle := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (_root_.GD.N0232.N0719.N1024.d010710 hk : Fin 3 → Fin k) (triangle : Fin 3 → Fin k)
    (_root_.GD.N0232.N0719.N1024.d010710 hk).injective triangle.injective
  refine ⟨σ, ?_⟩
  ext j
  exact congrArg Fin.val (hσ j)



theorem d010790
    {k : ℕ} (sizes : Fin k → ℕ) (σ : Equiv.Perm (Fin k))
    (target : ℝ) (scales : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) target
        (_root_.GD.N0232.N0719.N0852.d010159 σ triangle) =
      _root_.GD.N0232.N0719.N1015.d010080
        (_root_.GD.N0232.N0719.d009176 k (sizes ∘ σ) 0 (scales ∘ σ))
        target triangle := by
  have hmap :=
    _root_.GD.N0232.N0719.N0851.d010786 sizes σ 0 scales
  unfold _root_.GD.N0232.N0719.N1015.d010080 _root_.GD.N0232.N0719.N1015.d010078 _root_.GD.N0232.N0719.N1015.d010079
  rw [← hmap]
  rw [integral_map_of_stronglyMeasurable
    (μ := _root_.GD.N0232.N0719.d009176 k sizes 0 scales)
    (φ := _root_.GD.N0232.N0719.N0851.d010783 sizes σ)
    (f := fun ω =>
      (_root_.GD.N0232.N0719.N0900.d009111 k (sizes ∘ σ) ω - target) *
        _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0900.d009104 k (sizes ∘ σ) ω))
    (_root_.GD.N0232.N0719.N0851.d010783 sizes σ).measurable
    (((_root_.GD.N0232.N0719.N0900.d009122 k (sizes ∘ σ)).sub measurable_const).mul
      ((_root_.GD.N0232.N0719.N1018.d010044 triangle).comp
        (_root_.GD.N0232.N0719.N0900.d009115 k (sizes ∘ σ)))).stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with ω
  rw [_root_.GD.N0232.N0719.N0851.d010787,
    _root_.GD.N0232.N0719.N0851.d010785, _root_.GD.N0232.N0719.N0852.d010175]


theorem d010791
    {k : ℕ} (sizes : Fin k → ℕ) (σ : Equiv.Perm (Fin k))
    (scales : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N1015.d010081 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales)
        (_root_.GD.N0232.N0719.N0852.d010159 σ triangle) =
      _root_.GD.N0232.N0719.N1015.d010081
        (_root_.GD.N0232.N0719.d009176 k (sizes ∘ σ) 0 (scales ∘ σ)) triangle := by
  have hmap :=
    _root_.GD.N0232.N0719.N0851.d010786 sizes σ 0 scales
  unfold _root_.GD.N0232.N0719.N1015.d010081 _root_.GD.N0232.N0719.N1015.d010079
  rw [← hmap]
  rw [integral_map_of_stronglyMeasurable
    (μ := _root_.GD.N0232.N0719.d009176 k sizes 0 scales)
    (φ := _root_.GD.N0232.N0719.N0851.d010783 sizes σ)
    (f := fun ω =>
      _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0900.d009104 k (sizes ∘ σ) ω) ^ 2)
    (_root_.GD.N0232.N0719.N0851.d010783 sizes σ).measurable
    (((_root_.GD.N0232.N0719.N1018.d010044 triangle).comp
      (_root_.GD.N0232.N0719.N0900.d009115 k (sizes ∘ σ))).pow_const 2).stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with ω
  rw [_root_.GD.N0232.N0719.N0851.d010785, _root_.GD.N0232.N0719.N0852.d010175]



def d010792
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (σ : Equiv.Perm (Fin k)) : ℝ :=
  _root_.GD.N0232.N0719.N0950.d010597 (by omega)
    (_root_.GD.N0232.N0719.N0954.d009355 (sizes ∘ σ))
    (_root_.GD.N0232.N0719.N1024.d010710 hk)




def d010793
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin k), _root_.GD.N0232.N0719.N0851.d010792 hk sizes σ

theorem d010794
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (σ : Equiv.Perm (Fin k)) :
    0 < _root_.GD.N0232.N0719.N0851.d010792 hk sizes σ := by
  unfold _root_.GD.N0232.N0719.N0851.d010792
  apply _root_.GD.N0232.N0719.N0950.d010598
  intro i
  exact _root_.GD.N0232.N0719.N0954.d009358
    (fun j => hsizes (σ j)) i

theorem d010795
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i) :
    0 < _root_.GD.N0232.N0719.N0851.d010793 hk sizes := by
  unfold _root_.GD.N0232.N0719.N0851.d010793
  exact Finset.sum_pos'
    (fun σ _ => (_root_.GD.N0232.N0719.N0851.d010794 hk sizes hsizes σ).le)
    ⟨Equiv.refl (Fin k), Finset.mem_univ _,
      _root_.GD.N0232.N0719.N0851.d010794 hk sizes hsizes _⟩

theorem d010796
    {k : ℕ} (hk : 3 ≤ k) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (σ : Equiv.Perm (Fin k)) :
    _root_.GD.N0232.N0719.N0851.d010792 hk sizes σ ≤
      _root_.GD.N0232.N0719.N0851.d010793 hk sizes := by
  unfold _root_.GD.N0232.N0719.N0851.d010793
  exact Finset.single_le_sum
    (fun τ _ => (_root_.GD.N0232.N0719.N0851.d010794 hk sizes hsizes τ).le)
    (Finset.mem_univ σ)



theorem d010797
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) 0 triangle < 0 ∧
      _root_.GD.N0232.N0719.N1015.d010081 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) triangle ≤
        _root_.GD.N0232.N0719.N0851.d010793 hk sizes *
          (-_root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) 0 triangle) := by
  obtain ⟨σ, hσ⟩ :=
    _root_.GD.N0232.N0719.N0851.d010789 hk triangle
  have hprojective :=
    _root_.GD.N0232.N0719.N0912.d010782
      hk (sizes ∘ σ) (fun i => hsizes (σ i))
      (scales ∘ σ) (fun i => hscales (σ i))
  have hcrossTransport :=
    _root_.GD.N0232.N0719.N0851.d010790 sizes σ 0 scales (_root_.GD.N0232.N0719.N1024.d010710 hk)
  have henergyTransport :=
    _root_.GD.N0232.N0719.N0851.d010791 sizes σ scales (_root_.GD.N0232.N0719.N1024.d010710 hk)
  rw [hσ] at hcrossTransport henergyTransport
  have hcross :
      _root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) 0 triangle < 0 := by
    rw [hcrossTransport]
    simpa [_root_.GD.N0232.N0719.N1024.d010712,
      _root_.GD.N0232.N0719.N1024.d010711] using hprojective.1
  have hbranch :
      _root_.GD.N0232.N0719.N1015.d010081 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) triangle ≤
        _root_.GD.N0232.N0719.N0851.d010792 hk sizes σ *
          (-_root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) 0 triangle) := by
    rw [henergyTransport, hcrossTransport]
    simpa [_root_.GD.N0232.N0719.N1024.d010713,
      _root_.GD.N0232.N0719.N1024.d010712, _root_.GD.N0232.N0719.N1024.d010711,
      _root_.GD.N0232.N0719.N0851.d010792] using hprojective.2
  refine ⟨hcross, hbranch.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (_root_.GD.N0232.N0719.N0851.d010796
      hk sizes hsizes σ)
    (neg_nonneg.mpr hcross.le)



theorem d010798
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.N0874.d010204
        (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) 0 < 0 ∧
      _root_.GD.N0232.N0719.N0874.d010205
          (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) ≤
        _root_.GD.N0232.N0719.N0851.d010793 hk sizes *
          (-_root_.GD.N0232.N0719.N0874.d010204
            (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) 0) := by
  apply _root_.GD.N0232.N0719.N0874.d010209 hk
  · exact (_root_.GD.N0232.N0719.N0851.d010795 hk sizes hsizes).le
  · intro triangle
    exact _root_.GD.N0232.N0719.N0910.d010296
      sizes (by omega) hsizes 0 scales hscales triangle
  · intro triangle
    exact (_root_.GD.N0232.N0719.N0910.d010295
      sizes (by omega) hsizes 0 scales hscales triangle).integrable_sq
  · intro triangle
    exact (_root_.GD.N0232.N0719.N0851.d010797
      hk sizes hsizes scales hscales triangle).1
  · intro triangle
    exact (_root_.GD.N0232.N0719.N0851.d010797
      hk sizes hsizes scales hscales triangle).2





theorem d010799
    {k : ℕ} (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (triangle : Fin 3 ↪ Fin k)
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N1015.d010078 location
          (_root_.GD.N0232.N0719.N0900.d009095 k sizes location 1 ω) *
        _root_.GD.N0232.N0719.N1015.d010079 triangle
          (_root_.GD.N0232.N0719.N0900.d009095 k sizes location 1 ω) =
      _root_.GD.N0232.N0719.N1015.d010078 0 ω * _root_.GD.N0232.N0719.N1015.d010079 triangle ω := by
  have hk0 : 0 < k := by omega
  have hsizes0 : ∀ i, 0 < sizes i := fun i =>
    Nat.zero_lt_of_lt (hsizes i)
  have hbase :=
    _root_.GD.N0232.N0719.N0900.d009146
      hk0 hsizes0 location (scale := 1) one_ne_zero ω
  have hsummary :=
    _root_.GD.N0232.N0719.N0900.d009139 hsizes0 location 1 ω
  have hcorrection :=
    _root_.GD.N0232.N0719.N1018.d010057
      hk0 triangle location (scale := 1) one_ne_zero
      (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)
  unfold _root_.GD.N0232.N0719.N1015.d010078 _root_.GD.N0232.N0719.N1015.d010079
  rw [hbase, hsummary, hcorrection]
  ring


theorem d010800
    {k : ℕ} (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
        location triangle =
      _root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) 0 triangle := by
  have hmap := _root_.GD.N0232.N0719.d009178
    k sizes location scales
  unfold _root_.GD.N0232.N0719.N1015.d010080 _root_.GD.N0232.N0719.N1015.d010078 _root_.GD.N0232.N0719.N1015.d010079
  rw [← hmap]
  rw [integral_map_of_stronglyMeasurable
    (μ := _root_.GD.N0232.N0719.d009176 k sizes 0 scales)
    (φ := _root_.GD.N0232.N0719.N0900.d009095 k sizes location 1)
    (f := fun ω =>
      (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) *
        _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω))
    (_root_.GD.N0232.N0719.N0900.d009112 k sizes location 1)
    (((_root_.GD.N0232.N0719.N0900.d009122 k sizes).sub measurable_const).mul
      ((_root_.GD.N0232.N0719.N1018.d010044 triangle).comp
        (_root_.GD.N0232.N0719.N0900.d009115 k sizes))).stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with ω
  exact _root_.GD.N0232.N0719.N0851.d010799
    sizes hk hsizes location triangle ω


theorem d010801
    {k : ℕ} (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N1015.d010081 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
        triangle =
      _root_.GD.N0232.N0719.N1015.d010081 (_root_.GD.N0232.N0719.d009176 k sizes 0 scales) triangle := by
  have hmap := _root_.GD.N0232.N0719.d009178
    k sizes location scales
  unfold _root_.GD.N0232.N0719.N1015.d010081 _root_.GD.N0232.N0719.N1015.d010079
  rw [← hmap]
  rw [integral_map_of_stronglyMeasurable
    (μ := _root_.GD.N0232.N0719.d009176 k sizes 0 scales)
    (φ := _root_.GD.N0232.N0719.N0900.d009095 k sizes location 1)
    (f := fun ω => _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) ^ 2)
    (_root_.GD.N0232.N0719.N0900.d009112 k sizes location 1)
    (((_root_.GD.N0232.N0719.N1018.d010044 triangle).comp
      (_root_.GD.N0232.N0719.N0900.d009115 k sizes)).pow_const 2).stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with ω
  have hsizes0 : ∀ i, 0 < sizes i := fun i =>
    Nat.zero_lt_of_lt (hsizes i)
  have hsummary := _root_.GD.N0232.N0719.N0900.d009139 hsizes0 location 1 ω
  have hcorrection := _root_.GD.N0232.N0719.N1018.d010057
    (by omega : 0 < k) triangle location (scale := 1) one_ne_zero
    (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)
  rw [hsummary, hcorrection]
  ring



theorem d010802
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    (triangle : Fin 3 ↪ Fin k) :
    _root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
        location triangle < 0 ∧
      _root_.GD.N0232.N0719.N1015.d010081 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
          triangle ≤
        _root_.GD.N0232.N0719.N0851.d010793 hk sizes *
          (-_root_.GD.N0232.N0719.N1015.d010080 (_root_.GD.N0232.N0719.d009176 k sizes location scales)
            location triangle) := by
  have hzero := _root_.GD.N0232.N0719.N0851.d010797
    hk sizes hsizes scales hscales triangle
  rw [_root_.GD.N0232.N0719.N0851.d010800 sizes hk hsizes location scales triangle,
    _root_.GD.N0232.N0719.N0851.d010801 sizes hk hsizes location scales triangle]
  exact hzero







theorem d010803
    {k : ℕ} (hk : 3 ≤ k)
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    (∫ ω,
        (_root_.GD.N0232.N0719.N0852.d010179 k sizes
              (1 / (1 + _root_.GD.N0232.N0719.N0851.d010793 hk sizes)) ω -
            location) ^ 2
          ∂_root_.GD.N0232.N0719.d009176 k sizes location scales) <
      ∫ ω,
        (_root_.GD.N0232.N0719.N0900.d009111 k sizes ω - location) ^ 2
          ∂_root_.GD.N0232.N0719.d009176 k sizes location scales := by
  apply _root_.GD.N0232.N0719.N0874.d010213 hk
  · exact (_root_.GD.N0232.N0719.N0851.d010795 hk sizes hsizes).le
  · exact (_root_.GD.N0232.N0719.N0910.d010294
      sizes (by omega) hsizes location scales).integrable_sq
  · intro triangle
    exact _root_.GD.N0232.N0719.N0910.d010296
      sizes (by omega) hsizes location scales hscales triangle
  · intro triangle
    exact (_root_.GD.N0232.N0719.N0910.d010295
      sizes (by omega) hsizes location scales hscales triangle).integrable_sq
  · intro triangle
    exact (_root_.GD.N0232.N0719.N0851.d010802
      hk sizes hsizes location scales hscales triangle).1
  · intro triangle
    exact (_root_.GD.N0232.N0719.N0851.d010802
      hk sizes hsizes location scales hscales triangle).2

end


end GD.N0232.N0719.N0851
