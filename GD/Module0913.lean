import GD.Module0791
import GD.Module0632
import GD.Module0744
import GD.Module0822
import GD.Module0912

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace GD.N0076.N0310

noncomputable section

open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0932

variable (k : ℕ) (sizes : Fin k → ℕ)

def d014203 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : Measure (_root_.GD.N0232.N0719.N0859.d010811 k sizes) :=
  Measure.pi (fun i => Measure.pi (fun _ : Fin (sizes i) =>
    gaussianReal θ.location (_root_.GD.N0232.N0719.N0932.d009193 (θ.scale i))))

theorem d014204 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes θ = _root_.GD.N0076.N0310.d014203 k sizes θ := by
  simp only [_root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.d009176, _root_.GD.N0076.N0310.d014203,
    _root_.GD.N0232.N0719.N0932.d009211]

theorem d014205 (n : ℕ) (x : _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009084 x = (∑ j, x j) / (n : ℝ) := by
  simp [_root_.GD.N0107.d009084, _root_.GD.N0126.d006420,
    _root_.GD.N0126.d006419]

theorem d014206 (n : ℕ) (x : _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009085 x =
      (∑ j, (x j - _root_.GD.N0107.d009084 x) ^ 2) / ((n - 1 : ℕ) : ℝ) := rfl

def d014207 (ω : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    (Fin k → ℝ) × (Fin k → ℝ) :=
  (fun i => _root_.GD.N0107.d009084 (ω i), fun i => _root_.GD.N0107.d009085 (ω i))

def d014208 (s : (Fin k → ℝ) × (Fin k → ℝ)) : _root_.GD.N0232.N0719.N0900.d009096 k :=
  ⟨s.1, fun i => s.2 i / (sizes i : ℝ)⟩

def d014209 (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    (Fin k → ℝ) × (Fin k → ℝ) :=
  (s.mean, fun i => s.meanVariance i * (sizes i : ℝ))

@[fun_prop] theorem d014210 : Measurable (_root_.GD.N0076.N0310.d014207 k sizes) := by
  unfold _root_.GD.N0076.N0310.d014207
  fun_prop

@[fun_prop] theorem d014211 : Measurable (_root_.GD.N0076.N0310.d014208 k sizes) := by
  rw [measurable_comap_iff]
  change Measurable (fun s : (Fin k → ℝ) × (Fin k → ℝ) =>
    (s.1, fun i => s.2 i / (sizes i : ℝ)))
  fun_prop

@[fun_prop] theorem d014212 : Measurable (_root_.GD.N0076.N0310.d014209 k sizes) := by
  unfold _root_.GD.N0076.N0310.d014209
  fun_prop

def d014213 (hsizes : ∀ i, sizes i ≠ 0) :
    ((Fin k → ℝ) × (Fin k → ℝ)) ≃ᵐ _root_.GD.N0232.N0719.N0900.d009096 k where
  toFun := _root_.GD.N0076.N0310.d014208 k sizes
  invFun := _root_.GD.N0076.N0310.d014209 k sizes
  left_inv s := by
    ext i <;> simp [_root_.GD.N0076.N0310.d014208, _root_.GD.N0076.N0310.d014209, hsizes i]
  right_inv s := by
    ext i <;> simp [_root_.GD.N0076.N0310.d014208, _root_.GD.N0076.N0310.d014209, hsizes i]
  measurable_toFun := _root_.GD.N0076.N0310.d014211 k sizes
  measurable_invFun := _root_.GD.N0076.N0310.d014212 k sizes

theorem d014214 (ω : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    _root_.GD.N0232.N0719.N0900.d009104 k sizes ω =
      _root_.GD.N0076.N0310.d014208 k sizes (_root_.GD.N0076.N0310.d014207 k sizes ω) := rfl

theorem d014215
    (hsizes : ∀ i, 2 ≤ sizes i) (ω : _root_.GD.N0232.N0719.N0859.d010811 k sizes) :
    _root_.GD.N0076.N0310.d014207 k sizes ω =
      _root_.GD.N0076.N0310.d014209 k sizes (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) := by
  have h := (_root_.GD.N0076.N0310.d014213 k sizes (fun i => by have := hsizes i; omega)).left_inv
    (_root_.GD.N0076.N0310.d014207 k sizes ω)
  exact h.symm

def d014216 (ω : _root_.GD.N0232.N0719.N0859.d010811 k sizes) : ℝ :=
  (∑ i, (sizes i : ℝ) * _root_.GD.N0107.d009084 (ω i) / _root_.GD.N0107.d009085 (ω i)) /
    (∑ i, (sizes i : ℝ) / _root_.GD.N0107.d009085 (ω i))

@[fun_prop] theorem d014217 : Measurable (_root_.GD.N0076.N0310.d014216 k sizes) := by
  unfold _root_.GD.N0076.N0310.d014216
  fun_prop

theorem d014218
    (hsizes : ∀ i, 2 ≤ sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ∀ᵐ ω ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, ∀ i, 0 < _root_.GD.N0107.d009085 (ω i) := by
  apply ae_all_iff.mpr
  intro i
  filter_upwards [_root_.GD.N0232.N0719.N0832.d012011
    k sizes hsizes θ i] with ω hω
  change 0 < @_root_.GD.N0126.d006422 (Fin (sizes i)) _ (ω i) /
    ((sizes i - 1 : ℕ) : ℝ)
  apply div_pos hω
  exact_mod_cast (show 0 < sizes i - 1 by have := hsizes i; omega)

theorem d014219
    (hk : 0 < k) (hsizes : ∀ i, 2 ≤ sizes i) (ω : _root_.GD.N0232.N0719.N0859.d010811 k sizes)
    (hpos : ∀ i, 0 < _root_.GD.N0107.d009085 (ω i)) :
    _root_.GD.N0076.N0310.d014216 k sizes ω = _root_.GD.N0232.N0719.N0859.d010815 k sizes ω := by
  let s := _root_.GD.N0232.N0719.N0900.d009104 k sizes ω
  have hsize (i : Fin k) : 0 < (sizes i : ℝ) := by
    exact_mod_cast (show 0 < sizes i by have := hsizes i; omega)
  have hprec (i : Fin k) : _root_.GD.N0232.N0719.N0900.d009106 s i =
      (sizes i : ℝ) / _root_.GD.N0107.d009085 (ω i) := by
    dsimp [s, _root_.GD.N0232.N0719.N0900.d009106, _root_.GD.N0232.N0719.N0900.d009104,
      _root_.GD.N0232.N0719.N0900.d009103]
    rw [_root_.GD.N0232.N0719.N0900.d009127 (div_pos (hpos i) (hsize i))]
    exact inv_div _ _
  have hden : 0 < ∑ i, (sizes i : ℝ) / _root_.GD.N0107.d009085 (ω i) := by
    apply Finset.sum_pos'
    · intro i _
      exact (div_pos (hsize i) (hpos i)).le
    · exact ⟨⟨0, hk⟩, Finset.mem_univ _, div_pos (hsize _) (hpos _)⟩
  have htotal : _root_.GD.N0232.N0719.N0900.d009107 s =
      ∑ i, (sizes i : ℝ) / _root_.GD.N0107.d009085 (ω i) := by
    unfold _root_.GD.N0232.N0719.N0900.d009107
    simp only [hprec]
  change _root_.GD.N0076.N0310.d014216 k sizes ω = _root_.GD.N0232.N0719.N0900.d009110 s
  unfold _root_.GD.N0076.N0310.d014216 _root_.GD.N0232.N0719.N0900.d009110
  simp only [_root_.GD.N0232.N0719.N0900.d009108, hprec, htotal, hden.ne', ↓reduceIte]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [s, _root_.GD.N0232.N0719.N0900.d009104, _root_.GD.N0232.N0719.N0900.d009102]
  ring

theorem d014220
    (hk : 2 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0076.N0310.d014216 k sizes =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] _root_.GD.N0232.N0719.N0859.d010815 k sizes := by
  filter_upwards [_root_.GD.N0076.N0310.d014218 k sizes hsizes θ] with ω hω
  exact _root_.GD.N0076.N0310.d014219 k sizes (by omega) hsizes ω hω

theorem d014221
    (hk : 2 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0076.N0310.d014216 k sizes =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0232.N0719.N0859.d010815 k sizes :=
  _root_.GD.N0076.N0310.d014220 k sizes hk hsizes (_root_.GD.N0232.N0719.N0859.d010810 k)

theorem d014222 (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    {d e : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ} :
    d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] e ↔
      d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] e :=
  _root_.GD.N0232.N0719.d009184 k sizes θ.location θ.scale θ.scale_pos

theorem d014223 {d e : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ} :
    d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] e ↔
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] e := by
  constructor
  · intro h θ
    exact (_root_.GD.N0076.N0310.d014222 k sizes θ).mpr h
  · intro h
    exact h (_root_.GD.N0232.N0719.N0859.d010810 k)

def d014224 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((d ω - θ.location) ^ 2) ∂_root_.GD.N0076.N0310.d014203 k sizes θ

theorem d014225 (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) :
    _root_.GD.N0076.N0310.d014224 k sizes θ d = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d := by
  rw [_root_.GD.N0076.N0310.d014224, ← _root_.GD.N0076.N0310.d014204]
  rfl

theorem d014226 (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : Integrable (fun ω => (d ω - θ.location) ^ 2) (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d =
      ENNReal.ofReal (∫ ω, (d ω - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) :=
  (ofReal_integral_eq_lintegral_ofReal hd
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm

theorem d014227 (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    {d e : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hde : d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] e) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ e :=
  _root_.GD.N0232.N0719.N0896.d011094 k sizes θ
    ((_root_.GD.N0076.N0310.d014222 k sizes θ).mpr hde)

theorem d014228
    (hk : 2 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0076.N0310.d014224 k sizes θ (_root_.GD.N0076.N0310.d014216 k sizes) =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes) := by
  rw [_root_.GD.N0076.N0310.d014225]
  exact _root_.GD.N0076.N0310.d014227 k sizes θ
    (_root_.GD.N0076.N0310.d014221 k sizes hk hsizes)

abbrev d014229 := {d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ // Measurable d}

def d014230 : Setoid (_root_.GD.N0076.N0310.d014229 k sizes) where
  r d e := d.val =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] e.val
  iseqv := ⟨fun _ => Filter.EventuallyEq.rfl,
    fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

def d014231 := Quotient (_root_.GD.N0076.N0310.d014230 k sizes)

def d014232 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0076.N0310.d014231 k sizes → ℝ≥0∞ :=
  Quotient.lift (fun d : _root_.GD.N0076.N0310.d014229 k sizes => _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d.val)
    (fun _ _ h => _root_.GD.N0076.N0310.d014227 k sizes θ h)

theorem d014233 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : Measurable d) :
    _root_.GD.N0076.N0310.d014232 k sizes θ (Quotient.mk (_root_.GD.N0076.N0310.d014230 k sizes) ⟨d, hd⟩) =
      _root_.GD.N0076.N0310.d014224 k sizes θ d := (_root_.GD.N0076.N0310.d014225 k sizes θ d).symm

theorem d014234 (q : _root_.GD.N0076.N0310.d014231 k sizes) :
    ∃ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ, ∃ hd : Measurable d,
      Quotient.mk (_root_.GD.N0076.N0310.d014230 k sizes) ⟨d, hd⟩ = q := by
  obtain ⟨d, rfl⟩ := Quotient.exists_rep q
  exact ⟨d.val, d.property, rfl⟩

theorem d014235
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hd : Measurable d)
    (hfinite : _root_.GD.N0076.N0310.d014224 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d ≠ ⊤) :
    MemLp d 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  apply _root_.GD.N0232.N0719.N0896.d011095
    k sizes d hd
  rwa [_root_.GD.N0076.N0310.d014225] at hfinite

theorem d014236 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : MemLp d 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0076.N0310.d014224 k sizes θ d = _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (MemLp.toLp d hd) := by
  rw [_root_.GD.N0076.N0310.d014225]
  exact _root_.GD.N0232.N0719.N0859.d010841 k sizes θ d hd

theorem d014237
    (hk : 2 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes θ = _root_.GD.N0076.N0310.d014203 k sizes θ ∧
    (∀ ω, _root_.GD.N0076.N0310.d014207 k sizes ω =
      _root_.GD.N0076.N0310.d014209 k sizes (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)) ∧
    (∀ᵐ ω ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, ∀ i, 0 < _root_.GD.N0107.d009085 (ω i)) ∧
    _root_.GD.N0076.N0310.d014216 k sizes =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] _root_.GD.N0232.N0719.N0859.d010815 k sizes ∧
    (∀ d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      _root_.GD.N0076.N0310.d014224 k sizes θ d = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d) ∧
    (∀ d e : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      d =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] e ↔
        d =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] e) :=
  ⟨_root_.GD.N0076.N0310.d014204 k sizes θ,
    _root_.GD.N0076.N0310.d014215 k sizes hsizes,
    _root_.GD.N0076.N0310.d014218 k sizes hsizes θ,
    _root_.GD.N0076.N0310.d014220 k sizes hk hsizes θ,
    _root_.GD.N0076.N0310.d014225 k sizes θ,
    fun _ _ => _root_.GD.N0076.N0310.d014222 k sizes θ⟩

namespace N0759

open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1497

abbrev d014238 := _root_.GD.N0232.N0720.N1080.d014168
abbrev d014239 (m n : ℕ) :=
  _root_.GD.N0232.N0720.N1080.d014170 m n

def d014240 (θ : _root_.GD.N0076.N0310.N0759.d014238) : _root_.GD.N0232.N0719.N0859.d010809 2 where
  location := θ.location
  scale := ![θ.scale₁, θ.scale₂]
  scale_pos i := by
    fin_cases i
    · exact θ.scale₁_pos
    · exact θ.scale₂_pos

theorem d014241 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∀ i, 2 ≤ _root_.GD.N0232.N0720.N1467.d012537 m n i := by
  intro i
  fin_cases i
  · exact hm
  · exact hn

theorem d014242 (m n : ℕ) (θ : _root_.GD.N0076.N0310.N0759.d014238) :
    MeasurePreserving (_root_.GD.N0232.N0720.N1467.d012541 m n)
      (_root_.GD.N0232.N0720.N1080.d014171 m n θ)
      (_root_.GD.N0232.N0719.N0859.d010812 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) (_root_.GD.N0076.N0310.N0759.d014240 θ)) :=
  _root_.GD.N0232.N0720.N1497.d012552 m n θ.location θ.scale₁ θ.scale₂

theorem d014243 (m n : ℕ) (θ : _root_.GD.N0076.N0310.N0759.d014238)
    (d : _root_.GD.N0232.N0719.N0859.d010811 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) → ℝ) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ
      (d ∘ _root_.GD.N0232.N0720.N1467.d012541 m n) =
      _root_.GD.N0232.N0719.N0859.d010840 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) (_root_.GD.N0076.N0310.N0759.d014240 θ) d :=
  (_root_.GD.N0076.N0310.N0759.d014242 m n θ).lintegral_comp_emb
    (_root_.GD.N0232.N0720.N1467.d012540 m n).symm.measurableEmbedding
    (fun ω => ENNReal.ofReal ((d ω - θ.location) ^ 2))

def d014244 (m n : ℕ) :
    {d : _root_.GD.N0076.N0310.N0759.d014239 m n → ℝ // Measurable d} ≃
      _root_.GD.N0076.N0310.d014229 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) where
  toFun d := ⟨d.val ∘ _root_.GD.N0232.N0720.N1467.d012540 m n,
    d.property.comp (_root_.GD.N0232.N0720.N1467.d012540 m n).measurable⟩
  invFun d := ⟨d.val ∘ _root_.GD.N0232.N0720.N1467.d012541 m n,
    d.property.comp (_root_.GD.N0232.N0720.N1497.d012554 m n)⟩
  left_inv d := by
    apply Subtype.ext
    funext ω
    exact congrArg d.val (_root_.GD.N0232.N0720.N1467.d012549 m n ω)
  right_inv d := by
    apply Subtype.ext
    funext ω
    exact congrArg d.val ((_root_.GD.N0232.N0720.N1467.d012540 m n).symm_apply_apply ω)

theorem d014245 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (θ : _root_.GD.N0076.N0310.N0759.d014238) :
    _root_.GD.N0076.N0310.d014216 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) ∘ _root_.GD.N0232.N0720.N1467.d012541 m n =ᵐ[
      _root_.GD.N0232.N0720.N1080.d014171 m n θ]
      _root_.GD.N0232.N0720.N1080.d014175 m n := by
  have hpos := (_root_.GD.N0076.N0310.N0759.d014242 m n θ).quasiMeasurePreserving.ae
    (_root_.GD.N0076.N0310.d014218 2 (_root_.GD.N0232.N0720.N1467.d012537 m n)
      (_root_.GD.N0076.N0310.N0759.d014241 m n hm hn) (_root_.GD.N0076.N0310.N0759.d014240 θ))
  filter_upwards [hpos] with ω hω
  have hx : 0 < _root_.GD.N0107.d009085 ω.1 := hω 0
  have hy : 0 < _root_.GD.N0107.d009085 ω.2 := hω 1
  have hm' : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsum : 0 < (m : ℝ) / _root_.GD.N0107.d009085 ω.1 +
      (n : ℝ) / _root_.GD.N0107.d009085 ω.2 :=
    add_pos (div_pos hm' hx) (div_pos hn' hy)
  have hsum' : 0 < _root_.GD.N0107.d009085 ω.1 / (m : ℝ) +
      _root_.GD.N0107.d009085 ω.2 / (n : ℝ) :=
    add_pos (div_pos hx hm') (div_pos hy hn')
  simp only [Function.comp_apply, _root_.GD.N0076.N0310.d014216, Fin.sum_univ_two,
    _root_.GD.N0232.N0720.N1467.d012538, _root_.GD.N0232.N0720.N1467.d012539,
    _root_.GD.N0232.N0720.N1467.d012543, _root_.GD.N0232.N0720.N1467.d012544,
    _root_.GD.N0232.N0720.N1080.d014175,
    _root_.GD.N0107.d012733, _root_.GD.N0107.d009091, _root_.GD.N0107.d009090]
  field_simp [hm'.ne', hn'.ne', hx.ne', hy.ne', hsum.ne', hsum'.ne']
  ring

theorem d014246 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (θ : _root_.GD.N0076.N0310.N0759.d014238) :
    _root_.GD.N0232.N0719.N0859.d010815 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) ∘ _root_.GD.N0232.N0720.N1467.d012541 m n =ᵐ[
      _root_.GD.N0232.N0720.N1080.d014171 m n θ]
      _root_.GD.N0232.N0720.N1080.d014175 m n := by
  have h := (_root_.GD.N0076.N0310.N0759.d014242 m n θ).quasiMeasurePreserving.ae
    (_root_.GD.N0076.N0310.d014220 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) (by omega)
      (_root_.GD.N0076.N0310.N0759.d014241 m n hm hn) (_root_.GD.N0076.N0310.N0759.d014240 θ))
  filter_upwards [h, _root_.GD.N0076.N0310.N0759.d014245 m n hm hn θ] with ω hω hω'
  exact hω.symm.trans hω'

theorem d014247 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (θ : _root_.GD.N0076.N0310.N0759.d014238) :
    _root_.GD.N0232.N0719.N0859.d010840 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) (_root_.GD.N0076.N0310.N0759.d014240 θ)
      (_root_.GD.N0232.N0719.N0859.d010815 2 (_root_.GD.N0232.N0720.N1467.d012537 m n)) =
      _root_.GD.N0232.N0720.N1080.d014197 m n θ
        (_root_.GD.N0232.N0720.N1080.d014175 m n) := by
  rw [← _root_.GD.N0076.N0310.N0759.d014243]
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0076.N0310.N0759.d014246 m n hm hn θ] with ω hω
  rw [hω]

end N0759

end
end GD.N0076.N0310

#print axioms _root_.GD.N0076.N0310.d014213
#print axioms _root_.GD.N0076.N0310.d014237
#print axioms _root_.GD.N0076.N0310.d014228
#print axioms _root_.GD.N0076.N0310.d014233
#print axioms _root_.GD.N0076.N0310.d014234
#print axioms _root_.GD.N0076.N0310.d014235
#print axioms _root_.GD.N0076.N0310.d014236
#print axioms _root_.GD.N0076.N0310.N0759.d014242
#print axioms _root_.GD.N0076.N0310.N0759.d014243
#print axioms _root_.GD.N0076.N0310.N0759.d014244
#print axioms _root_.GD.N0076.N0310.N0759.d014247
