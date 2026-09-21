import GD.Module0808
import GD.Module0807
import GD.Module0811











open MeasureTheory Set
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0232.N0719.N0966

noncomputable section

open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0965 _root_.GD.N0232.N0719.N0967
open _root_.GD.N0232.N0719.N0843
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0632
open _root_.GD.N0230.N0611

variable (k : ℕ) (sizes : Fin k → ℕ)

def d012351 (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0965.d012292 (k := k) (sizes := sizes)
    (fun θ : F ↦ θ.val) (fun θ ↦ w θ.val)

theorem d012352
    (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    _root_.GD.N0232.N0719.N0966.d012351 k sizes F w ≤ ‖p‖ ^ 2 + ∑ θ ∈ F, w θ * (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ p).toReal := by
  classical
  have h := _root_.GD.N0232.N0719.N0965.d012295
    (k := k) (sizes := sizes) (fun θ : F ↦ θ.val) (fun θ ↦ w θ.val)
    (fun θ ↦ hw θ.val θ.property) p (fun θ ↦ hp θ.val)
  have hnonneg : 0 ≤ ∫ ω,
      _root_.GD.N0232.N0719.N0965.d012275 (fun θ : F ↦ θ.val) (fun θ ↦ w θ.val) ω *
        (p ω - _root_.GD.N0232.N0719.N0965.d012276 (fun θ : F ↦ θ.val)
          (fun θ ↦ w θ.val) ω) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
    apply integral_nonneg
    intro ω
    apply mul_nonneg _ (sq_nonneg _)
    exact (_root_.GD.N0230.N0617.d000169
      (fun θ : F ↦ w θ.val) (_root_.GD.N0232.N0719.N0965.d012273 (fun θ : F ↦ θ.val))
      (fun θ ↦ hw θ.val θ.property) (_root_.GD.N0232.N0719.N0965.d012279 _) ω).le
  simp only [_root_.GD.N0232.N0719.N0965.d012291] at h
  rw [Finset.sum_coe_sort F (fun θ ↦ w θ * (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ p).toReal)] at h
  change _ = _ + _root_.GD.N0232.N0719.N0966.d012351 k sizes F w at h
  linarith

theorem d012353
    (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ) :
    ∃ p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes),
      _root_.GD.N0232.N0719.N0896.d011103 k sizes p ∧
      ‖p‖ ^ 2 + ∑ θ ∈ F, w θ * (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ p).toReal = _root_.GD.N0232.N0719.N0966.d012351 k sizes F w := by
  classical
  let packet : F → _root_.GD.N0232.N0719.N0859.d010809 k := fun θ ↦ θ.val
  let weight : F → ℝ := fun θ ↦ w θ.val
  have hw' : ∀ θ, 0 ≤ weight θ := fun θ ↦ hw θ.val θ.property
  let p := _root_.GD.N0232.N0719.N0965.d012286 (k := k) (sizes := sizes) packet weight hw'
  refine ⟨p, _root_.GD.N0232.N0719.N0965.d012288 packet weight hw', ?_⟩
  have h : ‖p‖ ^ 2 + (∑ θ : F, w θ.val * (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ.val p).toReal) =
      _root_.GD.N0232.N0719.N0966.d012351 k sizes F w :=
    _root_.GD.N0232.N0719.N0965.d012297 (k := k) (sizes := sizes) packet weight hw'
  rw [Finset.sum_coe_sort F (fun θ ↦ w θ * (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ p).toReal)] at h
  exact h

theorem d012354
    (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ) :
    0 ≤ _root_.GD.N0232.N0719.N0966.d012351 k sizes F w := by
  obtain ⟨p, _, heq⟩ := _root_.GD.N0232.N0719.N0966.d012353 k sizes F w hw
  rw [← heq]
  exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun θ hθ ↦
    mul_nonneg (hw θ hθ) ENNReal.toReal_nonneg)

theorem d012355
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ) (hC : 0 ≤ C) :
    (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ C).Nonempty ↔
      ∀ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0232.N0719.N0966.d012351 k sizes F w ≤
          C * γ.value (_root_.GD.N0232.N0719.N0859.d010810 k) + ∑ θ ∈ F, w θ * (C * γ.value θ) := by
  constructor
  · rintro ⟨p, hp⟩ F w hw
    have hpF : _root_.GD.N0232.N0719.N0896.d011103 k sizes p := _root_.GD.N0232.N0719.N0843.d012219 k sizes γ hp
    apply (_root_.GD.N0232.N0719.N0966.d012352 k sizes F w hw p hpF).trans
    apply add_le_add
    · exact _root_.GD.N0232.N0719.N0843.d012220 k sizes γ hC hp
    · apply Finset.sum_le_sum
      intro θ hθ
      apply mul_le_mul_of_nonneg_left _ (hw θ hθ)
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hp θ)).trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg hC (γ.positive θ).le))
  · intro htest
    apply (_root_.GD.N0232.N0719.N0967.d012301 k sizes hk hsizes γ C hC).mpr
    intro F w hw a ha
    by_contra hnot
    have hgap : 0 < a - ∑ θ ∈ F, w θ * (C * γ.value θ) :=
      sub_pos.mpr (lt_of_not_ge hnot)
    let t := (C * γ.value (_root_.GD.N0232.N0719.N0859.d010810 k) + 1) /
      (a - ∑ θ ∈ F, w θ * (C * γ.value θ))
    have ht : 0 < t := div_pos
      (by nlinarith [γ.positive (_root_.GD.N0232.N0719.N0859.d010810 k)]) hgap
    have htw : ∀ θ ∈ F, 0 ≤ t * w θ := fun θ hθ ↦ mul_nonneg ht.le (hw θ hθ)
    obtain ⟨p, hp, heq⟩ := _root_.GD.N0232.N0719.N0966.d012353 k sizes F
      (fun θ ↦ t * w θ) htw
    have htest' := htest F (fun θ ↦ t * w θ) htw
    have ha' := mul_le_mul_of_nonneg_left (ha p hp) ht.le
    have hsum (f : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) :
        (∑ θ ∈ F, (t * w θ) * f θ) = t * ∑ θ ∈ F, w θ * f θ := by
      simp only [mul_assoc, Finset.mul_sum]
    rw [hsum] at heq htest'
    have htgap : t * (a - ∑ θ ∈ F, w θ * (C * γ.value θ)) =
        C * γ.value (_root_.GD.N0232.N0719.N0859.d010810 k) + 1 := div_mul_cancel₀ _ hgap.ne'
    nlinarith [sq_nonneg ‖p‖]

def d012356 (γ : _root_.GD.N0232.N0719.N0843.d012215 k)
    (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) : ℝ :=
  γ.value (_root_.GD.N0232.N0719.N0859.d010810 k) + ∑ θ ∈ F, w θ * γ.value θ

theorem d012357 (γ : _root_.GD.N0232.N0719.N0843.d012215 k)
    (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ) : 0 < _root_.GD.N0232.N0719.N0966.d012356 k γ F w := by
  apply add_pos_of_pos_of_nonneg (γ.positive (_root_.GD.N0232.N0719.N0859.d010810 k))
  exact Finset.sum_nonneg fun θ hθ ↦ mul_nonneg (hw θ hθ) (γ.positive θ).le

theorem d012358
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ) (hC : 0 ≤ C) :
    _root_.GD.N0232.N0719.N0844.d012248 k sizes γ ≤ ENNReal.ofReal C ↔
      ∀ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0232.N0719.N0966.d012351 k sizes F w ≤ C * _root_.GD.N0232.N0719.N0966.d012356 k γ F w := by
  rw [_root_.GD.N0232.N0719.N0967.d012308 k sizes hk hsizes γ,
    ← _root_.GD.N0232.N0719.N0967.d012307 k sizes hk hsizes γ C hC,
    _root_.GD.N0232.N0719.N0966.d012355 k sizes hk hsizes γ C hC]
  simp only [_root_.GD.N0232.N0719.N0966.d012356, mul_add, Finset.mul_sum, mul_left_comm]

def d012359 (γ : _root_.GD.N0232.N0719.N0843.d012215 k) : ℝ≥0∞ :=
  ⨆ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) (_ : ∀ θ ∈ F, 0 ≤ w θ),
    ENNReal.ofReal (_root_.GD.N0232.N0719.N0966.d012351 k sizes F w / _root_.GD.N0232.N0719.N0966.d012356 k γ F w)



theorem d012360
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (γ : _root_.GD.N0232.N0719.N0843.d012215 k) :
    _root_.GD.N0232.N0719.N0844.d012248 k sizes γ = _root_.GD.N0232.N0719.N0966.d012359 k sizes γ := by
  apply le_antisymm
  · by_cases htop : _root_.GD.N0232.N0719.N0966.d012359 k sizes γ = ⊤
    · rw [htop]
      exact le_top
    have hcut : _root_.GD.N0232.N0719.N0844.d012248 k sizes γ ≤
        ENNReal.ofReal (_root_.GD.N0232.N0719.N0966.d012359 k sizes γ).toReal := by
      apply (_root_.GD.N0232.N0719.N0966.d012358 k sizes hk hsizes γ _ ENNReal.toReal_nonneg).mpr
      intro F w hw
      have hb : ENNReal.ofReal (_root_.GD.N0232.N0719.N0966.d012351 k sizes F w / _root_.GD.N0232.N0719.N0966.d012356 k γ F w) ≤
          _root_.GD.N0232.N0719.N0966.d012359 k sizes γ :=
        le_iSup_of_le F (le_iSup_of_le w (le_iSup_of_le hw le_rfl))
      rw [← ENNReal.ofReal_toReal htop] at hb
      have hr := (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hb
      exact (div_le_iff₀ (_root_.GD.N0232.N0719.N0966.d012357 k γ F w hw)).mp hr
    rwa [ENNReal.ofReal_toReal htop] at hcut
  · by_cases htop : _root_.GD.N0232.N0719.N0844.d012248 k sizes γ = ⊤
    · rw [htop]
      exact le_top
    have hcut := (_root_.GD.N0232.N0719.N0966.d012358 k sizes hk hsizes γ
      (_root_.GD.N0232.N0719.N0844.d012248 k sizes γ).toReal ENNReal.toReal_nonneg).mp
      (le_of_eq (ENNReal.ofReal_toReal htop).symm)
    apply iSup_le
    intro F
    apply iSup_le
    intro w
    apply iSup_le
    intro hw
    have hr := (div_le_iff₀ (_root_.GD.N0232.N0719.N0966.d012357 k γ F w hw)).mpr (hcut F w hw)
    exact (ENNReal.ofReal_le_ofReal hr).trans_eq (ENNReal.ofReal_toReal htop)

theorem d012361
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (γ : _root_.GD.N0232.N0719.N0843.d012215 k) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ)
      (_root_.GD.N0232.N0719.N0962.d012190 k sizes) = _root_.GD.N0232.N0719.N0966.d012359 k sizes γ := by
  rw [← _root_.GD.N0232.N0719.N0844.d012256 k sizes γ hk hsizes]
  exact _root_.GD.N0232.N0719.N0966.d012360 k sizes hk hsizes γ

theorem d012362
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (γ : _root_.GD.N0232.N0719.N0843.d012215 k) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ)
      (_root_.GD.N0232.N0719.N0962.d012191 k sizes) = _root_.GD.N0232.N0719.N0966.d012359 k sizes γ := by
  rw [← _root_.GD.N0232.N0719.N0844.d012257 k sizes γ hk hsizes]
  exact _root_.GD.N0232.N0719.N0966.d012361 k sizes hk hsizes γ

theorem d012363
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ) (hC : 0 ≤ C) :
    ENNReal.ofReal C < _root_.GD.N0232.N0719.N0844.d012248 k sizes γ ↔
      ∃ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ C * _root_.GD.N0232.N0719.N0966.d012356 k γ F w < _root_.GD.N0232.N0719.N0966.d012351 k sizes F w := by
  classical
  have h := (_root_.GD.N0232.N0719.N0966.d012358 k sizes hk hsizes γ C hC).not
  push Not at h
  exact h

theorem d012364
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (γ : _root_.GD.N0232.N0719.N0843.d012215 k) :
    _root_.GD.N0232.N0719.N0844.d012248 k sizes γ ≠ ⊤ ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) → _root_.GD.N0232.N0719.N0966.d012351 k sizes F w ≤ C * _root_.GD.N0232.N0719.N0966.d012356 k γ F w := by
  constructor
  · intro hv
    refine ⟨(_root_.GD.N0232.N0719.N0844.d012248 k sizes γ).toReal, ENNReal.toReal_nonneg, ?_⟩
    apply (_root_.GD.N0232.N0719.N0966.d012358 k sizes hk hsizes γ _ ENNReal.toReal_nonneg).mp
    exact le_of_eq (ENNReal.ofReal_toReal hv).symm
  · rintro ⟨C, hC, hb⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((_root_.GD.N0232.N0719.N0966.d012358 k sizes hk hsizes γ C hC).mpr hb)

theorem d012365
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (γ : _root_.GD.N0232.N0719.N0843.d012215 k) :
    _root_.GD.N0232.N0719.N0844.d012248 k sizes γ = ⊤ ↔
      ∀ C : ℝ, 0 ≤ C → ∃ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ C * _root_.GD.N0232.N0719.N0966.d012356 k γ F w < _root_.GD.N0232.N0719.N0966.d012351 k sizes F w := by
  classical
  have h := (_root_.GD.N0232.N0719.N0966.d012364 k sizes hk hsizes γ).not
  push Not at h
  exact h



def d012366 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : ℝ≥0∞ :=
  _root_.GD.N0232.N0719.N0966.d012359 k sizes (_root_.GD.N0232.N0719.N0972.d012344 k sizes
    (by omega) (fun i ↦ by have := hsizes i; omega))

theorem d012367
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes =
      _root_.GD.N0232.N0719.N0966.d012366 k sizes hk hsizes := by
  exact _root_.GD.N0232.N0719.N0966.d012360 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0972.d012344 k sizes (by omega)
      (fun i ↦ by have := hsizes i; omega))

theorem d012368
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
      (_root_.GD.N0232.N0719.N0962.d012190 k sizes) =
        _root_.GD.N0232.N0719.N0966.d012366 k sizes hk hsizes := by
  exact _root_.GD.N0232.N0719.N0966.d012361 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0972.d012344 k sizes (by omega)
      (fun i ↦ by have := hsizes i; omega))

theorem d012369
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
      (_root_.GD.N0232.N0719.N0962.d012191 k sizes) =
        _root_.GD.N0232.N0719.N0966.d012366 k sizes hk hsizes := by
  exact _root_.GD.N0232.N0719.N0966.d012362 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0972.d012344 k sizes (by omega)
      (fun i ↦ by have := hsizes i; omega))

def d012370 (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0963.d012141 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) +
    ∑ θ ∈ F, w θ * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ

theorem d012371
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (C : ℝ) (hC : 0 ≤ C) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≤ ENNReal.ofReal C ↔
      ∀ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
        _root_.GD.N0232.N0719.N0966.d012351 k sizes F w ≤ C * _root_.GD.N0232.N0719.N0966.d012370 k sizes F w := by
  exact _root_.GD.N0232.N0719.N0966.d012358 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0972.d012344 k sizes (by omega)
      (fun i ↦ by have := hsizes i; omega)) C hC

theorem d012372
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (C : ℝ) (hC : 0 ≤ C) :
    ENNReal.ofReal C < _root_.GD.N0232.N0719.N0962.d012188 k sizes ↔
      ∃ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ C * _root_.GD.N0232.N0719.N0966.d012370 k sizes F w < _root_.GD.N0232.N0719.N0966.d012351 k sizes F w := by
  exact _root_.GD.N0232.N0719.N0966.d012363 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0972.d012344 k sizes (by omega)
      (fun i ↦ by have := hsizes i; omega)) C hC

theorem d012373
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes ≠ ⊤ ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) → _root_.GD.N0232.N0719.N0966.d012351 k sizes F w ≤ C * _root_.GD.N0232.N0719.N0966.d012370 k sizes F w := by
  exact _root_.GD.N0232.N0719.N0966.d012364 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0972.d012344 k sizes (by omega)
      (fun i ↦ by have := hsizes i; omega))

theorem d012374
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0962.d012188 k sizes = ⊤ ↔
      ∀ C : ℝ, 0 ≤ C → ∃ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ C * _root_.GD.N0232.N0719.N0966.d012370 k sizes F w < _root_.GD.N0232.N0719.N0966.d012351 k sizes F w := by
  exact _root_.GD.N0232.N0719.N0966.d012365 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0972.d012344 k sizes (by omega)
      (fun i ↦ by have := hsizes i; omega))

end
end GD.N0232.N0719.N0966

#print axioms _root_.GD.N0232.N0719.N0966.d012355
#print axioms _root_.GD.N0232.N0719.N0966.d012358
#print axioms _root_.GD.N0232.N0719.N0966.d012360
#print axioms _root_.GD.N0232.N0719.N0966.d012361
#print axioms _root_.GD.N0232.N0719.N0966.d012362
#print axioms _root_.GD.N0232.N0719.N0966.d012363
#print axioms _root_.GD.N0232.N0719.N0966.d012364
#print axioms _root_.GD.N0232.N0719.N0966.d012365
#print axioms _root_.GD.N0232.N0719.N0966.d012367
#print axioms _root_.GD.N0232.N0719.N0966.d012368
#print axioms _root_.GD.N0232.N0719.N0966.d012369
#print axioms _root_.GD.N0232.N0719.N0966.d012371
#print axioms _root_.GD.N0232.N0719.N0966.d012372
#print axioms _root_.GD.N0232.N0719.N0966.d012373
#print axioms _root_.GD.N0232.N0719.N0966.d012374
