import GD.Module1182























open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1446

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1506
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0137
open _root_.GD.N0107

variable (m n : ℕ)




def d019019 (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) : _root_.GD.N0232.N0720.N1080.d014170 m n := (-ω.1, -ω.2)

theorem d019020 (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1446.d019019 m n (_root_.GD.N0232.N0720.N1446.d019019 m n ω) = ω :=
  Prod.ext (neg_neg _) (neg_neg _)

theorem d019021 : Measurable (_root_.GD.N0232.N0720.N1446.d019019 m n) := by
  unfold _root_.GD.N0232.N0720.N1446.d019019
  fun_prop

theorem d019022 (k : ℕ) :
    MeasurePreserving (fun x : _root_.GD.N0137.d008894 k => -x)
      (_root_.GD.N0137.d008895 k) (_root_.GD.N0137.d008895 k) := by
  unfold _root_.GD.N0137.d008895 _root_.GD.N0140.d006650
  have h := measurePreserving_pi (fun _ : Fin k => gaussianReal 0 1)
    (fun _ : Fin k => gaussianReal 0 1) (f := fun _ (t : ℝ) => -t)
    (fun _ => ⟨measurable_neg, by simpa using gaussianReal_map_neg (μ := 0) (v := 1)⟩)
  exact h

theorem d019023 :
    MeasurePreserving (_root_.GD.N0232.N0720.N1446.d019019 m n) (_root_.GD.N0137.d008914 m n) (_root_.GD.N0137.d008914 m n) := by
  unfold _root_.GD.N0137.d008914
  exact (_root_.GD.N0232.N0720.N1446.d019022 m).prod (_root_.GD.N0232.N0720.N1446.d019022 n)


def d019024 (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := -θ.location
  scale₁ := θ.scale₁
  scale₂ := θ.scale₂
  scale₁_pos := θ.scale₁_pos
  scale₂_pos := θ.scale₂_pos

@[simp] theorem d019025 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1446.d019024 θ).location = -θ.location := rfl

@[simp] theorem d019026 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1446.d019024 θ).scale₁ = θ.scale₁ := rfl

@[simp] theorem d019027 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1446.d019024 θ).scale₂ = θ.scale₂ := rfl

theorem d019028 :
    _root_.GD.N0232.N0720.N1446.d019024 _root_.GD.N0232.N0720.N1080.d014169 = _root_.GD.N0232.N0720.N1080.d014169 := by
  apply _root_.GD.N0232.N0720.N1215.d014277 <;> simp [_root_.GD.N0232.N0720.N1080.d014169]

theorem d019029 (μ σ τ : ℝ) (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0107.d009024 m n μ σ τ (_root_.GD.N0232.N0720.N1446.d019019 m n ω) =
      _root_.GD.N0232.N0720.N1446.d019019 m n (_root_.GD.N0107.d009024 m n (-μ) σ τ ω) := by
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [_root_.GD.N0107.d009024, _root_.GD.N0107.d009018, _root_.GD.N0232.N0720.N1446.d019019, Pi.neg_apply]
    ring
  · simp only [_root_.GD.N0107.d009024, _root_.GD.N0107.d009018, _root_.GD.N0232.N0720.N1446.d019019, Pi.neg_apply]
    ring



theorem d019030 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1080.d014171 m n θ).map (_root_.GD.N0232.N0720.N1446.d019019 m n) = _root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171 _root_.GD.N0107.d009030
  rw [Measure.map_map (_root_.GD.N0232.N0720.N1446.d019021 m n)
    (_root_.GD.N0107.d009026 m n _ _ _)]
  have hcomm :
      _root_.GD.N0232.N0720.N1446.d019019 m n ∘ _root_.GD.N0107.d009024 m n θ.location θ.scale₁ θ.scale₂ =
        _root_.GD.N0107.d009024 m n (-θ.location) θ.scale₁ θ.scale₂ ∘ _root_.GD.N0232.N0720.N1446.d019019 m n := by
    funext ω
    show _root_.GD.N0232.N0720.N1446.d019019 m n (_root_.GD.N0107.d009024 m n θ.location θ.scale₁ θ.scale₂ ω) =
      _root_.GD.N0107.d009024 m n (-θ.location) θ.scale₁ θ.scale₂ (_root_.GD.N0232.N0720.N1446.d019019 m n ω)
    rw [_root_.GD.N0232.N0720.N1446.d019029, neg_neg]
  rw [hcomm, ← Measure.map_map (_root_.GD.N0107.d009026 m n _ _ _)
    (_root_.GD.N0232.N0720.N1446.d019021 m n),
    (_root_.GD.N0232.N0720.N1446.d019023 m n).map_eq]
  rfl

theorem d019031 :
    MeasurePreserving (_root_.GD.N0232.N0720.N1446.d019019 m n) (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  refine ⟨_root_.GD.N0232.N0720.N1446.d019021 m n, ?_⟩
  show (_root_.GD.N0232.N0720.N1080.d014171 m n _root_.GD.N0232.N0720.N1080.d014169).map (_root_.GD.N0232.N0720.N1446.d019019 m n) = _root_.GD.N0232.N0720.N1080.d014171 m n _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1446.d019030, _root_.GD.N0232.N0720.N1446.d019028]




def d019032 (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  -(Lp.compMeasurePreserving (_root_.GD.N0232.N0720.N1446.d019019 m n)
      (_root_.GD.N0232.N0720.N1446.d019031 m n) x)

theorem d019033 (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1446.d019032 m n (_root_.GD.N0232.N0720.N1446.d019032 m n x) = x := by
  unfold _root_.GD.N0232.N0720.N1446.d019032
  rw [map_neg, neg_neg, ← Lp.compMeasurePreserving_comp_apply]
  rw [_root_.GD.N0232.N0720.N1506.d019008 (f' := id)
    (by funext ω; exact _root_.GD.N0232.N0720.N1446.d019020 m n ω) _ (MeasurePreserving.id _)]
  exact Lp.compMeasurePreserving_id_apply x

theorem d019034 (x y : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1446.d019032 m n (x + y) = _root_.GD.N0232.N0720.N1446.d019032 m n x + _root_.GD.N0232.N0720.N1446.d019032 m n y := by
  unfold _root_.GD.N0232.N0720.N1446.d019032
  rw [map_add, neg_add]

theorem d019035 (c : ℝ) (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1446.d019032 m n (c • x) = c • _root_.GD.N0232.N0720.N1446.d019032 m n x := by
  have hsmul :
      Lp.compMeasurePreserving (_root_.GD.N0232.N0720.N1446.d019019 m n)
          (_root_.GD.N0232.N0720.N1446.d019031 m n) (c • x) =
        c • Lp.compMeasurePreserving (_root_.GD.N0232.N0720.N1446.d019019 m n)
          (_root_.GD.N0232.N0720.N1446.d019031 m n) x :=
    LinearMap.map_smul (Lp.compMeasurePreservingₗ ℝ (_root_.GD.N0232.N0720.N1446.d019019 m n)
      (_root_.GD.N0232.N0720.N1446.d019031 m n)) c x
  unfold _root_.GD.N0232.N0720.N1446.d019032
  rw [hsmul, smul_neg]

theorem d019036 (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖_root_.GD.N0232.N0720.N1446.d019032 m n x‖ = ‖x‖ := by
  unfold _root_.GD.N0232.N0720.N1446.d019032
  rw [norm_neg, Lp.norm_compMeasurePreserving]


theorem d019037 (θ : _root_.GD.N0232.N0720.N1080.d014168) (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1446.d019032 m n x) = _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) x := by
  have hpres := _root_.GD.N0232.N0720.N1446.d019031 m n
  have h1 : (fun ω => x ω) =ᵐ[(_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1446.d019019 m n)]
      _root_.GD.N0232.N0720.N1214.d014265 m n x := by
    rw [hpres.map_eq]
    exact (_root_.GD.N0232.N0720.N1214.d014267 m n x).symm
  have h2 := MeasureTheory.ae_eq_comp (_root_.GD.N0232.N0720.N1446.d019021 m n).aemeasurable h1
  have hae : ⇑(_root_.GD.N0232.N0720.N1446.d019032 m n x) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun ω => -(_root_.GD.N0232.N0720.N1214.d014265 m n x (_root_.GD.N0232.N0720.N1446.d019019 m n ω)) := by
    unfold _root_.GD.N0232.N0720.N1446.d019032
    refine (Lp.coeFn_neg _).trans ?_
    filter_upwards [(Lp.coeFn_compMeasurePreserving x hpres).trans h2] with ω hω
    simp only [Pi.neg_apply, hω, Function.comp]
  have hmem : MemLp (fun ω => -(_root_.GD.N0232.N0720.N1214.d014265 m n x (_root_.GD.N0232.N0720.N1446.d019019 m n ω))) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    ((_root_.GD.N0232.N0720.N1214.d014268 m n x).comp_measurePreserving hpres).neg
  have heq : _root_.GD.N0232.N0720.N1446.d019032 m n x = MemLp.toLp _ hmem :=
    Lp.ext (hae.trans hmem.coeFn_toLp.symm)
  rw [heq, ← _root_.GD.N0232.N0720.N1080.d014198 m n θ _ hmem,
    ← _root_.GD.N0232.N0720.N1215.d014286 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) x]
  unfold _root_.GD.N0232.N0720.N1080.d014197
  have hmeas : Measurable (fun ω =>
      ENNReal.ofReal ((_root_.GD.N0232.N0720.N1214.d014265 m n x ω - (_root_.GD.N0232.N0720.N1446.d019024 θ).location) ^ 2)) :=
    (((_root_.GD.N0232.N0720.N1214.d014266 m n x).sub measurable_const).pow_const 2).ennreal_ofReal
  rw [← _root_.GD.N0232.N0720.N1446.d019030 m n θ, lintegral_map hmeas (_root_.GD.N0232.N0720.N1446.d019021 m n)]
  apply lintegral_congr
  intro ω
  congr 1
  simp only [_root_.GD.N0232.N0720.N1446.d019025]
  ring





theorem d019038
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hprof : ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) d = _root_.GD.N0232.N0720.N1080.d014182 m n θ d)
    (hd : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d) :
    _root_.GD.N0232.N0720.N1446.d019032 m n d = d := by
  refine hd (_root_.GD.N0232.N0720.N1446.d019032 m n d) (fun θ => ?_)
  rw [_root_.GD.N0232.N0720.N1446.d019037, hprof θ]



theorem d019039 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) s.value = _root_.GD.N0232.N0720.N1080.d014182 m n θ s.value := by
  have hg := s.riskCharacter (_root_.GD.N0232.N0720.N1482.d015128 (-2 * θ.location)) θ
  have hparam :
      _root_.GD.N0232.N0720.N1215.d014272 (_root_.GD.N0232.N0720.N1482.d015128 (-2 * θ.location)) θ = _root_.GD.N0232.N0720.N1446.d019024 θ := by
    apply _root_.GD.N0232.N0720.N1215.d014277
    · simp [_root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0720.N1482.d015128, _root_.GD.N0232.N0720.N1446.d019024, _root_.GD.N0232.N0719.N0946.d009229.d009239]
      ring
    · simp [_root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0720.N1482.d015128, _root_.GD.N0232.N0720.N1446.d019024, _root_.GD.N0232.N0719.N0946.d009229.d009239]
    · simp [_root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0720.N1482.d015128, _root_.GD.N0232.N0720.N1446.d019024, _root_.GD.N0232.N0719.N0946.d009229.d009239]
  have hdil : (_root_.GD.N0232.N0720.N1482.d015128 (-2 * θ.location)).d009239 = 1 := by
    simp [_root_.GD.N0232.N0720.N1482.d015128, _root_.GD.N0232.N0719.N0946.d009229.d009239]
  rw [hparam, hdil] at hg
  simpa using hg


theorem d019040
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (hs : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value) :
    _root_.GD.N0232.N0720.N1446.d019032 m n s.value = s.value :=
  _root_.GD.N0232.N0720.N1446.d019038 m n s.value
    (_root_.GD.N0232.N0720.N1446.d019039 m n s) hs






theorem d019041
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hd : _root_.GD.N0232.N0720.N1446.d019032 m n d = d)
    (hsym : ∀ e, _root_.GD.N0232.N0720.N1446.d019032 m n e = e → _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e d → e = d) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d := by
  intro e he
  set r := _root_.GD.N0232.N0720.N1446.d019032 m n e with hr
  set mid : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := (2 : ℝ)⁻¹ • (e + r) with hmid
  have hprof : ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) d = _root_.GD.N0232.N0720.N1080.d014182 m n θ d := by
    intro θ
    rw [← _root_.GD.N0232.N0720.N1446.d019037, hd]

  have hmidfix : _root_.GD.N0232.N0720.N1446.d019032 m n mid = mid := by
    rw [hmid, _root_.GD.N0232.N0720.N1446.d019035, _root_.GD.N0232.N0720.N1446.d019034, ← hr,
      _root_.GD.N0232.N0720.N1446.d019033, add_comm]

  have hmiddom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) mid d := by
    intro θ
    have h := _root_.GD.N0232.N0720.N1506.d019013 m n (G := Fin 2) θ ![e, r]
    simp only [Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Nat.cast_ofNat] at h
    have hr_risk : _root_.GD.N0232.N0720.N1080.d014182 m n θ r ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ d := by
      rw [hr, _root_.GD.N0232.N0720.N1446.d019037]
      exact (he _).trans (le_of_eq (hprof θ))
    calc _root_.GD.N0232.N0720.N1080.d014182 m n θ mid ≤ (2 : ℝ≥0∞)⁻¹ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ e + _root_.GD.N0232.N0720.N1080.d014182 m n θ r) := h
      _ ≤ (2 : ℝ≥0∞)⁻¹ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ d + _root_.GD.N0232.N0720.N1080.d014182 m n θ d) :=
          mul_le_mul_right (add_le_add (he θ) hr_risk) _
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n θ d := by
          rw [← two_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have hmideq : mid = d := hsym mid hmidfix hmiddom

  have hnorm_le : ‖e‖ ^ 2 ≤ ‖d‖ ^ 2 := by
    have h := he _root_.GD.N0232.N0720.N1080.d014169
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at h
    simp only [zero_sub, norm_neg] at h
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp h
  have hnr : ‖r‖ = ‖e‖ := by rw [hr, _root_.GD.N0232.N0720.N1446.d019036]
  have hsum : ‖e + r‖ = 2 * ‖d‖ := by
    have : ‖mid‖ = (2 : ℝ)⁻¹ * ‖e + r‖ := by
      rw [hmid, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    rw [hmideq] at this
    linarith
  have hpar := parallelogram_law_with_norm ℝ e r
  rw [hnr, hsum] at hpar
  have hdiff : ‖e - r‖ * ‖e - r‖ ≤ 0 := by nlinarith [hpar, hnorm_le]
  have hzero : ‖e - r‖ = 0 := by nlinarith [norm_nonneg (e - r)]
  have her : e = r := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  have hmid_e : mid = e := by
    rw [hmid, ← her, ← two_smul ℝ e, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  rw [← hmid_e, hmideq]



theorem d019042
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hprof : ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 θ) d = _root_.GD.N0232.N0720.N1080.d014182 m n θ d) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d ↔
      _root_.GD.N0232.N0720.N1446.d019032 m n d = d ∧
        ∀ e, _root_.GD.N0232.N0720.N1446.d019032 m n e = e → _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e d → e = d := by
  constructor
  · intro hd
    exact ⟨_root_.GD.N0232.N0720.N1446.d019038 m n d hprof hd,
      fun e _ he => hd e he⟩
  · rintro ⟨hd, hsym⟩
    exact _root_.GD.N0232.N0720.N1446.d019041 m n d hd hsym


theorem d019043
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1446.d019032 m n s.value = s.value ∧
          ∀ e, _root_.GD.N0232.N0720.N1446.d019032 m n e = e →
            _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e s.value → e = s.value := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hs, ht⟩
    obtain ⟨hsym, hsu⟩ :=
      (_root_.GD.N0232.N0720.N1446.d019042 m n s.value
        (_root_.GD.N0232.N0720.N1446.d019039 m n s)).1 ht
    exact ⟨s, hs, hsym, hsu⟩
  · rintro ⟨s, hs, hsym, hsu⟩
    exact ⟨s, hs,
      (_root_.GD.N0232.N0720.N1446.d019042 m n s.value
        (_root_.GD.N0232.N0720.N1446.d019039 m n s)).2 ⟨hsym, hsu⟩⟩

end

end N1446
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1446.d019040
#print axioms _root_.GD.N0232.N0720.N1446.d019042
#print axioms _root_.GD.N0232.N0720.N1446.d019043
