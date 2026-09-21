import GD.Module1184
import GD.Module1172




























open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1043

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1506
open _root_.GD.N0232.N0720.N1047
open _root_.GD.N0232.N0720.N1048
open _root_.GD.N0137
open _root_.GD.N0107

variable (n : ℕ)




def d019054 (ω : _root_.GD.N0232.N0720.N1080.d014170 n n) : _root_.GD.N0232.N0720.N1080.d014170 n n := (ω.2, ω.1)

theorem d019055 (ω : _root_.GD.N0232.N0720.N1080.d014170 n n) :
    _root_.GD.N0232.N0720.N1043.d019054 n (_root_.GD.N0232.N0720.N1043.d019054 n ω) = ω := rfl

theorem d019056 : Measurable (_root_.GD.N0232.N0720.N1043.d019054 n) :=
  measurable_swap

theorem d019057 :
    MeasurePreserving (_root_.GD.N0232.N0720.N1043.d019054 n) (_root_.GD.N0137.d008914 n n) (_root_.GD.N0137.d008914 n n) := by
  unfold _root_.GD.N0137.d008914
  exact Measure.measurePreserving_swap


def d019058 (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := θ.location
  scale₁ := θ.scale₂
  scale₂ := θ.scale₁
  scale₁_pos := θ.scale₂_pos
  scale₂_pos := θ.scale₁_pos

@[simp] theorem d019059 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1043.d019058 θ).location = θ.location := rfl

@[simp] theorem d019060 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1043.d019058 θ).scale₁ = θ.scale₂ := rfl

@[simp] theorem d019061 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1043.d019058 θ).scale₂ = θ.scale₁ := rfl

theorem d019062 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1043.d019058 (_root_.GD.N0232.N0720.N1043.d019058 θ) = θ := by
  apply _root_.GD.N0232.N0720.N1215.d014277 <;> rfl

theorem d019063 :
    _root_.GD.N0232.N0720.N1043.d019058 _root_.GD.N0232.N0720.N1080.d014169 = _root_.GD.N0232.N0720.N1080.d014169 := by
  apply _root_.GD.N0232.N0720.N1215.d014277 <;> rfl

theorem d019064 (μ σ τ : ℝ) (ω : _root_.GD.N0232.N0720.N1080.d014170 n n) :
    _root_.GD.N0107.d009024 n n μ σ τ (_root_.GD.N0232.N0720.N1043.d019054 n ω) =
      _root_.GD.N0232.N0720.N1043.d019054 n (_root_.GD.N0107.d009024 n n μ τ σ ω) := rfl



theorem d019065 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1080.d014171 n n θ).map (_root_.GD.N0232.N0720.N1043.d019054 n) = _root_.GD.N0232.N0720.N1080.d014171 n n (_root_.GD.N0232.N0720.N1043.d019058 θ) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171 _root_.GD.N0107.d009030
  rw [Measure.map_map (_root_.GD.N0232.N0720.N1043.d019056 n)
    (_root_.GD.N0107.d009026 n n _ _ _)]
  have hcomm :
      _root_.GD.N0232.N0720.N1043.d019054 n ∘ _root_.GD.N0107.d009024 n n θ.location θ.scale₁ θ.scale₂ =
        _root_.GD.N0107.d009024 n n θ.location θ.scale₂ θ.scale₁ ∘ _root_.GD.N0232.N0720.N1043.d019054 n := by
    funext ω
    exact (_root_.GD.N0232.N0720.N1043.d019064 n θ.location θ.scale₂ θ.scale₁ ω).symm
  rw [hcomm, ← Measure.map_map (_root_.GD.N0107.d009026 n n _ _ _)
    (_root_.GD.N0232.N0720.N1043.d019056 n),
    (_root_.GD.N0232.N0720.N1043.d019057 n).map_eq]
  rfl

theorem d019066 :
    MeasurePreserving (_root_.GD.N0232.N0720.N1043.d019054 n) (_root_.GD.N0232.N0720.N1080.d014172 n n) (_root_.GD.N0232.N0720.N1080.d014172 n n) := by
  refine ⟨_root_.GD.N0232.N0720.N1043.d019056 n, ?_⟩
  show (_root_.GD.N0232.N0720.N1080.d014171 n n _root_.GD.N0232.N0720.N1080.d014169).map (_root_.GD.N0232.N0720.N1043.d019054 n) = _root_.GD.N0232.N0720.N1080.d014171 n n _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1043.d019065, _root_.GD.N0232.N0720.N1043.d019063]




def d019067 (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n) :=
  Lp.compMeasurePreserving (_root_.GD.N0232.N0720.N1043.d019054 n)
    (_root_.GD.N0232.N0720.N1043.d019066 n) x

theorem d019068 (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) :
    _root_.GD.N0232.N0720.N1043.d019067 n (_root_.GD.N0232.N0720.N1043.d019067 n x) = x := by
  unfold _root_.GD.N0232.N0720.N1043.d019067
  rw [← Lp.compMeasurePreserving_comp_apply]
  rw [_root_.GD.N0232.N0720.N1506.d019008 (f' := id)
    (by funext ω; exact _root_.GD.N0232.N0720.N1043.d019055 n ω) _ (MeasurePreserving.id _)]
  exact Lp.compMeasurePreserving_id_apply x

theorem d019069 (x y : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) :
    _root_.GD.N0232.N0720.N1043.d019067 n (x + y) = _root_.GD.N0232.N0720.N1043.d019067 n x + _root_.GD.N0232.N0720.N1043.d019067 n y := by
  unfold _root_.GD.N0232.N0720.N1043.d019067
  exact map_add _ x y

theorem d019070 (c : ℝ) (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) :
    _root_.GD.N0232.N0720.N1043.d019067 n (c • x) = c • _root_.GD.N0232.N0720.N1043.d019067 n x :=
  LinearMap.map_smul (Lp.compMeasurePreservingₗ ℝ (_root_.GD.N0232.N0720.N1043.d019054 n)
    (_root_.GD.N0232.N0720.N1043.d019066 n)) c x

theorem d019071 (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) :
    ‖_root_.GD.N0232.N0720.N1043.d019067 n x‖ = ‖x‖ := by
  unfold _root_.GD.N0232.N0720.N1043.d019067
  rw [Lp.norm_compMeasurePreserving]


theorem d019072 (θ : _root_.GD.N0232.N0720.N1080.d014168) (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) :
    _root_.GD.N0232.N0720.N1080.d014182 n n θ (_root_.GD.N0232.N0720.N1043.d019067 n x) = _root_.GD.N0232.N0720.N1080.d014182 n n (_root_.GD.N0232.N0720.N1043.d019058 θ) x := by
  have hpres := _root_.GD.N0232.N0720.N1043.d019066 n
  have h1 : (fun ω => x ω) =ᵐ[(_root_.GD.N0232.N0720.N1080.d014172 n n).map (_root_.GD.N0232.N0720.N1043.d019054 n)]
      _root_.GD.N0232.N0720.N1214.d014265 n n x := by
    rw [hpres.map_eq]
    exact (_root_.GD.N0232.N0720.N1214.d014267 n n x).symm
  have h2 := MeasureTheory.ae_eq_comp (_root_.GD.N0232.N0720.N1043.d019056 n).aemeasurable h1
  have hae : ⇑(_root_.GD.N0232.N0720.N1043.d019067 n x) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 n n]
      fun ω => _root_.GD.N0232.N0720.N1214.d014265 n n x (_root_.GD.N0232.N0720.N1043.d019054 n ω) := by
    unfold _root_.GD.N0232.N0720.N1043.d019067
    filter_upwards [(Lp.coeFn_compMeasurePreserving x hpres).trans h2] with ω hω
    simpa only [Function.comp] using hω
  have hmem : MemLp (fun ω => _root_.GD.N0232.N0720.N1214.d014265 n n x (_root_.GD.N0232.N0720.N1043.d019054 n ω)) 2
      (_root_.GD.N0232.N0720.N1080.d014172 n n) :=
    (_root_.GD.N0232.N0720.N1214.d014268 n n x).comp_measurePreserving hpres
  have heq : _root_.GD.N0232.N0720.N1043.d019067 n x = MemLp.toLp _ hmem :=
    Lp.ext (hae.trans hmem.coeFn_toLp.symm)
  rw [heq, ← _root_.GD.N0232.N0720.N1080.d014198 n n θ _ hmem,
    ← _root_.GD.N0232.N0720.N1215.d014286 n n (_root_.GD.N0232.N0720.N1043.d019058 θ) x]
  unfold _root_.GD.N0232.N0720.N1080.d014197
  have hmeas : Measurable (fun ω =>
      ENNReal.ofReal ((_root_.GD.N0232.N0720.N1214.d014265 n n x ω - (_root_.GD.N0232.N0720.N1043.d019058 θ).location) ^ 2)) :=
    (((_root_.GD.N0232.N0720.N1214.d014266 n n x).sub measurable_const).pow_const 2).ennreal_ofReal
  rw [← _root_.GD.N0232.N0720.N1043.d019065 n θ, lintegral_map hmeas (_root_.GD.N0232.N0720.N1043.d019056 n)]
  apply lintegral_congr
  intro ω
  simp only [_root_.GD.N0232.N0720.N1043.d019059]





theorem d019073
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n))
    (hprof : ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 n n (_root_.GD.N0232.N0720.N1043.d019058 θ) d = _root_.GD.N0232.N0720.N1080.d014182 n n θ d)
    (hd : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 n n) d) :
    _root_.GD.N0232.N0720.N1043.d019067 n d = d := by
  refine hd (_root_.GD.N0232.N0720.N1043.d019067 n d) (fun θ => ?_)
  rw [_root_.GD.N0232.N0720.N1043.d019072, hprof θ]






theorem d019074
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) (hd : _root_.GD.N0232.N0720.N1043.d019067 n d = d)
    (hsym : ∀ e, _root_.GD.N0232.N0720.N1043.d019067 n e = e → _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 n n) e d → e = d) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 n n) d := by
  intro e he
  set r := _root_.GD.N0232.N0720.N1043.d019067 n e with hr
  set mid : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n) := (2 : ℝ)⁻¹ • (e + r) with hmid
  have hprof : ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 n n (_root_.GD.N0232.N0720.N1043.d019058 θ) d = _root_.GD.N0232.N0720.N1080.d014182 n n θ d := by
    intro θ
    rw [← _root_.GD.N0232.N0720.N1043.d019072, hd]
  have hmidfix : _root_.GD.N0232.N0720.N1043.d019067 n mid = mid := by
    rw [hmid, _root_.GD.N0232.N0720.N1043.d019070, _root_.GD.N0232.N0720.N1043.d019069, ← hr,
      _root_.GD.N0232.N0720.N1043.d019068, add_comm]
  have hmiddom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 n n) mid d := by
    intro θ
    have h := _root_.GD.N0232.N0720.N1506.d019013 n n (G := Fin 2) θ ![e, r]
    simp only [Fintype.card_fin, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Nat.cast_ofNat] at h
    have hr_risk : _root_.GD.N0232.N0720.N1080.d014182 n n θ r ≤ _root_.GD.N0232.N0720.N1080.d014182 n n θ d := by
      rw [hr, _root_.GD.N0232.N0720.N1043.d019072]
      exact (he _).trans (le_of_eq (hprof θ))
    calc _root_.GD.N0232.N0720.N1080.d014182 n n θ mid ≤ (2 : ℝ≥0∞)⁻¹ * (_root_.GD.N0232.N0720.N1080.d014182 n n θ e + _root_.GD.N0232.N0720.N1080.d014182 n n θ r) := h
      _ ≤ (2 : ℝ≥0∞)⁻¹ * (_root_.GD.N0232.N0720.N1080.d014182 n n θ d + _root_.GD.N0232.N0720.N1080.d014182 n n θ d) :=
          mul_le_mul_right (add_le_add (he θ) hr_risk) _
      _ = _root_.GD.N0232.N0720.N1080.d014182 n n θ d := by
          rw [← two_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  have hmideq : mid = d := hsym mid hmidfix hmiddom
  have hnorm_le : ‖e‖ ^ 2 ≤ ‖d‖ ^ 2 := by
    have h := he _root_.GD.N0232.N0720.N1080.d014169
    rw [_root_.GD.N0232.N0720.N1080.d014190 n n, _root_.GD.N0232.N0720.N1080.d014190 n n] at h
    simp only [zero_sub, norm_neg] at h
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp h
  have hnr : ‖r‖ = ‖e‖ := by rw [hr, _root_.GD.N0232.N0720.N1043.d019071]
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



theorem d019075
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n))
    (hprof : ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 n n (_root_.GD.N0232.N0720.N1043.d019058 θ) d = _root_.GD.N0232.N0720.N1080.d014182 n n θ d) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 n n) d ↔
      _root_.GD.N0232.N0720.N1043.d019067 n d = d ∧
        ∀ e, _root_.GD.N0232.N0720.N1043.d019067 n e = e → _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 n n) e d → e = d := by
  constructor
  · intro hd
    exact ⟨_root_.GD.N0232.N0720.N1043.d019073 n d hprof hd,
      fun e _ he => hd e he⟩
  · rintro ⟨hd, hsym⟩
    exact _root_.GD.N0232.N0720.N1043.d019074 n d hd hsym




theorem d019076
    (hn : 2 ≤ n) (s : _root_.GD.N0232.N0720.N1159.d014639 n n)
    (hs : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 n n) s.value (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn))
    (hsym : _root_.GD.N0232.N0720.N1043.d019067 n s.value = s.value)
    (hsu : ∀ e, _root_.GD.N0232.N0720.N1043.d019067 n e = e →
      _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 n n) e s.value → e = s.value) :
    _root_.GD.N0232.N0720.N1159.d014661 n n := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := n) (n := n) hn hn]
  exact ⟨s, hs, _root_.GD.N0232.N0720.N1043.d019074 n s.value hsym hsu⟩





theorem d019077 (hn : 2 ≤ n) (ω : _root_.GD.N0232.N0720.N1080.d014170 n n)
    (hpos : 0 < _root_.GD.N0107.d009085 ω.1 / n + _root_.GD.N0107.d009085 ω.2 / n) :
    _root_.GD.N0232.N0720.N1080.d014175 n n (_root_.GD.N0232.N0720.N1043.d019054 n ω) = _root_.GD.N0232.N0720.N1080.d014175 n n ω := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact this.ne'
  have hS : _root_.GD.N0107.d009085 ω.1 / n + _root_.GD.N0107.d009085 ω.2 / n ≠ 0 :=
    hpos.ne'
  have hS2 : _root_.GD.N0107.d009085 ω.1 + _root_.GD.N0107.d009085 ω.2 ≠ 0 := by
    intro h
    apply hS
    rw [← add_div, h, zero_div]
  have hS2' : _root_.GD.N0107.d009085 ω.2 + _root_.GD.N0107.d009085 ω.1 ≠ 0 := by
    rw [add_comm]; exact hS2
  simp only [_root_.GD.N0232.N0720.N1080.d014175, _root_.GD.N0107.d012733, _root_.GD.N0107.d009091, _root_.GD.N0107.d009090,
    _root_.GD.N0232.N0720.N1043.d019054]
  field_simp
  ring



theorem d019078 (hn : 2 ≤ n) :
    (fun ω => _root_.GD.N0232.N0720.N1080.d014175 n n (_root_.GD.N0232.N0720.N1043.d019054 n ω)) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 n n]
      _root_.GD.N0232.N0720.N1080.d014175 n n := by
  have hpos := _root_.GD.N0119.d009075 n n hn hn
    (e := 1 / 2) (by norm_num) (by norm_num)
  have href : _root_.GD.N0232.N0720.N1080.d014172 n n = _root_.GD.N0137.d008914 n n := by
    rw [_root_.GD.N0232.N0720.N1449.d018839]
    rfl
  rw [href]
  filter_upwards [hpos] with ω hω
  apply _root_.GD.N0232.N0720.N1043.d019077 n hn ω
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : 0 < _root_.GD.N0107.d009085 ω.1 / n := div_pos hω.1 hn0
  have h2 : 0 < _root_.GD.N0107.d009085 ω.2 / n := div_pos hω.2 hn0
  linarith


theorem d019079 (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1043.d019067 n (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn) = _root_.GD.N0232.N0720.N1080.d014180 n n hn hn := by
  have hpres := _root_.GD.N0232.N0720.N1043.d019066 n
  have href : MemLp (_root_.GD.N0232.N0720.N1080.d014175 n n) 2 (_root_.GD.N0232.N0720.N1080.d014172 n n) := by
    simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
      _root_.GD.N0232.N0720.N1080.d014177 n n hn hn _root_.GD.N0232.N0720.N1080.d014169
  have hcoe : (fun ω => (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn) ω) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 n n] _root_.GD.N0232.N0720.N1080.d014175 n n := by
    simpa [_root_.GD.N0232.N0720.N1080.d014180] using href.coeFn_toLp
  have h1 : (fun ω => (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn) ω) =ᵐ[(_root_.GD.N0232.N0720.N1080.d014172 n n).map (_root_.GD.N0232.N0720.N1043.d019054 n)]
      _root_.GD.N0232.N0720.N1080.d014175 n n := by
    rw [hpres.map_eq]
    exact hcoe
  have h2 := MeasureTheory.ae_eq_comp (_root_.GD.N0232.N0720.N1043.d019056 n).aemeasurable h1
  apply Lp.ext
  unfold _root_.GD.N0232.N0720.N1043.d019067
  refine (Lp.coeFn_compMeasurePreserving (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn) hpres).trans ?_
  refine (h2.trans ?_).trans hcoe.symm
  exact _root_.GD.N0232.N0720.N1043.d019078 n hn


theorem d019080 (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 n n (_root_.GD.N0232.N0720.N1043.d019058 θ) (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn) = _root_.GD.N0232.N0720.N1080.d014182 n n θ (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn) := by
  rw [← _root_.GD.N0232.N0720.N1043.d019072, _root_.GD.N0232.N0720.N1043.d019079]




theorem d019081 (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1043.d019067 n (_root_.GD.N0232.N0720.N1047.d018650 n n hn hn) =
      _root_.GD.N0232.N0720.N1047.d018650 n n hn hn := by
  unfold _root_.GD.N0232.N0720.N1047.d018650
  apply _root_.GD.N0232.N0720.N1048.d019045 n n (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn)
    (_root_.GD.N0232.N0720.N1043.d019067 n)
  · intro θ
    rw [_root_.GD.N0232.N0720.N1043.d019072]
    calc _root_.GD.N0232.N0720.N1080.d014182 n n (_root_.GD.N0232.N0720.N1043.d019058 θ) (_root_.GD.N0232.N0720.N1159.d014633 n n (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn))
        ≤ _root_.GD.N0232.N0720.N1080.d014182 n n (_root_.GD.N0232.N0720.N1043.d019058 θ) (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn) :=
          (_root_.GD.N0232.N0720.N1159.d014634 n n (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn)).1 _
      _ = _root_.GD.N0232.N0720.N1080.d014182 n n θ (_root_.GD.N0232.N0720.N1080.d014180 n n hn hn) := _root_.GD.N0232.N0720.N1043.d019080 n hn θ
  · exact (_root_.GD.N0232.N0720.N1043.d019071 n _).le


theorem d019082 (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 n n (_root_.GD.N0232.N0720.N1043.d019058 θ) (_root_.GD.N0232.N0720.N1047.d018650 n n hn hn) =
      _root_.GD.N0232.N0720.N1080.d014182 n n θ (_root_.GD.N0232.N0720.N1047.d018650 n n hn hn) := by
  rw [← _root_.GD.N0232.N0720.N1043.d019072, _root_.GD.N0232.N0720.N1043.d019081]

end

end N1043
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1043.d019072
#print axioms _root_.GD.N0232.N0720.N1043.d019073
#print axioms _root_.GD.N0232.N0720.N1043.d019074
#print axioms _root_.GD.N0232.N0720.N1043.d019075
#print axioms _root_.GD.N0232.N0720.N1043.d019076
#print axioms _root_.GD.N0232.N0720.N1043.d019079
#print axioms _root_.GD.N0232.N0720.N1043.d019081
#print axioms _root_.GD.N0232.N0720.N1043.d019082
