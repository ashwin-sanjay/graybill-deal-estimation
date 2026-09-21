import GD.Module0979
import GD.Module1183









































set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0106.N0428.N0767

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1258
open _root_.GD.N0232.N0720.N1446
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0633
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0710
open _root_.GD.N0230.N0664
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)





def d021583 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  min (theta.scale₁ ^ 2 / m) (theta.scale₂ ^ 2 / n)

theorem d021584 (theta : _root_.GD.N0232.N0720.N1080.d014168) : 0 ≤ _root_.GD.N0106.N0428.N0767.d021583 m n theta :=
  le_min (by positivity) (by positivity)

theorem d021585 (hm : 1 ≤ m) (hn : 1 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0106.N0428.N0767.d021583 m n theta := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact lt_min (div_pos (sq_pos_of_pos theta.scale₁_pos) hm')
    (div_pos (sq_pos_of_pos theta.scale₂_pos) hn')


theorem d021586 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    ENNReal.ofReal (_root_.GD.N0106.N0428.N0767.d021583 m n theta) ≠ ⊤ :=
  ENNReal.ofReal_ne_top


theorem d021587 {theta eta : _root_.GD.N0232.N0720.N1080.d014168}
    (h₁ : theta.scale₁ = eta.scale₁) (h₂ : theta.scale₂ = eta.scale₂) :
    _root_.GD.N0106.N0428.N0767.d021583 m n theta = _root_.GD.N0106.N0428.N0767.d021583 m n eta := by
  simp [_root_.GD.N0106.N0428.N0767.d021583, h₁, h₂]


theorem d021588 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0106.N0428.N0767.d021583 m n (_root_.GD.N0232.N0720.N1446.d019024 theta) = _root_.GD.N0106.N0428.N0767.d021583 m n theta := rfl


theorem d021589 (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0106.N0428.N0767.d021583 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) = g.d009239 ^ 2 * _root_.GD.N0106.N0428.N0767.d021583 m n theta := by
  unfold _root_.GD.N0106.N0428.N0767.d021583
  simp only [_root_.GD.N0232.N0720.N1215.d014274, _root_.GD.N0232.N0720.N1215.d014275, mul_pow]
  rw [mul_div_assoc, mul_div_assoc, mul_min_of_nonneg _ _ (sq_nonneg g.d009239)]


theorem d021590 (hm : 1 ≤ m) (hn : 1 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0106.N0428.N0767.d021583 m n theta ≤ 2 * _root_.GD.N0232.N0720.N1257.d015508 m n theta := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < theta.scale₁ ^ 2 / m := div_pos (sq_pos_of_pos theta.scale₁_pos) hm'
  have hb : 0 < theta.scale₂ ^ 2 / n := div_pos (sq_pos_of_pos theta.scale₂_pos) hn'
  have ha' : (m : ℝ) / theta.scale₁ ^ 2 = (theta.scale₁ ^ 2 / m)⁻¹ := (inv_div _ _).symm
  have hb' : (n : ℝ) / theta.scale₂ ^ 2 = (theta.scale₂ ^ 2 / n)⁻¹ := (inv_div _ _).symm
  unfold _root_.GD.N0106.N0428.N0767.d021583 _root_.GD.N0232.N0720.N1257.d015508
  rw [ha', hb']
  set a := theta.scale₁ ^ 2 / m with ha_def
  set b := theta.scale₂ ^ 2 / n with hb_def
  have hsum : 0 < a⁻¹ + b⁻¹ := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hsum]
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, mul_add, mul_inv_cancel₀ ha.ne']
    have : a * b⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hb]
      exact hab
    linarith
  · rw [min_eq_right hab, mul_add, mul_inv_cancel₀ hb.ne']
    have : b * a⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one ha]
      exact hab
    linarith




def d021591 : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {p | ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≤ ENNReal.ofReal (_root_.GD.N0106.N0428.N0767.d021583 m n theta)}


theorem d021592 (hm : 1 ≤ m) (hn : 1 ≤ n) : _root_.GD.N0106.N0428.N0767.d021591 m n ⊆ _root_.GD.N0232.N0720.N1257.d015513 m n 2 := by
  intro p hp theta
  exact (hp theta).trans
    (ENNReal.ofReal_le_ofReal (_root_.GD.N0106.N0428.N0767.d021590 m n hm hn theta))

theorem d021593 {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hp : p ∈ _root_.GD.N0106.N0428.N0767.d021591 m n) : _root_.GD.N0232.N0720.N1159.d014637 m n p := by
  intro theta
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hp theta)

theorem d021594 : IsClosed (_root_.GD.N0106.N0428.N0767.d021591 m n) := by
  simpa [_root_.GD.N0106.N0428.N0767.d021591, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun theta ↦ ENNReal.ofReal (_root_.GD.N0106.N0428.N0767.d021583 m n theta))
      (_root_.GD.N0232.N0720.N1080.d014173 m n))

theorem d021595 : Convex ℝ (_root_.GD.N0106.N0428.N0767.d021591 m n) := by
  simpa [_root_.GD.N0106.N0428.N0767.d021591, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun theta ↦ ENNReal.ofReal (_root_.GD.N0106.N0428.N0767.d021583 m n theta))
      (_root_.GD.N0232.N0720.N1080.d014173 m n))


theorem d021596 {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hp : p ∈ _root_.GD.N0106.N0428.N0767.d021591 m n) : ‖p‖ ^ 2 ≤ _root_.GD.N0106.N0428.N0767.d021583 m n _root_.GD.N0232.N0720.N1080.d014169 := by
  have href := hp _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  exact (ENNReal.ofReal_le_ofReal_iff (_root_.GD.N0106.N0428.N0767.d021584 m n _root_.GD.N0232.N0720.N1080.d014169)).mp href

theorem d021597 {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hp : p ∈ _root_.GD.N0106.N0428.N0767.d021591 m n) : ‖p‖ ≤ Real.sqrt (_root_.GD.N0106.N0428.N0767.d021583 m n _root_.GD.N0232.N0720.N1080.d014169) := by
  have hs := Real.sq_sqrt (_root_.GD.N0106.N0428.N0767.d021584 m n _root_.GD.N0232.N0720.N1080.d014169)
  have hb := _root_.GD.N0106.N0428.N0767.d021596 m n hp
  nlinarith [norm_nonneg p, Real.sqrt_nonneg (_root_.GD.N0106.N0428.N0767.d021583 m n _root_.GD.N0232.N0720.N1080.d014169)]


def d021598 : Set (WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))) :=
  toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) '' _root_.GD.N0106.N0428.N0767.d021591 m n

theorem d021599 (x : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))) :
    x ∈ _root_.GD.N0106.N0428.N0767.d021598 m n ↔
      (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))).symm x ∈ _root_.GD.N0106.N0428.N0767.d021591 m n := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro hx
    exact ⟨_, hx, by simp⟩


theorem d021600 : IsCompact (_root_.GD.N0106.N0428.N0767.d021598 m n) :=
  _root_.GD.N0230.N0633.d001201
    (Real.sqrt (_root_.GD.N0106.N0428.N0767.d021583 m n _root_.GD.N0232.N0720.N1080.d014169))
    (_root_.GD.N0106.N0428.N0767.d021595 m n) (_root_.GD.N0106.N0428.N0767.d021594 m n)
    (fun p hp ↦ _root_.GD.N0106.N0428.N0767.d021597 m n hp)

theorem d021601 : Convex ℝ (_root_.GD.N0106.N0428.N0767.d021598 m n) :=
  (_root_.GD.N0106.N0428.N0767.d021595 m n).linear_image (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))).toLinearMap

theorem d021602 (hm : 1 ≤ m) (hn : 1 ≤ n) : _root_.GD.N0106.N0428.N0767.d021598 m n ⊆ _root_.GD.N0232.N0720.N1257.d015519 m n 2 :=
  Set.image_mono (_root_.GD.N0106.N0428.N0767.d021592 m n hm hn)



theorem d021603 (g : _root_.GD.N0232.N0719.N0946.d009229) {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hp : p ∈ _root_.GD.N0106.N0428.N0767.d021591 m n) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p (_root_.GD.N0106.N0428.N0767.d021593 m n hp) ∈ _root_.GD.N0106.N0428.N0767.d021591 m n := by
  intro eta
  let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta
  have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by simp [theta]
  rw [← heta, _root_.GD.N0232.N0720.N1159.d014643, _root_.GD.N0106.N0428.N0767.d021589]
  calc
    ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≤
        ENNReal.ofReal (g.d009239 ^ 2) * ENNReal.ofReal (_root_.GD.N0106.N0428.N0767.d021583 m n theta) :=
      mul_le_mul' le_rfl (hp theta)
    _ = ENNReal.ofReal (g.d009239 ^ 2 * _root_.GD.N0106.N0428.N0767.d021583 m n theta) :=
      (ENNReal.ofReal_mul (sq_nonneg g.d009239)).symm





theorem d021604
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤ ENNReal.ofReal (_root_.GD.N0106.N0428.N0767.d021583 m n theta)) :
    ∃ p ∈ _root_.GD.N0106.N0428.N0767.d021591 m n, ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta p = _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
  have hdLp : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n d hd
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound _root_.GD.N0232.N0720.N1080.d014169))
  refine ⟨hdLp.toLp d, ?_, ?_⟩
  · intro theta
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n theta d hdLp]
    exact hbound theta
  · intro theta
    exact (_root_.GD.N0232.N0720.N1080.d014198 m n theta d hdLp).symm





theorem d021605 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hne : (_root_.GD.N0106.N0428.N0767.d021591 m n).Nonempty) :
    ∃ p, ∃ hp : p ∈ _root_.GD.N0106.N0428.N0767.d021591 m n,
      ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
        _root_.GD.N0232.N0720.N1159.d014642 m n g p (_root_.GD.N0106.N0428.N0767.d021593 m n hp) = p := by
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := by omega
  have hC : (0 : ℝ) ≤ 2 := by norm_num
  have hsub : _root_.GD.N0106.N0428.N0767.d021598 m n ⊆ _root_.GD.N0232.N0720.N1257.d015519 m n 2 := _root_.GD.N0106.N0428.N0767.d021602 m n hm1 hn1
  have hb : _root_.GD.N0230.N0709.d001221 (_root_.GD.N0106.N0428.N0767.d021598 m n) :=
    _root_.GD.N0230.N0709.d001221.d001222
      (_root_.GD.N0232.N0720.N1258.d015541 m n 2 hC) hsub
  have hmaps (g : _root_.GD.N0232.N0719.N0946.d009229) :
      MapsTo (_root_.GD.N0232.N0720.N1258.d015532 m n 2 hC g) (_root_.GD.N0106.N0428.N0767.d021598 m n) (_root_.GD.N0106.N0428.N0767.d021598 m n) := by
    intro x hx
    rw [_root_.GD.N0232.N0720.N1258.d015534 m n 2 hC g x (hsub hx)]
    exact ⟨_, _root_.GD.N0106.N0428.N0767.d021603 m n g ((_root_.GD.N0106.N0428.N0767.d021599 m n x).mp hx), rfl⟩
  obtain ⟨x, hx, hfix⟩ := _root_.GD.N0230.N0664.d001257
    (fun b r ↦ _root_.GD.N0232.N0720.N1258.d015532 m n 2 hC ⟨b, r⟩) (_root_.GD.N0106.N0428.N0767.d021598 m n)
    (_root_.GD.N0106.N0428.N0767.d021600 m n) (_root_.GD.N0106.N0428.N0767.d021601 m n)
    (hne.image (toWeakSpace ℝ _)) hb
    (fun b r ↦ hmaps ⟨b, r⟩)
    (fun b r ↦ (_root_.GD.N0232.N0720.N1258.d015537 m n 2 hC ⟨b, r⟩).mono hsub)
    (fun shift logScale x hx y hy a b ha hb hab ↦
      _root_.GD.N0232.N0720.N1258.d015540 m n hm hn 2 hC ⟨shift, logScale⟩
        (hsub hx) (hsub hy) ha hb hab)
    (fun b r c t x hx ↦ _root_.GD.N0232.N0720.N1258.d015539 m n 2 hC ⟨b, r⟩ ⟨c, t⟩ x (hsub hx))
  refine ⟨(toWeakSpace ℝ _).symm x, (_root_.GD.N0106.N0428.N0767.d021599 m n x).mp hx, ?_⟩
  intro g
  have hg : _root_.GD.N0232.N0720.N1258.d015532 m n 2 hC g x = x := by
    cases g with
    | mk b r => exact hfix b r
  rw [_root_.GD.N0232.N0720.N1258.d015534 m n 2 hC g x (hsub hx)] at hg
  exact (toWeakSpace ℝ _).injective (hg.trans (by simp))





theorem d021606 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hne : (_root_.GD.N0106.N0428.N0767.d021591 m n).Nonempty) :
    ∃ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable e ∧
      (∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ omega, e (g • omega) = g • e omega) ∧
      ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤ ENNReal.ofReal (_root_.GD.N0106.N0428.N0767.d021583 m n theta) := by
  obtain ⟨p, hp, hfix⟩ := _root_.GD.N0106.N0428.N0767.d021605 m n hm hn hne
  obtain ⟨e, he, heae, hequiv⟩ :=
    _root_.GD.N0232.N0720.N1214.d014271 m n hm hn p
      (fun g ↦ _root_.GD.N0232.N0720.N1159.d014641 m n g p (_root_.GD.N0106.N0428.N0767.d021593 m n hp))
      hfix
  refine ⟨e, he, hequiv, ?_⟩
  intro theta
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n theta (heae theta), _root_.GD.N0232.N0720.N1215.d014286]
  exact hp theta




theorem d021607 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤ ENNReal.ofReal (_root_.GD.N0106.N0428.N0767.d021583 m n theta)) :
    ∃ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable e ∧
      (∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ omega, e (g • omega) = g • e omega) ∧
      (∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤ ENNReal.ofReal (_root_.GD.N0106.N0428.N0767.d021583 m n theta)) ∧
      ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≠ ⊤ := by
  obtain ⟨p, hp, _⟩ := _root_.GD.N0106.N0428.N0767.d021604 m n d hd hbound
  obtain ⟨e, he, hequiv, hrisk⟩ := _root_.GD.N0106.N0428.N0767.d021606 m n hm hn ⟨p, hp⟩
  exact ⟨e, he, hequiv, hrisk, fun theta ↦ ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hrisk theta)⟩

end

end GD.N0106.N0428.N0767

#print axioms _root_.GD.N0106.N0428.N0767.d021589
#print axioms _root_.GD.N0106.N0428.N0767.d021590
#print axioms _root_.GD.N0106.N0428.N0767.d021600
#print axioms _root_.GD.N0106.N0428.N0767.d021603
#print axioms _root_.GD.N0106.N0428.N0767.d021605
#print axioms _root_.GD.N0106.N0428.N0767.d021607
