import GD.Module1461

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0100.N0347
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1258
open _root_.GD.N0232.N0720.N1467 _root_.GD.N0232.N0720.N1468
open _root_.GD.N0232.N0720.N1472 _root_.GD.N0232.N0720.N1501
open _root_.GD.N0232.N0720.N1149
open _root_.GD.N0232.N0720.N1446 _root_.GD.N0232.N0720.N1028
open _root_.GD.N0232.N0720.N1476
open _root_.GD.N0232.N0720.N1342 _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1398
open _root_.GD.N0232.N0720.N1286 _root_.GD.N0232.N0720.N1459
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0633
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0710
open _root_.GD.N0230.N0664
open _root_.GD.N0230.N0668
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0095



structure d024036 (m n : ℕ) where
  bound : _root_.GD.N0232.N0720.N1080.d014168 → ℝ
  capValue : ℝ
  cap_nonneg : 0 ≤ capValue
  bound_nonneg : ∀ theta, 0 ≤ bound theta
  bound_le : ∀ theta, bound theta ≤ capValue * _root_.GD.N0232.N0720.N1257.d015508 m n theta
  affine : ∀ (g : _root_.GD.N0232.N0719.N0946.d009229) theta,
    bound (_root_.GD.N0232.N0720.N1215.d014272 g theta) = g.d009239 ^ 2 * bound theta
  reflection : ∀ theta, bound (_root_.GD.N0232.N0720.N1446.d019024 theta) = bound theta

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
variable (E : _root_.GD.N0100.N0347.d024036 m n)

def d024037 : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {p | ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≤ ENNReal.ofReal (E.bound theta)}

theorem d024038 : _root_.GD.N0100.N0347.d024037 m n E ⊆ _root_.GD.N0232.N0720.N1257.d015513 m n E.capValue := by
  intro p hp theta
  exact (hp theta).trans (ENNReal.ofReal_le_ofReal (E.bound_le theta))

theorem d024039 : IsClosed (_root_.GD.N0100.N0347.d024037 m n E) := by
  simpa [_root_.GD.N0100.N0347.d024037, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun theta ↦ ENNReal.ofReal (E.bound theta))
      (_root_.GD.N0232.N0720.N1080.d014173 m n))

theorem d024040 : Convex ℝ (_root_.GD.N0100.N0347.d024037 m n E) := by
  simpa [_root_.GD.N0100.N0347.d024037, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun theta ↦ ENNReal.ofReal (E.bound theta))
      (_root_.GD.N0232.N0720.N1080.d014173 m n))

theorem d024041 (g : _root_.GD.N0232.N0719.N0946.d009229)
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)} (hp : p ∈ _root_.GD.N0100.N0347.d024037 m n E) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p
      (_root_.GD.N0232.N0720.N1257.d015516 m n (_root_.GD.N0100.N0347.d024038 m n E hp)) ∈ _root_.GD.N0100.N0347.d024037 m n E := by
  intro eta
  let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta
  have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by simp [theta]
  rw [← heta, _root_.GD.N0232.N0720.N1159.d014643, E.affine]
  exact (mul_le_mul' le_rfl (hp theta)).trans_eq
    (ENNReal.ofReal_mul (sq_nonneg g.d009239)).symm

def d024042 : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  _root_.GD.N0100.N0347.d024037 m n E ∩ {p | _root_.GD.N0232.N0720.N1468.d018955 m n p}

def d024043 : Set (WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))) :=
  toWeakSpace ℝ _ '' _root_.GD.N0100.N0347.d024042 m n E

theorem d024044 : Convex ℝ (_root_.GD.N0100.N0347.d024042 m n E) := by
  intro x hx y hy a b ha hb hab
  refine ⟨_root_.GD.N0100.N0347.d024040 m n E hx.1 hy.1 ha hb hab, ?_⟩
  change _root_.GD.N0232.N0720.N1501.d016291 m n (a • x + b • y) = a • x + b • y
  rw [map_add, map_smul, map_smul, hx.2, hy.2]

theorem d024045 : IsClosed (_root_.GD.N0100.N0347.d024042 m n E) :=
  (_root_.GD.N0100.N0347.d024039 m n E).inter
    (isClosed_eq (_root_.GD.N0232.N0720.N1501.d016291 m n).continuous continuous_id)

include hm hn in
theorem d024046 (hne : (_root_.GD.N0100.N0347.d024037 m n E).Nonempty) :
    (_root_.GD.N0100.N0347.d024042 m n E).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  exact ⟨_root_.GD.N0232.N0720.N1501.d016291 m n p,
    (fun theta ↦ (_root_.GD.N0232.N0720.N1501.d016299 m n hm hn theta p).trans (hp theta)),
    _root_.GD.N0232.N0720.N1468.d018951 m n p⟩

theorem d024047 : IsCompact (_root_.GD.N0100.N0347.d024043 m n E) :=
  _root_.GD.N0230.N0633.d001201
    (Real.sqrt (E.capValue * _root_.GD.N0232.N0720.N1257.d015508 m n _root_.GD.N0232.N0720.N1080.d014169))
    (_root_.GD.N0100.N0347.d024044 m n E) (_root_.GD.N0100.N0347.d024045 m n E)
    (fun _ hp ↦ _root_.GD.N0232.N0720.N1257.d015518 m n E.cap_nonneg (_root_.GD.N0100.N0347.d024038 m n E hp.1))

theorem d024048 : Convex ℝ (_root_.GD.N0100.N0347.d024043 m n E) :=
  (_root_.GD.N0100.N0347.d024044 m n E).linear_image (toWeakSpace ℝ _).toLinearMap

theorem d024049 :
    _root_.GD.N0100.N0347.d024043 m n E ⊆ _root_.GD.N0232.N0720.N1257.d015519 m n E.capValue := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, _root_.GD.N0100.N0347.d024038 m n E hp.1, rfl⟩

include hm hn in
theorem d024050 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    MapsTo (_root_.GD.N0232.N0720.N1258.d015532 m n E.capValue E.cap_nonneg g)
      (_root_.GD.N0100.N0347.d024043 m n E) (_root_.GD.N0100.N0347.d024043 m n E) := by
  rintro _ ⟨p, hp, rfl⟩
  have hw : toWeakSpace ℝ _ p ∈ _root_.GD.N0232.N0720.N1257.d015519 m n E.capValue :=
    ⟨p, _root_.GD.N0100.N0347.d024038 m n E hp.1, rfl⟩
  rw [_root_.GD.N0232.N0720.N1258.d015534 m n E.capValue E.cap_nonneg g _ hw]
  simp only [LinearEquiv.symm_apply_apply]
  exact ⟨_, ⟨_root_.GD.N0100.N0347.d024041 m n E g hp.1,
    _root_.GD.N0095.d023051 m n hm hn
      (_root_.GD.N0232.N0720.N1257.d015516 m n (_root_.GD.N0100.N0347.d024038 m n E hp.1)) hp.2 g⟩, rfl⟩

include hm hn in
theorem d024051
    (hne : (_root_.GD.N0100.N0347.d024037 m n E).Nonempty) :
    ∃ p, ∃ hp : p ∈ _root_.GD.N0100.N0347.d024037 m n E, _root_.GD.N0232.N0720.N1468.d018955 m n p ∧
      ∀ g : _root_.GD.N0232.N0719.N0946.d009229, _root_.GD.N0232.N0720.N1159.d014642 m n g p
        (_root_.GD.N0232.N0720.N1257.d015516 m n (_root_.GD.N0100.N0347.d024038 m n E hp)) = p := by
  have hsub := _root_.GD.N0100.N0347.d024049 m n E
  obtain ⟨x, hx, hfix⟩ := _root_.GD.N0230.N0664.d001257
    (fun b r ↦ _root_.GD.N0232.N0720.N1258.d015532 m n E.capValue E.cap_nonneg ⟨b, r⟩)
    (_root_.GD.N0100.N0347.d024043 m n E)
    (_root_.GD.N0100.N0347.d024047 m n E) (_root_.GD.N0100.N0347.d024048 m n E)
    ((_root_.GD.N0100.N0347.d024046 m n hm hn E hne).image (toWeakSpace ℝ _))
    (_root_.GD.N0230.N0709.d001221.d001222
      (_root_.GD.N0232.N0720.N1258.d015541 m n E.capValue E.cap_nonneg) hsub)
    (fun b r ↦ _root_.GD.N0100.N0347.d024050 m n hm hn E ⟨b, r⟩)
    (fun b r ↦ (_root_.GD.N0232.N0720.N1258.d015537 m n E.capValue E.cap_nonneg ⟨b, r⟩).mono hsub)
    (fun b r x hx y hy a b' ha hb hab ↦
      _root_.GD.N0232.N0720.N1258.d015540 m n hm hn E.capValue E.cap_nonneg
        ⟨b, r⟩ (hsub hx) (hsub hy) ha hb hab)
    (fun b r c s x hx ↦ _root_.GD.N0232.N0720.N1258.d015539 m n E.capValue E.cap_nonneg
      ⟨b, r⟩ ⟨c, s⟩ x (hsub hx))
  obtain ⟨p, hp, rfl⟩ := hx
  refine ⟨p, hp.1, hp.2, ?_⟩
  intro g
  have hg : _root_.GD.N0232.N0720.N1258.d015532 m n E.capValue E.cap_nonneg g (toWeakSpace ℝ _ p) =
      toWeakSpace ℝ _ p := by
    cases g with
    | mk b r => exact hfix b r
  rw [_root_.GD.N0232.N0720.N1258.d015534 m n E.capValue E.cap_nonneg g _
    ⟨p, _root_.GD.N0100.N0347.d024038 m n E hp.1, rfl⟩] at hg
  exact (toWeakSpace ℝ _).injective hg

include hm hn in
theorem d024052
    (hne : (_root_.GD.N0100.N0347.d024037 m n E).Nonempty) :
    ∃ p, p ∈ _root_.GD.N0100.N0347.d024037 m n E ∧ _root_.GD.N0232.N0720.N1468.d018955 m n p ∧
      _root_.GD.N0232.N0720.N1159.d014652 m n p ∧ _root_.GD.N0232.N0720.N1446.d019032 m n p = p := by
  obtain ⟨p, hp, hs, hf⟩ :=
    _root_.GD.N0100.N0347.d024051 m n hm hn E hne
  have ha : _root_.GD.N0232.N0720.N1159.d014652 m n p :=
    (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn p
      (_root_.GD.N0232.N0720.N1257.d015516 m n (_root_.GD.N0100.N0347.d024038 m n E hp))).1 hf
  have hr : _root_.GD.N0232.N0720.N1446.d019032 m n p ∈ _root_.GD.N0100.N0347.d024037 m n E := by
    intro theta
    rw [_root_.GD.N0232.N0720.N1446.d019037]
    simpa only [E.reflection] using hp (_root_.GD.N0232.N0720.N1446.d019024 theta)
  let q := (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • _root_.GD.N0232.N0720.N1446.d019032 m n p
  have hq : q ∈ _root_.GD.N0100.N0347.d024037 m n E :=
    _root_.GD.N0100.N0347.d024040 m n E hp hr (by norm_num) (by norm_num) (by norm_num)
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · change _root_.GD.N0232.N0720.N1501.d016291 m n q = q
    dsimp [q]
    rw [map_add, map_smul, map_smul, hs, _root_.GD.N0232.N0720.N1472.d019545 m n hm hn hs]
  · have ha' := _root_.GD.N0232.N0720.N1028.d015330
      m n (1 / 2) p (_root_.GD.N0232.N0720.N1446.d019032 m n p) ha
      (_root_.GD.N0232.N0720.N1149.d019467 m n p ha)
    norm_num only [_root_.GD.N0230.N0668.d001343, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at ha'
    exact ha'
  · dsimp [q]
    rw [_root_.GD.N0232.N0720.N1446.d019034, _root_.GD.N0232.N0720.N1446.d019035, _root_.GD.N0232.N0720.N1446.d019035,
      _root_.GD.N0232.N0720.N1446.d019033, add_comm]

include hm hn in


theorem d024053
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤ ENNReal.ofReal (E.bound theta)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g ∧
      (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
        ENNReal.ofReal (E.bound theta) := by
  obtain ⟨p, _, hprisk⟩ := _root_.GD.N0232.N0720.N1257.d015531 m n E.capValue d hd
    (fun theta ↦ (hbound theta).trans (ENNReal.ofReal_le_ofReal (E.bound_le theta)))
  have hp : p ∈ _root_.GD.N0100.N0347.d024037 m n E := by
    intro theta
    rw [hprisk theta]
    exact hbound theta
  obtain ⟨q, hq, hqs, hqa, hqr⟩ :=
    _root_.GD.N0100.N0347.d024052 m n hm hn E ⟨p, hp⟩
  obtain ⟨r, hr, hrep, hra, hrr⟩ :=
    _root_.GD.N0232.N0720.N1149.d019466
      m n hm hn q (_root_.GD.N0232.N0720.N1257.d015516 m n (_root_.GD.N0100.N0347.d024038 m n E hq)) hqa hqs hqr
  let f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
    fun z ↦ _root_.GD.N0232.N0720.N1209.d012471 r z.1 z.2
  have hf : Measurable f :=
    _root_.GD.N0232.N0720.N1209.d012473 r hr
  have hraw (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1425.d014719 m n f =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1214.d014265 m n q :=
    (_root_.GD.N0232.N0720.N1342.d019639 m n hm hn r hra hrr theta).symm.trans
      ((hrep theta).trans
        (Filter.EventuallyEq.symm ((_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
          (_root_.GD.N0232.N0720.N1214.d014267 m n q))))
  have hfcap (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n f) ≤
        ENNReal.ofReal (E.bound theta) := by
    rw [_root_.GD.N0232.N0720.N1159.d014662 m n theta (hraw theta), _root_.GD.N0232.N0720.N1215.d014286]
    exact hq theta
  refine ⟨_root_.GD.N0232.N0720.N1286.d019582 f, _root_.GD.N0232.N0720.N1286.d019583 hf,
    _root_.GD.N0232.N0720.N1286.d019584 f, ?_⟩
  intro theta
  exact (_root_.GD.N0232.N0720.N1398.d019600 m n hm hn theta hf
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hfcap theta))).trans (hfcap theta)


def d024054 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  min (theta.scale₁ ^ 2 / (m : ℝ)) (theta.scale₂ ^ 2 / (n : ℝ))

include hm hn in
theorem d024055 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0100.N0347.d024054 m n theta ≤ 2 * _root_.GD.N0232.N0720.N1257.d015508 m n theta := by
  let a := theta.scale₁ ^ 2 / (m : ℝ)
  let b := theta.scale₂ ^ 2 / (n : ℝ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < a := div_pos (sq_pos_of_pos theta.scale₁_pos) hmR
  have hb : 0 < b := div_pos (sq_pos_of_pos theta.scale₂_pos) hnR
  have ho : _root_.GD.N0232.N0720.N1257.d015508 m n theta = a * b / (a + b) := by
    have hi : _root_.GD.N0232.N0720.N1257.d015508 m n theta = (a⁻¹ + b⁻¹)⁻¹ := by
      simp only [a, b, inv_div, _root_.GD.N0232.N0720.N1257.d015508]
    rw [hi]
    field_simp [ha.ne', hb.ne', (add_pos ha hb).ne']
    ring
  change min a b ≤ 2 * _root_.GD.N0232.N0720.N1257.d015508 m n theta
  rw [ho, ← mul_div_assoc]
  apply (le_div_iff₀ (add_pos ha hb)).mpr
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    nlinarith [mul_le_mul_of_nonneg_left hab ha.le]
  · rw [min_eq_right hba]
    nlinarith [mul_le_mul_of_nonneg_left hba hb.le]

def d024056 : _root_.GD.N0100.N0347.d024036 m n where
  bound := _root_.GD.N0100.N0347.d024054 m n
  capValue := 2
  cap_nonneg := by norm_num
  bound_nonneg := fun theta ↦ le_min (by positivity) (by positivity)
  bound_le := _root_.GD.N0100.N0347.d024055 m n hm hn
  affine := by
    intro g theta
    unfold _root_.GD.N0100.N0347.d024054
    simp only [_root_.GD.N0232.N0720.N1215.d014274, _root_.GD.N0232.N0720.N1215.d014275, mul_pow, mul_div_assoc]
    exact (mul_min_of_nonneg _ _ (sq_nonneg g.d009239)).symm
  reflection := by
    intro theta
    simp only [_root_.GD.N0100.N0347.d024054, _root_.GD.N0232.N0720.N1446.d019026, _root_.GD.N0232.N0720.N1446.d019027]

include hm hn in
theorem d024057
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (_root_.GD.N0100.N0347.d024054 m n theta)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g ∧
      (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
        ENNReal.ofReal (_root_.GD.N0100.N0347.d024054 m n theta) :=
  _root_.GD.N0100.N0347.d024053 m n hm hn (_root_.GD.N0100.N0347.d024056 m n hm hn) d hd hbound

open _root_.GD.N0045
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1424
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0232.N0720.N1396

theorem d024058 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0100.N0347.d024054 m n (_root_.GD.N0045.d023064 m n hm hn t) = min t.1 (1 - t.1) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold _root_.GD.N0100.N0347.d024054 _root_.GD.N0045.d023064 _root_.GD.N0232.N0720.N1424.d014846 _root_.GD.N0232.N0720.N1424.d014847
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr t.2.2.le)),
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) t.2.1.le)]
  simp [hm0, hn0, min_comm]

include hm hn in


theorem d024059
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (_root_.GD.N0100.N0347.d024054 m n theta)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g ∧
      (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
        (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 m n t) ≤
          (min t.1 (1 - t.1) / max t.1 (1 - t.1)) * t.1 * (1 - t.1) := by
  obtain ⟨g, hg, hgb, hcap⟩ :=
    _root_.GD.N0100.N0347.d024057 m n hm hn d hd hbound
  refine ⟨g, hg, hgb, ?_⟩
  intro t
  have hb := hcap (_root_.GD.N0045.d023064 m n hm hn t)
  rw [_root_.GD.N0232.N0720.N1335.d020089
    m n hm hn _ hg hgb] at hb
  have ho := _root_.GD.N0232.N0720.N1396.d014795 m n hm hn (_root_.GD.N0045.d023064 m n hm hn t)
  unfold _root_.GD.N0232.N0720.N1396.d014778 at ho
  rw [ho] at hb
  simp only [_root_.GD.N0045.d023065,
    _root_.GD.N0045.d023066, one_mul,
    _root_.GD.N0100.N0347.d024058] at hb
  have hb' := (ENNReal.ofReal_le_ofReal_iff
    (le_min t.2.1.le (sub_nonneg.mpr t.2.2.le))).mp hb
  have hid : min t.1 (1 - t.1) - t.1 * (1 - t.1) =
      (min t.1 (1 - t.1) / max t.1 (1 - t.1)) * t.1 * (1 - t.1) := by
    rcases le_total t.1 (1 - t.1) with h | h
    · rw [min_eq_left h, max_eq_right h]
      field_simp [(sub_pos.mpr t.2.2).ne']
      ring
    · rw [min_eq_right h, max_eq_left h]
      field_simp [t.2.1.ne']
  rw [← hid]
  change _ + (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 m n t) ≤ _ at hb'
  linarith

end
end GD.N0100.N0347

#print axioms _root_.GD.N0100.N0347.d024051
#print axioms _root_.GD.N0100.N0347.d024053
#print axioms _root_.GD.N0100.N0347.d024057
#print axioms _root_.GD.N0100.N0347.d024059
