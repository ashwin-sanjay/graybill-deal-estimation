import GD.Module1358
import GD.Module0979
import GD.Module1210
import GD.Module1234
import GD.Module0968
import GD.Module0982

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0095
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1258
open _root_.GD.N0232.N0720.N1467 _root_.GD.N0232.N0720.N1468
open _root_.GD.N0232.N0720.N1472
open _root_.GD.N0232.N0720.N1475 _root_.GD.N0232.N0720.N1501
open _root_.GD.N0230.N0602 _root_.GD.N0230.N0633
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0710
open _root_.GD.N0230.N0664
open _root_.GD.N0232.N0719.N0946

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn in
theorem d023051
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hsummary : _root_.GD.N0232.N0720.N1468.d018955 m n p)
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1468.d018955 m n (_root_.GD.N0232.N0720.N1159.d014642 m n g p hp) := by
  obtain ⟨value, hvalue, hrep⟩ :=
    _root_.GD.N0232.N0720.N1501.d016306 m n p
  rw [hsummary] at hrep
  let transportedValue :
      _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ :=
    fun summary ↦ g • value (g⁻¹ • summary)
  have htransportedValue : Measurable transportedValue := by
    unfold transportedValue
    exact measurable_const.smul
      (hvalue.comp (measurable_const.smul measurable_id))
  have hcanonical :
      (fun omega ↦ _root_.GD.N0232.N0720.N1159.d014642 m n g p hp omega) =ᵐ[
          _root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
    exact (_root_.GD.N0232.N0720.N1214.d014267 m n
      (_root_.GD.N0232.N0720.N1159.d014642 m n g p hp)).symm.trans
        (_root_.GD.N0232.N0720.N1482.d015160 g p hp)
  have hdecisionRep :
      _root_.GD.N0232.N0720.N1214.d014265 m n p =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n :=
    (_root_.GD.N0232.N0720.N1214.d014267 m n p).trans hrep
  have htransportRep :
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014261 m n g (value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) :=
    _root_.GD.N0232.N0720.N1215.d014909 m n g hdecisionRep
  have hpointwise :
      _root_.GD.N0232.N0720.N1214.d014261 m n g (value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =
        transportedValue ∘ _root_.GD.N0232.N0720.N1467.d012542 m n := by
    funext omega
    unfold _root_.GD.N0232.N0720.N1214.d014261 transportedValue
    simp only [Function.comp_apply]
    rw [_root_.GD.N0232.N0720.N1475.d018975 m n
      (lt_of_lt_of_le (by omega) hm)
      (lt_of_lt_of_le (by omega) hn) g⁻¹ omega]
  have hfactor :
      (fun omega ↦ _root_.GD.N0232.N0720.N1159.d014642 m n g p hp omega) =ᵐ[
          _root_.GD.N0232.N0720.N1080.d014172 m n]
        transportedValue ∘ _root_.GD.N0232.N0720.N1467.d012542 m n := by
    exact hcanonical.trans (htransportRep.trans
      (Filter.Eventually.of_forall fun omega ↦ congrFun hpointwise omega))
  apply (_root_.GD.N0232.N0720.N1472.d019544 m n _).2
  have hstrong : StronglyMeasurable[_root_.GD.N0232.N0720.N1501.d016287 m n]
      (transportedValue ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) :=
    (htransportedValue.comp
      (comap_measurable (_root_.GD.N0232.N0720.N1467.d012542 m n))).stronglyMeasurable
  exact hstrong.aestronglyMeasurable.congr hfactor.symm

def d023052 (C : ℝ) : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  _root_.GD.N0232.N0720.N1257.d015513 m n C ∩ {p | _root_.GD.N0232.N0720.N1468.d018955 m n p}

def d023053 (C : ℝ) : Set (WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))) :=
  toWeakSpace ℝ _ '' _root_.GD.N0095.d023052 m n C

theorem d023054 (C : ℝ) : Convex ℝ (_root_.GD.N0095.d023052 m n C) := by
  intro x hx y hy a b ha hb hab
  refine ⟨_root_.GD.N0232.N0720.N1257.d015515 m n C hx.1 hy.1 ha hb hab, ?_⟩
  change _root_.GD.N0232.N0720.N1501.d016291 m n (a • x + b • y) = a • x + b • y
  rw [map_add, map_smul, map_smul, hx.2, hy.2]

theorem d023055 (C : ℝ) : IsClosed (_root_.GD.N0095.d023052 m n C) :=
  (_root_.GD.N0232.N0720.N1257.d015514 m n C).inter
    (isClosed_eq (_root_.GD.N0232.N0720.N1501.d016291 m n).continuous continuous_id)

include hm hn in
theorem d023056 (C : ℝ) (hne : (_root_.GD.N0232.N0720.N1257.d015513 m n C).Nonempty) :
    (_root_.GD.N0095.d023052 m n C).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  exact ⟨_root_.GD.N0232.N0720.N1501.d016291 m n p,
    (fun theta ↦ (_root_.GD.N0232.N0720.N1501.d016299 m n hm hn theta p).trans (hp theta)),
    _root_.GD.N0232.N0720.N1468.d018951 m n p⟩

theorem d023057 (C : ℝ) (hC : 0 ≤ C) :
    IsCompact (_root_.GD.N0095.d023053 m n C) :=
  _root_.GD.N0230.N0633.d001201
    (Real.sqrt (C * _root_.GD.N0232.N0720.N1257.d015508 m n _root_.GD.N0232.N0720.N1080.d014169))
    (_root_.GD.N0095.d023054 m n C) (_root_.GD.N0095.d023055 m n C)
    (fun _ hp ↦ _root_.GD.N0232.N0720.N1257.d015518 m n hC hp.1)

theorem d023058 (C : ℝ) : Convex ℝ (_root_.GD.N0095.d023053 m n C) :=
  (_root_.GD.N0095.d023054 m n C).linear_image (toWeakSpace ℝ _).toLinearMap

theorem d023059 (C : ℝ) : _root_.GD.N0095.d023053 m n C ⊆ _root_.GD.N0232.N0720.N1257.d015519 m n C := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, hp.1, rfl⟩

include hm hn in
theorem d023060 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    MapsTo (_root_.GD.N0232.N0720.N1258.d015532 m n C hC g) (_root_.GD.N0095.d023053 m n C)
      (_root_.GD.N0095.d023053 m n C) := by
  rintro _ ⟨p, hp, rfl⟩
  have hw : toWeakSpace ℝ _ p ∈ _root_.GD.N0232.N0720.N1257.d015519 m n C := ⟨p, hp.1, rfl⟩
  rw [_root_.GD.N0232.N0720.N1258.d015534 m n C hC g _ hw]
  simp only [LinearEquiv.symm_apply_apply]
  exact ⟨_, ⟨_root_.GD.N0232.N0720.N1257.d015523 m n hC g hp.1,
    _root_.GD.N0095.d023051 m n hm hn
      (_root_.GD.N0232.N0720.N1257.d015516 m n hp.1) hp.2 g⟩, rfl⟩

include hm hn in


theorem d023061
    (C : ℝ) (hC : 0 ≤ C) (hne : (_root_.GD.N0232.N0720.N1257.d015513 m n C).Nonempty) :
    ∃ p, ∃ hp : p ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C, _root_.GD.N0232.N0720.N1468.d018955 m n p ∧
      ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
        _root_.GD.N0232.N0720.N1159.d014642 m n g p (_root_.GD.N0232.N0720.N1257.d015516 m n hp) = p := by
  have hsub := _root_.GD.N0095.d023059 m n C
  obtain ⟨x, hx, hfix⟩ := _root_.GD.N0230.N0664.d001257
    (fun b r ↦ _root_.GD.N0232.N0720.N1258.d015532 m n C hC ⟨b, r⟩) (_root_.GD.N0095.d023053 m n C)
    (_root_.GD.N0095.d023057 m n C hC) (_root_.GD.N0095.d023058 m n C)
    ((_root_.GD.N0095.d023056 m n hm hn C hne).image (toWeakSpace ℝ _))
    (_root_.GD.N0230.N0709.d001221.d001222
      (_root_.GD.N0232.N0720.N1258.d015541 m n C hC) hsub)
    (fun b r ↦ _root_.GD.N0095.d023060 m n hm hn C hC ⟨b, r⟩)
    (fun b r ↦ (_root_.GD.N0232.N0720.N1258.d015537 m n C hC ⟨b, r⟩).mono hsub)
    (fun b r x hx y hy a b' ha hb hab ↦
      _root_.GD.N0232.N0720.N1258.d015540 m n hm hn C hC ⟨b, r⟩
        (hsub hx) (hsub hy) ha hb hab)
    (fun b r c s x hx ↦ _root_.GD.N0232.N0720.N1258.d015539 m n C hC ⟨b, r⟩ ⟨c, s⟩ x (hsub hx))
  obtain ⟨p, hp, rfl⟩ := hx
  refine ⟨p, hp.1, hp.2, ?_⟩
  intro g
  have hg : _root_.GD.N0232.N0720.N1258.d015532 m n C hC g (toWeakSpace ℝ _ p) = toWeakSpace ℝ _ p := by
    cases g with
    | mk b r => exact hfix b r
  rw [_root_.GD.N0232.N0720.N1258.d015534 m n C hC g _ ⟨p, hp.1, rfl⟩] at hg
  exact (toWeakSpace ℝ _).injective hg

end
end GD.N0095

#print axioms _root_.GD.N0095.d023051
#print axioms _root_.GD.N0095.d023061

namespace GD.N0075
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
open _root_.GD.N0232.N0720.N1286
open _root_.GD.N0232.N0720.N1459
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0668
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0095

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn in


theorem d023062
    (C : ℝ) (hC : 0 ≤ C) (hne : (_root_.GD.N0232.N0720.N1257.d015513 m n C).Nonempty) :
    ∃ p, p ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C ∧ _root_.GD.N0232.N0720.N1468.d018955 m n p ∧
      _root_.GD.N0232.N0720.N1159.d014652 m n p ∧
      _root_.GD.N0232.N0720.N1446.d019032 m n p = p := by
  obtain ⟨p, hp, hs, hf⟩ :=
    _root_.GD.N0095.d023061 m n hm hn C hC hne
  have ha : _root_.GD.N0232.N0720.N1159.d014652 m n p :=
    (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn p (_root_.GD.N0232.N0720.N1257.d015516 m n hp)).1 hf
  have hr : _root_.GD.N0232.N0720.N1446.d019032 m n p ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C := by
    intro theta
    rw [_root_.GD.N0232.N0720.N1446.d019037]
    simpa only [_root_.GD.N0232.N0720.N1257.d015508, _root_.GD.N0232.N0720.N1446.d019026, _root_.GD.N0232.N0720.N1446.d019027]
      using hp (_root_.GD.N0232.N0720.N1446.d019024 theta)
  let q := (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • _root_.GD.N0232.N0720.N1446.d019032 m n p
  have hq : q ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C :=
    _root_.GD.N0232.N0720.N1257.d015515 m n C hp hr (by norm_num) (by norm_num) (by norm_num)
  refine ⟨q, hq, ?_, ?_, ?_⟩
  · change _root_.GD.N0232.N0720.N1501.d016291 m n q = q
    dsimp [q]
    rw [map_add, map_smul, map_smul, hs,
      _root_.GD.N0232.N0720.N1472.d019545 m n hm hn hs]
  · have ha' := _root_.GD.N0232.N0720.N1028.d015330
      m n (1 / 2) p (_root_.GD.N0232.N0720.N1446.d019032 m n p) ha
      (_root_.GD.N0232.N0720.N1149.d019467 m n p ha)
    norm_num only [_root_.GD.N0230.N0668.d001343, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at ha'
    exact ha'
  · dsimp [q]
    rw [_root_.GD.N0232.N0720.N1446.d019034, _root_.GD.N0232.N0720.N1446.d019035, _root_.GD.N0232.N0720.N1446.d019035,
      _root_.GD.N0232.N0720.N1446.d019033, add_comm]

include hm hn in



theorem d023063
    (C : ℝ) (hC : 0 ≤ C)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g ∧
      (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
  obtain ⟨p, hp, _⟩ := _root_.GD.N0232.N0720.N1257.d015531 m n C d hd hbound
  obtain ⟨q, hq, hqs, hqa, hqr⟩ :=
    _root_.GD.N0075.d023062 m n hm hn C hC ⟨p, hp⟩
  obtain ⟨r, hr, hrep, hra, hrr⟩ :=
    _root_.GD.N0232.N0720.N1149.d019466
      m n hm hn q (_root_.GD.N0232.N0720.N1257.d015516 m n hq) hqa hqs hqr
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
        ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
    rw [_root_.GD.N0232.N0720.N1159.d014662 m n theta (hraw theta), _root_.GD.N0232.N0720.N1215.d014286]
    exact hq theta
  refine ⟨_root_.GD.N0232.N0720.N1286.d019582 f, _root_.GD.N0232.N0720.N1286.d019583 hf,
    _root_.GD.N0232.N0720.N1286.d019584 f, ?_⟩
  intro theta
  exact (_root_.GD.N0232.N0720.N1398.d019600 m n hm hn theta hf
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hfcap theta))).trans (hfcap theta)

end
end GD.N0075

#print axioms _root_.GD.N0075.d023062
#print axioms _root_.GD.N0075.d023063

namespace GD.N0045
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1424
open _root_.GD.N0107 _root_.GD.N0137
open _root_.GD.N0232.N0720.N1396
open _root_.GD.N0230.N0611
open _root_.GD.N0075

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d023064 (t : _root_.GD.N0232.N0720.N1441.d013676) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := 0
  scale₁ := _root_.GD.N0232.N0720.N1424.d014846 m t.1
  scale₂ := _root_.GD.N0232.N0720.N1424.d014847 n t.1
  scale₁_pos := _root_.GD.N0232.N0720.N1424.d014848 hm t.2.2
  scale₂_pos := _root_.GD.N0232.N0720.N1424.d014849 hn t.2.1

theorem d023065 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0107.d009045 m n (_root_.GD.N0045.d023064 m n hm hn t).scale₁
      (_root_.GD.N0045.d023064 m n hm hn t).scale₂ = 1 :=
  _root_.GD.N0232.N0720.N1424.d014852 hm hn t.2.1 t.2.2

theorem d023066 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0107.d009046 m n
      (_root_.GD.N0045.d023064 m n hm hn t).scale₁
      (_root_.GD.N0045.d023064 m n hm hn t).scale₂ = t.1 :=
  _root_.GD.N0232.N0720.N1424.d014853 hm hn t.2.1 t.2.2

theorem d023067 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1257.d015508 m n (_root_.GD.N0045.d023064 m n hm hn t) = t.1 * (1 - t.1) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have ht0 : t.1 ≠ 0 := t.2.1.ne'
  have ht1 : 1 - t.1 ≠ 0 := (sub_pos.mpr t.2.2).ne'
  unfold _root_.GD.N0232.N0720.N1257.d015508 _root_.GD.N0045.d023064 _root_.GD.N0232.N0720.N1424.d014846 _root_.GD.N0232.N0720.N1424.d014847
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr t.2.2.le)),
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) t.2.1.le)]
  have hsum : (m : ℝ) / ((m : ℝ) * (1 - t.1)) +
      (n : ℝ) / ((n : ℝ) * t.1) = (t.1 * (1 - t.1))⁻¹ := by
    field_simp [hm0, hn0, ht0, ht1]
    ring
  rw [hsum, inv_inv]

include hm hn in


theorem d023068
    (C : ℝ) (hC : 0 ≤ C)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g ∧
      (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
        (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 m n t) ≤ (C - 1) * t.1 * (1 - t.1) := by
  obtain ⟨g, hg, hgb, hcap⟩ := _root_.GD.N0075.d023063
    m n hm hn C hC d hd hbound
  refine ⟨g, hg, hgb, ?_⟩
  intro t
  have hb := hcap (_root_.GD.N0045.d023064 m n hm hn t)
  rw [_root_.GD.N0232.N0720.N1335.d020089
    m n hm hn _ hg hgb] at hb
  have ho := _root_.GD.N0232.N0720.N1396.d014795 m n hm hn (_root_.GD.N0045.d023064 m n hm hn t)
  unfold _root_.GD.N0232.N0720.N1396.d014778 at ho
  rw [ho] at hb
  simp only [_root_.GD.N0045.d023065, _root_.GD.N0045.d023066, one_mul,
    _root_.GD.N0045.d023067] at hb
  have hb' := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (mul_nonneg t.2.1.le (sub_nonneg.mpr t.2.2.le)))).mp hb
  change _ + (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 m n t) ≤ _ at hb'
  nlinarith

include hm hn in


theorem d023069
    (C : ℝ) (hC : 0 ≤ C)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g ∧
      (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
        (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 m n t) ≤ C * t.1 * (1 - t.1) := by
  obtain ⟨g, hg, hb, hc⟩ := _root_.GD.N0045.d023068 m n hm hn C hC d hd hbound
  refine ⟨g, hg, hb, fun t ↦ (hc t).trans ?_⟩
  have ht : 0 ≤ t.1 * (1 - t.1) := mul_nonneg t.2.1.le (sub_nonneg.mpr t.2.2.le)
  nlinarith

include hm hn in


theorem d023070
    (hred : ∀ (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ), Measurable g →
      (∀ z, g z ∈ Icc (0 : ℝ) 1) → ∀ C : ℝ,
      ¬ (∀ t : _root_.GD.N0232.N0720.N1441.d013676,
        (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 m n t) ≤ C * t.1 * (1 - t.1))) :
    _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤ := by
  by_contra hfinite
  obtain ⟨e, he, heq⟩ :=
    _root_.GD.N0232.N0720.N1222.d015570 m n hm hn
  let C := (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hval : ENNReal.ofReal C = _root_.GD.N0232.N0720.N1256.d015549 m n := ENNReal.ofReal_toReal hfinite
  have hbound (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
    apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) C hC theta e).mp
    rw [hval, ← heq]
    exact le_iSup (fun eta ↦ _root_.GD.N0232.N0720.N1256.d015547 m n eta e) theta
  obtain ⟨g, hg, hb, hcap⟩ := _root_.GD.N0045.d023068 m n hm hn C hC e he.1.1 hbound
  exact hred g hg hb (C - 1) hcap

include hm hn in


theorem d023071 :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g ∧
      (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      _root_.GD.N0232.N0720.N1256.d015548 m n (_root_.GD.N0232.N0720.N1425.d014719 m n g) = _root_.GD.N0232.N0720.N1256.d015549 m n := by
  by_cases htop : _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤
  · refine ⟨fun _ ↦ 0, measurable_const, (fun _ ↦ by norm_num), ?_⟩
    apply le_antisymm
    · rw [htop]; exact le_top
    · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 m n)
        (_root_.GD.N0232.N0720.N1398.d019599 m n measurable_const)
  · obtain ⟨e, he, heq⟩ :=
      _root_.GD.N0232.N0720.N1222.d015570 m n hm hn
    let C := (_root_.GD.N0232.N0720.N1256.d015549 m n).toReal
    have hC : 0 ≤ C := ENNReal.toReal_nonneg
    have hval : ENNReal.ofReal C = _root_.GD.N0232.N0720.N1256.d015549 m n := ENNReal.ofReal_toReal htop
    have hbound (theta : _root_.GD.N0232.N0720.N1080.d014168) :
        _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
      apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) C hC theta e).mp
      rw [hval, ← heq]
      exact le_iSup (fun eta ↦ _root_.GD.N0232.N0720.N1256.d015547 m n eta e) theta
    obtain ⟨g, hg, hb, hc⟩ := _root_.GD.N0075.d023063 m n hm hn C hC e he.1.1 hbound
    refine ⟨g, hg, hb, le_antisymm ?_ ?_⟩
    · rw [← hval]
      exact iSup_le fun theta ↦
        (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) C hC theta _).mpr (hc theta)
    · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1256.d015547 m n)
        (_root_.GD.N0232.N0720.N1398.d019599 m n hg)

end
end GD.N0045

#print axioms _root_.GD.N0045.d023067
#print axioms _root_.GD.N0045.d023068
#print axioms _root_.GD.N0045.d023069
#print axioms _root_.GD.N0045.d023070

#print axioms _root_.GD.N0045.d023071
