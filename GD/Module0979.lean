import GD.Module0096
import GD.Module0978
import GD.Module0950

set_option autoImplicit false
set_option warningAsError true












open MeasureTheory Set

namespace GD.N0232.N0720.N1258

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1255
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0710
open _root_.GD.N0230.N0664
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)



def d015532 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (x : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))) :
    WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) := by
  classical
  exact if hx : x ∈ _root_.GD.N0232.N0720.N1257.d015519 m n C then
    (_root_.GD.N0232.N0720.N1257.d015528 m n C hC g ⟨x, hx⟩).1 else x

theorem d015533 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0232.N0720.N1257.d015519 m n C) :
    _root_.GD.N0232.N0720.N1258.d015532 m n C hC g p.1 = (_root_.GD.N0232.N0720.N1257.d015528 m n C hC g p).1 := by
  simp [_root_.GD.N0232.N0720.N1258.d015532, p.2]

theorem d015534 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (x : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)))
    (hx : x ∈ _root_.GD.N0232.N0720.N1257.d015519 m n C) :
    _root_.GD.N0232.N0720.N1258.d015532 m n C hC g x = toWeakSpace ℝ _
      (_root_.GD.N0232.N0720.N1159.d014642 m n g ((toWeakSpace ℝ _).symm x)
        (_root_.GD.N0232.N0720.N1257.d015516 m n ((_root_.GD.N0232.N0720.N1257.d015522 m n C x).mp hx))) := by
  simp [_root_.GD.N0232.N0720.N1258.d015532, hx, _root_.GD.N0232.N0720.N1257.d015528, _root_.GD.N0232.N0720.N1257.d015527, _root_.GD.N0232.N0720.N1257.d015524]

theorem d015535 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    MapsTo (_root_.GD.N0232.N0720.N1258.d015532 m n C hC g) (_root_.GD.N0232.N0720.N1257.d015519 m n C) (_root_.GD.N0232.N0720.N1257.d015519 m n C) := by
  intro x hx
  rw [show _root_.GD.N0232.N0720.N1258.d015532 m n C hC g x =
      (_root_.GD.N0232.N0720.N1257.d015528 m n C hC g ⟨x, hx⟩).1 from
        _root_.GD.N0232.N0720.N1258.d015533 m n C hC g ⟨x, hx⟩]
  exact (_root_.GD.N0232.N0720.N1257.d015528 m n C hC g ⟨x, hx⟩).2

theorem d015536 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    Continuous (_root_.GD.N0232.N0720.N1257.d015528 m n C hC g) := by
  apply _root_.GD.N0232.N0720.N1255.d014925 m n (_root_.GD.N0232.N0720.N1257.d015519 m n C) (_root_.GD.N0232.N0720.N1257.d015520 m n hC)
    (fun x hx ↦ _root_.GD.N0232.N0720.N1257.d015516 m n ((_root_.GD.N0232.N0720.N1257.d015522 m n C x).mp hx)) g
  intro p
  rfl

theorem d015537 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    ContinuousOn (_root_.GD.N0232.N0720.N1258.d015532 m n C hC g) (_root_.GD.N0232.N0720.N1257.d015519 m n C) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hc := continuous_subtype_val.comp (_root_.GD.N0232.N0720.N1258.d015536 m n C hC g)
  convert hc using 1
  funext p
  exact _root_.GD.N0232.N0720.N1258.d015533 m n C hC g p

theorem d015538 (C : ℝ) (hC : 0 ≤ C) (g h : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0232.N0720.N1257.d015519 m n C) :
    _root_.GD.N0232.N0720.N1257.d015528 m n C hC g (_root_.GD.N0232.N0720.N1257.d015528 m n C hC h p) =
      _root_.GD.N0232.N0720.N1257.d015528 m n C hC (g * h) p := by
  simp only [_root_.GD.N0232.N0720.N1257.d015528, Equiv.symm_apply_apply, _root_.GD.N0232.N0720.N1257.d015526]

theorem d015539 (C : ℝ) (hC : 0 ≤ C) (g h : _root_.GD.N0232.N0719.N0946.d009229)
    (x : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)))
    (hx : x ∈ _root_.GD.N0232.N0720.N1257.d015519 m n C) :
    _root_.GD.N0232.N0720.N1258.d015532 m n C hC g (_root_.GD.N0232.N0720.N1258.d015532 m n C hC h x) =
      _root_.GD.N0232.N0720.N1258.d015532 m n C hC (g * h) x := by
  let p : _root_.GD.N0232.N0720.N1257.d015519 m n C := ⟨x, hx⟩
  change _root_.GD.N0232.N0720.N1258.d015532 m n C hC g (_root_.GD.N0232.N0720.N1258.d015532 m n C hC h p.1) =
    _root_.GD.N0232.N0720.N1258.d015532 m n C hC (g * h) p.1
  simp only [_root_.GD.N0232.N0720.N1258.d015533]
  exact congrArg Subtype.val (_root_.GD.N0232.N0720.N1258.d015538 m n C hC g h p)

theorem d015540
    (hm : 2 ≤ m) (hn : 2 ≤ n) (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0230.N0710.d001232 (_root_.GD.N0232.N0720.N1258.d015532 m n C hC g) (_root_.GD.N0232.N0720.N1257.d015519 m n C) := by
  intro x hx y hy a b ha hb hab
  have hxy := _root_.GD.N0232.N0720.N1257.d015521 m n C hx hy ha hb hab
  rw [_root_.GD.N0232.N0720.N1258.d015534 m n C hC g _ hxy,
    _root_.GD.N0232.N0720.N1258.d015534 m n C hC g x hx,
    _root_.GD.N0232.N0720.N1258.d015534 m n C hC g y hy]
  have h := _root_.GD.N0232.N0720.N1257.d015529 m n hm hn g
    ((toWeakSpace ℝ _).symm x) ((toWeakSpace ℝ _).symm y)
    (_root_.GD.N0232.N0720.N1257.d015516 m n ((_root_.GD.N0232.N0720.N1257.d015522 m n C x).mp hx))
    (_root_.GD.N0232.N0720.N1257.d015516 m n ((_root_.GD.N0232.N0720.N1257.d015522 m n C y).mp hy)) hab
    (_root_.GD.N0232.N0720.N1257.d015516 m n (_root_.GD.N0232.N0720.N1257.d015515 m n C
      ((_root_.GD.N0232.N0720.N1257.d015522 m n C x).mp hx)
      ((_root_.GD.N0232.N0720.N1257.d015522 m n C y).mp hy) ha hb hab))
  simpa only [map_add, map_smul] using congrArg (toWeakSpace ℝ _) h

theorem d015541 (C : ℝ) (hC : 0 ≤ C) :
    _root_.GD.N0230.N0709.d001221 (_root_.GD.N0232.N0720.N1257.d015519 m n C) := by
  apply (Metric.isBounded_closedBall (x := (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)))
    (r := Real.sqrt (C * _root_.GD.N0232.N0720.N1257.d015508 m n _root_.GD.N0232.N0720.N1080.d014169))).subset
  rintro p ⟨x, hx, rfl⟩
  have hb := _root_.GD.N0232.N0720.N1257.d015518 m n hC ((_root_.GD.N0232.N0720.N1257.d015522 m n C x).mp hx)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hb


theorem d015542
    (hm : 2 ≤ m) (hn : 2 ≤ n) (C : ℝ) (hC : 0 ≤ C)
    (hne : (_root_.GD.N0232.N0720.N1257.d015513 m n C).Nonempty) :
    ∃ p, ∃ hp : p ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C,
      ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
        _root_.GD.N0232.N0720.N1159.d014642 m n g p (_root_.GD.N0232.N0720.N1257.d015516 m n hp) = p := by
  obtain ⟨x, hx, hfix⟩ := _root_.GD.N0230.N0664.d001257
    (fun b r ↦ _root_.GD.N0232.N0720.N1258.d015532 m n C hC ⟨b, r⟩) (_root_.GD.N0232.N0720.N1257.d015519 m n C)
    (_root_.GD.N0232.N0720.N1257.d015520 m n hC) (_root_.GD.N0232.N0720.N1257.d015521 m n C)
    (hne.image (toWeakSpace ℝ _)) (_root_.GD.N0232.N0720.N1258.d015541 m n C hC)
    (fun b r ↦ _root_.GD.N0232.N0720.N1258.d015535 m n C hC ⟨b, r⟩)
    (fun b r ↦ _root_.GD.N0232.N0720.N1258.d015537 m n C hC ⟨b, r⟩)
    (fun b r ↦ _root_.GD.N0232.N0720.N1258.d015540 m n hm hn C hC ⟨b, r⟩)
    (fun b r c s x hx ↦ _root_.GD.N0232.N0720.N1258.d015539 m n C hC ⟨b, r⟩ ⟨c, s⟩ x hx)
  refine ⟨(toWeakSpace ℝ _).symm x, (_root_.GD.N0232.N0720.N1257.d015522 m n C x).mp hx, ?_⟩
  intro g
  have hg : _root_.GD.N0232.N0720.N1258.d015532 m n C hC g x = x := by
    cases g with
    | mk b r => exact hfix b r
  rw [_root_.GD.N0232.N0720.N1258.d015534 m n C hC g x hx] at hg
  exact (toWeakSpace ℝ _).injective (hg.trans (by simp))



theorem d015543
    (hm : 2 ≤ m) (hn : 2 ≤ n) (C : ℝ) (hC : 0 ≤ C)
    (hne : (_root_.GD.N0232.N0720.N1257.d015513 m n C).Nonempty) :
    ∃ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable e ∧
      (∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ omega, e (g • omega) = g • e omega) ∧
      ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
  obtain ⟨p, hp, hfix⟩ := _root_.GD.N0232.N0720.N1258.d015542 m n hm hn C hC hne
  obtain ⟨e, he, heae, hequiv⟩ :=
    _root_.GD.N0232.N0720.N1214.d014271 m n hm hn p
      (fun g ↦ _root_.GD.N0232.N0720.N1159.d014641 m n g p (_root_.GD.N0232.N0720.N1257.d015516 m n hp))
      hfix
  refine ⟨e, he, hequiv, ?_⟩
  intro theta
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n theta (heae theta), _root_.GD.N0232.N0720.N1215.d014286]
  exact hp theta



theorem d015544
    (hm : 2 ≤ m) (hn : 2 ≤ n) (C : ℝ) (hC : 0 ≤ C)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta)) :
    ∃ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable e ∧
      (∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ omega, e (g • omega) = g • e omega) ∧
      ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
  obtain ⟨p, hp, _⟩ := _root_.GD.N0232.N0720.N1257.d015531 m n C d hd hbound
  exact _root_.GD.N0232.N0720.N1258.d015543 m n hm hn C hC ⟨p, hp⟩

end

end GD.N0232.N0720.N1258

#print axioms _root_.GD.N0232.N0720.N1258.d015542
#print axioms _root_.GD.N0232.N0720.N1258.d015544
