import GD.Module1831
import GD.Module1832
import GD.Module0979

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0024.N0269

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1258
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0633
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0710
open _root_.GD.N0230.N0664
open _root_.GD.N0046.N0305
open _root_.GD.N0096.N0340
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d030241 : Set (WeakSpace ℝ (_root_.GD.N0046.N0305.d030201 m n)) :=
  toWeakSpace ℝ (_root_.GD.N0046.N0305.d030201 m n) '' _root_.GD.N0046.N0305.d030202 m n hm hn

theorem d030242 (x : WeakSpace ℝ (_root_.GD.N0046.N0305.d030201 m n)) :
    x ∈ _root_.GD.N0024.N0269.d030241 m n hm hn ↔ (toWeakSpace ℝ (_root_.GD.N0046.N0305.d030201 m n)).symm x ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa using hp
  · intro h
    exact ⟨_, h, by simp⟩

theorem d030243 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v) :
    _root_.GD.N0046.N0305.d030202 m n hm hn ⊆ _root_.GD.N0232.N0720.N1257.d015513 m n v := by
  intro p hp θ
  have h := (hp θ).1
  rwa [hvalue, ← ENNReal.ofReal_mul hv] at h

theorem d030244 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v) :
    _root_.GD.N0024.N0269.d030241 m n hm hn ⊆ _root_.GD.N0232.N0720.N1257.d015519 m n v :=
  Set.image_mono (_root_.GD.N0024.N0269.d030243 m n hm hn v hv hvalue)

theorem d030245 : IsClosed (_root_.GD.N0046.N0305.d030202 m n hm hn) := by
  simpa only [_root_.GD.N0230.N0602.d000118, _root_.GD.N0046.N0305.d030202, _root_.GD.N0232.N0720.N1080.d014182, le_inf_iff] using
    _root_.GD.N0230.N0602.d000122 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun θ => min (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ))
        (_root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)))
      (_root_.GD.N0232.N0720.N1080.d014173 m n)

theorem d030246 : Convex ℝ (_root_.GD.N0024.N0269.d030241 m n hm hn) :=
  (_root_.GD.N0046.N0305.d030213 m n hm hn).linear_image (toWeakSpace ℝ (_root_.GD.N0046.N0305.d030201 m n)).toLinearMap

theorem d030247 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v) :
    IsCompact (_root_.GD.N0024.N0269.d030241 m n hm hn) := by
  exact _root_.GD.N0230.N0633.d001201
    (Real.sqrt (v * _root_.GD.N0232.N0720.N1257.d015508 m n _root_.GD.N0232.N0720.N1080.d014169))
    (_root_.GD.N0046.N0305.d030213 m n hm hn) (_root_.GD.N0024.N0269.d030245 m n hm hn)
    (fun p hp => _root_.GD.N0232.N0720.N1257.d015518 m n hv
      (_root_.GD.N0024.N0269.d030243 m n hm hn v hv hvalue hp))

theorem d030248 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    MapsTo (_root_.GD.N0232.N0720.N1258.d015532 m n v hv g) (_root_.GD.N0024.N0269.d030241 m n hm hn) (_root_.GD.N0024.N0269.d030241 m n hm hn) := by
  intro x hx
  have hcap := _root_.GD.N0024.N0269.d030244 m n hm hn v hv hvalue hx
  rw [_root_.GD.N0232.N0720.N1258.d015534 m n v hv g x hcap]
  exact ⟨_, _root_.GD.N0096.N0340.d030228 m n hm hn g
    ((_root_.GD.N0024.N0269.d030242 m n hm hn x).mp hx), rfl⟩

theorem d030249 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v)
    (hK : (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty) :
    ∃ p, ∃ hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn,
      ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
        _root_.GD.N0232.N0720.N1159.d014642 m n g p (_root_.GD.N0046.N0305.d030204 m n hp) = p := by
  have hsub := _root_.GD.N0024.N0269.d030244 m n hm hn v hv hvalue
  have hb : _root_.GD.N0230.N0709.d001221 (_root_.GD.N0024.N0269.d030241 m n hm hn) :=
    (_root_.GD.N0232.N0720.N1258.d015541 m n v hv).subset (Set.image_mono hsub)
  obtain ⟨x, hx, hfix⟩ := _root_.GD.N0230.N0664.d001257
    (fun b r => _root_.GD.N0232.N0720.N1258.d015532 m n v hv ⟨b, r⟩) (_root_.GD.N0024.N0269.d030241 m n hm hn)
    (_root_.GD.N0024.N0269.d030247 m n hm hn v hv hvalue) (_root_.GD.N0024.N0269.d030246 m n hm hn)
    (hK.image (toWeakSpace ℝ _)) hb
    (fun b r => _root_.GD.N0024.N0269.d030248 m n hm hn v hv hvalue ⟨b, r⟩)
    (fun b r => (_root_.GD.N0232.N0720.N1258.d015537 m n v hv ⟨b, r⟩).mono hsub)
    (fun shift logScale x hx y hy a b ha hb hab =>
      _root_.GD.N0232.N0720.N1258.d015540 m n hm hn v hv ⟨shift, logScale⟩
        (hsub hx) (hsub hy) ha hb hab)
    (fun b r c s x hx => _root_.GD.N0232.N0720.N1258.d015539 m n v hv ⟨b, r⟩ ⟨c, s⟩ x (hsub hx))
  refine ⟨(toWeakSpace ℝ _).symm x, (_root_.GD.N0024.N0269.d030242 m n hm hn x).mp hx, ?_⟩
  intro g
  have hg : _root_.GD.N0232.N0720.N1258.d015532 m n v hv g x = x := by
    cases g with
    | mk b r => exact hfix b r
  rw [_root_.GD.N0232.N0720.N1258.d015534 m n v hv g x (hsub hx)] at hg
  exact (toWeakSpace ℝ _).injective (hg.trans (by simp))

theorem d030250 (v : ℝ) (hv : 0 ≤ v)
    (hvalue : _root_.GD.N0232.N0720.N1256.d015549 m n = ENNReal.ofReal v)
    (hK : (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty) :
    ∃ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
      Measurable e ∧
      (∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ z, e (g • z) = g • e z) ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ e ≤ ENNReal.ofReal (v * _root_.GD.N0232.N0720.N1257.d015508 m n θ) ∧
        _root_.GD.N0232.N0720.N1080.d014197 m n θ e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) := by
  obtain ⟨p, hp, hfix⟩ := _root_.GD.N0024.N0269.d030249 m n hm hn v hv hvalue hK
  obtain ⟨e, he, heae, hequiv⟩ :=
    _root_.GD.N0232.N0720.N1214.d014271 m n hm hn p
      (fun g => _root_.GD.N0232.N0720.N1159.d014641 m n g p (_root_.GD.N0046.N0305.d030204 m n hp)) hfix
  refine ⟨e, he, hequiv, fun θ => ?_⟩
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n θ (heae θ), _root_.GD.N0232.N0720.N1215.d014286,
    _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
  exact ⟨_root_.GD.N0024.N0269.d030243 m n hm hn v hv hvalue hp θ, (hp θ).2⟩

end
end GD.N0024.N0269

#print axioms _root_.GD.N0024.N0269.d030249
#print axioms _root_.GD.N0024.N0269.d030250
