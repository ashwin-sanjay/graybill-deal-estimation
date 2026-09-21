import GD.Module1834

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0020
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
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1295 _root_.GD.N0232.N0720.N1446
open _root_.GD.N0024

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)


def d030253 (C : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  _root_.GD.N0232.N0720.N1257.d015513 m n C ∩ _root_.GD.N0232.N0720.N1159.d014630 m n s.value

def d030254 (C : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Set (WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))) :=
  toWeakSpace ℝ _ '' _root_.GD.N0020.d030253 m n C s

theorem d030255 (C : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (x : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))) :
    x ∈ _root_.GD.N0020.d030254 m n C s ↔ (toWeakSpace ℝ _).symm x ∈ _root_.GD.N0020.d030253 m n C s := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa using hp
  · intro h
    exact ⟨_, h, by simp⟩

theorem d030256 (C : ℝ) (hC : 0 ≤ C) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hp : p ∈ _root_.GD.N0020.d030253 m n C s) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p (_root_.GD.N0232.N0720.N1257.d015516 m n hp.1) ∈ _root_.GD.N0020.d030253 m n C s := by
  refine ⟨_root_.GD.N0232.N0720.N1257.d015523 m n hC g hp.1, ?_⟩
  intro η
  let θ := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ η
  have hη : _root_.GD.N0232.N0720.N1215.d014272 g θ = η := by simp [θ]
  rw [← hη, _root_.GD.N0232.N0720.N1159.d014643, s.riskCharacter]
  exact mul_le_mul_right (hp.2 θ) _

include hm hn in


theorem d030257 (C : ℝ) (hC : 0 ≤ C) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hK : (_root_.GD.N0020.d030253 m n C s).Nonempty) :
    ∃ p, ∃ hp : p ∈ _root_.GD.N0020.d030253 m n C s,
      ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
        _root_.GD.N0232.N0720.N1159.d014642 m n g p (_root_.GD.N0232.N0720.N1257.d015516 m n hp.1) = p := by
  have hsub : _root_.GD.N0020.d030254 m n C s ⊆ _root_.GD.N0232.N0720.N1257.d015519 m n C :=
    Set.image_mono (fun _ hp => hp.1)
  have hconv : Convex ℝ (_root_.GD.N0020.d030253 m n C s) :=
    (_root_.GD.N0232.N0720.N1257.d015515 m n C).inter (_root_.GD.N0232.N0720.N1159.d014632 m n s.value)
  have hclosed : IsClosed (_root_.GD.N0020.d030253 m n C s) :=
    (_root_.GD.N0232.N0720.N1257.d015514 m n C).inter (_root_.GD.N0232.N0720.N1159.d014631 m n s.value)
  have hcompact : IsCompact (_root_.GD.N0020.d030254 m n C s) :=
    _root_.GD.N0230.N0633.d001201
      (Real.sqrt (C * _root_.GD.N0232.N0720.N1257.d015508 m n _root_.GD.N0232.N0720.N1080.d014169)) hconv hclosed
      (fun p hp => _root_.GD.N0232.N0720.N1257.d015518 m n hC hp.1)
  have hb : _root_.GD.N0230.N0709.d001221 (_root_.GD.N0020.d030254 m n C s) :=
    (_root_.GD.N0232.N0720.N1258.d015541 m n C hC).subset (Set.image_mono hsub)
  have hmaps (g : _root_.GD.N0232.N0719.N0946.d009229) :
      MapsTo (_root_.GD.N0232.N0720.N1258.d015532 m n C hC g) (_root_.GD.N0020.d030254 m n C s) (_root_.GD.N0020.d030254 m n C s) := by
    intro x hx
    rw [_root_.GD.N0232.N0720.N1258.d015534 m n C hC g x (hsub hx)]
    exact ⟨_, _root_.GD.N0020.d030256 m n C hC s g
      ((_root_.GD.N0020.d030255 m n C s x).mp hx), rfl⟩
  obtain ⟨x, hx, hfix⟩ := _root_.GD.N0230.N0664.d001257
    (fun b r => _root_.GD.N0232.N0720.N1258.d015532 m n C hC ⟨b, r⟩) (_root_.GD.N0020.d030254 m n C s)
    hcompact (hconv.linear_image (toWeakSpace ℝ _).toLinearMap)
    (hK.image (toWeakSpace ℝ _)) hb
    (fun b r => hmaps ⟨b, r⟩)
    (fun b r => (_root_.GD.N0232.N0720.N1258.d015537 m n C hC ⟨b, r⟩).mono hsub)
    (fun shift logScale x hx y hy a b ha hb hab =>
      _root_.GD.N0232.N0720.N1258.d015540 m n hm hn C hC ⟨shift, logScale⟩
        (hsub hx) (hsub hy) ha hb hab)
    (fun b r c t x hx => _root_.GD.N0232.N0720.N1258.d015539 m n C hC ⟨b, r⟩ ⟨c, t⟩ x (hsub hx))
  refine ⟨(toWeakSpace ℝ _).symm x, (_root_.GD.N0020.d030255 m n C s x).mp hx, ?_⟩
  intro g
  have hg : _root_.GD.N0232.N0720.N1258.d015532 m n C hC g x = x := by
    cases g with
    | mk b r => exact hfix b r
  rw [_root_.GD.N0232.N0720.N1258.d015534 m n C hC g x (hsub hx)] at hg
  exact (toWeakSpace ℝ _).injective (hg.trans (by simp))

include hm hn in


theorem d030258 (C : ℝ) (hC : 0 ≤ C)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) :
    ∃ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e ∧
      (∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ z, e (g • z) = g • e z) ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ e ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n θ) ∧
        _root_.GD.N0232.N0720.N1080.d014197 m n θ e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) := by
  obtain ⟨p, hp, hprisk⟩ := _root_.GD.N0232.N0720.N1257.d015531 m n C d hd hcap
  have hbelow : p ∈ _root_.GD.N0020.d030253 m n C (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn) := by
    refine ⟨hp, fun θ => ?_⟩
    rw [hprisk θ]
    simpa only [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn,
      _root_.GD.N0232.N0720.N1047.d018649] using hbase θ
  obtain ⟨q, hq, hfix⟩ := _root_.GD.N0020.d030257 m n hm hn C hC
    (_root_.GD.N0232.N0720.N1047.d018648 m n hm hn) ⟨p, hbelow⟩
  obtain ⟨e, he, heae, hequiv⟩ :=
    _root_.GD.N0232.N0720.N1214.d014271 m n hm hn q
      (fun g => _root_.GD.N0232.N0720.N1159.d014641 m n g q (_root_.GD.N0232.N0720.N1257.d015516 m n hq.1)) hfix
  refine ⟨e, he, hequiv, fun θ => ?_⟩
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n θ (heae θ), _root_.GD.N0232.N0720.N1215.d014286,
    _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
  exact ⟨hq.1 θ, hq.2 θ⟩

include hm hn in


theorem d030259 (C : ℝ) (hC : 0 ≤ C)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n θ))
    (hbase : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable g ∧ (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n θ) ∧
        _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
          _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) := by
  obtain ⟨e, he, hequiv, heb⟩ := _root_.GD.N0020.d030258 m n hm hn C hC d hd hcap hbase
  let B : _root_.GD.N0232.N0720.N1080.d014168 → ℝ≥0∞ := fun θ =>
    min (ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n θ)) (_root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n))
  have hefinite : e ∈ _root_.GD.N0232.N0720.N1256.d015551 m n :=
    ⟨he, fun θ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (heb θ).1⟩
  have hBfinite (θ : _root_.GD.N0232.N0720.N1080.d014168) : B θ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  have hBreflection (θ : _root_.GD.N0232.N0720.N1080.d014168) : B (_root_.GD.N0232.N0720.N1446.d019024 θ) = B θ := by
    dsimp only [B]
    rw [_root_.GD.N0024.N0270.d030251 m n hm hn]
    rfl
  obtain ⟨g, hg, hgb, hgrisk⟩ :=
    _root_.GD.N0024.N0271.d028029 m n hm hn
      e hefinite ((_root_.GD.N0232.N0720.N1295.d019240 m n e).mpr hequiv)
      B hBfinite hBreflection (fun θ => le_min (heb θ).1 (heb θ).2)
  exact ⟨g, hg, hgb, fun θ => ⟨(hgrisk θ).trans (min_le_left _ _),
    (hgrisk θ).trans (min_le_right _ _)⟩⟩

end
end GD.N0020

#print axioms _root_.GD.N0020.d030256
#print axioms _root_.GD.N0020.d030257
#print axioms _root_.GD.N0020.d030258
#print axioms _root_.GD.N0020.d030259
