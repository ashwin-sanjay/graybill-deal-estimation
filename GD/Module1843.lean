import GD.Module1842
import GD.Module1363
import GD.Module1830

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0034.N0294

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1482 _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1257
open _root_.GD.N0046.N0305

variable (m n : ℕ)

def d030312 : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :=
  {d | Measurable d ∧ ∀ θ,
    _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1256.d015549 m n *
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ) ∧
    _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)}

def d030313 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : ℝ :=
  _root_.GD.N0034.N0292.d007212 (_root_.GD.N0232.N0720.N1080.d014172 m n)
    (fun z : _root_.GD.N0232.N0720.N1080.d014170 m n => (2 : ℝ) • z)
    (fun z : _root_.GD.N0232.N0720.N1080.d014170 m n =>
      ((fun i => 3 * z.1 i + 1), (fun j => 3 * z.2 j + 1))) d

def d030314 : Prop :=
  ∃ d ∈ _root_.GD.N0034.N0294.d030312 m n, 0 < _root_.GD.N0034.N0294.d030313 m n d

def d030315 : Prop :=
  ∀ d ∈ _root_.GD.N0034.N0294.d030312 m n, _root_.GD.N0034.N0294.d030313 m n d = 0

theorem d030316 (g : _root_.GD.N0232.N0720.N1482.d015118)
    {d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (h : d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] e) :
    (fun z => d (g • z)) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] (fun z => e (g • z)) := by
  have ht := _root_.GD.N0232.N0720.N1081.d014625 m n g⁻¹ h
  filter_upwards [ht] with z hz
  have heq := congrArg (fun y : ℝ => g • y) hz
  simpa only [_root_.GD.N0232.N0720.N1214.d014261, inv_inv, smul_inv_smul] using heq

theorem d030317
    {d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (h : d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] e) :
    _root_.GD.N0034.N0294.d030313 m n d = _root_.GD.N0034.N0294.d030313 m n e := by
  have htwo := _root_.GD.N0034.N0294.d030316 m n _root_.GD.N0232.N0720.N1482.d015130 h
  have hthree := _root_.GD.N0034.N0294.d030316 m n _root_.GD.N0232.N0720.N1482.d015131 h
  unfold _root_.GD.N0034.N0294.d030313 _root_.GD.N0034.N0292.d007212
  apply integral_congr_ae
  filter_upwards [h, htwo, hthree] with z hz h2 h3
  simp only [_root_.GD.N0034.N0291.d021967, _root_.GD.N0034.N0291.d021968] at h2 h3
  rw [hz, h2, h3]

theorem d030318 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : 0 ≤ _root_.GD.N0034.N0294.d030313 m n d :=
  _root_.GD.N0034.N0292.d007213 _ _ _ _

theorem d030319 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : d ∈ _root_.GD.N0034.N0294.d030312 m n) :
    d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n := by
  refine ⟨hd.1, fun θ => ?_⟩
  apply ne_top_of_le_ne_top _ (hd.2 θ).2
  rw [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn, _root_.GD.N0232.N0720.N1080.d014184]
  exact ENNReal.ofReal_ne_top

theorem d030320 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : d ∈ _root_.GD.N0034.N0294.d030312 m n) :
    _root_.GD.N0046.N0305.d030205 m n d (_root_.GD.N0034.N0294.d030319 m n hm hn hd) ∈
      _root_.GD.N0046.N0305.d030202 m n hm hn := by
  intro θ
  rw [_root_.GD.N0046.N0305.d030206]
  refine ⟨(hd.2 θ).1, ?_⟩
  simpa only [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn] using (hd.2 θ).2

theorem d030321 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n) :
    d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0046.N0305.d030205 m n d hd) := by
  let hmem := _root_.GD.N0232.N0720.N1215.d014285 m n d hd.1
    (hd.2 _root_.GD.N0232.N0720.N1080.d014169)
  exact hmem.coeFn_toLp.symm.trans
    (_root_.GD.N0232.N0720.N1214.d014267 m n (_root_.GD.N0046.N0305.d030205 m n d hd)).symm

theorem d030322 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {p : _root_.GD.N0046.N0305.d030201 m n} (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) :
    _root_.GD.N0232.N0720.N1214.d014265 m n p ∈ _root_.GD.N0034.N0294.d030312 m n := by
  refine ⟨_root_.GD.N0232.N0720.N1214.d014266 m n p, fun θ => ?_⟩
  rw [_root_.GD.N0232.N0720.N1215.d014286, _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
  exact hp θ

theorem d030323 (p : _root_.GD.N0046.N0305.d030201 m n) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0034.N0294.d030313 m n (_root_.GD.N0232.N0720.N1214.d014265 m n p) = _root_.GD.N0034.N0287.d021571 m n p :=
  (_root_.GD.N0034.N0291.d021971 m n p hp).symm

theorem d030324 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (_root_.GD.N0034.N0294.d030312 m n).Nonempty ↔ (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨_, _root_.GD.N0034.N0294.d030320 m n hm hn hd⟩
  · rintro ⟨p, hp⟩
    exact ⟨_, _root_.GD.N0034.N0294.d030322 m n hm hn hp⟩

theorem d030325 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0034.N0294.d030314 m n ↔ _root_.GD.N0034.N0286.d030283 m n hm hn := by
  constructor
  · rintro ⟨d, hd, he⟩
    let hf := _root_.GD.N0034.N0294.d030319 m n hm hn hd
    let p := _root_.GD.N0046.N0305.d030205 m n d hf
    have hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn :=
      _root_.GD.N0034.N0294.d030320 m n hm hn hd
    refine ⟨p, hp, ?_⟩
    have henergy : _root_.GD.N0034.N0294.d030313 m n d = _root_.GD.N0034.N0287.d021571 m n p :=
      (_root_.GD.N0034.N0294.d030317 m n (_root_.GD.N0034.N0294.d030321 m n d hf)).trans
        (_root_.GD.N0034.N0294.d030323 m n p (_root_.GD.N0046.N0305.d030204 m n hp))
    exact henergy ▸ he
  · rintro ⟨p, hp, he⟩
    refine ⟨_root_.GD.N0232.N0720.N1214.d014265 m n p, _root_.GD.N0034.N0294.d030322 m n hm hn hp, ?_⟩
    rw [_root_.GD.N0034.N0294.d030323 m n p (_root_.GD.N0046.N0305.d030204 m n hp)]
    exact he

theorem d030326 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0034.N0294.d030314 m n ↔ (_root_.GD.N0034.N0294.d030312 m n).Nonempty :=
  (_root_.GD.N0034.N0294.d030325 m n hm hn).trans
    ((_root_.GD.N0034.N0295.d030305 m n hm hn).trans
      (_root_.GD.N0034.N0294.d030324 m n hm hn).symm)

theorem d030327 :
    ¬ _root_.GD.N0034.N0294.d030315 m n ↔ _root_.GD.N0034.N0294.d030314 m n :=
  _root_.GD.N0034.N0292.d007211 (_root_.GD.N0034.N0294.d030312 m n) (_root_.GD.N0034.N0294.d030313 m n)
    (fun d _ => _root_.GD.N0034.N0294.d030318 m n d)

theorem d030328 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0034.N0294.d030315 m n ↔ _root_.GD.N0034.N0294.d030312 m n = ∅ := by
  constructor
  · intro hzero
    ext d
    constructor
    · intro hd
      obtain ⟨e, he, hpos⟩ :=
        (_root_.GD.N0034.N0294.d030326 m n hm hn).mpr ⟨d, hd⟩
      exact (hpos.ne' (hzero e he)).elim
    · intro hd
      exact hd.elim
  · intro hK d hd
    rw [hK] at hd
    exact hd.elim

theorem d030329 (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0034.N0294.d030314 m n ↔ _root_.GD.N0034.N0289.d030224 m n hm hn :=
  (_root_.GD.N0034.N0294.d030325 m n hm hn).trans
    (_root_.GD.N0034.N0295.d030306 m n hm hn)

end
end GD.N0034.N0294

#print axioms _root_.GD.N0034.N0294.d030316
#print axioms _root_.GD.N0034.N0294.d030317
#print axioms _root_.GD.N0034.N0294.d030324
#print axioms _root_.GD.N0034.N0294.d030325
#print axioms _root_.GD.N0034.N0294.d030327
#print axioms _root_.GD.N0034.N0294.d030328
#print axioms _root_.GD.N0034.N0294.d030329
