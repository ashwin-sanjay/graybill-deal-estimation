import GD.Module1832
import GD.Module1433
import GD.Module0510
import GD.Module1837
import GD.Module1860
import GD.Module1362

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0096.N0339

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1257
open _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1226
open _root_.GD.N0046.N0305
open _root_.GD.N0230.N0602
open _root_.GD.N0046.N0303
open _root_.GD.N0096.N0340 _root_.GD.N0096.N0343

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d030525 (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  Measurable f ∧ ∀ θ,
    _root_.GD.N0232.N0720.N1080.d014197 m n θ f ≤
      min (_root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n))
        (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ))

def d030526 : Prop :=
  ∃ f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, _root_.GD.N0096.N0339.d030525 m n f ∧ 0 < _root_.GD.N0096.N0343.d022808 m n f

def d030527 : Prop :=
  ∀ f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, _root_.GD.N0096.N0339.d030525 m n f → _root_.GD.N0096.N0343.d022808 m n f = 0

theorem d030528 :
    (¬ _root_.GD.N0096.N0339.d030527 m n) ↔ _root_.GD.N0096.N0339.d030526 m n :=
  _root_.GD.N0018.N0253.d005261 _ _
    (fun f _ => _root_.GD.N0096.N0343.d022815 m n f)

include hm hn

theorem d030529 {f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hf : _root_.GD.N0096.N0339.d030525 m n f) : f ∈ _root_.GD.N0232.N0720.N1256.d015551 m n := by
  refine ⟨hf.1, fun θ => ?_⟩
  have hbase : _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn, _root_.GD.N0232.N0720.N1080.d014184]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hbase (le_min_iff.mp (hf.2 θ)).1

theorem d030530 {f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hf : _root_.GD.N0096.N0339.d030525 m n f) :
    _root_.GD.N0046.N0305.d030205 m n f (_root_.GD.N0096.N0339.d030529 m n hm hn hf) ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := by
  intro θ
  rw [_root_.GD.N0046.N0305.d030206]
  have hθ := le_min_iff.mp (hf.2 θ)
  exact ⟨hθ.2, by simpa only [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn] using hθ.1⟩

theorem d030531 {p : _root_.GD.N0046.N0305.d030201 m n}
    (hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn) :
    _root_.GD.N0096.N0339.d030525 m n (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
  refine ⟨_root_.GD.N0232.N0720.N1214.d014266 m n p, fun θ => ?_⟩
  rw [_root_.GD.N0232.N0720.N1215.d014286, _root_.GD.N0232.N0720.N1080.d014199 m n hm hn,
    le_min_iff]
  exact ⟨(hp θ).2, (hp θ).1⟩

theorem d030532 {f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hf : _root_.GD.N0096.N0339.d030525 m n f) :
    Integrable (_root_.GD.N0018.N0253.d005249
      (_root_.GD.N0096.N0343.d022801 m n _root_.GD.N0232.N0720.N1482.d015130)
      (_root_.GD.N0096.N0343.d022801 m n _root_.GD.N0232.N0720.N1482.d015131) f)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  let hfin := _root_.GD.N0096.N0339.d030529 m n hm hn hf
  let p := _root_.GD.N0046.N0305.d030205 m n f hfin
  have hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := _root_.GD.N0096.N0339.d030530 m n hm hn hf
  have heq : _root_.GD.N0232.N0720.N1214.d014265 m n p =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] f :=
    (_root_.GD.N0232.N0720.N1214.d014267 m n p).trans
      (_root_.GD.N0232.N0720.N1215.d014285 m n f hfin.1
        (hfin.2 _root_.GD.N0232.N0720.N1080.d014169)).coeFn_toLp
  apply (_root_.GD.N0096.N0343.d022814 m n p (_root_.GD.N0046.N0305.d030204 m n hp)).congr
  filter_upwards [_root_.GD.N0096.N0343.d022816 m n
      _root_.GD.N0232.N0720.N1482.d015130 heq,
    _root_.GD.N0096.N0343.d022816 m n
      _root_.GD.N0232.N0720.N1482.d015131 heq] with z h₂ h₃
  simpa only [_root_.GD.N0018.N0253.d005249,
    ← _root_.GD.N0096.N0343.d022812, ← _root_.GD.N0096.N0343.d022813] using congrArg₂
      (fun a b : ℝ => a ^ 2 + b ^ 2) h₂ h₃

theorem d030533 :
    _root_.GD.N0096.N0339.d030526 m n ↔ _root_.GD.N0096.N0340.d030229 m n hm hn := by
  constructor
  · rintro ⟨f, hf, hE⟩
    let hfin := _root_.GD.N0096.N0339.d030529 m n hm hn hf
    let p := _root_.GD.N0046.N0305.d030205 m n f hfin
    have hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := _root_.GD.N0096.N0339.d030530 m n hm hn hf
    refine ⟨p, hp, (_root_.GD.N0096.N0343.d022820 m n p
      (_root_.GD.N0046.N0305.d030204 m n hp)).mp ?_⟩
    have heq : _root_.GD.N0096.N0343.d022808 m n (_root_.GD.N0232.N0720.N1214.d014265 m n p) = _root_.GD.N0096.N0343.d022808 m n f :=
      _root_.GD.N0096.N0343.d022818 m n f _
    rwa [heq]
  · rintro ⟨p, hp, hobs⟩
    exact ⟨_root_.GD.N0232.N0720.N1214.d014265 m n p, _root_.GD.N0096.N0339.d030531 m n hm hn hp,
      (_root_.GD.N0096.N0343.d022820 m n p (_root_.GD.N0046.N0305.d030204 m n hp)).mpr hobs⟩

theorem d030534 :
    _root_.GD.N0096.N0339.d030526 m n ↔ ¬ (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton := by
  rw [_root_.GD.N0096.N0339.d030533 m n hm hn,
    _root_.GD.N0096.N0340.d030234 m n hm hn]

theorem d030535 :
    _root_.GD.N0096.N0339.d030526 m n ↔ _root_.GD.N0232.N0720.N1226.d015578 m n := by
  rw [_root_.GD.N0096.N0339.d030533 m n hm hn,
    _root_.GD.N0096.N0340.d030235 m n hm hn]

theorem d030536 :
    _root_.GD.N0096.N0339.d030526 m n ↔
      ∃ f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, _root_.GD.N0232.N0720.N1226.d015576 m n f := by
  rw [_root_.GD.N0096.N0339.d030535 m n hm hn,
    _root_.GD.N0232.N0720.N1226.d015584]

theorem d030537 :
    _root_.GD.N0096.N0339.d030527 m n ↔ (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton := by
  classical
  have h := not_congr ((_root_.GD.N0096.N0339.d030528 m n).trans
    (_root_.GD.N0096.N0339.d030534 m n hm hn))
  simpa only [not_not] using h

theorem d030538 :
    _root_.GD.N0096.N0339.d030527 m n ↔
      _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ ∨ ∃ p : _root_.GD.N0046.N0305.d030201 m n, _root_.GD.N0046.N0305.d030202 m n hm hn = {p} := by
  rw [_root_.GD.N0096.N0339.d030537 m n hm hn]
  constructor
  · intro hs
    by_cases h : (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty
    · obtain ⟨p, hp⟩ := h
      right
      refine ⟨p, Set.Subset.antisymm ?_ (singleton_subset_iff.mpr hp)⟩
      intro q hq
      exact Set.mem_singleton_iff.mpr (hs hq hp)
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp h)
  · rintro (h | ⟨p, h⟩) <;> simp [h]

theorem d030539
    (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) (h : _root_.GD.N0096.N0339.d030526 m n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) → ε ≤ _root_.GD.N0096.N0342.d030268 m n hm hn F w :=
  _root_.GD.N0096.N0342.d030278 m n hm hn hV
    ((_root_.GD.N0096.N0339.d030533 m n hm hn).mp h)

theorem d030540
    (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    (hsaturation : ∀ ε : ℝ, 0 < ε →
      ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ _root_.GD.N0096.N0342.d030268 m n hm hn F w < ε) :
    _root_.GD.N0096.N0339.d030527 m n :=
  (_root_.GD.N0096.N0339.d030537 m n hm hn).mpr
    (_root_.GD.N0096.N0342.d030275 m n hm hn hV hsaturation)

theorem d030541
    (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤)
    {f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hf : _root_.GD.N0096.N0339.d030525 m n f)
    (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (hw : ∀ θ ∈ F, 0 ≤ w θ) :
    _root_.GD.N0096.N0343.d022808 m n f / 52 ≤ _root_.GD.N0096.N0342.d030268 m n hm hn F w := by
  let hfin := _root_.GD.N0096.N0339.d030529 m n hm hn hf
  let p := _root_.GD.N0046.N0305.d030205 m n f hfin
  have hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := _root_.GD.N0096.N0339.d030530 m n hm hn hf
  have heq : _root_.GD.N0096.N0343.d022808 m n (_root_.GD.N0232.N0720.N1214.d014265 m n p) = _root_.GD.N0096.N0343.d022808 m n f :=
    _root_.GD.N0096.N0343.d022818 m n f _
  rw [← heq, _root_.GD.N0096.N0343.d022822 m n p (_root_.GD.N0046.N0305.d030204 m n hp)]
  exact _root_.GD.N0096.N0342.d030274 m n hm hn hV F w hw hp
    (_root_.GD.N0096.N0340.d030228 m n hm hn
      _root_.GD.N0232.N0720.N1482.d015130⁻¹ hp)
    (_root_.GD.N0096.N0340.d030228 m n hm hn
      _root_.GD.N0232.N0720.N1482.d015131⁻¹ hp)

theorem d030542 :
    _root_.GD.N0096.N0339.d030526 m n ↔ (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty := by
  rw [_root_.GD.N0096.N0339.d030535 m n hm hn,
    _root_.GD.N0096.N0344.d030524 m n hm hn]

theorem d030543
    (hK : (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty) :
    ∃ f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable f ∧
      _root_.GD.N0232.N0720.N1256.d015548 m n f = _root_.GD.N0232.N0720.N1256.d015549 m n ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ f <
        min (_root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n))
          (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ)) := by
  classical
  have hnsub := _root_.GD.N0096.N0344.d030521 m n hm hn hK
  have hex : ∃ p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn, ∃ q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn, p ≠ q := by
    by_contra hnot
    push Not at hnot
    exact hnsub (fun p hp q hq => hnot p hp q hq)
  obtain ⟨p, hp, q, hq, hpq⟩ := hex
  let z := _root_.GD.N0230.N0718.d001528 p q
  have hz : z ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := _root_.GD.N0046.N0305.d030209 m n hp hq
  refine ⟨_root_.GD.N0232.N0720.N1214.d014265 m n z, _root_.GD.N0232.N0720.N1214.d014266 m n z,
    _root_.GD.N0046.N0305.d030208 m n hz, fun θ => ?_⟩
  rw [_root_.GD.N0232.N0720.N1215.d014286, _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
  have hcap : min (_root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
      (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (min_le_left _ _)
    rw [_root_.GD.N0232.N0720.N1080.d014184]
    exact ENNReal.ofReal_ne_top
  exact _root_.GD.N0046.N0303.d030188
    (_root_.GD.N0232.N0720.N1080.d014173 m n θ)
    (_root_.GD.N0046.N0305.d030203 m n θ) θ.location hcap
    (le_min (hp θ).2 (hp θ).1) (le_min (hq θ).2 (hq θ).1) hpq

theorem d030544 :
    _root_.GD.N0096.N0339.d030527 m n ↔ _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ := by
  classical
  have h := not_congr ((_root_.GD.N0096.N0339.d030528 m n).trans
    (_root_.GD.N0096.N0339.d030542 m n hm hn))
  simpa only [not_not, Set.not_nonempty_iff_eq_empty] using h

theorem d030545
    (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    _root_.GD.N0096.N0339.d030526 m n ↔
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) → 0 ≤ _root_.GD.N0096.N0342.d030268 m n hm hn F w := by
  rw [_root_.GD.N0096.N0339.d030542 m n hm hn,
    _root_.GD.N0096.N0342.d030270 m n hm hn hV]

theorem d030546
    (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    _root_.GD.N0096.N0339.d030526 m n ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) → ε ≤ _root_.GD.N0096.N0342.d030268 m n hm hn F w := by
  constructor
  · exact _root_.GD.N0096.N0339.d030539 m n hm hn hV
  · rintro ⟨ε, hε, hgap⟩
    exact (_root_.GD.N0096.N0339.d030545 m n hm hn hV).mpr
      (fun F w hw => hε.le.trans (hgap F w hw))

theorem d030547
    (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    _root_.GD.N0096.N0339.d030527 m n ↔
      ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) ∧ _root_.GD.N0096.N0342.d030268 m n hm hn F w < 0 := by
  rw [_root_.GD.N0096.N0339.d030544 m n hm hn,
    _root_.GD.N0096.N0342.d030271 m n hm hn hV]

theorem d030548 (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0096.N0339.d030525 m n f ↔ Measurable f ∧ ∀ θ,
      _root_.GD.N0232.N0720.N1080.d014197 m n θ f ≤
        min (_root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0096.N0341.d021956 m n))
          (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ)) := by
  simp only [_root_.GD.N0096.N0339.d030525,
    _root_.GD.N0096.N0341.d021966 m n hm hn]

theorem d030549
    (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    (∃ f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable f ∧
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ f ≤
        min (_root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0096.N0341.d021956 m n))
          (_root_.GD.N0232.N0720.N1256.d015549 m n * ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 m n θ))) ∧
      0 < _root_.GD.N0096.N0343.d022808 m n f) ↔
    ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) → 0 ≤ _root_.GD.N0096.N0342.d030268 m n hm hn F w := by
  rw [← _root_.GD.N0096.N0339.d030545 m n hm hn hV]
  simp only [_root_.GD.N0096.N0339.d030526, _root_.GD.N0096.N0339.d030548 m n hm hn, and_assoc]

theorem d030550 (hV : _root_.GD.N0232.N0720.N1256.d015549 m n ≠ ⊤) :
    ((¬ _root_.GD.N0096.N0339.d030527 m n) ↔ _root_.GD.N0096.N0339.d030526 m n) ∧
    (_root_.GD.N0096.N0339.d030527 m n ↔ _root_.GD.N0046.N0305.d030202 m n hm hn = ∅) ∧
    (_root_.GD.N0096.N0339.d030526 m n ↔
      ∀ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) → 0 ≤ _root_.GD.N0096.N0342.d030268 m n hm hn F w) :=
  ⟨_root_.GD.N0096.N0339.d030528 m n,
    _root_.GD.N0096.N0339.d030544 m n hm hn,
    _root_.GD.N0096.N0339.d030545 m n hm hn hV⟩

end
end GD.N0096.N0339

#print axioms _root_.GD.N0096.N0339.d030528
#print axioms _root_.GD.N0096.N0339.d030532
#print axioms _root_.GD.N0096.N0339.d030533
#print axioms _root_.GD.N0096.N0339.d030534
#print axioms _root_.GD.N0096.N0339.d030535
#print axioms _root_.GD.N0096.N0339.d030536
#print axioms _root_.GD.N0096.N0339.d030537
#print axioms _root_.GD.N0096.N0339.d030538
#print axioms _root_.GD.N0096.N0339.d030539
#print axioms _root_.GD.N0096.N0339.d030540
#print axioms _root_.GD.N0096.N0339.d030541
#print axioms _root_.GD.N0096.N0339.d030542
#print axioms _root_.GD.N0096.N0339.d030543
#print axioms _root_.GD.N0096.N0339.d030544
#print axioms _root_.GD.N0096.N0339.d030545
#print axioms _root_.GD.N0096.N0339.d030546
#print axioms _root_.GD.N0096.N0339.d030547
#print axioms _root_.GD.N0096.N0339.d030548
#print axioms _root_.GD.N0096.N0339.d030549
#print axioms _root_.GD.N0096.N0339.d030550
