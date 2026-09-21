import GD.Module1860
import GD.Module0919
import GD.Module1049
import GD.Module0246

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0076.N0313

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1226
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0633
open _root_.GD.N0230.N0586
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0686
open _root_.GD.N0096.N0344
open _root_.GD.N0046.N0303

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

abbrev d030564 := _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)

def d030565 (θ : _root_.GD.N0232.N0720.N1080.d014168) : ℝ := (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ).toReal

theorem d030566 (θ : _root_.GD.N0232.N0720.N1080.d014168) : 0 < _root_.GD.N0076.N0313.d030565 m n hm hn θ :=
  ENNReal.toReal_pos (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn θ)
    (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ)

theorem d030567 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    ENNReal.ofReal (_root_.GD.N0076.N0313.d030565 m n hm hn θ) = _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ :=
  ENNReal.ofReal_toReal (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ)

def d030568 (θ : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0232.N0720.N1080.d014197 m n θ d / _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ

def d030569 : ℝ≥0∞ :=
  _root_.GD.N0230.N0611.d003517 (_root_.GD.N0076.N0313.d030568 m n hm hn) (_root_.GD.N0232.N0720.N1256.d015551 m n)

def d030570 (c : ℝ) : Set (_root_.GD.N0076.N0313.d030564 m n) :=
  {p | ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 m n hm hn θ)}

theorem d030571 (c : ℝ) (hc : 0 ≤ c)
    (θ : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0076.N0313.d030568 m n hm hn θ d ≤ ENNReal.ofReal c ↔
      _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 m n hm hn θ) := by
  unfold _root_.GD.N0076.N0313.d030568
  rw [ENNReal.div_le_iff (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn θ)
    (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ), ENNReal.ofReal_mul hc,
    _root_.GD.N0076.N0313.d030567]

theorem d030572 {p : _root_.GD.N0076.N0313.d030564 m n} (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1214.d014265 m n p ∈ _root_.GD.N0232.N0720.N1256.d015551 m n := by
  refine ⟨_root_.GD.N0232.N0720.N1214.d014266 m n p, ?_⟩
  intro θ
  rw [_root_.GD.N0232.N0720.N1215.d014286]
  exact hp θ

theorem d030573 : _root_.GD.N0076.N0313.d030569 m n hm hn ≤ 1 := by
  have hb : _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) :=
    fun θ => _root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ
  apply (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0076.N0313.d030568 m n hm hn)
    (_root_.GD.N0076.N0313.d030572 m n hb)).trans
  apply iSup_le
  intro θ
  unfold _root_.GD.N0076.N0313.d030568
  rw [_root_.GD.N0232.N0720.N1215.d014286]
  change _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ / _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ ≤ 1
  rw [ENNReal.div_self (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn θ)
    (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ)]

theorem d030574 : _root_.GD.N0076.N0313.d030569 m n hm hn ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (_root_.GD.N0076.N0313.d030573 m n hm hn)

theorem d030575 : (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal ≤ 1 := by
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num)
    (by simpa using _root_.GD.N0076.N0313.d030573 m n hm hn)

theorem d030576 {c : ℝ} {p : _root_.GD.N0076.N0313.d030564 m n}
    (hp : p ∈ _root_.GD.N0076.N0313.d030570 m n hm hn c) : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
  fun θ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hp θ)

theorem d030577 (c : ℝ) : IsClosed (_root_.GD.N0076.N0313.d030570 m n hm hn c) := by
  simpa [_root_.GD.N0076.N0313.d030570, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun θ => ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 m n hm hn θ))
      (_root_.GD.N0232.N0720.N1080.d014173 m n))

theorem d030578 (c : ℝ) : Convex ℝ (_root_.GD.N0076.N0313.d030570 m n hm hn c) := by
  simpa [_root_.GD.N0076.N0313.d030570, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun θ => ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 m n hm hn θ))
      (_root_.GD.N0232.N0720.N1080.d014173 m n))

theorem d030579 {c : ℝ} (hc : 0 ≤ c) {p : _root_.GD.N0076.N0313.d030564 m n}
    (hp : p ∈ _root_.GD.N0076.N0313.d030570 m n hm hn c) :
    ‖p‖ ≤ Real.sqrt (c * _root_.GD.N0076.N0313.d030565 m n hm hn _root_.GD.N0232.N0720.N1080.d014169) := by
  have h := hp _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n] at h
  simp only [zero_sub, norm_neg] at h
  have hnonneg := mul_nonneg hc (_root_.GD.N0076.N0313.d030566 m n hm hn _root_.GD.N0232.N0720.N1080.d014169).le
  have hh := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp h
  nlinarith [Real.sq_sqrt hnonneg,
    Real.sqrt_nonneg (c * _root_.GD.N0076.N0313.d030565 m n hm hn _root_.GD.N0232.N0720.N1080.d014169), norm_nonneg p]

def d030580 (c : ℝ) : Set (WeakSpace ℝ (_root_.GD.N0076.N0313.d030564 m n)) :=
  toWeakSpace ℝ (_root_.GD.N0076.N0313.d030564 m n) '' _root_.GD.N0076.N0313.d030570 m n hm hn c

theorem d030581 {c : ℝ} (hc : 0 ≤ c) :
    IsCompact (_root_.GD.N0076.N0313.d030580 m n hm hn c) :=
  _root_.GD.N0230.N0633.d001201
    (Real.sqrt (c * _root_.GD.N0076.N0313.d030565 m n hm hn _root_.GD.N0232.N0720.N1080.d014169))
    (_root_.GD.N0076.N0313.d030578 m n hm hn c) (_root_.GD.N0076.N0313.d030577 m n hm hn c)
    (fun _p hp => _root_.GD.N0076.N0313.d030579 m n hm hn hc hp)

theorem d030582 : Monotone (_root_.GD.N0076.N0313.d030570 m n hm hn) := by
  intro a b hab p hp θ
  exact (hp θ).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hab (_root_.GD.N0076.N0313.d030566 m n hm hn θ).le))

theorem d030583 (c : ℝ) (x : WeakSpace ℝ (_root_.GD.N0076.N0313.d030564 m n)) :
    x ∈ _root_.GD.N0076.N0313.d030580 m n hm hn c ↔
      (toWeakSpace ℝ (_root_.GD.N0076.N0313.d030564 m n)).symm x ∈ _root_.GD.N0076.N0313.d030570 m n hm hn c := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa using hp
  · exact fun hp => ⟨_, hp, by simp⟩

theorem d030584 (c : ℝ) (hc : 0 ≤ c)
    (hv : _root_.GD.N0076.N0313.d030569 m n hm hn < ENNReal.ofReal c) :
    (_root_.GD.N0076.N0313.d030570 m n hm hn c).Nonempty := by
  change (⨅ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n, _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) d) <
    ENNReal.ofReal c at hv
  obtain ⟨d, hd⟩ := iInf_lt_iff.mp hv
  obtain ⟨hd, hbound⟩ := iInf_lt_iff.mp hd
  have hmem := _root_.GD.N0232.N0720.N1215.d014285 m n d hd.1
    (hd.2 _root_.GD.N0232.N0720.N1080.d014169)
  refine ⟨hmem.toLp d, ?_⟩
  intro θ
  rw [← _root_.GD.N0232.N0720.N1080.d014198 m n θ d hmem]
  apply (_root_.GD.N0076.N0313.d030571 m n hm hn c hc θ d).mp
  exact (le_iSup (fun η => _root_.GD.N0076.N0313.d030568 m n hm hn η d) θ).trans hbound.le

theorem d030585 :
    (_root_.GD.N0076.N0313.d030570 m n hm hn (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal).Nonempty := by
  let v := (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hV : ENNReal.ofReal v = _root_.GD.N0076.N0313.d030569 m n hm hn :=
    ENNReal.ofReal_toReal (_root_.GD.N0076.N0313.d030574 m n hm hn)
  have hne : ∀ c : ℝ, v < c → (_root_.GD.N0076.N0313.d030580 m n hm hn c).Nonempty := by
    intro c hc
    apply Set.Nonempty.image
    apply _root_.GD.N0076.N0313.d030584 m n hm hn c (hv.trans hc.le)
    rw [← hV]
    exact (ENNReal.ofReal_lt_ofReal_iff (hv.trans_lt hc)).mpr hc
  obtain ⟨x, hx⟩ := _root_.GD.N0230.N0586.d003514
    (_root_.GD.N0076.N0313.d030580 m n hm hn)
    (fun a b hab => Set.image_mono (_root_.GD.N0076.N0313.d030582 m n hm hn hab)) v
    (fun c hc => _root_.GD.N0076.N0313.d030581 m n hm hn (hv.trans hc.le)) hne
  let p := (toWeakSpace ℝ (_root_.GD.N0076.N0313.d030564 m n)).symm x
  refine ⟨p, ?_⟩
  intro θ
  rw [← _root_.GD.N0232.N0720.N1215.d014286 m n θ p]
  apply (_root_.GD.N0076.N0313.d030571 m n hm hn v hv θ _).mp
  apply _root_.GD.N0230.N0586.d003515 hv
  intro c hc
  apply (_root_.GD.N0076.N0313.d030571 m n hm hn c (hv.trans hc.le) θ _).mpr
  rw [_root_.GD.N0232.N0720.N1215.d014286]
  exact ((_root_.GD.N0076.N0313.d030583 m n hm hn c x).mp (hx c hc)) θ

theorem d030586 {c : ℝ} {p q : _root_.GD.N0076.N0313.d030564 m n}
    (hp : p ∈ _root_.GD.N0076.N0313.d030570 m n hm hn c) (hq : ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ q ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ p) :
    q ∈ _root_.GD.N0076.N0313.d030570 m n hm hn c := fun θ => (hq θ).trans (hp θ)

theorem d030587 {c : ℝ} (hc : c ≤ 1) {p : _root_.GD.N0076.N0313.d030564 m n}
    (hp : p ∈ _root_.GD.N0076.N0313.d030570 m n hm hn c) :
    ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ := by
  intro θ
  calc
    _ ≤ _ := hp θ
    _ ≤ ENNReal.ofReal (_root_.GD.N0076.N0313.d030565 m n hm hn θ) :=
      ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (_root_.GD.N0076.N0313.d030566 m n hm hn θ).le hc)
    _ = _ := _root_.GD.N0076.N0313.d030567 m n hm hn θ

theorem d030588 (g : _root_.GD.N0232.N0720.N1482.d015118)
    {c : ℝ} {p : _root_.GD.N0076.N0313.d030564 m n} (hp : p ∈ _root_.GD.N0076.N0313.d030570 m n hm hn c) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p (_root_.GD.N0076.N0313.d030576 m n hm hn hp) ∈
      _root_.GD.N0076.N0313.d030570 m n hm hn c := by
  intro η
  let θ := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ η
  have hη : _root_.GD.N0232.N0720.N1215.d014272 g θ = η := by simp [θ]
  have hb : _root_.GD.N0076.N0313.d030565 m n hm hn (_root_.GD.N0232.N0720.N1215.d014272 g θ) =
      g.d009239 ^ 2 * _root_.GD.N0076.N0313.d030565 m n hm hn θ := by
    unfold _root_.GD.N0076.N0313.d030565 _root_.GD.N0232.N0720.N1066.d014320
    rw [_root_.GD.N0232.N0720.N1215.d014293, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg g.d009239)]
  rw [← hη, _root_.GD.N0232.N0720.N1159.d014643, hb]
  calc
    _ ≤ ENNReal.ofReal (g.d009239 ^ 2) *
        ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 m n hm hn θ) := mul_le_mul' le_rfl (hp θ)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (sq_nonneg g.d009239)]
      congr 1
      ring

theorem d030589 {c : ℝ} (hc : c ≤ 1)
    (hne : (_root_.GD.N0076.N0313.d030570 m n hm hn c).Nonempty) :
    ¬ (_root_.GD.N0076.N0313.d030570 m n hm hn c).Subsingleton := by
  intro hsub
  obtain ⟨p, hp⟩ := hne
  have hfinite := _root_.GD.N0076.N0313.d030576 m n hm hn hp
  have hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p :=
    fun q hq => hsub (_root_.GD.N0076.N0313.d030586 m n hm hn hp hq) hp
  have hfixed : ∀ g, _root_.GD.N0232.N0720.N1159.d014642 m n g p hfinite = p :=
    fun g => hsub (_root_.GD.N0076.N0313.d030588 m n hm hn g hp) hp
  obtain ⟨d, hd, hdae, hequiv⟩ :=
    (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn p hfinite).mp hfixed
  have hrisk (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014197 m n θ d = _root_.GD.N0232.N0720.N1080.d014182 m n θ p := by
    rw [_root_.GD.N0232.N0720.N1159.d014662 m n θ (hdae θ), _root_.GD.N0232.N0720.N1215.d014286]
  apply _root_.GD.N0096.N0344.d030520 m n hm hn
  refine ⟨d, ⟨hd, hequiv, ?_, ?_⟩, ?_⟩
  · intro θ
    rw [hrisk]
    exact hfinite θ
  · intro e he hbelow θ
    have heBelow : ∀ η, _root_.GD.N0232.N0720.N1080.d014197 m n η e ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n η (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
      intro η
      rw [_root_.GD.N0232.N0720.N1215.d014286, ← hrisk]
      exact hbelow η
    exact (_root_.GD.N0232.N0720.N1226.d015581 m n p hterminal
      e he heBelow θ).trans (hdae θ).symm
  · intro θ
    rw [hrisk, _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
    exact _root_.GD.N0076.N0313.d030587 m n hm hn hc hp θ

theorem d030590 {p : _root_.GD.N0076.N0313.d030564 m n}
    (hp : p ∈ _root_.GD.N0076.N0313.d030570 m n hm hn (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal) :
    _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) (_root_.GD.N0232.N0720.N1214.d014265 m n p) = _root_.GD.N0076.N0313.d030569 m n hm hn := by
  apply le_antisymm
  · apply iSup_le
    intro θ
    rw [← ENNReal.ofReal_toReal (_root_.GD.N0076.N0313.d030574 m n hm hn)]
    apply (_root_.GD.N0076.N0313.d030571 m n hm hn _ ENNReal.toReal_nonneg θ _).mpr
    rw [_root_.GD.N0232.N0720.N1215.d014286]
    exact hp θ
  · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0076.N0313.d030568 m n hm hn)
      (_root_.GD.N0076.N0313.d030572 m n (_root_.GD.N0076.N0313.d030576 m n hm hn hp))

def d030591 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  ∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
    (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ d) →
    ∀ θ, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] d

def d030592 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  ∃ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e ∧
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0720.N1482.d015118)
        (z : _root_.GD.N0232.N0720.N1080.d014170 m n) => g • z)
      (fun (g : _root_.GD.N0232.N0720.N1482.d015118)
        (y : ℝ) => g • y) e ∧
    e =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] d

include hm hn in
theorem d030593
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n)
    (hterminal : _root_.GD.N0076.N0313.d030591 m n d)
    (hbelow : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
      _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) :
    ¬ _root_.GD.N0076.N0313.d030592 m n d := by
  rintro ⟨e, he, hecov, hae⟩
  have haeθ (θ : _root_.GD.N0232.N0720.N1080.d014168) : e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] d :=
    (_root_.GD.N0232.N0720.N1080.d014173 m n θ).ae_eq hae
  have hrisk (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014197 m n θ e =
      _root_.GD.N0232.N0720.N1080.d014197 m n θ d := _root_.GD.N0232.N0720.N1159.d014662 m n θ (haeθ θ)
  apply _root_.GD.N0096.N0344.d030520 m n hm hn
  refine ⟨e, ⟨he, hecov, ?_, ?_⟩, ?_⟩
  · intro θ
    rw [hrisk]
    exact hd.2 θ
  · intro f hf hfe θ
    have hfd : ∀ η, _root_.GD.N0232.N0720.N1080.d014197 m n η f ≤ _root_.GD.N0232.N0720.N1080.d014197 m n η d := by
      intro η
      rw [← hrisk]
      exact hfe η
    exact (hterminal f hf hfd θ).trans (haeθ θ).symm
  · intro θ
    rw [hrisk]
    exact hbelow θ

theorem d030594 :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n,
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d < _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      _root_.GD.N0076.N0313.d030591 m n d ∧
      _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) d = _root_.GD.N0076.N0313.d030569 m n hm hn := by
  classical
  have hnot := _root_.GD.N0076.N0313.d030589 m n hm hn (_root_.GD.N0076.N0313.d030575 m n hm hn)
    (_root_.GD.N0076.N0313.d030585 m n hm hn)
  have hex : ∃ p ∈ _root_.GD.N0076.N0313.d030570 m n hm hn (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal,
      ∃ q ∈ _root_.GD.N0076.N0313.d030570 m n hm hn (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal, p ≠ q := by
    by_contra hnone
    push Not at hnone
    exact hnot (fun p hp q hq => hnone p hp q hq)
  obtain ⟨p, hp, q, hq, hpq⟩ := hex
  let s := _root_.GD.N0230.N0718.d001528 p q
  have hs : s ∈ _root_.GD.N0076.N0313.d030570 m n hm hn (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal := by
    intro θ
    exact _root_.GD.N0046.N0303.d030187
      (_root_.GD.N0232.N0720.N1080.d014173 m n θ) θ.location (hp θ) (hq θ)
  have hsStrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
    intro θ
    exact _root_.GD.N0046.N0303.d030188
      (_root_.GD.N0232.N0720.N1080.d014173 m n θ)
      (_root_.GD.N0046.N0305.d030203 m n θ)
      θ.location (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ)
      (_root_.GD.N0076.N0313.d030587 m n hm hn (_root_.GD.N0076.N0313.d030575 m n hm hn) hp θ)
      (_root_.GD.N0076.N0313.d030587 m n hm hn (_root_.GD.N0076.N0313.d030575 m n hm hn) hq θ) hpq
  let t := _root_.GD.N0232.N0720.N1159.d014633 m n s
  have ht : t ∈ _root_.GD.N0076.N0313.d030570 m n hm hn (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal :=
    _root_.GD.N0076.N0313.d030586 m n hm hn hs (_root_.GD.N0232.N0720.N1159.d014634 m n s).1
  have htStrict := _root_.GD.N0232.N0720.N1159.d014636
    m n s (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hsStrict
  refine ⟨_root_.GD.N0232.N0720.N1214.d014265 m n t,
    _root_.GD.N0076.N0313.d030572 m n (_root_.GD.N0076.N0313.d030576 m n hm hn ht), ?_, ?_,
    _root_.GD.N0076.N0313.d030590 m n hm hn ht⟩
  · intro θ
    rw [_root_.GD.N0232.N0720.N1215.d014286, _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
    exact htStrict θ
  · exact _root_.GD.N0232.N0720.N1226.d015581 m n t
      (_root_.GD.N0232.N0720.N1159.d014634 m n s).2.1

theorem d030595 :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n,
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d < _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      _root_.GD.N0076.N0313.d030591 m n d ∧
      _root_.GD.N0230.N0686.d003545 (_root_.GD.N0076.N0313.d030568 m n hm hn) (_root_.GD.N0232.N0720.N1256.d015551 m n) =
        ((1 - (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal : ℝ) : EReal) ∧
      _root_.GD.N0230.N0686.d003544 (_root_.GD.N0076.N0313.d030568 m n hm hn) d =
        _root_.GD.N0230.N0686.d003545 (_root_.GD.N0076.N0313.d030568 m n hm hn) (_root_.GD.N0232.N0720.N1256.d015551 m n) := by
  letI : Nonempty _root_.GD.N0232.N0720.N1080.d014168 := ⟨_root_.GD.N0232.N0720.N1080.d014169⟩
  obtain ⟨d, hd, hstrict, hterminal, hvalue⟩ :=
    _root_.GD.N0076.N0313.d030594 m n hm hn
  have hpoint : ∀ e ∈ _root_.GD.N0232.N0720.N1256.d015551 m n, ∀ θ, _root_.GD.N0076.N0313.d030568 m n hm hn θ e ≠ ⊤ := by
    intro e he θ
    exact ENNReal.div_ne_top (he.2 θ) (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn θ)
  have h := _root_.GD.N0230.N0686.d003549 (_root_.GD.N0076.N0313.d030568 m n hm hn)
    (_root_.GD.N0232.N0720.N1256.d015551 m n) hpoint d hd hvalue (_root_.GD.N0076.N0313.d030574 m n hm hn)
  exact ⟨d, hd, hstrict, hterminal, h⟩

theorem d030596 :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n,
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d < _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      _root_.GD.N0076.N0313.d030591 m n d ∧
      ¬ _root_.GD.N0076.N0313.d030592 m n d ∧
      _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) d = _root_.GD.N0076.N0313.d030569 m n hm hn := by
  obtain ⟨d, hd, hstrict, hterminal, hvalue⟩ :=
    _root_.GD.N0076.N0313.d030594 m n hm hn
  exact ⟨d, hd, hstrict, hterminal,
    _root_.GD.N0076.N0313.d030593 m n hm hn hd
      hterminal (fun θ => (hstrict θ).le), hvalue⟩

theorem d030597 :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n,
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d < _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      _root_.GD.N0076.N0313.d030591 m n d ∧
      ¬ _root_.GD.N0076.N0313.d030592 m n d ∧
      _root_.GD.N0232.N0720.N1228.d016753 m n hm hn
        (_root_.GD.N0232.N0720.N1256.d015551 m n) = ((1 - (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal : ℝ) : EReal) ∧
      _root_.GD.N0232.N0720.N1228.d016752 m n hm hn d =
        _root_.GD.N0232.N0720.N1228.d016753 m n hm hn
          (_root_.GD.N0232.N0720.N1256.d015551 m n) := by
  obtain ⟨d, hd, hstrict, hterminal, hopt, hattains⟩ :=
    _root_.GD.N0076.N0313.d030595 m n hm hn
  exact ⟨d, hd, hstrict, hterminal,
    _root_.GD.N0076.N0313.d030593 m n hm hn hd
      hterminal (fun θ => (hstrict θ).le), hopt, hattains⟩

end
end GD.N0076.N0313

#print axioms _root_.GD.N0076.N0313.d030585
#print axioms _root_.GD.N0076.N0313.d030589
#print axioms _root_.GD.N0076.N0313.d030594
#print axioms _root_.GD.N0076.N0313.d030595
#print axioms _root_.GD.N0076.N0313.d030596
#print axioms _root_.GD.N0076.N0313.d030597
