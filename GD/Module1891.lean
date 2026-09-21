import GD.Module1889
import GD.Module1179
import GD.Module0939

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace GD.N0078.N0317

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1256
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0611
open _root_.GD.N0082 _root_.GD.N0076.N0313
open _root_.GD.N0232.N0720.N1501 _root_.GD.N0232.N0720.N1470
open _root_.GD.N0230.N0642
open _root_.GD.N0230.N0642.d001800

section Design

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn in
theorem d030762
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n)
    (ht : _root_.GD.N0076.N0313.d030591 m n d) :
    ∃ q : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable q ∧
      ∀ θ, (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] d := by
  have hmem := _root_.GD.N0232.N0720.N1215.d014285 m n d hd.1
    (hd.2 _root_.GD.N0232.N0720.N1080.d014169)
  let p := hmem.toLp d
  have hp : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p := by
    intro e he
    have hdom : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1214.d014265 m n e) ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n θ d := by
      intro θ
      rw [_root_.GD.N0232.N0720.N1215.d014286, _root_.GD.N0232.N0720.N1080.d014198 m n θ d hmem]
      exact he θ
    apply Lp.ext
    exact (_root_.GD.N0232.N0720.N1214.d014267 m n e).symm.trans
      ((ht _ (_root_.GD.N0232.N0720.N1214.d014266 m n e) hdom _root_.GD.N0232.N0720.N1080.d014169).trans
        hmem.coeFn_toLp.symm)
  obtain ⟨q, hq, hpq⟩ :=
    _root_.GD.N0232.N0720.N1470.d018970 m n hm hn p hp
  refine ⟨q, hq, fun θ => ?_⟩
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n θ).ae_eq
    (hpq.symm.trans hmem.coeFn_toLp)

theorem d030763
    {d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0076.N0313.d030591 m n d)
    (hae : ∀ θ, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] d) : _root_.GD.N0076.N0313.d030591 m n e := by
  intro f hf hdom θ
  have hdomd : ∀ η, _root_.GD.N0232.N0720.N1080.d014197 m n η f ≤ _root_.GD.N0232.N0720.N1080.d014197 m n η d := by
    intro η
    rw [← _root_.GD.N0232.N0720.N1159.d014662 m n η (hae η)]
    exact hdom η
  exact (hd f hf hdomd θ).trans (hae θ).symm

def d030764 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  ∀ (κ : Kernel (_root_.GD.N0232.N0720.N1080.d014170 m n) ℝ), IsMarkovKernel κ →
    (∀ θ, _root_.GD.N0230.N0642.d001800.d001823 κ (_root_.GD.N0232.N0720.N1080.d014171 m n θ) θ.location ≤
      _root_.GD.N0232.N0720.N1080.d014197 m n θ d) →
    ∀ θ, ∀ᵐ z ∂_root_.GD.N0232.N0720.N1080.d014171 m n θ, κ z = Measure.dirac (d z)

theorem d030765
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n)
    (ht : _root_.GD.N0076.N0313.d030591 m n d) : _root_.GD.N0078.N0317.d030764 m n d := by
  intro κ hκ hdom
  letI : IsMarkovKernel κ := hκ
  exact _root_.GD.N0230.N0642.d001800.d001839
    (_root_.GD.N0232.N0720.N1080.d014171 m n) (fun θ : _root_.GD.N0232.N0720.N1080.d014168 => θ.location) d κ _root_.GD.N0232.N0720.N1080.d014169
    ht (hd.2 _root_.GD.N0232.N0720.N1080.d014169) hdom (_root_.GD.N0232.N0720.N1080.d014173 m n)

def d030766 : Prop :=
  ∃ (J : ℕ) (q : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ),
    1 ≤ J ∧ Measurable q ∧
    (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) ∈ _root_.GD.N0232.N0720.N1256.d015551 m n ∧
    (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) ≤
      ENNReal.ofReal (_root_.GD.N0082.d030598 J) * _root_.GD.N0232.N0720.N1066.d014320 m n hm hn θ) ∧
    _root_.GD.N0076.N0313.d030591 m n (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) ∧
    _root_.GD.N0078.N0317.d030764 m n (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) ∧
    ¬ _root_.GD.N0076.N0313.d030592 m n (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) ∧
    _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =
      _root_.GD.N0076.N0313.d030569 m n hm hn

theorem d030767 :
    _root_.GD.N0082.d030603 m n hm hn ↔ _root_.GD.N0078.N0317.d030766 m n hm hn := by
  constructor
  · intro hu
    obtain ⟨J, hJ, d, hd, hcap, ht, hna, hv⟩ :=
      (_root_.GD.N0082.d030611 m n hm hn).mp hu
    obtain ⟨q, hq, hae⟩ := _root_.GD.N0078.N0317.d030762 m n hm hn hd ht
    have hrisk : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =
        _root_.GD.N0232.N0720.N1080.d014197 m n θ d :=
      fun θ => _root_.GD.N0232.N0720.N1159.d014662 m n θ (hae θ)
    have hqfinite : (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) ∈ _root_.GD.N0232.N0720.N1256.d015551 m n := by
      refine ⟨hq.comp (_root_.GD.N0232.N0720.N1501.d016289 m n), fun θ => ?_⟩
      rw [hrisk]
      exact hd.2 θ
    have hqt := _root_.GD.N0078.N0317.d030763 m n ht hae
    refine ⟨J, q, hJ, hq, hqfinite, ?_, hqt,
      _root_.GD.N0078.N0317.d030765 m n hqfinite hqt, ?_, ?_⟩
    · intro θ
      rw [hrisk]
      exact hcap θ
    · rintro ⟨e, he, hecov, herep⟩
      exact hna ⟨e, he, hecov, herep.trans (hae _root_.GD.N0232.N0720.N1080.d014169)⟩
    · have heq : (fun θ => _root_.GD.N0076.N0313.d030568 m n hm hn θ (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n)) =
          (fun θ => _root_.GD.N0076.N0313.d030568 m n hm hn θ d) := by
        funext θ
        unfold _root_.GD.N0076.N0313.d030568
        rw [hrisk]
      exact (congrArg iSup heq).trans hv
  · rintro ⟨J, q, hJ, _hq, hfinite, hcap, _ht, _hκ, _hna, _hv⟩
    exact ⟨J, hJ, q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n, hfinite.1, hcap⟩

theorem d030768 :
    ¬ _root_.GD.N0082.d030602 m n hm hn ↔
      _root_.GD.N0078.N0317.d030766 m n hm hn :=
  (_root_.GD.N0082.d030610 m n hm hn).trans
    (_root_.GD.N0078.N0317.d030767 m n hm hn)

end Design

theorem d030769 :
    _root_.GD.N0078.N0317.d030766 3 3 (by omega) (by omega) :=
  (_root_.GD.N0078.N0317.d030767 3 3 (by omega) (by omega)).mp
    _root_.GD.N0082.N0330.d030755

theorem d030770 :
    (¬ _root_.GD.N0082.d030602 3 3 (by omega) (by omega)) ∧
    _root_.GD.N0078.N0317.d030766 3 3 (by omega) (by omega) ∧
    (∀ (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n),
      _root_.GD.N0082.d030603 m n hm hn ↔ _root_.GD.N0078.N0317.d030766 m n hm hn) :=
  ⟨_root_.GD.N0082.N0330.d030756, _root_.GD.N0078.N0317.d030769,
    _root_.GD.N0078.N0317.d030767⟩

end
end GD.N0078.N0317

#print axioms _root_.GD.N0078.N0317.d030762
#print axioms _root_.GD.N0078.N0317.d030763
#print axioms _root_.GD.N0078.N0317.d030765
#print axioms _root_.GD.N0078.N0317.d030767
#print axioms _root_.GD.N0078.N0317.d030768
#print axioms _root_.GD.N0078.N0317.d030769
#print axioms _root_.GD.N0078.N0317.d030770
