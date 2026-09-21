import GD.Module1865
import GD.Module0356
import GD.Module0955

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0214.N0531
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1066
open _root_.GD.N0230.N0718
open _root_.GD.N0046.N0303
open _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1226
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0611
open _root_.GD.N0076.N0313
open _root_.GD.N0004.N0241

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

theorem d030663 :
    ∃ p : _root_.GD.N0076.N0313.d030564 m n,
      _root_.GD.N0232.N0720.N1214.d014265 m n p ∈ _root_.GD.N0232.N0720.N1256.d015551 m n ∧
      _root_.GD.N0076.N0313.d030591 m n (_root_.GD.N0232.N0720.N1214.d014265 m n p) ∧
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1214.d014265 m n p) <
        _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) (_root_.GD.N0232.N0720.N1214.d014265 m n p) = _root_.GD.N0076.N0313.d030569 m n hm hn ∧
      ∀ θ, _root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p) < _root_.GD.N0076.N0313.d030569 m n hm hn := by
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
  have hss (θ) : _root_.GD.N0232.N0720.N1080.d014182 m n θ s <
      ENNReal.ofReal ((_root_.GD.N0076.N0313.d030569 m n hm hn).toReal * _root_.GD.N0076.N0313.d030565 m n hm hn θ) :=
    _root_.GD.N0046.N0303.d030188
      (_root_.GD.N0232.N0720.N1080.d014173 m n θ)
      (_root_.GD.N0046.N0305.d030203 m n θ)
      θ.location ENNReal.ofReal_ne_top (hp θ) (hq θ) hpq
  let t := _root_.GD.N0232.N0720.N1159.d014633 m n s
  have ht : t ∈ _root_.GD.N0076.N0313.d030570 m n hm hn (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal :=
    _root_.GD.N0076.N0313.d030586 m n hm hn hs (_root_.GD.N0232.N0720.N1159.d014634 m n s).1
  have hr (θ) : _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1214.d014265 m n t) <
      ENNReal.ofReal ((_root_.GD.N0076.N0313.d030569 m n hm hn).toReal * _root_.GD.N0076.N0313.d030565 m n hm hn θ) := by
    rw [_root_.GD.N0232.N0720.N1215.d014286]
    exact ((_root_.GD.N0232.N0720.N1159.d014634 m n s).1 θ).trans_lt (hss θ)
  refine ⟨t, _root_.GD.N0076.N0313.d030572 m n (_root_.GD.N0076.N0313.d030576 m n hm hn ht),
    _root_.GD.N0232.N0720.N1226.d015581 m n t
      (_root_.GD.N0232.N0720.N1159.d014634 m n s).2.1, ?_, _root_.GD.N0076.N0313.d030590 m n hm hn ht, ?_⟩
  · intro θ
    refine (hr θ).trans_le ?_
    rw [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
    calc
      _ ≤ ENNReal.ofReal (_root_.GD.N0076.N0313.d030565 m n hm hn θ) := ENNReal.ofReal_le_ofReal
        (mul_le_of_le_one_left (_root_.GD.N0076.N0313.d030566 m n hm hn θ).le (_root_.GD.N0076.N0313.d030575 m n hm hn))
      _ = _ := _root_.GD.N0076.N0313.d030567 m n hm hn θ
  · intro θ
    unfold _root_.GD.N0076.N0313.d030568
    apply (ENNReal.div_lt_iff (Or.inl (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn θ))
      (Or.inl (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn θ))).mpr
    convert hr θ using 1
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (_root_.GD.N0076.N0313.d030574 m n hm hn), _root_.GD.N0076.N0313.d030567]

variable [MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168] [OpensMeasurableSpace _root_.GD.N0232.N0720.N1080.d014168]

theorem d030664 (p : _root_.GD.N0076.N0313.d030564 m n) :
    Measurable (fun θ => (_root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal) := by
  have hp := (_root_.GD.N0232.N0720.N1499.d015008 m n p).measurable
  have hb := (_root_.GD.N0232.N0720.N1499.d015008 m n
    (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)).measurable
  have h := (hp.div hb).ennreal_toReal
  simpa only [_root_.GD.N0076.N0313.d030568, _root_.GD.N0232.N0720.N1215.d014286, _root_.GD.N0232.N0720.N1066.d014320] using h

theorem d030665 :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n, _root_.GD.N0076.N0313.d030591 m n d ∧
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d < _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) d = _root_.GD.N0076.N0313.d030569 m n hm hn ∧
      (∀ θ, (_root_.GD.N0076.N0313.d030568 m n hm hn θ d).toReal < (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal) ∧
      ∀ μ : Measure _root_.GD.N0232.N0720.N1080.d014168, IsProbabilityMeasure μ →
        (∫ θ, (_root_.GD.N0076.N0313.d030568 m n hm hn θ d).toReal ∂μ) < (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal := by
  obtain ⟨p, hp, ht, hs, hv, hcap⟩ :=
    _root_.GD.N0214.N0531.d030663 m n hm hn
  have hcap' (θ) : (_root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal <
      (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal :=
    (ENNReal.toReal_lt_toReal (ne_top_of_lt (hcap θ)) (_root_.GD.N0076.N0313.d030574 m n hm hn)).mpr (hcap θ)
  refine ⟨_root_.GD.N0232.N0720.N1214.d014265 m n p, hp, ht, hs, hv, hcap', ?_⟩
  intro μ hμ
  letI := hμ
  exact _root_.GD.N0004.N0241.d005269 μ (_root_.GD.N0214.N0531.d030664 m n hm hn p)
    (fun _ => ENNReal.toReal_nonneg) hcap'

theorem d030666 :
    ¬ ∃ μ : Measure _root_.GD.N0232.N0720.N1080.d014168, IsProbabilityMeasure μ ∧
      ∀ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n, (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal ≤
        ∫ θ, (_root_.GD.N0076.N0313.d030568 m n hm hn θ d).toReal ∂μ := by
  rintro ⟨μ, hμ, hmin⟩
  obtain ⟨d, hd, _, _, _, _, hp⟩ := _root_.GD.N0214.N0531.d030665 m n hm hn
  exact (not_lt_of_ge (hmin d hd)) (hp μ hμ)

end
end GD.N0214.N0531

#print axioms _root_.GD.N0214.N0531.d030663
#print axioms _root_.GD.N0214.N0531.d030664
#print axioms _root_.GD.N0214.N0531.d030665
#print axioms _root_.GD.N0214.N0531.d030666
