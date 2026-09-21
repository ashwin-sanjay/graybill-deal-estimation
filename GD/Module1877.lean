import GD.Module1875

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0214.N0531
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1256
open _root_.GD.N0076.N0313
open _root_.GD.N0046.N0303
open _root_.GD.N0004.N0241

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
variable [MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168] [OpensMeasurableSpace _root_.GD.N0232.N0720.N1080.d014168]

theorem d030670 :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n, _root_.GD.N0076.N0313.d030591 m n d ∧
      (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d < _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      _root_.GD.N0230.N0611.d003516 (_root_.GD.N0076.N0313.d030568 m n hm hn) d =
        _root_.GD.N0076.N0313.d030569 m n hm hn ∧
      ∀ μ : Measure _root_.GD.N0232.N0720.N1080.d014168, IsProbabilityMeasure μ →
        (∫⁻ θ, _root_.GD.N0076.N0313.d030568 m n hm hn θ d ∂μ) < _root_.GD.N0076.N0313.d030569 m n hm hn := by
  obtain ⟨p, hp, ht, hs, hv, hcap⟩ :=
    _root_.GD.N0214.N0531.d030663 m n hm hn
  have hcap' (θ) : (_root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal <
      (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal :=
    (ENNReal.toReal_lt_toReal (ne_top_of_lt (hcap θ)) (_root_.GD.N0076.N0313.d030574 m n hm hn)).mpr (hcap θ)
  refine ⟨_root_.GD.N0232.N0720.N1214.d014265 m n p, hp, ht, hs, hv, ?_⟩
  intro μ hμ
  letI := hμ
  have hrm := _root_.GD.N0214.N0531.d030664 m n hm hn p
  have hi := _root_.GD.N0004.N0241.d005268 μ hrm (fun _ => ENNReal.toReal_nonneg)
    (fun θ => (hcap' θ).le)
  have hlt := _root_.GD.N0004.N0241.d005269 μ hrm (fun _ => ENNReal.toReal_nonneg) hcap'
  have heq : (∫⁻ θ, _root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p) ∂μ) =
      ENNReal.ofReal (∫ θ, (_root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal ∂μ) := by
    calc
      _ = ∫⁻ θ, ENNReal.ofReal (_root_.GD.N0076.N0313.d030568 m n hm hn θ (_root_.GD.N0232.N0720.N1214.d014265 m n p)).toReal ∂μ :=
        lintegral_congr_ae (Filter.Eventually.of_forall fun θ =>
          (ENNReal.ofReal_toReal (ne_top_of_lt (hcap θ))).symm)
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm
  have hvpos : 0 < (_root_.GD.N0076.N0313.d030569 m n hm hn).toReal :=
    ENNReal.toReal_pos (ne_of_gt (bot_le.trans_lt (hcap _root_.GD.N0232.N0720.N1080.d014169)))
      (_root_.GD.N0076.N0313.d030574 m n hm hn)
  rw [heq, ← ENNReal.ofReal_toReal (_root_.GD.N0076.N0313.d030574 m n hm hn)]
  exact (ENNReal.ofReal_lt_ofReal_iff hvpos).mpr hlt

theorem d030671 :
    ¬ ∃ μ : Measure _root_.GD.N0232.N0720.N1080.d014168, IsProbabilityMeasure μ ∧
      ∀ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n, _root_.GD.N0076.N0313.d030569 m n hm hn ≤
        ∫⁻ θ, _root_.GD.N0076.N0313.d030568 m n hm hn θ d ∂μ := by
  rintro ⟨μ, hμ, hmin⟩
  obtain ⟨d, hd, _, _, _, hp⟩ :=
    _root_.GD.N0214.N0531.d030670 m n hm hn
  exact (not_lt_of_ge (hmin d hd)) (hp μ hμ)

end
end GD.N0214.N0531

#print axioms _root_.GD.N0214.N0531.d030670
#print axioms _root_.GD.N0214.N0531.d030671
