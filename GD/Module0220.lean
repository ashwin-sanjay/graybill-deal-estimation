import GD.Module0219
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds





















namespace GD
namespace N0232
namespace N0720
namespace N1089

noncomputable section


def d003092 (l : ℝ) : ℝ :=
  l ^ 2 / (l ^ 2 + (1 - l) ^ 2)


def d003093 (l : ℝ) : ℝ :=
  l ^ 2 / (l ^ 2 + (1 - l) ^ 2) ^ 2


def d003094 (l : ℝ) : ℝ :=
  Real.arctan (2 * l - 1) / 2 -
    (1 + (2 * l - 1) ^ 2)⁻¹ / 2


theorem d003095 (l : ℝ) :
    0 < l ^ 2 + (1 - l) ^ 2 := by
  nlinarith [sq_nonneg l, sq_nonneg (1 - l)]



theorem d003096 (l : ℝ) :
    _root_.GD.N0232.N0720.N1089.d003093 l + _root_.GD.N0232.N0720.N1089.d003093 (1 - l) =
      1 / (l ^ 2 + (1 - l) ^ 2) := by
  unfold _root_.GD.N0232.N0720.N1089.d003093
  have hden : l ^ 2 + (1 - l) ^ 2 ≠ 0 :=
    ne_of_gt (_root_.GD.N0232.N0720.N1089.d003095 l)
  have hden' : (1 - l) ^ 2 + (1 - (1 - l)) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg l, sq_nonneg (1 - l)]
  field_simp [hden, hden']
  ring


theorem d003097 (l : ℝ) :
    0 < 1 + (2 * l - 1) ^ 2 := by
  positivity


theorem d003098 (l : ℝ) :
    HasDerivAt _root_.GD.N0232.N0720.N1089.d003094 (_root_.GD.N0232.N0720.N1089.d003093 l) l := by
  have hlin : HasDerivAt (fun x : ℝ ↦ 2 * x - 1) 2 l := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id l).const_mul (2 : ℝ)).sub_const 1)
  have hden := (hlin.pow 2).const_add 1
  have hatan :=
    (Real.hasDerivAt_arctan (2 * l - 1)).comp l hlin
  have hinv := hden.inv (ne_of_gt (_root_.GD.N0232.N0720.N1089.d003097 l))
  have hprimitive := (hatan.div_const 2).sub (hinv.div_const 2)
  have hfun : _root_.GD.N0232.N0720.N1089.d003094 =
      (fun x : ℝ ↦
        Real.arctan (2 * x - 1) / 2 -
          (1 + (2 * x - 1) ^ 2)⁻¹ / 2) := by
    rfl
  rw [hfun]
  apply hprimitive.congr_deriv
  unfold _root_.GD.N0232.N0720.N1089.d003093
  have hc : l ^ 2 + (1 - l) ^ 2 ≠ 0 :=
    ne_of_gt (_root_.GD.N0232.N0720.N1089.d003095 l)
  have hz : 1 + (2 * l - 1) ^ 2 ≠ 0 :=
    ne_of_gt (_root_.GD.N0232.N0720.N1089.d003097 l)
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hc, hz]
  ring


theorem d003099 :
    (∫ l : ℝ in (0 : ℝ)..1, _root_.GD.N0232.N0720.N1089.d003093 l) = Real.pi / 4 := by
  calc
    (∫ l : ℝ in (0 : ℝ)..1, _root_.GD.N0232.N0720.N1089.d003093 l) =
        _root_.GD.N0232.N0720.N1089.d003094 1 - _root_.GD.N0232.N0720.N1089.d003094 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro l _hl
        exact _root_.GD.N0232.N0720.N1089.d003098 l
      · have hnum : Continuous (fun l : ℝ ↦ l ^ 2) := by fun_prop
        have hden :
            Continuous (fun l : ℝ ↦
              (l ^ 2 + (1 - l) ^ 2) ^ 2) := by fun_prop
        have hne : ∀ l : ℝ,
            (l ^ 2 + (1 - l) ^ 2) ^ 2 ≠ 0 := fun l =>
          pow_ne_zero 2 (ne_of_gt (_root_.GD.N0232.N0720.N1089.d003095 l))
        exact (hnum.div hden hne).intervalIntegrable 0 1
    _ = Real.pi / 4 := by
      simp only [_root_.GD.N0232.N0720.N1089.d003094]
      rw [show 2 * (1 : ℝ) - 1 = 1 by norm_num,
        show 2 * (0 : ℝ) - 1 = -1 by norm_num,
        Real.arctan_one, Real.arctan_neg, Real.arctan_one]
      norm_num
      ring


theorem d003100 :
    (∫ l : ℝ in (0 : ℝ)..1, _root_.GD.N0232.N0720.N1089.d003093 l) < 1 := by
  rw [_root_.GD.N0232.N0720.N1089.d003099]
  have hpi : Real.pi < 4 := Real.pi_lt_four
  linarith


theorem d003101 (l : ℝ) :
    _root_.GD.N0232.N0720.N1089.d003092 l =
      _root_.GD.N0232.N0720.N1463.d003070 2 l := by
  unfold _root_.GD.N0232.N0720.N1089.d003092
  simp [_root_.GD.N0232.N0720.N1463.d003070]
  ring



theorem d003102
    {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1089.d003092 (1 - l) = 1 - _root_.GD.N0232.N0720.N1089.d003092 l := by
  rw [_root_.GD.N0232.N0720.N1089.d003101,
    _root_.GD.N0232.N0720.N1089.d003101]
  exact
    _root_.GD.N0232.N0720.N1463.d003074 hl 2



theorem d003103
    {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1089.d003092 l = l ↔ l = 1 / 2 := by
  have hden : l ^ 2 + (1 - l) ^ 2 ≠ 0 :=
    ne_of_gt (_root_.GD.N0232.N0720.N1089.d003095 l)
  constructor
  · intro h
    unfold _root_.GD.N0232.N0720.N1089.d003092 at h
    field_simp [hden] at h
    have hfactor : l * (2 * l - 1) * (l - 1) = 0 := by
      calc
        l * (2 * l - 1) * (l - 1) =
            l * (l ^ 2 + (1 - l) ^ 2) - l ^ 2 := by ring
        _ = 0 := by rw [← h]; ring
    rcases mul_eq_zero.mp hfactor with hleft | hone
    · rcases mul_eq_zero.mp hleft with hzero | hmid
      · exact False.elim ((ne_of_gt hl.1) hzero)
      · nlinarith
    · exact False.elim ((sub_ne_zero.mpr (ne_of_lt hl.2)) hone)
  · rintro rfl
    norm_num [_root_.GD.N0232.N0720.N1089.d003092]





theorem d003104
    {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 1) (action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003069 2 l
        (_root_.GD.N0232.N0720.N1089.d003092 l) ≤
      _root_.GD.N0232.N0720.N1463.d003069 2 l action := by
  have hleft : 0 < (1 - l) ^ (2 : ℝ) :=
    Real.rpow_pos_of_pos (sub_pos.mpr hl.2) 2
  have hright : 0 < l ^ (2 : ℝ) :=
    Real.rpow_pos_of_pos hl.1 2
  simpa [_root_.GD.N0232.N0720.N1463.d003069,
    _root_.GD.N0232.N0720.N1463.d003047,
    _root_.GD.N0232.N0720.N1089.d003092, _root_.GD.N0232.N0720.N1463.d003048,
    Real.rpow_two, add_comm] using
    (_root_.GD.N0232.N0720.N1463.d003050
      hleft hright action)



theorem d003105
    {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 1) (action : ℝ) :
    _root_.GD.N0232.N0720.N1463.d003069 2 l action =
        _root_.GD.N0232.N0720.N1463.d003069 2 l
          (_root_.GD.N0232.N0720.N1089.d003092 l) ↔
      action = _root_.GD.N0232.N0720.N1089.d003092 l := by
  rw [_root_.GD.N0232.N0720.N1089.d003101]
  exact
    _root_.GD.N0232.N0720.N1463.d003073
      hl 2 action




theorem d003106
    {l : ℝ} (hl : l ∈ Set.Ioo (0 : ℝ) 1) (hbal : l ≠ 1 / 2) :
    _root_.GD.N0232.N0720.N1463.d003069 2 l
        (_root_.GD.N0232.N0720.N1089.d003092 l) <
      _root_.GD.N0232.N0720.N1463.d003069 2 l l := by
  have hle := _root_.GD.N0232.N0720.N1089.d003104 hl l
  refine lt_of_le_of_ne hle ?_
  intro heq
  have haction : l = _root_.GD.N0232.N0720.N1089.d003092 l :=
    (_root_.GD.N0232.N0720.N1089.d003105 hl l).mp heq.symm
  exact hbal ((_root_.GD.N0232.N0720.N1089.d003103 hl).mp haction.symm)



theorem d003107 :
    1 - (∫ l : ℝ in (0 : ℝ)..1, _root_.GD.N0232.N0720.N1089.d003093 l) =
      1 - Real.pi / 4 := by
  rw [_root_.GD.N0232.N0720.N1089.d003099]

theorem d003108 :
    0 < 1 - (∫ l : ℝ in (0 : ℝ)..1, _root_.GD.N0232.N0720.N1089.d003093 l) := by
  rw [_root_.GD.N0232.N0720.N1089.d003099]
  linarith [Real.pi_lt_four]

#print axioms _root_.GD.N0232.N0720.N1089.d003099
#print axioms _root_.GD.N0232.N0720.N1089.d003106
#print axioms _root_.GD.N0232.N0720.N1089.d003108

end

end N1089
end N0720
end N0232
end GD
