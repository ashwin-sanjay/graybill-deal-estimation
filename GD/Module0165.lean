import GD.Module0038
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic




















open scoped BigOperators ENNReal NNReal

namespace GD
namespace N0232
namespace N0720
namespace N1203

noncomputable section

set_option linter.unusedSectionVars false

variable {I Omega : Type*} [Fintype I]


def d001905 (q : ℝ) : ℝ := q * (1 - q)

@[simp] theorem d001906 (q : ℝ) :
    _root_.GD.N0232.N0720.N1203.d001905 (1 - q) = _root_.GD.N0232.N0720.N1203.d001905 q := by
  unfold _root_.GD.N0232.N0720.N1203.d001905
  ring



def d001907 (weight scale q : ℝ) : ℝ :=
  4 * weight * scale * _root_.GD.N0232.N0720.N1203.d001905 q ^ 2


def d001908 (weight scale q : ℝ) : ℝ :=
  2 * _root_.GD.N0232.N0720.N1203.d001907 weight scale q

theorem d001909
    (weight scale q : ℝ) :
    _root_.GD.N0232.N0720.N1203.d001908 weight scale q =
      8 * weight * scale * _root_.GD.N0232.N0720.N1203.d001905 q ^ 2 := by
  simp [_root_.GD.N0232.N0720.N1203.d001908, _root_.GD.N0232.N0720.N1203.d001907]
  ring


theorem d001910
    {M S q : ℝ}
    (hS : S ≠ 0) (hq : _root_.GD.N0232.N0720.N1203.d001905 q ≠ 0) :
    _root_.GD.N0232.N0720.N1203.d001907 (M / (8 * S * _root_.GD.N0232.N0720.N1203.d001905 q ^ 2)) S q = M / 2 := by
  unfold _root_.GD.N0232.N0720.N1203.d001907
  field_simp
  ring



def d001911
    (weight scale fraction : I → ℝ) (q : ℝ) : ℝ :=
  ∑ i, if fraction i = q ∨ fraction i = 1 - q then 0
    else _root_.GD.N0232.N0720.N1203.d001908 (weight i) (scale i) (fraction i)



theorem d001912
    (weight scale fraction : I → ℝ) (q : ℝ)
    (hweight : ∀ i, 0 < weight i)
    (hscale : ∀ i, 0 < scale i)
    (hfraction : ∀ i, 0 < fraction i ∧ fraction i < 1)
    (hout : _root_.GD.N0232.N0720.N1203.d001911 weight scale fraction q = 0) :
    ∀ i, fraction i = q ∨ fraction i = 1 - q := by
  intro i
  by_contra hi
  have htermPos :
      0 < (if fraction i = q ∨ fraction i = 1 - q then 0
        else _root_.GD.N0232.N0720.N1203.d001908 (weight i) (scale i) (fraction i)) := by
    rw [if_neg hi]
    rw [_root_.GD.N0232.N0720.N1203.d001909]
    have hb : 0 < _root_.GD.N0232.N0720.N1203.d001905 (fraction i) := by
      unfold _root_.GD.N0232.N0720.N1203.d001905
      exact mul_pos (hfraction i).1 (sub_pos.mpr (hfraction i).2)
    have hpref : 0 < 8 * weight i * scale i :=
      mul_pos (mul_pos (by norm_num) (hweight i)) (hscale i)
    exact mul_pos hpref (sq_pos_of_pos hb)
  have hnonneg : ∀ j ∈ (Finset.univ : Finset I),
      0 ≤ (if fraction j = q ∨ fraction j = 1 - q then 0
        else _root_.GD.N0232.N0720.N1203.d001908 (weight j) (scale j) (fraction j)) := by
    intro j hj
    split_ifs
    · exact le_rfl
    · rw [_root_.GD.N0232.N0720.N1203.d001909]
      have hb : 0 < _root_.GD.N0232.N0720.N1203.d001905 (fraction j) := by
        unfold _root_.GD.N0232.N0720.N1203.d001905
        exact mul_pos (hfraction j).1 (sub_pos.mpr (hfraction j).2)
      have hpref : 0 < 8 * weight j * scale j :=
        mul_pos (mul_pos (by norm_num) (hweight j)) (hscale j)
      exact (mul_pos hpref (sq_pos_of_pos hb)).le
  have hzeroEach :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp (by
      simpa [_root_.GD.N0232.N0720.N1203.d001911] using hout)
  exact (ne_of_gt htermPos) (hzeroEach i (Finset.mem_univ i))


def d001913 (M q : ℝ) : ℝ :=
  M / (8 * _root_.GD.N0232.N0720.N1203.d001905 q ^ 2)



theorem d001914
    (weight scale fraction : I → ℝ) (q : ℝ)
    (hsupport : ∀ i, fraction i = q ∨ fraction i = 1 - q) :
    (∑ i, _root_.GD.N0232.N0720.N1203.d001908 (weight i) (scale i) (fraction i)) =
      8 * _root_.GD.N0232.N0720.N1203.d001905 q ^ 2 * ∑ i, weight i * scale i := by
  simp only [_root_.GD.N0232.N0720.N1203.d001909]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hsupport i with h | h
  · rw [h]
    ring
  · rw [h, _root_.GD.N0232.N0720.N1203.d001906]
    ring


theorem d001915
    (weight scale fraction : I → ℝ) {M q : ℝ}
    (hq : _root_.GD.N0232.N0720.N1203.d001905 q ≠ 0)
    (hsupport : ∀ i, fraction i = q ∨ fraction i = 1 - q)
    (hcontact :
      (∑ i, _root_.GD.N0232.N0720.N1203.d001908 (weight i) (scale i) (fraction i)) = M) :
    (∑ i, weight i * scale i) = _root_.GD.N0232.N0720.N1203.d001913 M q := by
  rw [_root_.GD.N0232.N0720.N1203.d001914 weight scale fraction q hsupport]
    at hcontact
  unfold _root_.GD.N0232.N0720.N1203.d001913
  have hdenom : 8 * _root_.GD.N0232.N0720.N1203.d001905 q ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hq)
  apply (eq_div_iff hdenom).2
  simpa [mul_comm] using hcontact





def d001916
    (weight scale : I → ℝ) (budget : ℝ) (i : I) : ℝ :=
  weight i * scale i / budget

theorem d001917
    (weight scale : I → ℝ) {budget : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hscale : ∀ i, 0 ≤ scale i)
    (hbudget : 0 ≤ budget) :
    ∀ i, 0 ≤ _root_.GD.N0232.N0720.N1203.d001916 weight scale budget i := by
  intro i
  exact div_nonneg (mul_nonneg (hweight i) (hscale i)) hbudget

theorem d001918
    (weight scale : I → ℝ) {budget : ℝ}
    (hbudget : budget ≠ 0)
    (hmoment : ∑ i, weight i * scale i = budget) :
    ∑ i, _root_.GD.N0232.N0720.N1203.d001916 weight scale budget i = 1 := by
  simp only [_root_.GD.N0232.N0720.N1203.d001916, ← Finset.sum_div]
  rw [hmoment, div_self hbudget]





def d001919
    (probabilityWeight scale : I → ℝ) (budget : ℝ) (i : I) : ℝ :=
  budget * probabilityWeight i / scale i

theorem d001920
    (probabilityWeight scale : I → ℝ) {budget : ℝ}
    (hprobability : ∀ i, 0 ≤ probabilityWeight i)
    (hscale : ∀ i, 0 ≤ scale i) (hbudget : 0 ≤ budget) :
    ∀ i, 0 ≤ _root_.GD.N0232.N0720.N1203.d001919 probabilityWeight scale budget i := by
  intro i
  exact div_nonneg (mul_nonneg hbudget (hprobability i)) (hscale i)


theorem d001921
    (probabilityWeight scale : I → ℝ) {budget : ℝ}
    (hscale : ∀ i, scale i ≠ 0)
    (hsum : ∑ i, probabilityWeight i = 1) :
    ∑ i, _root_.GD.N0232.N0720.N1203.d001919 probabilityWeight scale budget i * scale i =
      budget := by
  calc
    ∑ i, _root_.GD.N0232.N0720.N1203.d001919 probabilityWeight scale budget i * scale i =
        ∑ i, budget * probabilityWeight i := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold _root_.GD.N0232.N0720.N1203.d001919
      field_simp [hscale i]
    _ = budget * ∑ i, probabilityWeight i := by rw [Finset.mul_sum]
    _ = budget := by rw [hsum, mul_one]



theorem d001922
    (probabilityWeight scale : I → ℝ) {budget : ℝ}
    (hbudget : budget ≠ 0) (hscale : ∀ i, scale i ≠ 0) :
    _root_.GD.N0232.N0720.N1203.d001916
      (_root_.GD.N0232.N0720.N1203.d001919 probabilityWeight scale budget)
      scale budget = probabilityWeight := by
  funext i
  unfold _root_.GD.N0232.N0720.N1203.d001916 _root_.GD.N0232.N0720.N1203.d001919
  field_simp [hbudget, hscale i]



theorem d001923
    (probabilityWeight scale fraction : I → ℝ) {budget q : ℝ}
    (hscale : ∀ i, scale i ≠ 0)
    (hsum : ∑ i, probabilityWeight i = 1)
    (hsupport : ∀ i, fraction i = q ∨ fraction i = 1 - q) :
    ∑ i, _root_.GD.N0232.N0720.N1203.d001908
        (_root_.GD.N0232.N0720.N1203.d001919 probabilityWeight scale budget i)
        (scale i) (fraction i) =
      8 * _root_.GD.N0232.N0720.N1203.d001905 q ^ 2 * budget := by
  rw [_root_.GD.N0232.N0720.N1203.d001914 _ _ _ q hsupport]
  rw [_root_.GD.N0232.N0720.N1203.d001921 probabilityWeight scale hscale hsum]



theorem d001924
    (probabilityWeight scale fraction : I → ℝ) {M q : ℝ}
    (hq : _root_.GD.N0232.N0720.N1203.d001905 q ≠ 0)
    (hscale : ∀ i, scale i ≠ 0)
    (hsum : ∑ i, probabilityWeight i = 1)
    (hsupport : ∀ i, fraction i = q ∨ fraction i = 1 - q) :
    ∑ i, _root_.GD.N0232.N0720.N1203.d001908
        (_root_.GD.N0232.N0720.N1203.d001919 probabilityWeight scale (_root_.GD.N0232.N0720.N1203.d001913 M q) i)
        (scale i) (fraction i) = M := by
  rw [_root_.GD.N0232.N0720.N1203.d001923 probabilityWeight scale fraction
    hscale hsum hsupport]
  unfold _root_.GD.N0232.N0720.N1203.d001913
  field_simp [hq]




def d001925
    (probabilityWeight : I → ℝ≥0∞)
    (hsum : ∑ i, probabilityWeight i = 1) : PMF I :=
  PMF.ofFintype probabilityWeight hsum

@[simp] theorem d001926
    (probabilityWeight : I → ℝ≥0∞)
    (hsum : ∑ i, probabilityWeight i = 1) (i : I) :
    _root_.GD.N0232.N0720.N1203.d001925 probabilityWeight hsum i = probabilityWeight i := rfl




def d001927
    (probabilityWeight : I → ℝ) (scale : I → ℝ)
    (likelihood : I → Omega → ℝ) (omega : Omega) : ℝ :=
  ∑ i, probabilityWeight i * likelihood i omega / scale i


def d001928
    (probabilityWeight : I → ℝ) (scale location : I → ℝ)
    (likelihood : I → Omega → ℝ) (omega : Omega) : ℝ :=
  ∑ i, probabilityWeight i * location i * likelihood i omega / scale i


theorem d001929
    (weight scale : I → ℝ) (likelihood : I → Omega → ℝ)
    {budget : ℝ} (hbudget : budget ≠ 0)
    (hscale : ∀ i, scale i ≠ 0) (omega : Omega) :
    budget * _root_.GD.N0232.N0720.N1203.d001927
      (_root_.GD.N0232.N0720.N1203.d001916 weight scale budget) scale likelihood omega =
      ∑ i, weight i * likelihood i omega := by
  simp only [_root_.GD.N0232.N0720.N1203.d001927, _root_.GD.N0232.N0720.N1203.d001916, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hscale i, hbudget]


theorem d001930
    (weight scale location : I → ℝ)
    (likelihood : I → Omega → ℝ)
    {budget : ℝ} (hbudget : budget ≠ 0)
    (hscale : ∀ i, scale i ≠ 0) (omega : Omega) :
    budget * _root_.GD.N0232.N0720.N1203.d001928
      (_root_.GD.N0232.N0720.N1203.d001916 weight scale budget) scale location likelihood omega =
      ∑ i, weight i * location i * likelihood i omega := by
  simp only [_root_.GD.N0232.N0720.N1203.d001928, _root_.GD.N0232.N0720.N1203.d001916, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [hscale i, hbudget]


def d001931 (budget evidence current target : ℝ) : ℝ :=
  ((1 + budget * evidence) * target - budget * current) ^ 2 /
    (1 + budget * evidence)


theorem d001932
    {budget evidence current target : ℝ}
    (hdenom : 1 + budget * evidence ≠ 0) :
    _root_.GD.N0232.N0720.N1203.d001931 budget evidence current target =
      (1 + budget * evidence) *
        (target - budget * current / (1 + budget * evidence)) ^ 2 := by
  unfold _root_.GD.N0232.N0720.N1203.d001931
  field_simp [hdenom]


theorem d001933
    (weight scale location : I → ℝ)
    (likelihood : I → Omega → ℝ)
    {budget target : ℝ}
    (hbudget : budget ≠ 0) (hscale : ∀ i, scale i ≠ 0)
    (omega : Omega) :
    let evidence := ∑ i, weight i * likelihood i omega
    let current := ∑ i, weight i * location i * likelihood i omega
    ((1 + evidence) * target - current) ^ 2 / (1 + evidence) =
      _root_.GD.N0232.N0720.N1203.d001931 budget
        (_root_.GD.N0232.N0720.N1203.d001927 (_root_.GD.N0232.N0720.N1203.d001916 weight scale budget)
          scale likelihood omega)
        (_root_.GD.N0232.N0720.N1203.d001928 (_root_.GD.N0232.N0720.N1203.d001916 weight scale budget)
          scale location likelihood omega)
        target := by
  dsimp only
  rw [_root_.GD.N0232.N0720.N1203.d001931,
    _root_.GD.N0232.N0720.N1203.d001929 weight scale likelihood hbudget hscale omega,
    _root_.GD.N0232.N0720.N1203.d001930 weight scale location likelihood hbudget hscale omega]



theorem d001934
    (probabilityWeight scale location : I → ℝ)
    (likelihood : I → Omega → ℝ)
    {budget target : ℝ}
    (hbudget : budget ≠ 0) (hscale : ∀ i, scale i ≠ 0)
    (omega : Omega) :
    let packetWeight :=
      _root_.GD.N0232.N0720.N1203.d001919 probabilityWeight scale budget
    let evidence := ∑ i, packetWeight i * likelihood i omega
    let current := ∑ i, packetWeight i * location i * likelihood i omega
    ((1 + evidence) * target - current) ^ 2 / (1 + evidence) =
      _root_.GD.N0232.N0720.N1203.d001931 budget
        (_root_.GD.N0232.N0720.N1203.d001927 probabilityWeight scale likelihood omega)
        (_root_.GD.N0232.N0720.N1203.d001928 probabilityWeight scale location likelihood omega)
        target := by
  dsimp only
  have hnormalized := _root_.GD.N0232.N0720.N1203.d001922
    probabilityWeight scale hbudget hscale
  simpa [hnormalized] using
    _root_.GD.N0232.N0720.N1203.d001933
      (_root_.GD.N0232.N0720.N1203.d001919 probabilityWeight scale budget)
      scale location likelihood hbudget hscale omega




def d001935 (S q J : ℝ) : ℝ :=
  S * _root_.GD.N0232.N0720.N1203.d001905 q / 2 +
    (3 / (4 * Real.pi)) * S * _root_.GD.N0232.N0720.N1203.d001905 q ^ 2 * J



def d001936
    (weight scale fraction : I → ℝ) (J : ℝ → ℝ) : ℝ :=
  ∑ i, _root_.GD.N0232.N0720.N1203.d001907 (weight i) (scale i) (fraction i) *
    (J (fraction i) + J (1 - fraction i))




theorem d001937
    (weight scale fraction : I → ℝ) (J : ℝ → ℝ)
    (hJ : ∀ q, J (1 - q) = J q) :
    (∑ i, weight i * _root_.GD.N0232.N0720.N1203.d001935 (scale i) (fraction i) (J (fraction i))) =
      (∑ i, weight i * scale i * _root_.GD.N0232.N0720.N1203.d001905 (fraction i) / 2) +
        (3 / (32 * Real.pi)) *
          _root_.GD.N0232.N0720.N1203.d001936 weight scale fraction J := by
  simp only [_root_.GD.N0232.N0720.N1203.d001935, _root_.GD.N0232.N0720.N1203.d001936, _root_.GD.N0232.N0720.N1203.d001907, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hJ]
    ring

end

end N1203
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1203.d001912
#print axioms _root_.GD.N0232.N0720.N1203.d001915
#print axioms _root_.GD.N0232.N0720.N1203.d001918
#print axioms _root_.GD.N0232.N0720.N1203.d001924
#print axioms _root_.GD.N0232.N0720.N1203.d001922
#print axioms _root_.GD.N0232.N0720.N1203.d001929
#print axioms _root_.GD.N0232.N0720.N1203.d001933
#print axioms _root_.GD.N0232.N0720.N1203.d001934
#print axioms _root_.GD.N0232.N0720.N1203.d001937
