import GD.Module0998

























open Filter Set Topology
open scoped BigOperators

namespace GD
namespace N0230
namespace N0620

noncomputable section

open RealInnerProductSpace
open _root_.GD.N0230.N0621

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



def d015831
    (center : ι → E) (weight : ι → ℝ) : E :=
  (1 + _root_.GD.N0230.N0621.d015800 weight)⁻¹ • _root_.GD.N0230.N0621.d015801 center weight




theorem d015832
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (x : E) :
    ‖x‖ ^ 2 +
        ∑ i, weight i * (‖x - center i‖ ^ 2 - radiusSq i) =
      _root_.GD.N0230.N0621.d015803 center radiusSq weight +
        (1 + _root_.GD.N0230.N0621.d015800 weight) *
          ‖x - _root_.GD.N0230.N0620.d015831 center weight‖ ^ 2 := by
  let alpha := 1 + _root_.GD.N0230.N0621.d015800 weight
  let moment := _root_.GD.N0230.N0621.d015801 center weight
  let constant := _root_.GD.N0230.N0621.d015802 center radiusSq weight
  have halpha : 0 < alpha := _root_.GD.N0230.N0621.d015804 hweight
  rw [_root_.GD.N0230.N0621.d015805]
  unfold _root_.GD.N0230.N0621.d015803 _root_.GD.N0230.N0620.d015831
  change alpha * ‖x‖ ^ 2 - 2 * ⟪x, moment⟫ + constant =
    constant - ‖moment‖ ^ 2 / alpha +
      alpha * ‖x - alpha⁻¹ • moment‖ ^ 2
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_right,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr halpha)]
  field_simp [halpha.ne']
  ring



theorem d015833
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    {q : E} (hq : _root_.GD.N0230.N0621.d015799 center radiusSq q) :
    _root_.GD.N0230.N0621.d015796
        (fun i x ↦ ‖x - center i‖ ^ 2) radiusSq weight q ≤ 0 := by
  unfold _root_.GD.N0230.N0621.d015796
  apply Finset.sum_nonpos
  intro i hi
  exact mul_nonpos_of_nonneg_of_nonpos
    (hweight i) (sub_nonpos.mpr (hq i))






theorem d015834
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (q : E) (U : ℝ) :
    U - _root_.GD.N0230.N0621.d015803 center radiusSq weight =
      (U - ‖q‖ ^ 2) +
        (-_root_.GD.N0230.N0621.d015796
          (fun i x ↦ ‖x - center i‖ ^ 2) radiusSq weight q) +
        (1 + _root_.GD.N0230.N0621.d015800 weight) *
          ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ ^ 2 := by
  have hidentity :=
    _root_.GD.N0230.N0620.d015832
      center radiusSq weight hweight q
  unfold _root_.GD.N0230.N0621.d015796
  linarith




theorem d015835
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    {q : E} (hq : _root_.GD.N0230.N0621.d015799 center radiusSq q) :
    _root_.GD.N0230.N0621.d015803 center radiusSq weight +
        (1 + _root_.GD.N0230.N0621.d015800 weight) *
      ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ ^ 2 ≤
      ‖q‖ ^ 2 := by
  have hpenalty := _root_.GD.N0230.N0620.d015833
    center radiusSq weight hweight hq
  rw [← _root_.GD.N0230.N0620.d015832
    center radiusSq weight hweight q]
  unfold _root_.GD.N0230.N0621.d015796 at hpenalty
  linarith



theorem d015836
    {weight : ι → ℝ} (hweight : ∀ i, 0 ≤ weight i) :
    1 ≤ 1 + _root_.GD.N0230.N0621.d015800 weight := by
  have hmass : 0 ≤ _root_.GD.N0230.N0621.d015800 weight := by
    unfold _root_.GD.N0230.N0621.d015800
    exact Finset.sum_nonneg fun i hi ↦ hweight i
  linarith



theorem d015837
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    {q : E} (hq : _root_.GD.N0230.N0621.d015799 center radiusSq q)
    {U : ℝ} (hupper : ‖q‖ ^ 2 ≤ U) :
    (1 + _root_.GD.N0230.N0621.d015800 weight) *
        ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ ^ 2 ≤
      U - _root_.GD.N0230.N0621.d015803 center radiusSq weight := by
  have hgrowth := _root_.GD.N0230.N0620.d015835
    center radiusSq weight hweight hq
  linarith




theorem d015838
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    {q : E} (hq : _root_.GD.N0230.N0621.d015799 center radiusSq q)
    {U : ℝ} (hupper : ‖q‖ ^ 2 ≤ U) :
    ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ ^ 2 ≤
      U - _root_.GD.N0230.N0621.d015803 center radiusSq weight := by
  have hstrong := _root_.GD.N0230.N0620.d015835
    center radiusSq weight hweight hq
  have halpha := _root_.GD.N0230.N0620.d015836 hweight
  have hsqNonneg :
      0 ≤ ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ ^ 2 :=
    sq_nonneg _
  have hcoefficient :
      ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ ^ 2 ≤
        (1 + _root_.GD.N0230.N0621.d015800 weight) *
          ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ ^ 2 := by
    nlinarith
  linarith




theorem d015839
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    {q : E} (hq : _root_.GD.N0230.N0621.d015799 center radiusSq q)
    {U : ℝ} (hupper : ‖q‖ ^ 2 ≤ U) :
    ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ ≤
      Real.sqrt (U - _root_.GD.N0230.N0621.d015803 center radiusSq weight) := by
  have hsq := _root_.GD.N0230.N0620.d015838
    center radiusSq weight hweight hq hupper
  have hgapNonneg :
      0 ≤ U - _root_.GD.N0230.N0621.d015803 center radiusSq weight :=
    (sq_nonneg _).trans hsq
  rw [← Real.sqrt_sq (norm_nonneg _), Real.sqrt_le_sqrt_iff hgapNonneg]
  exact hsq



def d015840
    (center : ι → E) (radiusSq weight : ι → ℝ) (q : E) : Prop :=
  ∀ i, weight i * (‖q - center i‖ ^ 2 - radiusSq i) = 0



theorem d015841
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    {q : E} (hq : _root_.GD.N0230.N0621.d015799 center radiusSq q) :
    _root_.GD.N0230.N0621.d015796
        (fun i x ↦ ‖x - center i‖ ^ 2) radiusSq weight q = 0 ↔
      _root_.GD.N0230.N0620.d015840 center radiusSq weight q := by
  constructor
  · intro hsum
    have htermNonnegative : ∀ i ∈ (Finset.univ : Finset ι),
        0 ≤ -(weight i * (‖q - center i‖ ^ 2 - radiusSq i)) := by
      intro i hi
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
        (hweight i) (sub_nonpos.mpr (hq i)))
    have hsumNeg :
        (∑ i, -(weight i * (‖q - center i‖ ^ 2 - radiusSq i))) = 0 := by
      rw [Finset.sum_neg_distrib]
      unfold _root_.GD.N0230.N0621.d015796 at hsum
      rw [hsum]
      simp
    have hall :=
      (Finset.sum_eq_zero_iff_of_nonneg htermNonnegative).mp hsumNeg
    intro i
    have hi := hall i (Finset.mem_univ i)
    linarith
  · intro hall
    unfold _root_.GD.N0230.N0621.d015796
    exact Finset.sum_eq_zero fun i hi ↦ hall i





theorem d015842
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    {q : E} (hq : _root_.GD.N0230.N0621.d015799 center radiusSq q)
    {U : ℝ} (hupper : ‖q‖ ^ 2 ≤ U) :
    U - _root_.GD.N0230.N0621.d015803 center radiusSq weight = 0 ↔
      U = ‖q‖ ^ 2 ∧
        _root_.GD.N0230.N0621.d015796
          (fun i x ↦ ‖x - center i‖ ^ 2) radiusSq weight q = 0 ∧
        q = _root_.GD.N0230.N0620.d015831 center weight := by
  constructor
  · intro hgap
    have hupperTax : 0 ≤ U - ‖q‖ ^ 2 := sub_nonneg.mpr hupper
    have hpenalty := _root_.GD.N0230.N0620.d015833
      center radiusSq weight hweight hq
    have halpha := _root_.GD.N0230.N0621.d015804 hweight
    have hdistanceSq :
        0 ≤ ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ ^ 2 :=
      sq_nonneg _
    have hdistanceTax :
        0 ≤ (1 + _root_.GD.N0230.N0621.d015800 weight) *
          ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ ^ 2 :=
      mul_nonneg (le_of_lt halpha) hdistanceSq
    have hdecomposition := _root_.GD.N0230.N0620.d015834
      center radiusSq weight hweight q U
    have hupperZero : U - ‖q‖ ^ 2 = 0 := by nlinarith
    have hpenaltyZero :
        _root_.GD.N0230.N0621.d015796
          (fun i x ↦ ‖x - center i‖ ^ 2) radiusSq weight q = 0 := by
      nlinarith
    have hdistanceZero :
        ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ ^ 2 = 0 := by
      nlinarith
    have hnormZero :
        ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ = 0 := by
      nlinarith [norm_nonneg
        (q - _root_.GD.N0230.N0620.d015831 center weight)]
    exact ⟨by linarith, hpenaltyZero,
      sub_eq_zero.mp (norm_eq_zero.mp hnormZero)⟩
  · rintro ⟨hupperEq, hpenaltyZero, hcompletion⟩
    have hdecomposition := _root_.GD.N0230.N0620.d015834
      center radiusSq weight hweight q U
    have hdistanceZero :
        ‖q - _root_.GD.N0230.N0620.d015831 center weight‖ ^ 2 = 0 := by
      simp [hcompletion]
    rw [hupperEq, sub_self, hpenaltyZero, neg_zero, zero_add,
      hdistanceZero, mul_zero] at hdecomposition
    simpa [hupperEq] using hdecomposition


theorem d015843
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    {q : E} (hq : _root_.GD.N0230.N0621.d015799 center radiusSq q)
    {U : ℝ} (hupper : ‖q‖ ^ 2 ≤ U) :
    U - _root_.GD.N0230.N0621.d015803 center radiusSq weight = 0 ↔
      U = ‖q‖ ^ 2 ∧
        _root_.GD.N0230.N0620.d015840 center radiusSq weight q ∧
        q = _root_.GD.N0230.N0620.d015831 center weight := by
  rw [_root_.GD.N0230.N0620.d015842
    center radiusSq weight hweight hq hupper]
  constructor
  · rintro ⟨hupperEq, hpenaltyZero, hcompletion⟩
    exact ⟨hupperEq,
      (_root_.GD.N0230.N0620.d015841
        center radiusSq weight hweight hq).mp hpenaltyZero,
      hcompletion⟩
  · rintro ⟨hupperEq, hcomplementarity, hcompletion⟩
    exact ⟨hupperEq,
      (_root_.GD.N0230.N0620.d015841
        center radiusSq weight hweight hq).mpr hcomplementarity,
      hcompletion⟩




def d015844 (r : E) : Fin 1 → E :=
  fun _ ↦ (2 : ℝ) • r



def d015845 (q r : E) : Fin 1 → ℝ :=
  fun _ ↦ ‖q - (2 : ℝ) • r‖ ^ 2


def d015846 : Fin 1 → ℝ := fun _ ↦ 1


theorem d015847 :
    ∀ i, 0 ≤ _root_.GD.N0230.N0620.d015846 i := by
  intro i
  simp [_root_.GD.N0230.N0620.d015846]


theorem d015848 (q r : E) :
    _root_.GD.N0230.N0621.d015799
      (_root_.GD.N0230.N0620.d015844 r) (_root_.GD.N0230.N0620.d015845 q r) q := by
  intro i
  simp [_root_.GD.N0230.N0620.d015844, _root_.GD.N0230.N0620.d015845]



theorem d015849 (r : E) :
    _root_.GD.N0230.N0620.d015831
      (_root_.GD.N0230.N0620.d015844 r) _root_.GD.N0230.N0620.d015846 = r := by
  simp [_root_.GD.N0230.N0620.d015831, _root_.GD.N0230.N0620.d015844,
    _root_.GD.N0230.N0620.d015846, _root_.GD.N0230.N0621.d015800, _root_.GD.N0230.N0621.d015801, smul_smul]
  norm_num





theorem d015850 (q r : E) :
    _root_.GD.N0230.N0621.d015803
        (_root_.GD.N0230.N0620.d015844 r) (_root_.GD.N0230.N0620.d015845 q r)
        _root_.GD.N0230.N0620.d015846 =
      ‖q‖ ^ 2 - 2 * ‖q - r‖ ^ 2 := by
  have hidentity :=
    _root_.GD.N0230.N0620.d015832
      (_root_.GD.N0230.N0620.d015844 r) (_root_.GD.N0230.N0620.d015845 q r)
      _root_.GD.N0230.N0620.d015846 _root_.GD.N0230.N0620.d015847 q
  rw [_root_.GD.N0230.N0620.d015849] at hidentity
  simp [_root_.GD.N0230.N0620.d015844, _root_.GD.N0230.N0620.d015845,
    _root_.GD.N0230.N0620.d015846, _root_.GD.N0230.N0621.d015800] at hidentity
  linarith




theorem d015851 (q : E) :
    _root_.GD.N0230.N0620.d015831
        (_root_.GD.N0230.N0620.d015844 q) _root_.GD.N0230.N0620.d015846 = q ∧
      _root_.GD.N0230.N0621.d015803
          (_root_.GD.N0230.N0620.d015844 q) (_root_.GD.N0230.N0620.d015845 q q)
          _root_.GD.N0230.N0620.d015846 = ‖q‖ ^ 2 := by
  constructor
  · exact _root_.GD.N0230.N0620.d015849 q
  · simpa using _root_.GD.N0230.N0620.d015850 q q

end
end N0620
end N0230

namespace N0232
namespace N0720
namespace N1138

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0621
open _root_.GD.N0230.N0620
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1099
open _root_.GD.N0232.N0720.N1200
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1204
open _root_.GD.N0232.N0720.N1194

variable (m n : ℕ)













theorem d015852
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (alpha ell upper : ℕ → ℝ)
    (halpha : ∀ j, 1 ≤ alpha j)
    (hstrong : ∀ j,
      ell j + alpha j *
          ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value - r j‖ ^ 2 ≤
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖ ^ 2)
    (hupper : ∀ j,
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖ ^ 2 ≤ upper j)
    (hgap : Tendsto (fun j ↦ upper j - ell j) atTop (nhds 0))
    (hfixedTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hfixedThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let q : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := fun j ↦
    _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value
  have hcloseSq : ∀ j, ‖q j - r j‖ ^ 2 ≤ upper j - ell j := by
    intro j
    have hsqNonneg : 0 ≤ ‖q j - r j‖ ^ 2 := sq_nonneg _
    have hcoefficient :
        ‖q j - r j‖ ^ 2 ≤ alpha j * ‖q j - r j‖ ^ 2 := by
      nlinarith [halpha j]
    dsimp only [q]
    linarith [hstrong j, hupper j]
  have hcloseSqZero : Tendsto (fun j ↦ ‖q j - r j‖ ^ 2)
      atTop (nhds 0) := by
    exact squeeze_zero (fun j ↦ sq_nonneg _) hcloseSq hgap
  have hclose : Tendsto (fun j ↦ ‖q j - r j‖)
      atTop (nhds 0) := by
    have hsqrt := hcloseSqZero.sqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  exact _root_.GD.N0232.N0720.N1204.d015788
    m n hm hn seed hdesc hstrict r hclose hfixedTwo hfixedThree


















theorem d015853
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (center : ℕ → ι → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (radiusSq weight : ℕ → ι → ℝ)
    (upper : ℕ → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hfeasible : ∀ j,
      _root_.GD.N0230.N0621.d015799 (center j) (radiusSq j)
        (_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value))
    (hupper : ∀ j,
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖ ^ 2 ≤ upper j)
    (hgap : Tendsto
      (fun j ↦ upper j -
        _root_.GD.N0230.N0621.d015803 (center j) (radiusSq j) (weight j))
      atTop (nhds 0))
    (hfixedTwo : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n
            (_root_.GD.N0230.N0620.d015831 (center j) (weight j)) -
          _root_.GD.N0230.N0620.d015831 (center j) (weight j)‖)
      atTop (nhds 0))
    (hfixedThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n
            (_root_.GD.N0230.N0620.d015831 (center j) (weight j)) -
          _root_.GD.N0230.N0620.d015831 (center j) (weight j)‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := fun j ↦
    _root_.GD.N0230.N0620.d015831 (center j) (weight j)
  let alpha : ℕ → ℝ := fun j ↦ 1 + _root_.GD.N0230.N0621.d015800 (weight j)
  let ell : ℕ → ℝ := fun j ↦
    _root_.GD.N0230.N0621.d015803 (center j) (radiusSq j) (weight j)
  apply _root_.GD.N0232.N0720.N1138.d015852
    m n hm hn seed hdesc hstrict r alpha ell upper
  · intro j
    exact _root_.GD.N0230.N0620.d015836 (hweight j)
  · intro j
    exact _root_.GD.N0230.N0620.d015835
      (center j) (radiusSq j) (weight j) (hweight j) (hfeasible j)
  · exact hupper
  · exact hgap
  · exact hfixedTwo
  · exact hfixedThree






theorem d015854
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (center : ℕ → ι → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (radiusSq weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hballsContainCone : ∀ j q,
      q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n (seed j).value →
        _root_.GD.N0230.N0621.d015799 (center j) (radiusSq j) q)
    (hgap : Tendsto
      (fun j ↦ ‖(seed j).value‖ ^ 2 -
        _root_.GD.N0230.N0621.d015803 (center j) (radiusSq j) (weight j))
      atTop (nhds 0))
    (hfixedTwo : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n
            (_root_.GD.N0230.N0620.d015831 (center j) (weight j)) -
          _root_.GD.N0230.N0620.d015831 (center j) (weight j)‖)
      atTop (nhds 0))
    (hfixedThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n
            (_root_.GD.N0230.N0620.d015831 (center j) (weight j)) -
          _root_.GD.N0230.N0620.d015831 (center j) (weight j)‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1138.d015853
    m n hm hn seed hdesc hstrict center radiusSq weight
      (fun j ↦ ‖(seed j).value‖ ^ 2) hweight
  · intro j
    apply hballsContainCone j
    exact (_root_.GD.N0232.N0720.N1159.d014634 m n (seed j).value).1
  · intro j
    have hnorm := _root_.GD.N0232.N0720.N1194.d015818 m n (seed j)
    nlinarith [norm_nonneg (_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value),
      norm_nonneg (seed j).value]
  · exact hgap
  · exact hfixedTwo
  · exact hfixedThree

end
end N1138
end N0720
end N0232
end GD

#print axioms _root_.GD.N0230.N0620.d015832
#print axioms _root_.GD.N0230.N0620.d015834
#print axioms _root_.GD.N0230.N0620.d015835
#print axioms _root_.GD.N0230.N0620.d015837
#print axioms _root_.GD.N0230.N0620.d015838
#print axioms _root_.GD.N0230.N0620.d015843
#print axioms _root_.GD.N0230.N0620.d015850
#print axioms _root_.GD.N0230.N0620.d015851
#print axioms _root_.GD.N0232.N0720.N1138.d015852
#print axioms _root_.GD.N0232.N0720.N1138.d015853
#print axioms _root_.GD.N0232.N0720.N1138.d015854
