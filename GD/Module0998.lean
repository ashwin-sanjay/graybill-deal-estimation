import GD.Module0997





























open Filter Set Topology
open scoped BigOperators

namespace GD



namespace N0230
namespace N0621

noncomputable section

open RealInnerProductSpace

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def d015795
    (constraint : ι → E → ℝ) (cap : ι → ℝ) (q : E) : Prop :=
  ∀ i, constraint i q ≤ cap i


def d015796
    (constraint : ι → E → ℝ) (cap weight : ι → ℝ) (q : E) : ℝ :=
  ∑ i, weight i * (constraint i q - cap i)


def d015797
    (constraint : ι → E → ℝ) (cap weight : ι → ℝ)
    (ell : ℝ) : Prop :=
  (∀ i, 0 ≤ weight i) ∧
    ∀ x : E,
      ell ≤ ‖x‖ ^ 2 + _root_.GD.N0230.N0621.d015796 constraint cap weight x




theorem d015798
    {constraint : ι → E → ℝ} {cap weight : ι → ℝ} {ell : ℝ}
    (hcertificate :
      _root_.GD.N0230.N0621.d015797 constraint cap weight ell)
    {q : E} (hq : _root_.GD.N0230.N0621.d015795 constraint cap q) :
    ell ≤ ‖q‖ ^ 2 := by
  have hpenalty : _root_.GD.N0230.N0621.d015796 constraint cap weight q ≤ 0 := by
    unfold _root_.GD.N0230.N0621.d015796
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos
      (hcertificate.1 i) (sub_nonpos.mpr (hq i))
  exact (hcertificate.2 q).trans (by linarith)




def d015799
    (center : ι → E) (radiusSq : ι → ℝ) (q : E) : Prop :=
  ∀ i, ‖q - center i‖ ^ 2 ≤ radiusSq i


def d015800 (weight : ι → ℝ) : ℝ :=
  ∑ i, weight i


def d015801 (center : ι → E) (weight : ι → ℝ) : E :=
  ∑ i, weight i • center i


def d015802
    (center : ι → E) (radiusSq weight : ι → ℝ) : ℝ :=
  ∑ i, weight i * (‖center i‖ ^ 2 - radiusSq i)


def d015803
    (center : ι → E) (radiusSq weight : ι → ℝ) : ℝ :=
  _root_.GD.N0230.N0621.d015802 center radiusSq weight -
    ‖_root_.GD.N0230.N0621.d015801 center weight‖ ^ 2 / (1 + _root_.GD.N0230.N0621.d015800 weight)


theorem d015804
    {weight : ι → ℝ} (hweight : ∀ i, 0 ≤ weight i) :
    0 < 1 + _root_.GD.N0230.N0621.d015800 weight := by
  have hmass : 0 ≤ _root_.GD.N0230.N0621.d015800 weight := by
    unfold _root_.GD.N0230.N0621.d015800
    exact Finset.sum_nonneg fun i hi ↦ hweight i
  linarith



theorem d015805
    (center : ι → E) (radiusSq weight : ι → ℝ) (x : E) :
    ‖x‖ ^ 2 +
        ∑ i, weight i * (‖x - center i‖ ^ 2 - radiusSq i) =
      (1 + _root_.GD.N0230.N0621.d015800 weight) * ‖x‖ ^ 2 -
        2 * ⟪x, _root_.GD.N0230.N0621.d015801 center weight⟫ +
          _root_.GD.N0230.N0621.d015802 center radiusSq weight := by
  unfold _root_.GD.N0230.N0621.d015800 _root_.GD.N0230.N0621.d015801 _root_.GD.N0230.N0621.d015802
  rw [inner_sum]
  simp_rw [real_inner_smul_right]
  have hsum :
      (∑ i, weight i * (‖x - center i‖ ^ 2 - radiusSq i)) =
        ∑ i, (weight i * ‖x‖ ^ 2 -
          2 * (weight i * ⟪x, center i⟫) +
            weight i * (‖center i‖ ^ 2 - radiusSq i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [norm_sub_sq_real]
    ring
  rw [hsum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring


theorem d015806
    {alpha : ℝ} (halpha : 0 < alpha) (x moment : E) :
    -( ‖moment‖ ^ 2 / alpha) ≤
      alpha * ‖x‖ ^ 2 - 2 * ⟪x, moment⟫ := by
  have hinner : ⟪x, moment⟫ ≤ ‖x‖ * ‖moment‖ :=
    real_inner_le_norm x moment
  have hidentity :
      alpha *
          (alpha * ‖x‖ ^ 2 - 2 * ‖x‖ * ‖moment‖ +
            ‖moment‖ ^ 2 / alpha) =
        (alpha * ‖x‖ - ‖moment‖) ^ 2 := by
    field_simp [halpha.ne']
    ring
  have hproduct : 0 ≤
      alpha *
        (alpha * ‖x‖ ^ 2 - 2 * ‖x‖ * ‖moment‖ +
          ‖moment‖ ^ 2 / alpha) := by
    rw [hidentity]
    exact sq_nonneg _
  have hquadratic : 0 ≤
      alpha * ‖x‖ ^ 2 - 2 * ‖x‖ * ‖moment‖ +
        ‖moment‖ ^ 2 / alpha := by
    by_contra hnot
    have hneg := mul_neg_of_pos_of_neg halpha (lt_of_not_ge hnot)
    exact (not_lt_of_ge hproduct) hneg
  nlinarith



theorem d015807
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (x : E) :
    _root_.GD.N0230.N0621.d015803 center radiusSq weight ≤
      ‖x‖ ^ 2 +
        ∑ i, weight i * (‖x - center i‖ ^ 2 - radiusSq i) := by
  let alpha := 1 + _root_.GD.N0230.N0621.d015800 weight
  let moment := _root_.GD.N0230.N0621.d015801 center weight
  let constant := _root_.GD.N0230.N0621.d015802 center radiusSq weight
  have halpha : 0 < alpha := _root_.GD.N0230.N0621.d015804 hweight
  have hlower := _root_.GD.N0230.N0621.d015806 halpha x moment
  rw [_root_.GD.N0230.N0621.d015805]
  unfold _root_.GD.N0230.N0621.d015803
  change constant - ‖moment‖ ^ 2 / alpha ≤
    alpha * ‖x‖ ^ 2 - 2 * ⟪x, moment⟫ + constant
  linarith



theorem d015808
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0230.N0621.d015797
      (fun i x ↦ ‖x - center i‖ ^ 2) radiusSq weight
      (_root_.GD.N0230.N0621.d015803 center radiusSq weight) := by
  refine ⟨hweight, ?_⟩
  intro x
  simpa only [_root_.GD.N0230.N0621.d015796] using
    _root_.GD.N0230.N0621.d015807
      center radiusSq weight hweight x



theorem d015809
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0230.N0621.d015803 center radiusSq weight =
      ‖(1 + _root_.GD.N0230.N0621.d015800 weight)⁻¹ • _root_.GD.N0230.N0621.d015801 center weight‖ ^ 2 +
        ∑ i, weight i *
          (‖(1 + _root_.GD.N0230.N0621.d015800 weight)⁻¹ •
                _root_.GD.N0230.N0621.d015801 center weight - center i‖ ^ 2 -
            radiusSq i) := by
  let alpha := 1 + _root_.GD.N0230.N0621.d015800 weight
  let moment := _root_.GD.N0230.N0621.d015801 center weight
  have halpha : 0 < alpha := _root_.GD.N0230.N0621.d015804 hweight
  rw [_root_.GD.N0230.N0621.d015805]
  unfold _root_.GD.N0230.N0621.d015803
  change _root_.GD.N0230.N0621.d015802 center radiusSq weight - ‖moment‖ ^ 2 / alpha =
    alpha * ‖alpha⁻¹ • moment‖ ^ 2 -
      2 * ⟪alpha⁻¹ • moment, moment⟫ +
        _root_.GD.N0230.N0621.d015802 center radiusSq weight
  rw [norm_smul, real_inner_smul_left, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr halpha), real_inner_self_eq_norm_sq]
  field_simp [halpha.ne']
  ring



theorem d015810
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    IsLeast
      (Set.range (fun x : E ↦
        ‖x‖ ^ 2 +
          ∑ i, weight i * (‖x - center i‖ ^ 2 - radiusSq i)))
      (_root_.GD.N0230.N0621.d015803 center radiusSq weight) := by
  constructor
  · refine ⟨(1 + _root_.GD.N0230.N0621.d015800 weight)⁻¹ •
        _root_.GD.N0230.N0621.d015801 center weight, ?_⟩
    exact
      (_root_.GD.N0230.N0621.d015809
        center radiusSq weight hweight).symm
  · rintro _ ⟨x, rfl⟩
    exact _root_.GD.N0230.N0621.d015807
      center radiusSq weight hweight x




theorem d015811
    (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    {q : E} (hq : _root_.GD.N0230.N0621.d015799 center radiusSq q) :
    _root_.GD.N0230.N0621.d015803 center radiusSq weight ≤ ‖q‖ ^ 2 := by
  have hpenalty :
      (∑ i, weight i * (‖q - center i‖ ^ 2 - radiusSq i)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos
      (hweight i) (sub_nonpos.mpr (hq i))
  exact (_root_.GD.N0230.N0621.d015807
    center radiusSq weight hweight q).trans (by linarith)



theorem d015812
    (C : Set E) (center : ι → E) (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hballs : ∀ q ∈ C, _root_.GD.N0230.N0621.d015799 center radiusSq q) :
    ∀ q ∈ C,
      _root_.GD.N0230.N0621.d015803 center radiusSq weight ≤ ‖q‖ ^ 2 := by
  intro q hq
  exact _root_.GD.N0230.N0621.d015811
    center radiusSq weight hweight (hballs q hq)

end
end N0621
end N0230



namespace N0232
namespace N0720
namespace N1194

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0621
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1099
open _root_.GD.N0232.N0720.N1161
open _root_.GD.N0232.N0720.N1160
open _root_.GD.N0232.N0720.N1200
open _root_.GD.N0232.N0720.N1204
open _root_.GD.N0232.N0720.N1205
open _root_.GD.N0232.N0720.N1146

variable (m n : ℕ)




def d015813
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (ell : ℝ) : Prop :=
  ∀ q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value, ell ≤ ‖q‖ ^ 2



theorem d015814
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) {ell : ℝ}
    (hlower : _root_.GD.N0232.N0720.N1194.d015813 m n s ell) :
    ell ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  exact hlower _ (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1





theorem d015815
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (constraint : ι → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) → ℝ)
    (cap weight : ι → ℝ) (ell : ℝ)
    (hcertificate :
      _root_.GD.N0230.N0621.d015797 constraint cap weight ell)
    (hfeasible : ∀ q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value,
      _root_.GD.N0230.N0621.d015795 constraint cap q) :
    _root_.GD.N0232.N0720.N1194.d015813 m n s ell := by
  intro q hq
  exact _root_.GD.N0230.N0621.d015798
    hcertificate (hfeasible q hq)



theorem d015816
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (center : ι → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (radiusSq weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hballs : ∀ q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value,
      _root_.GD.N0230.N0621.d015799 center radiusSq q) :
    _root_.GD.N0232.N0720.N1194.d015813 m n s
      (_root_.GD.N0230.N0621.d015803 center radiusSq weight) := by
  exact _root_.GD.N0230.N0621.d015812
    (_root_.GD.N0232.N0720.N1159.d014630 m n s.value) center radiusSq weight hweight hballs






theorem d015817
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (ell epsilon delta : ℕ → ℝ)
    (hlower : ∀ j, _root_.GD.N0232.N0720.N1194.d015813 m n (seed j) (ell j))
    (hradiusTax : ∀ j, ‖r j‖ ^ 2 - ell j ≤ epsilon j)
    (hdeltaNonneg : ∀ j, 0 ≤ delta j)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hdelta : Tendsto delta atTop (nhds 0))
    (hnear : ∀ j,
      Metric.infDist (r j) (_root_.GD.N0232.N0720.N1159.d014630 m n (seed (j + 1)).value) ≤
        delta j)
    (hfixedTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hfixedThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have hradial : ∀ j, ‖r j‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖ ^ 2 + epsilon j := by
    intro j
    have hcert := _root_.GD.N0232.N0720.N1194.d015814
      m n (seed j) (hlower j)
    linarith [hradiusTax j]
  exact _root_.GD.N0232.N0720.N1204.d015791
    m n hm hn seed hdesc hstrict r epsilon delta hdeltaNonneg
      hepsilon hdelta hnear hradial hfixedTwo hfixedThree





theorem d015818
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ≤ ‖s.value‖ := by
  have href := (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.2 s.value
    (_root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value)
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  have hsq : ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      ‖s.value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖s.value‖)).mp href
  nlinarith [norm_nonneg (_root_.GD.N0232.N0720.N1159.d014633 m n s.value),
    norm_nonneg s.value]



noncomputable def d015819
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (B epsilon delta : ℝ)
    (r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  ((_root_.GD.N0232.N0720.N1146.d015213 m n certificate + 1) *
      _root_.GD.N0232.N0720.N1204.d015789 B epsilon delta +
    ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate r - r‖) ^ 2


noncomputable def d015820
    (B epsilon delta : ℝ)
    (r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  _root_.GD.N0232.N0720.N1194.d015819 m n
      (_root_.GD.N0232.N0720.N1146.d015221 m n) B epsilon delta r +
    _root_.GD.N0232.N0720.N1194.d015819 m n
      (_root_.GD.N0232.N0720.N1146.d015222 m n)
      B epsilon delta r



theorem d015821
    (s t : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value t.value)
    (r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    {ell epsilon delta : ℝ}
    (hlower : _root_.GD.N0232.N0720.N1194.d015813 m n s ell)
    (hradiusTax : ‖r‖ ^ 2 - ell ≤ epsilon)
    (hdelta : 0 ≤ delta)
    (hnear : Metric.infDist r (_root_.GD.N0232.N0720.N1159.d014630 m n t.value) ≤ delta) :
    _root_.GD.N0232.N0720.N1204.d015779 m n
        (_root_.GD.N0232.N0720.N1159.d014633 m n t.value) r ≤
      _root_.GD.N0232.N0720.N1194.d015820 m n ‖s.value‖ epsilon delta r := by
  have hell := _root_.GD.N0232.N0720.N1194.d015814
    m n s hlower
  have hradial : ‖r‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + epsilon := by
    linarith
  have hclose : ‖_root_.GD.N0232.N0720.N1159.d014633 m n t.value - r‖ ≤
      _root_.GD.N0232.N0720.N1204.d015789 ‖s.value‖ epsilon delta := by
    exact _root_.GD.N0232.N0720.N1205.d015507 m n s t hdesc r
      hnear hdelta (_root_.GD.N0232.N0720.N1194.d015818 m n s) hradial
  have hrepairNonneg : 0 ≤ _root_.GD.N0232.N0720.N1204.d015789 ‖s.value‖ epsilon delta :=
    (norm_nonneg _).trans hclose
  have htwo :
      _root_.GD.N0232.N0720.N1204.d015774 m n
          (_root_.GD.N0232.N0720.N1146.d015221 m n)
          (_root_.GD.N0232.N0720.N1159.d014633 m n t.value) r ≤
        (_root_.GD.N0232.N0720.N1146.d015213 m n
              (_root_.GD.N0232.N0720.N1146.d015221 m n) + 1) *
            _root_.GD.N0232.N0720.N1204.d015789 ‖s.value‖ epsilon delta +
          ‖_root_.GD.N0232.N0720.N1146.d015228 m n r - r‖ := by
    unfold _root_.GD.N0232.N0720.N1204.d015774 _root_.GD.N0232.N0720.N1146.d015228
    exact add_le_add
      (mul_le_mul_of_nonneg_left hclose
        (add_nonneg
          (_root_.GD.N0232.N0720.N1146.d015214 m n
            (_root_.GD.N0232.N0720.N1146.d015221 m n)) zero_le_one))
      (le_refl _)
  have hthree :
      _root_.GD.N0232.N0720.N1204.d015774 m n
          (_root_.GD.N0232.N0720.N1146.d015222 m n)
          (_root_.GD.N0232.N0720.N1159.d014633 m n t.value) r ≤
        (_root_.GD.N0232.N0720.N1146.d015213 m n
              (_root_.GD.N0232.N0720.N1146.d015222 m n) + 1) *
            _root_.GD.N0232.N0720.N1204.d015789 ‖s.value‖ epsilon delta +
          ‖_root_.GD.N0232.N0720.N1146.d015229 m n r - r‖ := by
    unfold _root_.GD.N0232.N0720.N1204.d015774 _root_.GD.N0232.N0720.N1146.d015229
    exact add_le_add
      (mul_le_mul_of_nonneg_left hclose
        (add_nonneg
          (_root_.GD.N0232.N0720.N1146.d015214 m n
            (_root_.GD.N0232.N0720.N1146.d015222 m n)) zero_le_one))
      (le_refl _)
  have htwoRightNonneg : 0 ≤
      (_root_.GD.N0232.N0720.N1146.d015213 m n
            (_root_.GD.N0232.N0720.N1146.d015221 m n) + 1) *
          _root_.GD.N0232.N0720.N1204.d015789 ‖s.value‖ epsilon delta +
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n r - r‖ := by
    exact add_nonneg
      (mul_nonneg
        (add_nonneg
          (_root_.GD.N0232.N0720.N1146.d015214 m n
            (_root_.GD.N0232.N0720.N1146.d015221 m n)) zero_le_one)
        hrepairNonneg)
      (norm_nonneg _)
  have hthreeRightNonneg : 0 ≤
      (_root_.GD.N0232.N0720.N1146.d015213 m n
            (_root_.GD.N0232.N0720.N1146.d015222 m n) + 1) *
          _root_.GD.N0232.N0720.N1204.d015789 ‖s.value‖ epsilon delta +
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n r - r‖ := by
    exact add_nonneg
      (mul_nonneg
        (add_nonneg
          (_root_.GD.N0232.N0720.N1146.d015214 m n
            (_root_.GD.N0232.N0720.N1146.d015222 m n)) zero_le_one)
        hrepairNonneg)
      (norm_nonneg _)
  have htwoSq :=
    (sq_le_sq₀
      (_root_.GD.N0232.N0720.N1204.d015775 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) _ _)
      htwoRightNonneg).2 htwo
  have hthreeSq :=
    (sq_le_sq₀
      (_root_.GD.N0232.N0720.N1204.d015775 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) _ _)
      hthreeRightNonneg).2 hthree
  unfold _root_.GD.N0232.N0720.N1204.d015779 _root_.GD.N0232.N0720.N1194.d015820
    _root_.GD.N0232.N0720.N1194.d015819
  exact add_le_add htwoSq hthreeSq






def d015822
    (hm : 2 ≤ m) (hn : 2 ≤ n) (kappa : ℝ) : Prop :=
  ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
    _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s →
      ∃ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t ∧
          ∃ (r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
              (ell epsilon delta : ℝ),
            _root_.GD.N0232.N0720.N1194.d015813 m n s ell ∧
            ‖r‖ ^ 2 - ell ≤ epsilon ∧
            0 ≤ delta ∧
            Metric.infDist r (_root_.GD.N0232.N0720.N1159.d014630 m n t.value) ≤ delta ∧
            _root_.GD.N0232.N0720.N1194.d015820 m n
                ‖s.value‖ epsilon delta r ≤
              kappa * _root_.GD.N0232.N0720.N1477.d015749 m n s





def d015823
    (hm : 2 ≤ m) (hn : 2 ≤ n) (kappa : ℝ) : Prop :=
  ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
    _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s →
      ∃ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t ∧
          ∃ r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
            _root_.GD.N0232.N0720.N1204.d015779 m n
                (_root_.GD.N0232.N0720.N1159.d014633 m n t.value) r ≤
              kappa * _root_.GD.N0232.N0720.N1477.d015749 m n s


def d015824
    (hm : 2 ≤ m) (hn : 2 ≤ n) (kappa : ℝ) : Prop :=
  ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
    _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s →
      ∃ t : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0232.N0720.N1161.d015496 m n hm hn s t ∧
          _root_.GD.N0232.N0720.N1477.d015749 m n t ≤
            kappa * _root_.GD.N0232.N0720.N1477.d015749 m n s



theorem d015825
    (hm : 2 ≤ m) (hn : 2 ≤ n) (kappa : ℝ)
    (hcertified :
      _root_.GD.N0232.N0720.N1194.d015822 m n hm hn kappa) :
    _root_.GD.N0232.N0720.N1194.d015823 m n hm hn kappa := by
  intro s hs
  obtain ⟨t, ht, r, ell, epsilon, delta,
    hlower, hradius, hdelta, hnear, hupper⟩ := hcertified s hs
  refine ⟨t, ht, r, ?_⟩
  exact (_root_.GD.N0232.N0720.N1194.d015821
    m n s t ht.2 r hlower hradius hdelta hnear).trans hupper





theorem d015826
    (hm : 2 ≤ m) (hn : 2 ≤ n) (kappa : ℝ) :
    _root_.GD.N0232.N0720.N1194.d015823 m n hm hn kappa ↔
      _root_.GD.N0232.N0720.N1194.d015824 m n hm hn kappa := by
  constructor
  · intro hcomparison s hs
    obtain ⟨t, ht, r, hr⟩ := hcomparison s hs
    refine ⟨t, ht, ?_⟩
    exact (_root_.GD.N0232.N0720.N1204.d015781 m n t r).trans hr
  · intro henergy s hs
    obtain ⟨t, ht, hcontract⟩ := henergy s hs
    refine ⟨t, ht, _root_.GD.N0232.N0720.N1159.d014633 m n t.value, ?_⟩
    rw [← _root_.GD.N0232.N0720.N1204.d015782 m n t]
    exact hcontract



theorem d015827
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {kappa : ℝ} (hkappaNonneg : 0 ≤ kappa) (hkappaLt : kappa < 1)
    (hcontract :
      _root_.GD.N0232.N0720.N1194.d015824 m n hm hn kappa)
    (s₀ : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hs₀ : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s₀) :
    ∃ seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n,
      (seed 0 = s₀) ∧
      (∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value) ∧
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1477.d015749 m n (seed j))
        atTop (nhds 0) := by
  classical
  let StrictSeed := {s : _root_.GD.N0232.N0720.N1159.d014639 m n //
    _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s}
  let start : StrictSeed := ⟨s₀, hs₀⟩
  have hnext : ∀ u : StrictSeed,
      ∃ v : StrictSeed,
        _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) u.1.value v.1.value ∧
          _root_.GD.N0232.N0720.N1477.d015749 m n v.1 ≤
            kappa * _root_.GD.N0232.N0720.N1477.d015749 m n u.1 := by
    intro u
    obtain ⟨t, ht, henergy⟩ := hcontract u.1 u.2
    exact ⟨⟨t, ht.1⟩, ht.2, henergy⟩
  let next : StrictSeed → StrictSeed := fun u ↦ Classical.choose (hnext u)
  have next_spec (u : StrictSeed) :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) u.1.value (next u).1.value ∧
        _root_.GD.N0232.N0720.N1477.d015749 m n (next u).1 ≤
          kappa * _root_.GD.N0232.N0720.N1477.d015749 m n u.1 :=
    Classical.choose_spec (hnext u)
  let chain : ℕ → StrictSeed := fun j ↦ Nat.rec start (fun _ u ↦ next u) j
  have chain_zero : (chain 0).1 = s₀ := rfl
  have chain_succ (j : ℕ) : chain (j + 1) = next (chain j) := by
    simp only [chain]
  have hdesc (j : ℕ) :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (chain j).1.value (chain (j + 1)).1.value := by
    rw [chain_succ]
    exact (next_spec (chain j)).1
  have hstep (j : ℕ) :
      _root_.GD.N0232.N0720.N1477.d015749 m n (chain (j + 1)).1 ≤
        kappa * _root_.GD.N0232.N0720.N1477.d015749 m n (chain j).1 := by
    rw [chain_succ]
    exact (next_spec (chain j)).2
  have hgeom : ∀ j,
      _root_.GD.N0232.N0720.N1477.d015749 m n (chain j).1 ≤
        kappa ^ j * _root_.GD.N0232.N0720.N1477.d015749 m n s₀ := by
    intro j
    induction j with
    | zero =>
        rw [chain_zero, pow_zero, one_mul]
    | succ j ih =>
        calc
          _root_.GD.N0232.N0720.N1477.d015749 m n (chain (j + 1)).1 ≤
              kappa * _root_.GD.N0232.N0720.N1477.d015749 m n (chain j).1 :=
            hstep j
          _ ≤ kappa *
              (kappa ^ j * _root_.GD.N0232.N0720.N1477.d015749 m n s₀) :=
            mul_le_mul_of_nonneg_left ih hkappaNonneg
          _ = kappa ^ (j + 1) *
              _root_.GD.N0232.N0720.N1477.d015749 m n s₀ := by
            rw [pow_succ]
            ring
  have hgeomTendsto : Tendsto
      (fun j ↦ kappa ^ j * _root_.GD.N0232.N0720.N1477.d015749 m n s₀)
      atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hkappaNonneg hkappaLt).mul_const
        (_root_.GD.N0232.N0720.N1477.d015749 m n s₀)
  have henergy : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1477.d015749 m n (chain j).1)
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦
        _root_.GD.N0232.N0720.N1099.d015757
          m n (chain j).1)
      hgeom hgeomTendsto
  exact ⟨fun j ↦ (chain j).1, chain_zero, hdesc, henergy⟩



theorem d015828
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {kappa : ℝ} (hkappaNonneg : 0 ≤ kappa) (hkappaLt : kappa < 1)
    (hcontract : _root_.GD.N0232.N0720.N1194.d015823 m n hm hn kappa)
    (s₀ : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hs₀ : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s₀) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have henergyContract :
      _root_.GD.N0232.N0720.N1194.d015824 m n hm hn kappa :=
    (_root_.GD.N0232.N0720.N1194.d015826
      m n hm hn kappa).1 hcontract
  obtain ⟨seed, hzero, hdesc, henergy⟩ :=
    _root_.GD.N0232.N0720.N1194.d015827
      m n hm hn hkappaNonneg hkappaLt henergyContract s₀ hs₀
  apply _root_.GD.N0232.N0720.N1099.d015762
    m n hm hn seed hdesc henergy
  rw [hzero]
  exact hs₀





theorem d015829
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {kappa : ℝ} (hkappaNonneg : 0 ≤ kappa) (hkappaLt : kappa < 1)
    (hcontract :
      _root_.GD.N0232.N0720.N1194.d015822 m n hm hn kappa)
    (s₀ : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hs₀ : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s₀) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact _root_.GD.N0232.N0720.N1194.d015828
    m n hm hn hkappaNonneg hkappaLt
      (_root_.GD.N0232.N0720.N1194.d015825
        m n hm hn kappa hcontract) s₀ hs₀



theorem d015830
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {kappa : ℝ} (hkappaNonneg : 0 ≤ kappa) (hkappaLt : kappa < 1)
    (s₀ : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hs₀ : _root_.GD.N0232.N0720.N1200.d015250 m n hm hn s₀)
    (hfailure : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n) :
    ¬ _root_.GD.N0232.N0720.N1194.d015823 m n hm hn kappa := by
  intro hcontract
  exact hfailure
    (_root_.GD.N0232.N0720.N1194.d015828
      m n hm hn hkappaNonneg hkappaLt hcontract s₀ hs₀)

end
end N1194
end N0720
end N0232
end GD

#print axioms _root_.GD.N0230.N0621.d015798
#print axioms _root_.GD.N0230.N0621.d015808
#print axioms _root_.GD.N0230.N0621.d015810
#print axioms _root_.GD.N0230.N0621.d015811
#print axioms _root_.GD.N0232.N0720.N1194.d015815
#print axioms _root_.GD.N0232.N0720.N1194.d015816
#print axioms _root_.GD.N0232.N0720.N1194.d015817
#print axioms _root_.GD.N0232.N0720.N1194.d015821
#print axioms _root_.GD.N0232.N0720.N1194.d015825
#print axioms _root_.GD.N0232.N0720.N1194.d015826
#print axioms _root_.GD.N0232.N0720.N1194.d015827
#print axioms _root_.GD.N0232.N0720.N1194.d015828
#print axioms _root_.GD.N0232.N0720.N1194.d015829
#print axioms _root_.GD.N0232.N0720.N1194.d015830
