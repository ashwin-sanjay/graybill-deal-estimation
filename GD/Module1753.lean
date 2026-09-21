import GD.Module1752

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal

namespace GD.N0225.N0535

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0842 _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0970 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0097 _root_.GD.N0226

noncomputable section

variable {k : ℕ} (sizes : Fin k → ℕ)

def d029027 (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ z, f (fun i j => c * z i j) = c * f z

def d029028 (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (t : ℝ) : Prop :=
  (fun z => f (fun i j => Real.exp t * z i j)) =ᵐ[
    _root_.GD.N0232.N0719.N0859.d010813 k sizes] fun z => Real.exp t * f z

theorem d029029
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (t : ℝ) :
    t ∈ _root_.GD.N0226.d028198 sizes f ↔ _root_.GD.N0225.N0535.d029028 sizes f t := by
  constructor
  · exact _root_.GD.N0226.d029008 sizes f
  · intro h
    have hpull := (_root_.GD.N0232.N0719.N0896.d011119
      k sizes 0 (Real.exp (-t)) (Real.exp_pos (-t))).ae_eq h
    filter_upwards [hpull] with z hz
    change f (fun i j => Real.exp t * (0 + Real.exp (-t) * z i j)) =
      Real.exp t * f (fun i j => 0 + Real.exp (-t) * z i j) at hz
    have he : Real.exp t ≠ 0 := Real.exp_ne_zero t
    simp only [zero_add, Real.exp_neg, ← mul_assoc, mul_inv_cancel₀ he, one_mul] at hz
    change 0 + Real.exp t * f (_root_.GD.N0232.N0719.N0842.d010907 k sizes 0 (Real.exp t) z) = f z
    have hinv : _root_.GD.N0232.N0719.N0842.d010907 k sizes 0 (Real.exp t) z =
        (fun i j => (Real.exp t)⁻¹ * z i j) := by
      ext i j
      change -((Real.exp t)⁻¹ * 0) + (Real.exp t)⁻¹ * z i j =
        (Real.exp t)⁻¹ * z i j
      ring
    rw [hinv, zero_add]
    exact hz.symm

private def d029030 := Multiplicative ℝ

local instance d029031 : Group _root_.GD.N0225.N0535.d029030 :=
  inferInstanceAs (Group (Multiplicative ℝ))

local instance d029032 : MeasurableSpace _root_.GD.N0225.N0535.d029030 :=
  inferInstanceAs (MeasurableSpace ℝ)

local instance d029033 : MeasurableInv _root_.GD.N0225.N0535.d029030 where
  measurable_inv := by
    change Measurable (fun t : ℝ => -t)
    fun_prop

local instance d029034 : MulAction _root_.GD.N0225.N0535.d029030 ℝ where
  smul t y := Real.exp t.toAdd * y
  one_smul y := by change Real.exp 0 * y = y; rw [Real.exp_zero, one_mul]
  mul_smul s t y := by
    change Real.exp (s.toAdd + t.toAdd) * y = Real.exp s.toAdd * (Real.exp t.toAdd * y)
    rw [Real.exp_add, mul_assoc]

local instance d029035 : MulAction _root_.GD.N0225.N0535.d029030
    (_root_.GD.N0232.N0719.N0859.d010811 k sizes) where
  smul t z := fun i j => Real.exp t.toAdd * z i j
  one_smul z := by
    ext i j
    change Real.exp 0 * z i j = z i j
    rw [Real.exp_zero, one_mul]
  mul_smul s t z := by
    ext i j
    change Real.exp (s.toAdd + t.toAdd) * z i j =
      Real.exp s.toAdd * (Real.exp t.toAdd * z i j)
    rw [Real.exp_add, mul_assoc]

local instance d029036 : MeasurableSMul₂ _root_.GD.N0225.N0535.d029030 ℝ where
  measurable_smul := by
    change Measurable (fun z : ℝ × ℝ => Real.exp z.1 * z.2)
    fun_prop

local instance d029037 : MeasurableSMul₂ _root_.GD.N0225.N0535.d029030
    (_root_.GD.N0232.N0719.N0859.d010811 k sizes) where
  measurable_smul := by
    change Measurable (fun z : ℝ × _root_.GD.N0232.N0719.N0859.d010811 k sizes =>
      fun i j => Real.exp z.1 * z.2 i j)
    fun_prop

private def d029038 : Measure _root_.GD.N0225.N0535.d029030 := gaussianReal 0 1

local instance d029039 : IsProbabilityMeasure _root_.GD.N0225.N0535.d029038 := by
  change IsProbabilityMeasure (gaussianReal 0 1)
  infer_instance

private theorem d029040 (h : _root_.GD.N0225.N0535.d029030) :
    Measure.QuasiMeasurePreserving (fun g : _root_.GD.N0225.N0535.d029030 => g * h)
      _root_.GD.N0225.N0535.d029038 _root_.GD.N0225.N0535.d029038 := by
  change Measure.QuasiMeasurePreserving (fun g : ℝ => g + h.toAdd)
    (gaussianReal 0 1) (gaussianReal 0 1)
  refine ⟨by fun_prop, ?_⟩
  rw [gaussianReal_map_add_const, zero_add]
  exact (gaussianReal_absolutelyContinuous h.toAdd one_ne_zero).trans
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero)

local instance d029041 : IsProbabilityMeasure
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010813 _root_.GD.N0232.N0719.d009182
  infer_instance

theorem d029042
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : Measurable f)
    (hcov : ∀ t : ℝ, _root_.GD.N0225.N0535.d029028 sizes f t) :
    ∃ g : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable g ∧ _root_.GD.N0225.N0535.d029027 sizes g ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, g =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f := by
  obtain ⟨g, hg, hgf, hge⟩ :=
    _root_.GD.N0230.N0605.d000343
      (G := _root_.GD.N0225.N0535.d029030) (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      _root_.GD.N0225.N0535.d029038 f (fun _ => 0) hf measurable_const
      (by intro t z; change 0 = Real.exp t.toAdd * 0; exact (mul_zero _).symm)
      (fun t => hcov t.toAdd) _root_.GD.N0225.N0535.d029040
  refine ⟨g, hg, ?_, fun θ => (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hgf⟩
  intro c hc z
  have h := hge (Multiplicative.ofAdd (Real.log c)) z
  change g (fun i j => Real.exp (Real.log c) * z i j) = Real.exp (Real.log c) * g z at h
  simpa only [Real.exp_log hc] using h

theorem d029043
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (a b : ℝ) (hab : Irrational (a / b))
    (ha : _root_.GD.N0225.N0535.d029028 sizes f a) (hb : _root_.GD.N0225.N0535.d029028 sizes f b) :
    ∀ t : ℝ, t ∈ _root_.GD.N0226.d028198 sizes f := by
  have hle : AddSubgroup.closure ({a, b} : Set ℝ) ≤ _root_.GD.N0226.d028198 sizes f := by
    apply (AddSubgroup.closure_le (_root_.GD.N0226.d028198 sizes f)).mpr
    exact Set.pair_subset ((_root_.GD.N0225.N0535.d029029 sizes f a).mpr ha)
      ((_root_.GD.N0225.N0535.d029029 sizes f b).mpr hb)
  exact _root_.GD.N0226.d028203 sizes f hf
    ((dense_addSubgroupClosure_pair_iff.mpr hab).mono hle)

theorem d029044
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (a b : ℝ) (hab : Irrational (a / b))
    (ha : _root_.GD.N0225.N0535.d029028 sizes f a) (hb : _root_.GD.N0225.N0535.d029028 sizes f b) :
    ∃ g : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable g ∧ _root_.GD.N0225.N0535.d029027 sizes g ∧
      ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, g =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f := by
  apply _root_.GD.N0225.N0535.d029042 sizes f hf.1
  intro t
  exact (_root_.GD.N0225.N0535.d029029 sizes f t).mp
    (_root_.GD.N0225.N0535.d029043 sizes f hf a b hab ha hb t)

theorem d029045
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (a b : ℝ) (hab : Irrational (a / b)) :
    (∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable f ∧ _root_.GD.N0225.N0535.d029027 sizes f ∧
      _root_.GD.N0232.N0719.N0970.d012309 k sizes f ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes f) ↔
    (∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable f ∧ _root_.GD.N0232.N0719.N0970.d012309 k sizes f ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes f ∧
      _root_.GD.N0225.N0535.d029028 sizes f a ∧ _root_.GD.N0225.N0535.d029028 sizes f b) := by
  constructor
  · rintro ⟨f, hf, he, ht, hs⟩
    exact ⟨f, hf, ht, hs, ae_of_all _ (he _ (Real.exp_pos a)),
      ae_of_all _ (he _ (Real.exp_pos b))⟩
  · rintro ⟨f, hf, ht, hs, ha, hb⟩
    obtain ⟨g, hg, hge, hgf⟩ := _root_.GD.N0225.N0535.d029044 sizes f
      (_root_.GD.N0097.d028188 sizes hk hn f hf hs) a b hab ha hb
    have hrisk (θ : _root_.GD.N0232.N0719.N0859.d010809 k) := _root_.GD.N0232.N0719.N0896.d011094 k sizes θ (hgf θ)
    refine ⟨g, hg, hge, ?_, ?_⟩
    · intro e he hdom θ
      exact (ht e he (fun θ => by simpa only [hrisk θ] using hdom θ) θ).trans
        (hgf θ).symm
    · intro θ
      rw [hrisk θ]
      exact hs θ

theorem d029046
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    (∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable f ∧ _root_.GD.N0225.N0535.d029027 sizes f ∧
      _root_.GD.N0232.N0719.N0970.d012309 k sizes f ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes f) ↔
    (∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ,
      Measurable f ∧ _root_.GD.N0232.N0719.N0970.d012309 k sizes f ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes f ∧
      _root_.GD.N0225.N0535.d029028 sizes f (Real.sqrt 2) ∧ _root_.GD.N0225.N0535.d029028 sizes f 1) :=
  _root_.GD.N0225.N0535.d029045 sizes hk hn (Real.sqrt 2) 1
    (by simpa using irrational_sqrt_two)

theorem d029047
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : Measurable f) (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f)
    (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes f)
    (a b : ℝ) (hab : Irrational (a / b))
    (ha : _root_.GD.N0225.N0535.d029028 sizes f a) (hb : _root_.GD.N0225.N0535.d029028 sizes f b) :
    _root_.GD.N0097.d028168 sizes f = ⊥ :=
  _root_.GD.N0003.N0240.d029026 sizes hk hn
    f hf ht hs (_root_.GD.N0225.N0535.d029043 sizes f
      (_root_.GD.N0097.d028188 sizes hk hn f hf hs) a b hab ha hb)

end
end GD.N0225.N0535

#print axioms _root_.GD.N0225.N0535.d029029
#print axioms _root_.GD.N0225.N0535.d029042
#print axioms _root_.GD.N0225.N0535.d029043
#print axioms _root_.GD.N0225.N0535.d029044
#print axioms _root_.GD.N0225.N0535.d029045
#print axioms _root_.GD.N0225.N0535.d029046
#print axioms _root_.GD.N0225.N0535.d029047
