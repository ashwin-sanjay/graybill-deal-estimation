import GD.Module1661
import GD.Module1748
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.Topology.Connected.TotallyDisconnected

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace GD.N0226

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0842 _root_.GD.N0232.N0719.N0946 _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0970 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0097

noncomputable section

variable {k : ℕ} (sizes : Fin k → ℕ)


theorem d029008
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    {t : ℝ} (ht : t ∈ _root_.GD.N0226.d028198 sizes f) :
    (fun z => f (fun i j => Real.exp t * z i j)) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes]
      fun z => Real.exp t * f z := by
  have hpull := (_root_.GD.N0232.N0719.N0896.d011119
    k sizes 0 (Real.exp t) (Real.exp_pos t)).ae_eq ht
  filter_upwards [hpull] with z hz
  change _root_.GD.N0226.d028194 sizes t f (_root_.GD.N0232.N0719.N0900.d009095 k sizes 0 (Real.exp t) z) =
    f (_root_.GD.N0232.N0719.N0900.d009095 k sizes 0 (Real.exp t) z) at hz
  rw [_root_.GD.N0226.d028194, _root_.GD.N0232.N0719.N0842.d010913
    k sizes 0 (Real.exp t) (Real.exp_ne_zero t) f z] at hz
  have hobs : _root_.GD.N0232.N0719.N0900.d009095 k sizes 0 (Real.exp t) z =
      (fun i j => Real.exp t * z i j) := by
    ext i j
    exact zero_add _
  rw [hobs, zero_add] at hz
  exact hz.symm

local instance d029009 : IsProbabilityMeasure
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010813 _root_.GD.N0232.N0719.d009182
  infer_instance




theorem d029010
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : Measurable f) (htrans : _root_.GD.N0097.d028173 sizes f)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes f) :
    ¬ Dense (_root_.GD.N0226.d028198 sizes f : Set ℝ) := by
  intro hd
  have hfin := _root_.GD.N0097.d028188 sizes hk hn f hf hs
  have hall := _root_.GD.N0226.d028203 sizes f hfin hd
  have hcov (a : _root_.GD.N0232.N0719.N0946.d009229) :
      (fun z => f (a • z)) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
        fun z => a • f z := by
    have hscale := _root_.GD.N0226.d029008 sizes f (hall a.logScale)
    filter_upwards [hscale] with z hz
    change f (fun i j => a.shift + Real.exp a.logScale * z i j) =
      a.shift + Real.exp a.logScale * f z
    rw [htrans a.shift, hz]
  obtain ⟨g, hg, hgf, hge⟩ :=
    _root_.GD.N0232.N0719.N0946.d009261
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (by omega) (fun i => by have := hn i; omega) f hf hcov
  have hgfθ (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : g =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f :=
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hgf
  have hrisk (θ : _root_.GD.N0232.N0719.N0859.d010809 k) := _root_.GD.N0232.N0719.N0896.d011094 k sizes θ (hgfθ θ)
  apply _root_.GD.N0212.N0466.d028993 hk sizes hn
  refine ⟨g, hg, hge, ?_, ?_⟩
  · intro θ
    rw [hrisk θ]
    exact hs θ
  · intro e he hdom θ
    exact (ht e he (fun θ => by simpa only [hrisk θ] using hdom θ) θ).trans
      (hgfθ θ).symm



theorem d029011
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : Measurable f) (htrans : _root_.GD.N0097.d028173 sizes f)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes f) :
    _root_.GD.N0226.d028198 sizes f = ⊥ ∨
      ∃ a : ℝ, 0 < a ∧ _root_.GD.N0226.d028198 sizes f = AddSubgroup.zmultiples a := by
  have hnd := _root_.GD.N0226.d029010
    sizes hk hn f hf htrans ht hs
  obtain ⟨a, ha⟩ := (_root_.GD.N0226.d028198 sizes f).dense_or_cyclic.resolve_left hnd
  rw [← AddSubgroup.zmultiples_eq_closure] at ha
  rcases lt_trichotomy a 0 with hneg | rfl | hpos
  · right
    exact ⟨-a, neg_pos.mpr hneg, by simpa only [AddSubgroup.zmultiples_neg] using ha⟩
  · left
    simpa using ha
  · exact Or.inr ⟨a, hpos, ha⟩


theorem d029012
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : Measurable f) (htrans : _root_.GD.N0097.d028173 sizes f)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes f) :
    DiscreteTopology (_root_.GD.N0226.d028198 sizes f) := by
  rcases _root_.GD.N0226.d029011 sizes hk hn f hf htrans ht hs with h | ⟨a, _, h⟩
  · rw [h]
    infer_instance
  · rw [h]
    infer_instance


theorem d029013
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : Measurable f) (htrans : _root_.GD.N0097.d028173 sizes f)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes f) :
    (_root_.GD.N0226.d028198 sizes f : Set ℝ).Countable := by
  rcases _root_.GD.N0226.d029011 sizes hk hn f hf htrans ht hs with h | ⟨a, _, h⟩
  · rw [h]
    exact Set.countable_singleton 0
  · rw [h]
    exact Set.countable_range (fun n : ℤ => n • a)



theorem d029014
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : Measurable f) (htrans : _root_.GD.N0097.d028173 sizes f)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes f) :
    volume (_root_.GD.N0226.d028198 sizes f : Set ℝ) = 0 :=
  (_root_.GD.N0226.d029013 sizes hk hn f hf htrans ht hs).measure_zero volume




theorem d029015
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : Measurable f) (htrans : _root_.GD.N0097.d028173 sizes f)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ _root_.GD.N0226.d028198 sizes f, t ≠ 0 → ε ≤ |t| := by
  have hnd := _root_.GD.N0226.d029010
    sizes hk hn f hf htrans ht hs
  have hgap : ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ _root_.GD.N0226.d028198 sizes f, 0 < t → ε ≤ t := by
    by_contra! hno
    apply hnd
    exact (_root_.GD.N0226.d028198 sizes f).dense_of_not_isolated_zero hno
  obtain ⟨ε, hε, hgap⟩ := hgap
  refine ⟨ε, hε, ?_⟩
  intro t hmem hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · rw [abs_of_neg hneg]
    exact hgap (-t) ((_root_.GD.N0226.d028198 sizes f).neg_mem hmem) (neg_pos.mpr hneg)
  · rw [abs_of_pos hpos]
    exact hgap t hmem hpos



theorem d029016
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : Measurable f) (htrans : _root_.GD.N0097.d028173 sizes f)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes f)
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (γ : X → ℝ) (hγ : Continuous γ)
    (hfixed : ∀ x, γ x ∈ _root_.GD.N0226.d028198 sizes f) (x y : X) :
    γ x = γ y := by
  letI : DiscreteTopology (_root_.GD.N0226.d028198 sizes f) :=
    _root_.GD.N0226.d029012 sizes hk hn f hf htrans ht hs
  let γH : X → _root_.GD.N0226.d028198 sizes f := fun x => ⟨γ x, hfixed x⟩
  have hγH : Continuous γH := hγ.subtype_mk _
  exact congrArg Subtype.val (TotallyDisconnectedSpace.eq_of_continuous γH hγH x y)


theorem d029017
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : Measurable f) (htrans : _root_.GD.N0097.d028173 sizes f)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes f)
    {a b : ℝ} (ha : a ∈ _root_.GD.N0226.d028198 sizes f)
    (hb : b ∈ _root_.GD.N0226.d028198 sizes f) : ¬ Irrational (a / b) := by
  intro hirr
  have hle : AddSubgroup.closure ({a, b} : Set ℝ) ≤ _root_.GD.N0226.d028198 sizes f := by
    apply (AddSubgroup.closure_le (_root_.GD.N0226.d028198 sizes f)).mpr
    exact Set.pair_subset ha hb
  exact _root_.GD.N0226.d029010 sizes hk hn f hf htrans ht hs
    ((dense_addSubgroupClosure_pair_iff.mpr hirr).mono hle)

end
end GD.N0226

#print axioms _root_.GD.N0226.d029010
#print axioms _root_.GD.N0226.d029011
#print axioms _root_.GD.N0226.d029012
#print axioms _root_.GD.N0226.d029013
#print axioms _root_.GD.N0226.d029014
#print axioms _root_.GD.N0226.d029015
#print axioms _root_.GD.N0226.d029016
#print axioms _root_.GD.N0226.d029017
