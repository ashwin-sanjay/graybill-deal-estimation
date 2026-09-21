import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic























open Set
open scoped BigOperators

namespace GD
namespace N0230
namespace N0614

noncomputable section

set_option linter.unusedSectionVars false

variable {E I : Type*}
variable [AddCommGroup E] [Module ℝ E]
variable [Fintype I] [DecidableEq I]



def d000146
    (D : Set E) (objective : E → ℝ) (constraint : I → E → ℝ)
    (weight : I → ℝ) (a : ℝ) : Prop :=
  (∀ i, 0 ≤ weight i) ∧
    ∀ x ∈ D, a ≤ objective x + ∑ i, weight i * constraint i x


private def d000147 (r : ℝ) (v : I → ℝ) : Option I → ℝ
  | none => r
  | some i => v i

@[simp] private theorem d000148 (r : ℝ) (v : I → ℝ) :
    _root_.GD.N0230.N0614.d000147 r v none = r := rfl

@[simp] private theorem d000149 (r : ℝ) (v : I → ℝ) (i : I) :
    _root_.GD.N0230.N0614.d000147 r v (some i) = v i := rfl









theorem d000150
    (D : Set E) (objective : E → ℝ) (constraint : I → E → ℝ)
    (hD : Convex ℝ D)
    (hobjective : ConvexOn ℝ D objective)
    (hconstraint : ∀ i, ConvexOn ℝ D (constraint i))
    (a : ℝ)
    (hlower : ∀ x ∈ D, (∀ i, constraint i x ≤ 0) →
      a ≤ objective x)
    (hslater : ∃ s ∈ D, ∀ i, constraint i s < 0) :
    ∃ weight : I → ℝ,
      _root_.GD.N0230.N0614.d000146
        D objective constraint weight a := by
  classical
  let V := Option I → ℝ
  let A : Set V := {y | ∃ x ∈ D,
    objective x < y none ∧ ∀ i, constraint i x < y (some i)}
  let z : V := _root_.GD.N0230.N0614.d000147 a (fun _ => 0)
  have hAopen : IsOpen A := by
    rw [isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨x, hxD, hxobjective, hxconstraint⟩ := hy
    let U : Set V :=
      {w | objective x < w none} ∩
        ⋂ i, {w | constraint i x < w (some i)}
    refine ⟨U, ?_, ?_, ?_⟩
    · intro w hw
      exact ⟨x, hxD, hw.1, fun i ↦ Set.mem_iInter.mp hw.2 i⟩
    · exact
        (isOpen_lt continuous_const (continuous_apply none)).inter
          (isOpen_iInter_of_finite fun i ↦
            isOpen_lt continuous_const (continuous_apply (some i)))
    · exact ⟨hxobjective, Set.mem_iInter.mpr hxconstraint⟩
  have hAconvex : Convex ℝ A := by
    intro y hy w hw c d hc hd hcd
    obtain ⟨x, hxD, hxobjective, hxconstraint⟩ := hy
    obtain ⟨q, hqD, hqobjective, hqconstraint⟩ := hw
    have hweighted_lt {u u' v v' : ℝ}
        (hu : u < u') (hv : v < v') :
        c * u + d * v < c * u' + d * v' := by
      rcases eq_or_lt_of_le hc with hczero | hcpos
      · have hcZero : c = 0 := hczero.symm
        have hdOne : d = 1 := by linarith
        rw [hcZero, hdOne]
        simpa using hv
      · have hleft : c * u < c * u' :=
          mul_lt_mul_of_pos_left hu hcpos
        have hright : d * v ≤ d * v' :=
          mul_le_mul_of_nonneg_left hv.le hd
        linarith
    refine ⟨c • x + d • q, hD hxD hqD hc hd hcd, ?_, ?_⟩
    · have hjensen := hobjective.2 hxD hqD hc hd hcd
      have hstrict := hweighted_lt hxobjective hqobjective
      change objective (c • x + d • q) <
        c * y none + d * w none
      exact hjensen.trans_lt hstrict
    · intro i
      have hjensen := (hconstraint i).2 hxD hqD hc hd hcd
      have hstrict := hweighted_lt (hxconstraint i) (hqconstraint i)
      change constraint i (c • x + d • q) <
        c * y (some i) + d * w (some i)
      exact hjensen.trans_lt hstrict
  have hz_not_mem : z ∉ A := by
    rintro ⟨x, hxD, hxobjective, hxconstraint⟩
    have hfeasible : ∀ i, constraint i x ≤ 0 := by
      intro i
      exact (hxconstraint i).le
    have hbound := hlower x hxD hfeasible
    change objective x < a at hxobjective
    linarith
  obtain ⟨f, hf⟩ :=
    geometric_hahn_banach_point_open hAconvex hAopen hz_not_mem
  obtain ⟨s, hsD, hsstrict⟩ := hslater
  let ybase : V := _root_.GD.N0230.N0614.d000147 (objective s + 1)
    (fun i ↦ constraint i s + 1)
  have hybase : ybase ∈ A := by
    refine ⟨s, hsD, ?_, ?_⟩
    · simp [ybase]
    · intro i
      simp [ybase]
  let coeff : Option I → ℝ := fun j ↦ f (Pi.single j 1)
  have hf_value (y : V) :
      f y = coeff none * y none + ∑ i, coeff (some i) * y (some i) := by
    have hydecomp := pi_eq_sum_univ' y
    calc
      f y = f (∑ j, (y j) • Pi.single j (1 : ℝ)) := by
        rw [← hydecomp]
      _ = ∑ j, f ((y j) • Pi.single j (1 : ℝ)) := by
        rw [map_sum]
      _ = ∑ j, coeff j * y j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_smul, smul_eq_mul, coeff]
        ring
      _ = coeff none * y none + ∑ i, coeff (some i) * y (some i) := by
        rw [Fintype.sum_option]
  have hA_upward (y : V) (hy : y ∈ A) (j : Option I)
      (t : ℝ) (ht : 0 < t) :
      y + t • Pi.single j (1 : ℝ) ∈ A := by
    obtain ⟨x, hxD, hxobjective, hxconstraint⟩ := hy
    refine ⟨x, hxD, ?_, ?_⟩
    · cases j with
      | none =>
          change objective x <
            y none + t *
              Pi.single (M := fun _ : Option I ↦ ℝ) none (1 : ℝ) none
          simpa [Pi.single_apply] using
            (show objective x < y none + t by linarith)
      | some j =>
          change objective x <
            y none + t *
              Pi.single (M := fun _ : Option I ↦ ℝ) (some j) (1 : ℝ) none
          simpa [Pi.single_apply] using hxobjective
    · intro i
      cases j with
      | none =>
          change constraint i x <
            y (some i) + t *
              Pi.single (M := fun _ : Option I ↦ ℝ) none (1 : ℝ) (some i)
          simpa [Pi.single_apply] using hxconstraint i
      | some j =>
          by_cases hij : i = j
          · subst i
            change constraint j x <
              y (some j) + t *
                Pi.single (M := fun _ : Option I ↦ ℝ)
                  (some j) (1 : ℝ) (some j)
            simpa [Pi.single_apply] using
              (show constraint j x < y (some j) + t by
                linarith [hxconstraint j])
          · change constraint i x <
              y (some i) + t *
                Pi.single (M := fun _ : Option I ↦ ℝ)
                  (some j) (1 : ℝ) (some i)
            simpa [Pi.single_apply, hij] using hxconstraint i
  have hcoeff_nonneg : ∀ j, 0 ≤ coeff j := by
    intro j
    by_contra hj
    have hjneg : coeff j < 0 := lt_of_not_ge hj
    let t : ℝ := (f ybase - f z + 1) / (-coeff j)
    have hsepBase : f z < f ybase := hf ybase hybase
    have ht : 0 < t := by
      exact div_pos (by linarith) (neg_pos.mpr hjneg)
    have hsepMoved := hf
      (ybase + t • Pi.single j (1 : ℝ))
      (hA_upward ybase hybase j t ht)
    have hcoeffEval : f (Pi.single j (1 : ℝ)) = coeff j := rfl
    have htIdentity : f ybase + t * coeff j = f z - 1 := by
      dsimp only [t]
      field_simp [ne_of_lt hjneg]
      ring
    rw [map_add, map_smul, hcoeffEval, smul_eq_mul,
      htIdentity] at hsepMoved
    linarith
  have hcoeffObjective_pos : 0 < coeff none := by
    have hsep : f z < f (_root_.GD.N0230.N0614.d000147 (objective s + 1)
        (fun i ↦ constraint i s / 2)) := by
      apply hf
      refine ⟨s, hsD, ?_, ?_⟩
      · simp
      · intro i
        simp only [_root_.GD.N0230.N0614.d000149]
        linarith [hsstrict i]
    by_contra hnot
    have hzero : coeff none = 0 :=
      le_antisymm (le_of_not_gt hnot) (hcoeff_nonneg none)
    have hsumNonpos :
        (∑ i, coeff (some i) * (constraint i s / 2)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      exact mul_nonpos_of_nonneg_of_nonpos
        (hcoeff_nonneg (some i)) (by linarith [hsstrict i])
    rw [hf_value, hf_value] at hsep
    simp only [z, _root_.GD.N0230.N0614.d000148, _root_.GD.N0230.N0614.d000149, mul_zero,
      Finset.sum_const_zero, add_zero, hzero, zero_mul] at hsep
    linarith
  let weight : I → ℝ := fun i ↦ coeff (some i) / coeff none
  refine ⟨weight, ?_, ?_⟩
  · intro i
    exact div_nonneg (hcoeff_nonneg (some i)) hcoeffObjective_pos.le
  · intro x hxD
    apply le_of_forall_pos_le_add
    intro ε hε
    let mass : ℝ := 1 + ∑ i, weight i
    have hmass : 0 < mass := by
      have hsum : 0 ≤ ∑ i, weight i :=
        Finset.sum_nonneg fun i hi ↦
          div_nonneg (hcoeff_nonneg (some i)) hcoeffObjective_pos.le
      dsimp only [mass]
      linarith
    let delta : ℝ := ε / mass
    have hdelta : 0 < delta := div_pos hε hmass
    let y : V := _root_.GD.N0230.N0614.d000147 (objective x + delta)
      (fun i ↦ constraint i x + delta)
    have hy : y ∈ A := by
      refine ⟨x, hxD, ?_, ?_⟩
      · simp [y, hdelta]
      · intro i
        simp [y, hdelta]
    have hsep := hf y hy
    rw [hf_value, hf_value] at hsep
    have hcoeffWeight : ∀ i,
        coeff (some i) = coeff none * weight i := by
      intro i
      dsimp only [weight]
      field_simp [ne_of_gt hcoeffObjective_pos]
    simp only [z, y, _root_.GD.N0230.N0614.d000148, _root_.GD.N0230.N0614.d000149, mul_zero,
      Finset.sum_const_zero, add_zero] at hsep
    simp_rw [hcoeffWeight] at hsep
    have hdeltaMass : delta * mass = ε := by
      dsimp only [delta]
      exact div_mul_cancel₀ ε (ne_of_gt hmass)
    have hfactor :
        coeff none * (objective x + delta) +
            ∑ i, coeff none * weight i * (constraint i x + delta) =
          coeff none *
            (objective x + ∑ i, weight i * constraint i x +
              delta * mass) := by
      have hsumConstraint :
          (∑ i, coeff none * weight i * constraint i x) =
            coeff none * ∑ i, weight i * constraint i x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hsumDelta :
          (∑ i, coeff none * weight i * delta) =
            coeff none * delta * ∑ i, weight i := by
        calc
          (∑ i, coeff none * weight i * delta) =
              ∑ i, (coeff none * delta) * weight i := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = coeff none * delta * ∑ i, weight i := by
            rw [Finset.mul_sum]
      dsimp only [mass]
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [hsumConstraint, hsumDelta]
      ring
    rw [hfactor, hdeltaMass] at hsep
    have hnormalized :
        a < objective x + ∑ i, weight i * constraint i x + ε := by
      by_contra hnot
      have hle : objective x + ∑ i, weight i * constraint i x + ε ≤ a :=
        le_of_not_gt hnot
      have hmul := mul_le_mul_of_nonneg_left hle hcoeffObjective_pos.le
      nlinarith [hsep]
    linarith

end

end N0614
end N0230
end GD

#print axioms _root_.GD.N0230.N0614.d000150
