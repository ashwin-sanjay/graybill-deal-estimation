import GD.Module0543
import GD.Module0548
import GD.Module1685
import GD.Module1652

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0220
noncomputable section
open _root_.GD.N0213.N0522
open _root_.GD.N0213.N0509
open _root_.GD.N0213.N0508
open _root_.GD.N0101.N0362
open _root_.GD.N0101.N0403
open _root_.GD.N0101.N0365
open _root_.GD.N0101.N0397
open _root_.GD.N0217

def d028624 : Fin 2 → ℝ := fun _ => 1/2

def d028625 (z : ℝ × ℝ) : Fin 2 → ℝ := _root_.GD.N0101.N0397.d028118.symm (_root_.GD.N0217.d008091 z)

@[fun_prop] theorem d028626 : Measurable _root_.GD.N0220.d028625 :=
  _root_.GD.N0101.N0397.d028118.symm.measurable.comp _root_.GD.N0217.d008092

theorem d028627 (z : ℝ × ℝ) : _root_.GD.N0220.d028625 z ∈ _root_.GD.N0101.N0362.d007944 := by
  change ∀ i : Fin 2, 0 < _root_.GD.N0220.d028625 z i
  intro i
  fin_cases i <;> exact Real.exp_pos _

theorem d028628 (z : ℝ × ℝ) :
    _root_.GD.N0101.N0362.d007945 (_root_.GD.N0220.d028625 z) = z.1 ∧ _root_.GD.N0101.N0362.d007946 (_root_.GD.N0220.d028625 z) = z.2 := by
  change (Real.log (Real.exp (z.1+z.2)) + Real.log (Real.exp (z.1-z.2))) / 2 = z.1 ∧
    (Real.log (Real.exp (z.1+z.2)) - Real.log (Real.exp (z.1-z.2))) / 2 = z.2
  simp only [Real.log_exp]
  constructor <;> ring

theorem d028629 (N : ℝ) (z : ℝ × ℝ) :
    _root_.GD.N0101.N0362.d007947 N (_root_.GD.N0220.d028625 z) =
      _root_.GD.N0208.N0455.d007937 N z.1 *
        _root_.GD.N0208.N0455.d007937 N z.2 := by
  rw [_root_.GD.N0101.N0362.d007947, if_pos (_root_.GD.N0220.d028627 z),
    (_root_.GD.N0220.d028628 z).1, (_root_.GD.N0220.d028628 z).2]

theorem d028630 (z : ℝ × ℝ) :
    _root_.GD.N0213.N0509.d023108 _root_.GD.N0220.d028624 (_root_.GD.N0220.d028625 z) = (1 + Real.exp z.1)⁻¹ := by
  rw [show _root_.GD.N0220.d028624 = fun _ : Fin 2 => (1/2 : ℝ) by rfl,
    _root_.GD.N0101.N0397.d028123 _ _ (fun i => (_root_.GD.N0220.d028627 z i).le)]
  change (1 + (Real.exp (z.1+z.2) * Real.exp (z.1-z.2)) ^ (1/2 : ℝ))⁻¹ = _
  rw [← Real.exp_add, ← Real.exp_mul]
  congr 2
  ring

theorem d028631 :
    (volume : Measure (Fin 2 → ℝ)).map _root_.GD.N0101.N0397.d028118 = _root_.GD.N0217.d008090 :=
  (measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure ℝ))).map_eq



theorem d028632 :
    (_root_.GD.N0213.N0522.d008020 (fun _ : Fin 2 => 1)).map _root_.GD.N0101.N0397.d028118 = _root_.GD.N0217.d008089 := by
  rw [_root_.GD.N0213.N0522.d008020, _root_.GD.N0213.N0522.d008018, _root_.GD.N0220.d028631]
  have hd : (fun z : ℝ × ℝ => ENNReal.ofReal (_root_.GD.N0213.N0522.d008019 (fun _ : Fin 2 => 1)
      (_root_.GD.N0101.N0397.d028118.symm z))) = (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun _ => 1) := by
    funext z
    have hp : (∀ i : Fin 2, 0 < _root_.GD.N0101.N0397.d028118.symm z i) ↔
        z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
      simp only [Fin.forall_fin_two, mem_prod, mem_Ioi]
      rfl
    by_cases hz : z ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
    · rw [_root_.GD.N0213.N0522.d008019, if_pos (hp.mpr hz), indicator_of_mem hz]
      norm_num
    · rw [_root_.GD.N0213.N0522.d008019, if_neg (mt hp.mp hz), indicator_of_notMem hz]
      simp
  rw [hd]
  change _root_.GD.N0217.d008090.withDensity ((Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator
    (1 : (ℝ × ℝ) → ℝ≥0∞)) = _root_.GD.N0217.d008089
  rw [withDensity_indicator_one (s := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))
    (measurableSet_Ioi.prod measurableSet_Ioi)]
  exact (Measure.prod_restrict _ _).symm

def d028633 (N : ℝ) (z : ℝ × ℝ) : ℝ :=
  _root_.GD.N0213.N0509.d023108 _root_.GD.N0220.d028624 (_root_.GD.N0101.N0397.d028118.symm z) ^ 2 * _root_.GD.N0101.N0362.d007947 N (_root_.GD.N0101.N0397.d028118.symm z) ^ 2

@[fun_prop] theorem d028634 (N : ℝ) :
    Measurable (_root_.GD.N0220.d028633 N) :=
  (((_root_.GD.N0213.N0509.d023110 _root_.GD.N0220.d028624).comp _root_.GD.N0101.N0397.d028118.symm.measurable).pow_const 2).mul
    (((_root_.GD.N0101.N0362.d007949 N).comp _root_.GD.N0101.N0397.d028118.symm.measurable).pow_const 2)

theorem d028635 (N : ℝ) :
    (_root_.GD.N0101.N0365.d028458 _root_.GD.N0220.d028624 N).map _root_.GD.N0101.N0397.d028118 =
      _root_.GD.N0217.d008089.withDensity (fun z => ENNReal.ofReal (_root_.GD.N0220.d028633 N z)) := by
  rw [_root_.GD.N0101.N0365.d028458, _root_.GD.N0101.N0403.d028436, _root_.GD.N0213.N0522.d008018,
    _root_.GD.N0213.N0508.d028429, _root_.GD.N0213.N0522.d008018, _root_.GD.N0220.d028632]
  have hm₁ : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal
      (_root_.GD.N0213.N0509.d023108 _root_.GD.N0220.d028624 (_root_.GD.N0101.N0397.d028118.symm z) ^ 2)) := by
    simpa only [Function.comp_def] using
      (((_root_.GD.N0213.N0509.d023110 _root_.GD.N0220.d028624).comp _root_.GD.N0101.N0397.d028118.symm.measurable).pow_const 2).ennreal_ofReal
  have hm₂ : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal
      (_root_.GD.N0101.N0362.d007947 N (_root_.GD.N0101.N0397.d028118.symm z) ^ 2)) := by
    simpa only [Function.comp_def] using
      (((_root_.GD.N0101.N0362.d007949 N).comp _root_.GD.N0101.N0397.d028118.symm.measurable).pow_const 2).ennreal_ofReal
  rw [← withDensity_mul _ hm₁ hm₂]
  apply congrArg (fun D => _root_.GD.N0217.d008089.withDensity D)
  funext z
  dsimp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  rfl



theorem d028636 (N : ℝ) (z : ℝ × ℝ) :
    (2 * Real.exp (2*z.1)) * _root_.GD.N0220.d028633 N (_root_.GD.N0217.d008091 z) =
      _root_.GD.N0219.d008145 N N z := by
  change (2 * Real.exp (2*z.1)) *
    (_root_.GD.N0213.N0509.d023108 _root_.GD.N0220.d028624 (_root_.GD.N0220.d028625 z) ^ 2 * _root_.GD.N0101.N0362.d007947 N (_root_.GD.N0220.d028625 z) ^ 2) = _
  rw [_root_.GD.N0220.d028630, _root_.GD.N0220.d028629,
    _root_.GD.N0219.d008145,
    _root_.GD.N0219.d008143]
  have hp : 1 + Real.exp z.1 ≠ 0 := by positivity
  field_simp [hp]

theorem d028637 (N : ℝ) :
    (_root_.GD.N0219.d008150 N N).map _root_.GD.N0217.d008091 =
      (_root_.GD.N0101.N0365.d028458 _root_.GD.N0220.d028624 N).map _root_.GD.N0101.N0397.d028118 := by
  rw [_root_.GD.N0220.d028635]
  have h := _root_.GD.N0217.d008099 (_root_.GD.N0220.d028633 N) (_root_.GD.N0220.d028634 N)
  simp_rw [_root_.GD.N0220.d028636] at h
  exact h



theorem d028638 (N : ℝ) :
    (_root_.GD.N0219.d008150 N N).map _root_.GD.N0220.d028625 =
      _root_.GD.N0101.N0365.d028458 _root_.GD.N0220.d028624 N := by
  have h := congrArg (fun μ : Measure (ℝ × ℝ) => _root_.MeasureTheory.Measure.map _root_.GD.N0101.N0397.d028118.symm μ)
    (_root_.GD.N0220.d028637 N)
  rw [Measure.map_map _root_.GD.N0101.N0397.d028118.symm.measurable _root_.GD.N0217.d008092,
    Measure.map_map _root_.GD.N0101.N0397.d028118.symm.measurable _root_.GD.N0101.N0397.d028118.measurable] at h
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply] at h
  change (_root_.GD.N0219.d008150 N N).map _root_.GD.N0220.d028625 =
    (_root_.GD.N0101.N0365.d028458 _root_.GD.N0220.d028624 N).map id at h
  rwa [Measure.map_id] at h

theorem d028639 (N : ℝ) (g : (Fin 2 → ℝ) → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ β, g β ∂_root_.GD.N0101.N0365.d028458 _root_.GD.N0220.d028624 N) =
      ∫⁻ z, g (_root_.GD.N0220.d028625 z) ∂(_root_.GD.N0219.d008150 N N) := by
  rw [← _root_.GD.N0220.d028638]
  exact lintegral_map hg _root_.GD.N0220.d028626

end
end GD.N0220

#print axioms _root_.GD.N0220.d028627
#print axioms _root_.GD.N0220.d028628
#print axioms _root_.GD.N0220.d028629
#print axioms _root_.GD.N0220.d028630
#print axioms _root_.GD.N0220.d028632
#print axioms _root_.GD.N0220.d028635
#print axioms _root_.GD.N0220.d028636
#print axioms _root_.GD.N0220.d028637
#print axioms _root_.GD.N0220.d028638
#print axioms _root_.GD.N0220.d028639
