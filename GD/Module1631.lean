import GD.Module1365
import GD.Module0663
import GD.Module1223
import GD.Module0744
import GD.Module1262
import GD.Module0809
import GD.Module1270
import GD.Module1228





set_option autoImplicit false
set_option warningAsError true










open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace GD.N0232.N0719.N0981

open _root_.GD.N0232.N0719.N0980 _root_.GD.N0232.N0719.N0885
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0107 _root_.GD.N0232.N0719.N0932

noncomputable section

variable {k : ℕ} [NeZero k] (sizes : Fin k → ℕ)

abbrev d020643 := Sigma fun i : Fin k => Fin (sizes i)
abbrev d020644 := _root_.GD.N0232.N0719.N0981.d020643 sizes → ℝ

def d020645 : _root_.GD.N0232.N0719.N0981.d020644 sizes ≃ᵐ _root_.GD.N0232.N0719.N0986.d020359 sizes :=
  MeasurableEquiv.piCurry (fun (i : Fin k) (_ : Fin (sizes i)) => ℝ)

def d020646 (x : _root_.GD.N0232.N0719.N0981.d020644 sizes) (i : Fin k) : ℝ :=
  (∑ j, x ⟨i, j⟩) / (sizes i : ℝ)

def d020647 (x : _root_.GD.N0232.N0719.N0981.d020644 sizes) : ℝ := Finset.univ.inf' Finset.univ_nonempty (_root_.GD.N0232.N0719.N0981.d020646 sizes x)
def d020648 (x : _root_.GD.N0232.N0719.N0981.d020644 sizes) : ℝ := Finset.univ.sup' Finset.univ_nonempty (_root_.GD.N0232.N0719.N0981.d020646 sizes x)

omit [NeZero k] in
@[fun_prop] theorem d020649 (i : Fin k) : Continuous (fun x => _root_.GD.N0232.N0719.N0981.d020646 sizes x i) := by
  unfold _root_.GD.N0232.N0719.N0981.d020646
  fun_prop

@[fun_prop] theorem d020650 : Continuous (_root_.GD.N0232.N0719.N0981.d020647 sizes) :=
  Continuous.finset_inf'_apply _ (fun i _ => _root_.GD.N0232.N0719.N0981.d020649 sizes i)

@[fun_prop] theorem d020651 : Continuous (_root_.GD.N0232.N0719.N0981.d020648 sizes) :=
  Continuous.finset_sup'_apply _ (fun i _ => _root_.GD.N0232.N0719.N0981.d020649 sizes i)

theorem d020652 (x : _root_.GD.N0232.N0719.N0981.d020644 sizes) (i : Fin k) : _root_.GD.N0232.N0719.N0981.d020647 sizes x ≤ _root_.GD.N0232.N0719.N0981.d020646 sizes x i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem d020653 (x : _root_.GD.N0232.N0719.N0981.d020644 sizes) (i : Fin k) : _root_.GD.N0232.N0719.N0981.d020646 sizes x i ≤ _root_.GD.N0232.N0719.N0981.d020648 sizes x :=
  Finset.le_sup' _ (Finset.mem_univ i)

theorem d020654 (x : _root_.GD.N0232.N0719.N0981.d020644 sizes) : _root_.GD.N0232.N0719.N0981.d020647 sizes x ≤ _root_.GD.N0232.N0719.N0981.d020648 sizes x :=
  (_root_.GD.N0232.N0719.N0981.d020652 sizes x 0).trans (_root_.GD.N0232.N0719.N0981.d020653 sizes x 0)

omit [NeZero k] in
theorem d020655 (hn : ∀ i, 0 < sizes i) (c : ℝ) (x : _root_.GD.N0232.N0719.N0981.d020644 sizes) (i : Fin k) :
    _root_.GD.N0232.N0719.N0981.d020646 sizes (fun j => c + x j) i = c + _root_.GD.N0232.N0719.N0981.d020646 sizes x i := by
  have hi : (sizes i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hn i).ne'
  simp only [_root_.GD.N0232.N0719.N0981.d020646, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, add_div]
  field_simp

theorem d020656 (hn : ∀ i, 0 < sizes i) : _root_.GD.N0232.N0719.N0980.d009696 (_root_.GD.N0232.N0719.N0981.d020647 sizes) := by
  intro c x
  simp only [_root_.GD.N0232.N0719.N0981.d020647, _root_.GD.N0232.N0719.N0981.d020655 sizes hn]
  exact (map_finset_inf' (OrderIso.addLeft c) _ (_root_.GD.N0232.N0719.N0981.d020646 sizes x)).symm

theorem d020657 (hn : ∀ i, 0 < sizes i) : _root_.GD.N0232.N0719.N0980.d009696 (_root_.GD.N0232.N0719.N0981.d020648 sizes) := by
  intro c x
  simp only [_root_.GD.N0232.N0719.N0981.d020648, _root_.GD.N0232.N0719.N0981.d020655 sizes hn]
  exact (map_finset_sup' (OrderIso.addLeft c) _ (_root_.GD.N0232.N0719.N0981.d020646 sizes x)).symm

def d020658 (v : Fin k → ℝ≥0) (j : _root_.GD.N0232.N0719.N0981.d020643 sizes) : ℝ≥0 := v j.1

theorem d020659 (hn : ∀ i, 0 < sizes i)
    (v : Fin k → ℝ≥0) (hv : ∀ i, 0 < v i) (x : _root_.GD.N0232.N0719.N0981.d020644 sizes) :
    _root_.GD.N0232.N0719.N0981.d020647 sizes x ≤ _root_.GD.N0232.N0719.N0980.d009698 (_root_.GD.N0232.N0719.N0981.d020658 sizes v) x ∧
      _root_.GD.N0232.N0719.N0980.d009698 (_root_.GD.N0232.N0719.N0981.d020658 sizes v) x ≤ _root_.GD.N0232.N0719.N0981.d020648 sizes x := by
  letI : ∀ i, Nonempty (Fin (sizes i)) := fun i => Fin.pos_iff_nonempty.mp (hn i)
  letI : Nonempty (_root_.GD.N0232.N0719.N0981.d020643 sizes) := ⟨⟨0, ⟨0, hn 0⟩⟩⟩
  let w : Fin k → ℝ := fun i => (v i : ℝ)⁻¹ / _root_.GD.N0232.N0719.N0885.d009322 (_root_.GD.N0232.N0719.N0981.d020658 sizes v)
  have hw (i : Fin k) : 0 ≤ w i := div_nonneg (inv_nonneg.mpr (v i).coe_nonneg)
    (_root_.GD.N0232.N0719.N0885.d009324 (_root_.GD.N0232.N0719.N0981.d020658 sizes v) (fun j => hv j.1)).le
  have hsum : ∑ i, (sizes i : ℝ) * w i = 1 := by
    have h := _root_.GD.N0232.N0719.N0885.d009325 (_root_.GD.N0232.N0719.N0981.d020658 sizes v) (fun j => hv j.1)
    simpa [_root_.GD.N0232.N0719.N0885.d009323, _root_.GD.N0232.N0719.N0981.d020658, Fintype.sum_sigma, w] using h
  have horacle : _root_.GD.N0232.N0719.N0980.d009698 (_root_.GD.N0232.N0719.N0981.d020658 sizes v) x =
      ∑ i, (sizes i : ℝ) * w i * _root_.GD.N0232.N0719.N0981.d020646 sizes x i := by
    simp only [_root_.GD.N0232.N0719.N0980.d009698, _root_.GD.N0232.N0719.N0885.d009311, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro i _
    have hi : (sizes i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hn i).ne'
    simp only [_root_.GD.N0232.N0719.N0885.d009323, _root_.GD.N0232.N0719.N0981.d020658, ← Finset.mul_sum, _root_.GD.N0232.N0719.N0981.d020646]
    change w i * (∑ j, x ⟨i, j⟩) = _
    field_simp
  rw [horacle]
  constructor
  · calc
      _ = ∑ i, (sizes i : ℝ) * w i * _root_.GD.N0232.N0719.N0981.d020647 sizes x := by
        rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (_root_.GD.N0232.N0719.N0981.d020652 sizes x i) (mul_nonneg (Nat.cast_nonneg _) (hw i)))
  · calc
      _ ≤ ∑ i, (sizes i : ℝ) * w i * _root_.GD.N0232.N0719.N0981.d020648 sizes x :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
          (_root_.GD.N0232.N0719.N0981.d020653 sizes x i) (mul_nonneg (Nat.cast_nonneg _) (hw i)))
      _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

def d020660 (f : _root_.GD.N0232.N0719.N0986.d020359 sizes → ℝ) (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0980.d009704 (_root_.GD.N0232.N0719.N0981.d020647 sizes) (_root_.GD.N0232.N0719.N0981.d020648 sizes) (f ∘ _root_.GD.N0232.N0719.N0981.d020645 sizes) ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z)

@[fun_prop] theorem d020661 {f : _root_.GD.N0232.N0719.N0986.d020359 sizes → ℝ} (hf : Measurable f) :
    Measurable (_root_.GD.N0232.N0719.N0981.d020660 sizes f) :=
  (_root_.GD.N0232.N0719.N0980.d009706 (_root_.GD.N0232.N0719.N0981.d020650 sizes).measurable (_root_.GD.N0232.N0719.N0981.d020651 sizes).measurable
    (hf.comp (_root_.GD.N0232.N0719.N0981.d020645 sizes).measurable)).comp (_root_.GD.N0232.N0719.N0981.d020645 sizes).symm.measurable

theorem d020662 (f : _root_.GD.N0232.N0719.N0986.d020359 sizes → ℝ) (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) :
    _root_.GD.N0232.N0719.N0981.d020647 sizes ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z) ≤ _root_.GD.N0232.N0719.N0981.d020660 sizes f z ∧
      _root_.GD.N0232.N0719.N0981.d020660 sizes f z ≤ _root_.GD.N0232.N0719.N0981.d020648 sizes ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z) := by
  exact ⟨le_max_left _ _, max_le (_root_.GD.N0232.N0719.N0981.d020654 sizes _) (min_le_left _ _)⟩

theorem d020663 (hn : ∀ i, 0 < sizes i) (m : ℝ) (v : Fin k → ℝ≥0)
    (hv : ∀ i, 0 < v i) (f : _root_.GD.N0232.N0719.N0986.d020359 sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (h2 : MemLp f 2 (Measure.pi fun i => Measure.pi fun _ : Fin (sizes i) =>
      gaussianReal m (v i))) :
    MemLp (_root_.GD.N0232.N0719.N0981.d020660 sizes f) 2 (Measure.pi fun i => Measure.pi fun _ : Fin (sizes i) =>
      gaussianReal m (v i)) ∧
    (∫ z, (_root_.GD.N0232.N0719.N0981.d020660 sizes f z - m) ^ 2
      ∂(Measure.pi fun i => Measure.pi fun _ : Fin (sizes i) => gaussianReal m (v i))) ≤
      ∫ z, (f z - m) ^ 2
        ∂(Measure.pi fun i => Measure.pi fun _ : Fin (sizes i) => gaussianReal m (v i)) := by
  letI : ∀ i, Nonempty (Fin (sizes i)) := fun i => Fin.pos_iff_nonempty.mp (hn i)
  letI : Nonempty (_root_.GD.N0232.N0719.N0981.d020643 sizes) := ⟨⟨0, ⟨0, hn 0⟩⟩⟩
  have hmap : MeasurePreserving (_root_.GD.N0232.N0719.N0981.d020645 sizes)
      (_root_.GD.N0232.N0719.N0980.d009697 m (_root_.GD.N0232.N0719.N0981.d020658 sizes v))
      (Measure.pi fun i => Measure.pi fun _ : Fin (sizes i) => gaussianReal m (v i)) := by
    simpa only [_root_.GD.N0232.N0719.N0981.d020645, MeasurableEquiv.symm_symm, _root_.GD.N0232.N0719.N0980.d009697, _root_.GD.N0232.N0719.N0981.d020658] using
      (_root_.GD.N0232.N0719.N0997.d019803
        (fun (i : Fin k) (_ : Fin (sizes i)) => gaussianReal m (v i))).symm
  have h2' : MemLp (f ∘ _root_.GD.N0232.N0719.N0981.d020645 sizes) 2 (_root_.GD.N0232.N0719.N0980.d009697 m (_root_.GD.N0232.N0719.N0981.d020658 sizes v)) := by
    apply (_root_.GD.N0232.N0719.N0981.d020645 sizes).memLp_map_measure_iff.mp
    rw [hmap.map_eq]
    exact h2
  have hbound := _root_.GD.N0232.N0719.N0980.d009708 m (_root_.GD.N0232.N0719.N0981.d020658 sizes v) (fun j => hv j.1)
    (_root_.GD.N0232.N0719.N0981.d020647 sizes) (_root_.GD.N0232.N0719.N0981.d020648 sizes) (f ∘ _root_.GD.N0232.N0719.N0981.d020645 sizes)
    (_root_.GD.N0232.N0719.N0981.d020650 sizes).measurable (_root_.GD.N0232.N0719.N0981.d020651 sizes).measurable
    (hf.comp (_root_.GD.N0232.N0719.N0981.d020645 sizes).measurable) (_root_.GD.N0232.N0719.N0981.d020656 sizes hn) (_root_.GD.N0232.N0719.N0981.d020657 sizes hn)
    (fun c x => he c (_root_.GD.N0232.N0719.N0981.d020645 sizes x))
    (fun x => (_root_.GD.N0232.N0719.N0981.d020659 sizes hn v hv x).1)
    (fun x => (_root_.GD.N0232.N0719.N0981.d020659 sizes hn v hv x).2) h2'
  constructor
  · rw [← hmap.map_eq]
    apply (_root_.GD.N0232.N0719.N0981.d020645 sizes).memLp_map_measure_iff.mpr
    simpa only [_root_.GD.N0232.N0719.N0981.d020660, Function.comp_def, MeasurableEquiv.symm_apply_apply] using hbound.1
  have hleft := hmap.integral_comp' (fun z => (_root_.GD.N0232.N0719.N0981.d020660 sizes f z - m) ^ 2)
  have hright := hmap.integral_comp' (fun z => (f z - m) ^ 2)
  rw [← hleft, ← hright]
  simpa only [_root_.GD.N0232.N0719.N0981.d020660, Function.comp_def, MeasurableEquiv.symm_apply_apply] using hbound.2

end
end GD.N0232.N0719.N0981

#print axioms _root_.GD.N0232.N0719.N0981.d020659
#print axioms _root_.GD.N0232.N0719.N0981.d020663





set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GD.N0156.N0443

open _root_.GD.N0232.N0719.N0980

noncomputable section


theorem d020664 {l u t a : ℝ} (hl : l ≤ t) (hu : t ≤ u) :
    (max l (min u a) - t) ^ 2 + (a - max l (min u a)) ^ 2 ≤ (a - t) ^ 2 := by
  by_cases hal : a ≤ l
  · rw [min_eq_right (hal.trans (hl.trans hu)), max_eq_left hal]
    nlinarith [mul_nonneg (sub_nonneg.mpr hal) (sub_nonneg.mpr hl)]
  · by_cases hua : u ≤ a
    · rw [min_eq_left hua, max_eq_right (hl.trans hu)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hua) (sub_nonneg.mpr hu)]
    · rw [min_eq_right (le_of_not_ge hua), max_eq_right (le_of_not_ge hal)]
      simp

variable {I : Type*} [Fintype I] [Nonempty I]




theorem d020665 (m : ℝ) (v : I → ℝ≥0) (hv : ∀ i, 0 < v i)
    (lower upper f : (I → ℝ) → ℝ)
    (hlm : Measurable lower) (hum : Measurable upper) (hfm : Measurable f)
    (hle : _root_.GD.N0232.N0719.N0980.d009696 lower) (hue : _root_.GD.N0232.N0719.N0980.d009696 upper)
    (hfe : _root_.GD.N0232.N0719.N0980.d009696 f)
    (hl : ∀ x, lower x ≤ _root_.GD.N0232.N0719.N0980.d009698 v x) (hu : ∀ x, _root_.GD.N0232.N0719.N0980.d009698 v x ≤ upper x)
    (hf2 : MemLp f 2 (_root_.GD.N0232.N0719.N0980.d009697 m v)) :
    (∫ x, (_root_.GD.N0232.N0719.N0980.d009704 lower upper f x - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) +
      (∫ x, (f x - _root_.GD.N0232.N0719.N0980.d009704 lower upper f x) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) ≤
        ∫ x, (f x - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v := by
  have hc2 := (_root_.GD.N0232.N0719.N0980.d009708 m v hv lower upper f hlm hum hfm hle hue hfe hl hu hf2).1
  have hM2 : MemLp (_root_.GD.N0232.N0719.N0980.d009698 v) 2 (_root_.GD.N0232.N0719.N0980.d009697 m v) :=
    (_root_.GD.N0232.N0719.N0885.d009318
      m v (_root_.GD.N0232.N0719.N0885.d009323 v)).memLp_two
  have hC := (hc2.sub hM2).integrable_sq
  have hD := (hf2.sub hc2).integrable_sq
  have hF := (hf2.sub hM2).integrable_sq
  simp only [Pi.sub_apply] at hC hD hF
  rw [_root_.GD.N0232.N0719.N0980.d009703 m v hv _ (_root_.GD.N0232.N0719.N0980.d009706 hlm hum hfm)
      (_root_.GD.N0232.N0719.N0980.d009707 hle hue hfe) hc2,
    _root_.GD.N0232.N0719.N0980.d009703 m v hv f hfm hfe hf2]
  rw [add_assoc]
  apply add_le_add le_rfl
  have hsum := integral_add hC hD
  rw [← hsum]
  exact integral_mono (hC.add hD) hF (fun x => _root_.GD.N0156.N0443.d020664 (hl x) (hu x))



theorem d020666 (m : ℝ) (v : I → ℝ≥0) (hv : ∀ i, 0 < v i)
    (lower upper f : (I → ℝ) → ℝ)
    (hlm : Measurable lower) (hum : Measurable upper) (hfm : Measurable f)
    (hle : _root_.GD.N0232.N0719.N0980.d009696 lower) (hue : _root_.GD.N0232.N0719.N0980.d009696 upper)
    (hfe : _root_.GD.N0232.N0719.N0980.d009696 f)
    (hl : ∀ x, lower x ≤ _root_.GD.N0232.N0719.N0980.d009698 v x) (hu : ∀ x, _root_.GD.N0232.N0719.N0980.d009698 v x ≤ upper x)
    (hf2 : MemLp f 2 (_root_.GD.N0232.N0719.N0980.d009697 m v)) :
    (∫ x, (_root_.GD.N0232.N0719.N0980.d009704 lower upper f x - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) =
      (∫ x, (f x - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) ↔
        _root_.GD.N0232.N0719.N0980.d009704 lower upper f =ᵐ[_root_.GD.N0232.N0719.N0980.d009697 m v] f := by
  constructor
  · intro heq
    have hgap := _root_.GD.N0156.N0443.d020665 m v hv lower upper f hlm hum hfm hle hue hfe hl hu hf2
    rw [heq] at hgap
    have hzero : (∫ x, (f x - _root_.GD.N0232.N0719.N0980.d009704 lower upper f x) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) = 0 := by
      have hnonneg : 0 ≤ (∫ x, (f x - _root_.GD.N0232.N0719.N0980.d009704 lower upper f x) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) :=
        integral_nonneg (fun x => sq_nonneg (f x - _root_.GD.N0232.N0719.N0980.d009704 lower upper f x))
      linarith
    have hc2 := (_root_.GD.N0232.N0719.N0980.d009708 m v hv lower upper f hlm hum hfm hle hue hfe hl hu hf2).1
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x - _root_.GD.N0232.N0719.N0980.d009704 lower upper f x))
      (hf2.sub hc2).integrable_sq).mp hzero
    filter_upwards [hae] with x hx
    have hx' : (f x - _root_.GD.N0232.N0719.N0980.d009704 lower upper f x) ^ 2 = 0 := hx
    nlinarith
  · intro hae
    exact integral_congr_ae (hae.fun_comp (fun t : ℝ => (t - m) ^ 2))

end
end GD.N0156.N0443

#print axioms _root_.GD.N0156.N0443.d020664
#print axioms _root_.GD.N0156.N0443.d020665
#print axioms _root_.GD.N0156.N0443.d020666





set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0156.N0444

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0981
open _root_.GD.N0232.N0719.N0970 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0232.N0719.N0896 _root_.GD.N0232.N0719.N0932

noncomputable section

variable {k : ℕ} [NeZero k] (sizes : Fin k → ℕ)


def d020667 (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (z : _root_.GD.N0232.N0719.N0859.d010811 k sizes) : Prop :=
  _root_.GD.N0232.N0719.N0981.d020647 sizes ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z) ≤ f z ∧ f z ≤ _root_.GD.N0232.N0719.N0981.d020648 sizes ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z)

omit [NeZero k] in
theorem d020668 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010812 k sizes θ = Measure.pi (fun i => Measure.pi (fun _ : Fin (sizes i) =>
      gaussianReal θ.location (_root_.GD.N0232.N0719.N0932.d009193 (θ.scale i)))) := by
  simp only [_root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.d009176, _root_.GD.N0232.N0719.N0932.d009211]

omit [NeZero k] in
local instance d020669 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  unfold _root_.GD.N0232.N0719.N0859.d010812
  infer_instance

omit [NeZero k] in

theorem d020670 (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : Measurable f)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≠ ⊤) :
    MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  have herr : MemLp (fun z => f z - θ.location) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    apply (memLp_two_iff_integrable_sq (hf.sub measurable_const).aestronglyMeasurable).mpr
    have hint := integrable_toReal_of_lintegral_ne_top
      (((hf.sub measurable_const).pow_const 2).ennreal_ofReal.aemeasurable) hfinite
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint
  convert herr.add (memLp_const θ.location) using 1
  ext z
  simp

omit [NeZero k] in
theorem d020671 (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (hf : MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ)) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f = ENNReal.ofReal (∫ z, (f z - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  simpa only [_root_.GD.N0232.N0719.N0859.d010840, Pi.sub_apply] using
    (ofReal_integral_eq_lintegral_ofReal (hf.sub (memLp_const θ.location)).integrable_sq
      (ae_of_all _ fun z => sq_nonneg (f z - θ.location))).symm



theorem d020672 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes f) ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := by
  have h2 := _root_.GD.N0156.N0444.d020670 sizes f hf.1 θ (hf.2 θ)
  have h2' := h2
  rw [_root_.GD.N0156.N0444.d020668 sizes θ] at h2'
  have hclip := _root_.GD.N0232.N0719.N0981.d020663 sizes hn θ.location (fun i => _root_.GD.N0232.N0719.N0932.d009193 (θ.scale i))
    (fun i => pos_iff_ne_zero.mpr (_root_.GD.N0232.N0719.N0932.d009196 (θ.scale_pos i).ne')) f hf.1 he h2'
  have hc2 : MemLp (_root_.GD.N0232.N0719.N0981.d020660 sizes f) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
    rw [_root_.GD.N0156.N0444.d020668 sizes θ]
    exact hclip.1
  rw [_root_.GD.N0156.N0444.d020671 sizes _ θ hc2, _root_.GD.N0156.N0444.d020671 sizes f θ h2]
  apply ENNReal.ofReal_le_ofReal
  simpa only [_root_.GD.N0156.N0444.d020668 sizes θ] using hclip.2




theorem d020673 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ∀ᵐ z ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ, _root_.GD.N0156.N0444.d020667 sizes f z := by
  have hae := ht (_root_.GD.N0232.N0719.N0981.d020660 sizes f) (_root_.GD.N0232.N0719.N0981.d020661 sizes hf.1)
    (_root_.GD.N0156.N0444.d020672 sizes hn f hf he) θ
  filter_upwards [hae] with z hz
  have h := _root_.GD.N0232.N0719.N0981.d020662 sizes f z
  rwa [hz] at h

omit [NeZero k] in
theorem d020674 (hn : ∀ i, 0 < sizes i) (b a : ℝ)
    (x : _root_.GD.N0232.N0719.N0981.d020644 sizes) (i : Fin k) :
    _root_.GD.N0232.N0719.N0981.d020646 sizes (fun j => b + a * x j) i = b + a * _root_.GD.N0232.N0719.N0981.d020646 sizes x i := by
  have hi : (sizes i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hn i).ne'
  simp only [_root_.GD.N0232.N0719.N0981.d020646, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, add_div]
  field_simp

theorem d020675 (hn : ∀ i, 0 < sizes i) (b a : ℝ) (ha : 0 < a)
    (x : _root_.GD.N0232.N0719.N0981.d020644 sizes) :
    _root_.GD.N0232.N0719.N0981.d020647 sizes (fun j => b + a * x j) = b + a * _root_.GD.N0232.N0719.N0981.d020647 sizes x := by
  simp only [_root_.GD.N0232.N0719.N0981.d020647, _root_.GD.N0156.N0444.d020674 sizes hn]
  exact (map_finset_inf' ((OrderIso.mulLeft₀ a ha).trans (OrderIso.addLeft b))
    _ (_root_.GD.N0232.N0719.N0981.d020646 sizes x)).symm

theorem d020676 (hn : ∀ i, 0 < sizes i) (b a : ℝ) (ha : 0 < a)
    (x : _root_.GD.N0232.N0719.N0981.d020644 sizes) :
    _root_.GD.N0232.N0719.N0981.d020648 sizes (fun j => b + a * x j) = b + a * _root_.GD.N0232.N0719.N0981.d020648 sizes x := by
  simp only [_root_.GD.N0232.N0719.N0981.d020648, _root_.GD.N0156.N0444.d020674 sizes hn]
  exact (map_finset_sup' ((OrderIso.mulLeft₀ a ha).trans (OrderIso.addLeft b))
    _ (_root_.GD.N0232.N0719.N0981.d020646 sizes x)).symm



theorem d020677 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes) :
    _root_.GD.N0232.N0719.N0981.d020660 sizes f ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes := by
  refine ⟨_root_.GD.N0232.N0719.N0981.d020661 sizes hf.1, ?_⟩
  intro b a ha z
  change max (_root_.GD.N0232.N0719.N0981.d020647 sizes (fun j => b + a * ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z) j))
      (min (_root_.GD.N0232.N0719.N0981.d020648 sizes (fun j => b + a * ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z) j))
        (f (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a z))) = _
  rw [_root_.GD.N0156.N0444.d020675 sizes hn b a ha, _root_.GD.N0156.N0444.d020676 sizes hn b a ha, hf.2 b a ha]
  simp only [_root_.GD.N0232.N0719.N0981.d020660, _root_.GD.N0232.N0719.N0980.d009704, Function.comp_def,
    MeasurableEquiv.apply_symm_apply, add_min, add_max,
    mul_min_of_nonneg _ _ ha.le, mul_max_of_nonneg _ _ ha.le]




theorem d020678 (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes)
    (ht : _root_.GD.N0232.N0719.N0970.d012309 k sizes f) :
    _root_.GD.N0232.N0719.N0981.d020660 sizes f ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes ∧
      _root_.GD.N0232.N0719.N0970.d012309 k sizes (_root_.GD.N0232.N0719.N0981.d020660 sizes f) ∧
      (∀ z, _root_.GD.N0156.N0444.d020667 sizes (_root_.GD.N0232.N0719.N0981.d020660 sizes f) z) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes f) = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f) := by
  have he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z := by
    intro c z
    have h := hf.1.2 c 1 zero_lt_one z
    change f (fun i j => c + 1 * z i j) = c + 1 * f z at h
    simpa only [one_mul] using h
  have hb : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := ⟨hf.1.1, hf.2⟩
  have hae (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0981.d020660 sizes f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f :=
    ht (_root_.GD.N0232.N0719.N0981.d020660 sizes f) (_root_.GD.N0232.N0719.N0981.d020661 sizes hf.1.1)
      (_root_.GD.N0156.N0444.d020672 sizes hn f hb he) θ
  have hrisk (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0981.d020660 sizes f) =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := _root_.GD.N0232.N0719.N0896.d011094 k sizes θ (hae θ)
  refine ⟨⟨_root_.GD.N0156.N0444.d020677 sizes hn f hf.1, fun θ => by rw [hrisk]; exact hf.2 θ⟩,
    ?_, _root_.GD.N0232.N0719.N0981.d020662 sizes f, hrisk⟩
  intro e hem hedom θ
  exact (ht e hem (fun θ => by simpa only [hrisk θ] using hedom θ) θ).trans (hae θ).symm



theorem d020679 (hn : ∀ i, 0 < sizes i) :
    (∃ f ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      _root_.GD.N0232.N0719.N0970.d012309 k sizes f ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes f) ↔
    (∃ f ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes,
      _root_.GD.N0232.N0719.N0970.d012309 k sizes f ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes f ∧
        ∀ z, _root_.GD.N0156.N0444.d020667 sizes f z) := by
  constructor
  · rintro ⟨f, hf, ht, hs⟩
    obtain ⟨hc, hct, hinterval, hrisk⟩ := _root_.GD.N0156.N0444.d020678 sizes hn f hf ht
    refine ⟨_root_.GD.N0232.N0719.N0981.d020660 sizes f, hc, hct, ?_, hinterval⟩
    intro θ
    rw [hrisk θ]
    exact hs θ
  · rintro ⟨f, hf, ht, hs, _⟩
    exact ⟨f, hf, ht, hs⟩

omit [NeZero k] in


theorem d020680 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes)
    (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes f) : f ∈ _root_.GD.N0232.N0719.N0962.d012191 k sizes := by
  refine ⟨hf, fun θ => ne_top_of_le_ne_top ?_ (hs θ).le⟩
  rw [_root_.GD.N0232.N0719.N0859.d010842 k sizes hk hsizes,
    _root_.GD.N0232.N0719.N0859.d010823 k sizes hk hsizes]
  exact ENNReal.ofReal_ne_top




theorem d020681 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    (∃ f ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes,
      _root_.GD.N0232.N0719.N0970.d012309 k sizes f ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes f) ↔
    (∃ f ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes,
      _root_.GD.N0232.N0719.N0970.d012309 k sizes f ∧ _root_.GD.N0232.N0719.N0970.d012310 k sizes f ∧
        ∀ z, _root_.GD.N0156.N0444.d020667 sizes f z) := by
  constructor
  · rintro ⟨f, hf, ht, hs⟩
    have hfinite := _root_.GD.N0156.N0444.d020680 sizes hk hsizes f hf hs
    have hn : ∀ i, 0 < sizes i := fun i => lt_of_lt_of_le (by decide : 0 < 2) (hsizes i)
    obtain ⟨g, hg, hgt, hgs, hinterval⟩ :=
      (_root_.GD.N0156.N0444.d020679 sizes hn).mp ⟨f, hfinite, ht, hs⟩
    exact ⟨g, hg.1, hgt, hgs, hinterval⟩
  · rintro ⟨f, hf, ht, hs, _⟩
    exact ⟨f, hf, ht, hs⟩

end
end GD.N0156.N0444

#print axioms _root_.GD.N0156.N0444.d020672
#print axioms _root_.GD.N0156.N0444.d020673
#print axioms _root_.GD.N0156.N0444.d020678
#print axioms _root_.GD.N0156.N0444.d020679
#print axioms _root_.GD.N0156.N0444.d020681





set_option autoImplicit false
set_option warningAsError true











open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0213.N0500

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1314
  (d019720 d019721 d019722)
open _root_.GD.N0232.N0720.N1330
  (d020032 d020033 d020036 d020026)
open _root_.GD.N0238.N0753
open _root_.GD.N0230.N0556
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0719.N0990 _root_.GD.N0232.N0719.N0991
open _root_.GD.N0232.N0719.N0996 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0983
open _root_.GD.N0107

noncomputable section

variable {k d : ℕ} (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
variable (hn : ∀ i, 0 < sizes i)

def d027913 {I : Type*} (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) : Option I → _root_.GD.N0232.N0719.N0988.d019777 k
  | none => _root_.GD.N0232.N0719.N0988.d019778 k
  | some i => q i

theorem d027914 {I : Type*} (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) :
    _root_.GD.N0232.N0719.N0988.d019787 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q =
      fun i => _root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (_root_.GD.N0213.N0500.d027913 q i) := by
  funext i
  cases i <;> rfl



theorem d027915 (q : _root_.GD.N0232.N0719.N0988.d019777 k)
    {P : _root_.GD.N0232.N0720.N1341.d004414 d → Prop}
    (hP : ∀ᵐ omega ∂_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q),
      P (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega)) : ∀ᵐ x ∂volume, P x := by
  have hmap : ∀ᵐ x ∂(_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q)).map
      (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim), P x :=
    (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).measurableEmbedding.ae_map_iff.mpr hP
  rw [_root_.GD.N0232.N0719.N0997.d019814] at hmap
  have hm : Measurable (fun x : _root_.GD.N0232.N0720.N1341.d004414 d => ENNReal.ofReal
      (_root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x)) := by
    unfold _root_.GD.N0232.N0720.N1316.d004445
    fun_prop
  have hv := (ae_withDensity_iff hm).mp hmap
  filter_upwards [hv] with x hx
  apply hx
  apply (ENNReal.ofReal_pos.mpr ?_).ne'
  exact mul_pos (_root_.GD.N0232.N0720.N1316.d004446 _) (Real.exp_pos _)

include hn


theorem d027916 (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (ha : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0719.N0988.d019782 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim)) h) :
    ∃ (ell : ℕ → ℕ)
      (p : ∀ j, Option (Fin (ell j)) → _root_.GD.N0232.N0719.N0990.d020496 k)
      (a : ∀ j, Option (Fin (ell j)) → ℝ)
      (ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k)),
      (∀ j i, 0 ≤ a j i) ∧ (∀ j, ∑ i, a j i = 1) ∧
      (∀ j, (ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) =
        ∑ i, ENNReal.ofReal (a j i) • Measure.dirac (p j i)) ∧
      (∀ j i l, 0 < (_root_.GD.N0232.N0719.N0983.d009710 l (p j i).2 : ℝ)) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
        Tendsto (fun j => _root_.GD.N0232.N0719.N0991.d020538 sizes hdim (ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x)
          atTop (𝓝 (_root_.GD.N0232.N0720.N1341.d004418 h x))) := by
  obtain ⟨w, ns, hw, _hns, hlim⟩ :=
    _root_.GD.N0232.N0719.N0988.d019793 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) h ha
  let q : ∀ j, Option (Fin (ns j)) → _root_.GD.N0232.N0719.N0988.d019777 k :=
    fun j => _root_.GD.N0213.N0500.d027913 (fun i : Fin (ns j) => _root_.GD.N0232.N0719.N0988.d019790 k i)
  let v : ∀ j, Option (Fin (ns j)) → ℝ := fun j => _root_.GD.N0232.N0720.N1314.d019720 (w (ns j))
  have hv : ∀ j i, 0 ≤ v j i := fun j => _root_.GD.N0232.N0720.N1314.d019721 _ (hw (ns j))
  have hp : ∀ j, ∃ i, 0 < v j i := fun j => _root_.GD.N0232.N0720.N1314.d019722 _
  let ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k) :=
    fun j => _root_.GD.N0232.N0719.N0991.d020535 sizes hdim hn (q j) (v j) (hv j) (hp j)
  have hlim' : ∀ᵐ u : _root_.GD.N0232.N0720.N1341.d004415 d ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      Tendsto (fun j => _root_.GD.N0232.N0720.N1330.d020032
        (fun i => _root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q j i)) (v j) u)
        atTop (𝓝 (h u)) := by
    simpa only [q, v, _root_.GD.N0232.N0720.N1330.d020033, _root_.GD.N0213.N0500.d027914] using hlim
  have hraw := _root_.GD.N0232.N0720.N1330.d020026
    (fun j => _root_.GD.N0232.N0720.N1330.d020032 (fun i => _root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q j i)) (v j))
    (fun j => _root_.GD.N0232.N0720.N1330.d020036 _ (v j)) h hlim'
  refine ⟨ns, (fun j i => _root_.GD.N0232.N0719.N0990.d020507 sizes hdim hn (q j i)),
    (fun j => _root_.GD.N0232.N0719.N0991.d020532 sizes hdim (q j) (v j)), ν,
    (fun j i => _root_.GD.N0232.N0719.N0991.d020533 sizes hdim hn (q j) (v j) (hv j) (hp j) i),
    (fun j => _root_.GD.N0232.N0719.N0991.d020534 sizes hdim hn (q j) (v j) (hv j) (hp j)),
    (fun _ => rfl), ?_, ?_⟩
  · intro j i l
    exact div_pos (_root_.GD.N0232.N0719.N0990.d020503 sizes hn (q j i) l)
      (_root_.GD.N0232.N0719.N0990.d020504 sizes hdim hn (q j i))
  · filter_upwards [hraw] with x hx
    simpa only [ν, _root_.GD.N0232.N0719.N0991.d020539] using hx



theorem d027917
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∃ (ell : ℕ → ℕ)
      (p : ∀ j, Option (Fin (ell j)) → _root_.GD.N0232.N0719.N0990.d020496 k)
      (a : ∀ j, Option (Fin (ell j)) → ℝ)
      (ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k)),
      (∀ j i, 0 ≤ a j i) ∧ (∀ j, ∑ i, a j i = 1) ∧
      (∀ j, (ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) =
        ∑ i, ENNReal.ofReal (a j i) • Measure.dirac (p j i)) ∧
      (∀ j i l, 0 < (_root_.GD.N0232.N0719.N0983.d009710 l (p j i).2 : ℝ)) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
        Tendsto (fun j => _root_.GD.N0232.N0719.N0991.d020538 sizes hdim (ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x)
          atTop (𝓝 (s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)))) := by
  obtain ⟨h, ha, heq⟩ := _root_.GD.N0232.N0719.N0996.d019946 sizes hdim hs
  obtain ⟨ell, p, a, ν, han, has, hν, hpi, hlim⟩ :=
    _root_.GD.N0213.N0500.d027916 sizes hdim hn h ha
  have heqv : _root_.GD.N0232.N0720.N1341.d004418 h =ᵐ[volume] s ∘ (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm := by
    apply _root_.GD.N0213.N0500.d027915 sizes hdim (_root_.GD.N0232.N0719.N0988.d019778 k)
    simpa only [Filter.EventuallyEq, _root_.GD.N0232.N0719.N0996.d019931,
      Function.comp_def, MeasurableEquiv.symm_apply_apply,
      _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0996.d019935] using
      heq (_root_.GD.N0232.N0719.N0996.d019935 (_root_.GD.N0232.N0719.N0988.d019778 k))
  refine ⟨ell, p, a, ν, han, has, hν, hpi, ?_⟩
  filter_upwards [hlim, heqv] with x hx he
  simpa only [he, Function.comp_apply] using hx

end
end GD.N0213.N0500

#print axioms _root_.GD.N0213.N0500.d027917



set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace GD.N0213.N0501

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0996
open _root_.GD.N0232.N0719.N0988 _root_.GD.N0232.N0719.N0983
open _root_.GD.N0213.N0496
open _root_.GD.N0156.N0444

variable {k d : ℕ}

theorem d027918 [NeZero k]
    (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (hn : ∀ i, 0 < sizes i) (s : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)),
      (∀ c : ℝ, (∀ i, (_root_.GD.N0213.N0496.d022003 sizes hdim x).1 i ≤ c) →
        s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x) ≤ c) ∧
      (∀ c : ℝ, (∀ i, c ≤ (_root_.GD.N0213.N0496.d022003 sizes hdim x).1 i) →
        c ≤ s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)) := by
  have hf : s ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := ⟨hs.1, fun θ => ne_top_of_lt (hs.2.2.1 θ)⟩
  have he : ∀ c : ℝ, ∀ z, s (fun i j => c + z i j) = c + s z := by
    intro c z
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨c, 0⟩
    have h := hs.2.1 g z
    change s (fun i j => c + Real.exp 0 * z i j) = c + Real.exp 0 * s z at h
    simpa only [Real.exp_zero, one_mul] using h
  have hraw := _root_.GD.N0156.N0444.d020673 sizes hn s hf he hs.2.2.2
    (_root_.GD.N0232.N0719.N0996.d019935 (_root_.GD.N0232.N0719.N0988.d019778 k))
  have hvol : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)),
      _root_.GD.N0156.N0444.d020667 sizes s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x) := by
    apply _root_.GD.N0213.N0500.d027915 sizes hdim (_root_.GD.N0232.N0719.N0988.d019778 k)
    simpa only [MeasurableEquiv.symm_apply_apply, _root_.GD.N0232.N0719.N0859.d010812,
      _root_.GD.N0232.N0719.N0996.d019935] using hraw
  filter_upwards [hvol] with x hx
  constructor
  · intro c hc
    apply hx.2.trans
    apply Finset.sup'_le
    intro i _
    exact hc i
  · intro c hc
    apply le_trans _ hx.1
    apply Finset.le_inf'
    intro i _
    exact hc i

variable {I : Type*} [Fintype I]

theorem d027919 (p : I → _root_.GD.N0213.N0496.d022000 k) (weight : I → ℝ)
    (f : _root_.GD.N0213.N0496.d022000 k → ℝ) :
    Integrable f (∑ i, ENNReal.ofReal (weight i) • Measure.dirac (p i)) := by
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d027920 (p : I → _root_.GD.N0213.N0496.d022000 k) (weight : I → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (f : _root_.GD.N0213.N0496.d022000 k → ℝ) :
    (∫ y, f y ∂(∑ i, ENNReal.ofReal (weight i) • Measure.dirac (p i))) =
      ∑ i, weight i * f (p i) := by
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d027921 (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (p : I → _root_.GD.N0213.N0496.d022000 k) (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (x : _root_.GD.N0213.N0496.d021972 d) :
    _root_.GD.N0232.N0719.N0991.d020538 sizes hdim
      (∑ i, ENNReal.ofReal (weight i) • Measure.dirac (p i)) x =
      _root_.GD.N0213.N0496.d021984 d p weight (_root_.GD.N0213.N0496.d022003 sizes hdim x) := by
  unfold _root_.GD.N0232.N0719.N0991.d020538 _root_.GD.N0213.N0496.d021984
  rw [_root_.GD.N0213.N0501.d027920 p weight hw, _root_.GD.N0213.N0501.d027920 p weight hw]
  rfl

theorem d027922 [NeZero k]
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hdim : (∑ i, sizes i) = d + 1)
    (s : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∃ ν : ℕ → ProbabilityMeasure (_root_.GD.N0213.N0496.d022000 k),
      (∀ beta : ℝ, 0 < beta → beta < 1 / 2 → ∃ B : ℝ, ∀ j,
        Integrable (fun p : _root_.GD.N0213.N0496.d022000 k => Real.exp (beta * p.1 ^ 2))
          (ν j : Measure (_root_.GD.N0213.N0496.d022000 k)) ∧
        (∫ p, Real.exp (beta * p.1 ^ 2) ∂(ν j : Measure (_root_.GD.N0213.N0496.d022000 k))) ≤ B) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)), Tendsto
        (fun j => _root_.GD.N0232.N0719.N0991.d020538 sizes hdim
          (ν j : Measure (_root_.GD.N0213.N0496.d022000 k)) x) atTop
        (𝓝 (s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)))) := by
  have hn0 : ∀ i, 0 < sizes i := fun i => by have := hn i; omega
  have hd : 1 ≤ d := by
    have hsum : sizes (0 : Fin k) ≤ ∑ i, sizes i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (sizes i)) (Finset.mem_univ _)
    have hsize := hn (0 : Fin k)
    omega
  obtain ⟨ell, p, weight, ν, hw, hprob, hν, _hinterior, hlim⟩ :=
    _root_.GD.N0213.N0500.d027917
      sizes hdim hn0 hs
  have hlim' : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)), Tendsto
      (fun j => _root_.GD.N0213.N0496.d021984 d (p j) (weight j) (_root_.GD.N0213.N0496.d022003 sizes hdim x)) atTop
      (𝓝 (s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x))) := by
    simpa only [hν, _root_.GD.N0213.N0501.d027921 sizes hdim _ _ (hw _)] using hlim
  have hbounds := _root_.GD.N0213.N0501.d027918 sizes hdim hn0 s hs
  refine ⟨ν, ?_, hlim⟩
  intro beta hbeta hhalf
  obtain ⟨B, hB⟩ := _root_.GD.N0213.N0496.d021999 sizes hdim hn hd p weight hw hprob
    (fun x => s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)) hlim'
    (hbounds.mono fun _ hx => hx.1) (hbounds.mono fun _ hx => hx.2) hbeta.le hhalf
  refine ⟨B, fun j => ?_⟩
  constructor
  · rw [hν]
    exact _root_.GD.N0213.N0501.d027919 (p j) (weight j) _
  · rw [hν, _root_.GD.N0213.N0501.d027920 (p j) (weight j) (hw j)]
    exact hB j

end
end GD.N0213.N0501

#print axioms _root_.GD.N0213.N0501.d027918
#print axioms _root_.GD.N0213.N0501.d027922
