import GD.Module0942
import GD.Module0632
import GD.Module0268
import Mathlib.Tactic



















open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GD.N0232.N0720.N1397

noncomputable section

open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0232.N0720.N1053
open _root_.GD.N0232.N0720.N1155
open _root_.GD.N0232.N0719.N0932



abbrev d014798 := ℝ × (ℝ × (ℝ × ℝ))


def d014799 : Measure (ℝ × (ℝ × ℝ)) :=
  (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))

instance d014800 : IsProbabilityMeasure _root_.GD.N0232.N0720.N1397.d014799 := by
  unfold _root_.GD.N0232.N0720.N1397.d014799
  infer_instance




def d014801 :
    ((ℝ × ℝ) × (ℝ × ℝ)) → _root_.GD.N0232.N0720.N1397.d014798 :=
  fun z ↦ (z.1.1, (z.1.2, z.2))

@[fun_prop] theorem d014802 :
    Measurable _root_.GD.N0232.N0720.N1397.d014801 := by
  unfold _root_.GD.N0232.N0720.N1397.d014801
  fun_prop

theorem d014803 :
    _root_.GD.N0232.N0720.N1397.d014801 =
      (MeasurableEquiv.prodAssoc :
        ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ × (ℝ × (ℝ × ℝ))) := by
  rfl

def d014804 :
    (_root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2) → _root_.GD.N0232.N0720.N1397.d014798 :=
  _root_.GD.N0232.N0720.N1397.d014801 ∘ _root_.GD.N0232.N0720.N1053.d014746 (1 / 2) ∘ _root_.GD.N0232.N0720.N1053.d014743

@[fun_prop] theorem d014805 :
    Measurable _root_.GD.N0232.N0720.N1397.d014804 := by
  unfold _root_.GD.N0232.N0720.N1397.d014804
  fun_prop



theorem d014806 :
    (_root_.GD.N0137.d008914 2 2).map _root_.GD.N0232.N0720.N1397.d014804 =
      (gaussianReal 0 1).prod _root_.GD.N0232.N0720.N1397.d014799 := by
  calc
    (_root_.GD.N0137.d008914 2 2).map _root_.GD.N0232.N0720.N1397.d014804 =
        (((_root_.GD.N0137.d008914 2 2).map _root_.GD.N0232.N0720.N1053.d014743).map
          (_root_.GD.N0232.N0720.N1053.d014746 (1 / 2))).map _root_.GD.N0232.N0720.N1397.d014801 := by
      rw [Measure.map_map, Measure.map_map]
      · rfl
      all_goals fun_prop
    _ = ((_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map
          (_root_.GD.N0232.N0720.N1053.d014746 (1 / 2))).map _root_.GD.N0232.N0720.N1397.d014801 := by
      rw [_root_.GD.N0232.N0720.N1053.d014745]
    _ = (_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map
          _root_.GD.N0232.N0720.N1397.d014801 := by
      rw [_root_.GD.N0232.N0720.N1053.d014748 (by norm_num) (by norm_num)]
    _ = (gaussianReal 0 1).prod _root_.GD.N0232.N0720.N1397.d014799 := by
      unfold _root_.GD.N0232.N0720.N1155.d008950 _root_.GD.N0232.N0720.N1397.d014799
      rw [_root_.GD.N0232.N0720.N1397.d014803]
      exact Measure.prodAssoc_prod




def d014807 (mu s : ℝ) :
    _root_.GD.N0232.N0720.N1397.d014798 → _root_.GD.N0232.N0720.N1397.d014798 :=
  fun z ↦
    (mu + (s / 2) * z.1,
      (s * z.2.1, (s * z.2.2.1, s * z.2.2.2)))

@[fun_prop] theorem d014808 (mu s : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1397.d014807 mu s) := by
  unfold _root_.GD.N0232.N0720.N1397.d014807
  fun_prop


def d014809 (mu s : ℝ) : Measure _root_.GD.N0232.N0720.N1397.d014798 :=
  (gaussianReal mu (_root_.GD.N0232.N0719.N0932.d009193 (s / 2))).prod
    ((gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 s)).prod
      ((gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 s)).prod
        (gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 s))))

instance d014810 (mu s : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1397.d014809 mu s) := by
  unfold _root_.GD.N0232.N0720.N1397.d014809
  infer_instance



theorem d014811 (mu s : ℝ) :
    ((gaussianReal 0 1).prod _root_.GD.N0232.N0720.N1397.d014799).map
        (_root_.GD.N0232.N0720.N1397.d014807 mu s) = _root_.GD.N0232.N0720.N1397.d014809 mu s := by
  have hgauss (μ σ : ℝ) :
      (gaussianReal 0 1).map (fun x : ℝ => μ + σ * x) =
        gaussianReal μ (.mk (σ ^ 2) (sq_nonneg σ)) := by
    calc
      (gaussianReal 0 1).map (fun x : ℝ => μ + σ * x) =
          ((gaussianReal 0 1).map (fun x : ℝ => σ * x)).map
            (fun x : ℝ => μ + x) := by
              rw [Measure.map_map (by fun_prop) (by fun_prop)]
              congr 1
      _ = (gaussianReal 0 (.mk (σ ^ 2) (sq_nonneg σ))).map
            (fun x : ℝ => μ + x) := by
              rw [gaussianReal_map_const_mul]
              simp
      _ = gaussianReal μ (.mk (σ ^ 2) (sq_nonneg σ)) := by
            rw [gaussianReal_map_const_add]
            simp
  let f : ℝ → ℝ := fun x ↦ mu + (s / 2) * x
  let g : ℝ → ℝ := fun x ↦ s * x
  have hf : Measurable f := by unfold f; fun_prop
  have hg : Measurable g := by unfold g; fun_prop
  have hfg : Measurable (Prod.map g (Prod.map g g)) := by fun_prop
  change ((gaussianReal 0 1).prod _root_.GD.N0232.N0720.N1397.d014799).map
      (Prod.map f (Prod.map g (Prod.map g g))) = _root_.GD.N0232.N0720.N1397.d014809 mu s
  rw [← Measure.map_prod_map (gaussianReal 0 1) _root_.GD.N0232.N0720.N1397.d014799 hf hfg]
  unfold _root_.GD.N0232.N0720.N1397.d014799
  rw [← Measure.map_prod_map (gaussianReal 0 1)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) hg (by fun_prop),
    ← Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 1) hg hg]
  unfold _root_.GD.N0232.N0720.N1397.d014809 f g
  rw [hgauss]
  have hzero (c : ℝ) :
      (gaussianReal 0 1).map (fun x : ℝ ↦ c * x) =
        gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 c) := by
    have hvariance : (NNReal.mk (c ^ 2) (sq_nonneg c)) =
        _root_.GD.N0232.N0719.N0932.d009193 c := by
      apply NNReal.eq
      rfl
    simpa only [zero_add, mul_one, hvariance] using hgauss 0 c
  rw [hzero]
  rfl





def d014812 (mu s : ℝ) :
    (_root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2) → _root_.GD.N0232.N0720.N1397.d014798 :=
  _root_.GD.N0232.N0720.N1397.d014807 mu s ∘ _root_.GD.N0232.N0720.N1397.d014804 ∘
    _root_.GD.N0107.d009025 2 2 mu s s

@[fun_prop] theorem d014813 (mu s : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1397.d014812 mu s) := by
  unfold _root_.GD.N0232.N0720.N1397.d014812
  fun_prop





theorem d014814
    (mu s : ℝ) (hs : s ≠ 0) :
    _root_.GD.N0232.N0720.N1397.d014812 mu s =
      _root_.GD.N0232.N0720.N1397.d014812 0 1 := by
  funext omega
  rcases omega with ⟨x, y⟩
  ext <;>
    simp only [_root_.GD.N0232.N0720.N1397.d014812, Function.comp_apply,
      _root_.GD.N0232.N0720.N1397.d014807, _root_.GD.N0232.N0720.N1397.d014804,
      _root_.GD.N0232.N0720.N1397.d014801, _root_.GD.N0232.N0720.N1053.d014746, _root_.GD.N0232.N0720.N1053.d014743,
      _root_.GD.N0232.N0720.N1053.d014740, _root_.GD.N0137.d008920, _root_.GD.N0137.d008918,
      _root_.GD.N0137.d008919, _root_.GD.N0107.d009025, _root_.GD.N0107.d009019,
      MeasurableEquiv.finTwoArrow_apply] <;>
    field_simp [hs] <;>
    ring_nf <;>
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)] <;>
    ring


def d014815 :
    (_root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2) → _root_.GD.N0232.N0720.N1397.d014798 :=
  _root_.GD.N0232.N0720.N1397.d014812 0 1

@[fun_prop] theorem d014816 :
    Measurable _root_.GD.N0232.N0720.N1397.d014815 :=
  _root_.GD.N0232.N0720.N1397.d014813 0 1




theorem d014817
    (omega : _root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2) :
    _root_.GD.N0232.N0720.N1397.d014815 omega =
      ((omega.1 0 + omega.1 1 + omega.2 0 + omega.2 1) / 4,
        (((omega.1 0 + omega.1 1) - (omega.2 0 + omega.2 1)) / 2,
          (Real.sqrt (1 / 2) * (omega.1 0 - omega.1 1),
            Real.sqrt (1 / 2) * (omega.2 0 - omega.2 1)))) := by
  rcases omega with ⟨x, y⟩
  have hhalfSub : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  ext <;>
    simp only [_root_.GD.N0232.N0720.N1397.d014815,
      _root_.GD.N0232.N0720.N1397.d014812, Function.comp_apply,
      _root_.GD.N0232.N0720.N1397.d014807, _root_.GD.N0232.N0720.N1397.d014804,
      _root_.GD.N0232.N0720.N1397.d014801, _root_.GD.N0232.N0720.N1053.d014746, _root_.GD.N0232.N0720.N1053.d014743,
      _root_.GD.N0232.N0720.N1053.d014740, _root_.GD.N0137.d008920, _root_.GD.N0137.d008918,
      _root_.GD.N0137.d008919, _root_.GD.N0107.d009025, _root_.GD.N0107.d009019,
      MeasurableEquiv.finTwoArrow_apply] <;>
    simp only [hhalfSub, sub_zero, div_one, one_mul, zero_add] <;>
    ring_nf <;>
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)] <;>
    ring



theorem d014818
    (mu s : ℝ) (hs : s ≠ 0) :
    (_root_.GD.N0107.d009030 2 2 mu s s).map
        (_root_.GD.N0232.N0720.N1397.d014812 mu s) =
      _root_.GD.N0232.N0720.N1397.d014809 mu s := by
  calc
    (_root_.GD.N0107.d009030 2 2 mu s s).map
        (_root_.GD.N0232.N0720.N1397.d014812 mu s) =
      (((_root_.GD.N0107.d009030 2 2 mu s s).map
          (_root_.GD.N0107.d009025 2 2 mu s s)).map
        _root_.GD.N0232.N0720.N1397.d014804).map
          (_root_.GD.N0232.N0720.N1397.d014807 mu s) := by
      rw [Measure.map_map, Measure.map_map]
      · rfl
      all_goals fun_prop
    _ = (((_root_.GD.N0137.d008914 2 2).map _root_.GD.N0232.N0720.N1397.d014804).map
          (_root_.GD.N0232.N0720.N1397.d014807 mu s)) := by
      rw [_root_.GD.N0107.d009031 2 2 mu s s hs hs]
    _ = ((gaussianReal 0 1).prod _root_.GD.N0232.N0720.N1397.d014799).map
          (_root_.GD.N0232.N0720.N1397.d014807 mu s) := by
      rw [_root_.GD.N0232.N0720.N1397.d014806]
    _ = _root_.GD.N0232.N0720.N1397.d014809 mu s := _root_.GD.N0232.N0720.N1397.d014811 mu s




theorem d014819
    (mu s : ℝ) (hs : s ≠ 0) :
    (_root_.GD.N0107.d009030 2 2 mu s s).map _root_.GD.N0232.N0720.N1397.d014815 =
      _root_.GD.N0232.N0720.N1397.d014809 mu s := by
  rw [show _root_.GD.N0232.N0720.N1397.d014815 =
      _root_.GD.N0232.N0720.N1397.d014812 mu s by
        exact (_root_.GD.N0232.N0720.N1397.d014814 mu s hs).symm]
  exact _root_.GD.N0232.N0720.N1397.d014818 mu s hs



theorem d014820 :
    (_root_.GD.N0107.d009030 2 2 0 1 1).map
        _root_.GD.N0232.N0720.N1397.d014815 =
      (gaussianReal 0 (1 / 4)).prod _root_.GD.N0232.N0720.N1397.d014799 := by
  unfold _root_.GD.N0232.N0720.N1397.d014815
  rw [_root_.GD.N0232.N0720.N1397.d014818 0 1 (by norm_num)]
  have hhalf : _root_.GD.N0232.N0719.N0932.d009193 (1 / 2) = (1 / 4 : ℝ≥0) := by
    apply NNReal.eq
    norm_num [_root_.GD.N0232.N0719.N0932.d009194]
  unfold _root_.GD.N0232.N0720.N1397.d014809
  rw [hhalf, _root_.GD.N0232.N0719.N0932.d009195]
  rfl

end

end GD.N0232.N0720.N1397

#print axioms _root_.GD.N0232.N0720.N1397.d014806
#print axioms _root_.GD.N0232.N0720.N1397.d014818
#print axioms _root_.GD.N0232.N0720.N1397.d014819
#print axioms _root_.GD.N0232.N0720.N1397.d014820
