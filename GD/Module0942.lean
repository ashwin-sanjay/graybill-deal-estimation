import GD.Module0167
import GD.Module0941
import GD.Module0619
import GD.Module0632
import Mathlib.Tactic














open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD
namespace N0232
namespace N0720
namespace N1053

noncomputable section

open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0232.N0720.N1155
open _root_.GD.N0232.N0720.N1157
open _root_.GD.N0232.N0720.N1213
open _root_.GD.N0232.N0720.N1052




def d014740 (x : _root_.GD.N0137.d008894 2) : ℝ × ℝ :=
  _root_.GD.N0137.d008920 (1 / 2)
    ((MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ)) x)

@[fun_prop] theorem d014741 :
    Measurable _root_.GD.N0232.N0720.N1053.d014740 := by
  unfold _root_.GD.N0232.N0720.N1053.d014740
  fun_prop



theorem d014742 :
    (_root_.GD.N0137.d008895 2).map _root_.GD.N0232.N0720.N1053.d014740 = _root_.GD.N0232.N0720.N1155.d008950 := by
  have hfin :
      (_root_.GD.N0137.d008895 2).map
          (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ)) =
        _root_.GD.N0232.N0720.N1155.d008950 := by
    unfold _root_.GD.N0137.d008895 _root_.GD.N0140.d006650
    calc
      Measure.map
          (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ))
          (Measure.pi fun _ : Fin 2 ↦ gaussianReal 0 1) =
        Measure.map
          (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ))
          (Measure.pi ![gaussianReal 0 1, gaussianReal 0 1]) := by
            congr 2
            funext i
            fin_cases i <;> rfl
      _ = (gaussianReal 0 1).prod (gaussianReal 0 1) :=
        (measurePreserving_finTwoArrow_vec
          (gaussianReal 0 1) (gaussianReal 0 1)).map_eq
  calc
    (_root_.GD.N0137.d008895 2).map _root_.GD.N0232.N0720.N1053.d014740 =
        ((_root_.GD.N0137.d008895 2).map
          (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ))).map
            (_root_.GD.N0137.d008920 (1 / 2)) := by
      rw [Measure.map_map]
      · rfl
      · exact _root_.GD.N0137.d008921 _
      · fun_prop
    _ = _root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008920 (1 / 2)) := by
      rw [hfin]
    _ = _root_.GD.N0232.N0720.N1155.d008950 := by
      exact _root_.GD.N0137.d008927 (by norm_num) (by norm_num)


def d014743
    (omega : _root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2) :
    (ℝ × ℝ) × (ℝ × ℝ) :=
  (_root_.GD.N0232.N0720.N1053.d014740 omega.1, _root_.GD.N0232.N0720.N1053.d014740 omega.2)

@[fun_prop] theorem d014744 :
    Measurable _root_.GD.N0232.N0720.N1053.d014743 := by
  unfold _root_.GD.N0232.N0720.N1053.d014743
  fun_prop

theorem d014745 :
    (_root_.GD.N0137.d008914 2 2).map _root_.GD.N0232.N0720.N1053.d014743 =
      _root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950 := by
  unfold _root_.GD.N0137.d008914 _root_.GD.N0232.N0720.N1053.d014743
  change Measure.map (Prod.map _root_.GD.N0232.N0720.N1053.d014740 _root_.GD.N0232.N0720.N1053.d014740)
      ((_root_.GD.N0137.d008895 2).prod (_root_.GD.N0137.d008895 2)) = _
  rw [← Measure.map_prod_map
    (_root_.GD.N0137.d008895 2) (_root_.GD.N0137.d008895 2)
    _root_.GD.N0232.N0720.N1053.d014741 _root_.GD.N0232.N0720.N1053.d014741,
    _root_.GD.N0232.N0720.N1053.d014742]






def d014746 (p : ℝ) :
    ((ℝ × ℝ) × (ℝ × ℝ)) →
      ((ℝ × ℝ) × (ℝ × ℝ)) :=
  fun z ↦
    (_root_.GD.N0137.d008920 p (z.1.1, z.2.1),
      (z.1.2, z.2.2))

@[fun_prop] theorem d014747 (p : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1053.d014746 p) := by
  unfold _root_.GD.N0232.N0720.N1053.d014746 _root_.GD.N0137.d008920
    _root_.GD.N0137.d008918 _root_.GD.N0137.d008919
  fun_prop

theorem d014748
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map
        (_root_.GD.N0232.N0720.N1053.d014746 p) =
      _root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950 := by
  let regroup : ((ℝ × ℝ) × (ℝ × ℝ)) →
      ((ℝ × ℝ) × (ℝ × ℝ)) :=
    _root_.GD.N0137.d008910
  have hregroup :
      (_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map regroup =
        _root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950 := by
    simpa [_root_.GD.N0232.N0720.N1155.d008950, regroup] using
      (_root_.GD.N0137.d008913
        (gaussianReal 0 1) (gaussianReal 0 1)
        (gaussianReal 0 1) (gaussianReal 0 1))
  calc
    (_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map
        (_root_.GD.N0232.N0720.N1053.d014746 p) =
      ((_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map regroup).map
        (Prod.map (_root_.GD.N0137.d008920 p) id) := by
          rw [Measure.map_map]
          · rfl
          · fun_prop
          · dsimp [regroup]
            fun_prop
    _ = (_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map
        (Prod.map (_root_.GD.N0137.d008920 p) id) := by rw [hregroup]
    _ = (_root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008920 p)).prod
        (_root_.GD.N0232.N0720.N1155.d008950.map id) := by
          exact (Measure.map_prod_map
            _root_.GD.N0232.N0720.N1155.d008950 _root_.GD.N0232.N0720.N1155.d008950
            (_root_.GD.N0137.d008921 p) measurable_id).symm
    _ = _root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950 := by
      rw [_root_.GD.N0137.d008927 hp0 hp1, Measure.map_id]



def d014749 :
    ((ℝ × ℝ) × (ℝ × ℝ)) → ((ℝ × ℝ) × ℝ) :=
  fun z ↦ (z.2, z.1.2)

@[fun_prop] theorem d014750 :
    Measurable _root_.GD.N0232.N0720.N1053.d014749 := by
  unfold _root_.GD.N0232.N0720.N1053.d014749
  fun_prop

theorem d014751 :
    (_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map _root_.GD.N0232.N0720.N1053.d014749 =
      _root_.GD.N0232.N0720.N1155.d008950.prod (gaussianReal 0 1) := by
  let swap : ((ℝ × ℝ) × (ℝ × ℝ)) →
      ((ℝ × ℝ) × (ℝ × ℝ)) := Prod.swap
  have hswap :
      (_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map swap =
        _root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950 := by
    simpa [swap] using
      (Measure.measurePreserving_swap
        (μ := _root_.GD.N0232.N0720.N1155.d008950) (ν := _root_.GD.N0232.N0720.N1155.d008950)).map_eq
  calc
    (_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map _root_.GD.N0232.N0720.N1053.d014749 =
      ((_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map swap).map
        (Prod.map id Prod.snd) := by
          rw [Measure.map_map]
          · rfl
          all_goals fun_prop
    _ = (_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map
        (Prod.map id Prod.snd) := by rw [hswap]
    _ = (_root_.GD.N0232.N0720.N1155.d008950.map id).prod
        (_root_.GD.N0232.N0720.N1155.d008950.map Prod.snd) := by
          exact (Measure.map_prod_map
            _root_.GD.N0232.N0720.N1155.d008950 _root_.GD.N0232.N0720.N1155.d008950
            measurable_id measurable_snd).symm
    _ = _root_.GD.N0232.N0720.N1155.d008950.prod (gaussianReal 0 1) := by
      rw [Measure.map_id, measurePreserving_snd.map_eq]


def d014752 (p : ℝ) :
    (_root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2) → ((ℝ × ℝ) × ℝ) :=
  _root_.GD.N0232.N0720.N1053.d014749 ∘ _root_.GD.N0232.N0720.N1053.d014746 p ∘ _root_.GD.N0232.N0720.N1053.d014743

@[fun_prop] theorem d014753 (p : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1053.d014752 p) := by
  unfold _root_.GD.N0232.N0720.N1053.d014752
  fun_prop

theorem d014754
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (_root_.GD.N0137.d008914 2 2).map (_root_.GD.N0232.N0720.N1053.d014752 p) =
      _root_.GD.N0232.N0720.N1155.d008950.prod (gaussianReal 0 1) := by
  calc
    (_root_.GD.N0137.d008914 2 2).map (_root_.GD.N0232.N0720.N1053.d014752 p) =
      (((_root_.GD.N0137.d008914 2 2).map _root_.GD.N0232.N0720.N1053.d014743).map
        (_root_.GD.N0232.N0720.N1053.d014746 p)).map _root_.GD.N0232.N0720.N1053.d014749 := by
          rw [Measure.map_map, Measure.map_map]
          · rfl
          all_goals fun_prop
    _ = ((_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map
        (_root_.GD.N0232.N0720.N1053.d014746 p)).map _root_.GD.N0232.N0720.N1053.d014749 := by
          rw [_root_.GD.N0232.N0720.N1053.d014745]
    _ = (_root_.GD.N0232.N0720.N1155.d008950.prod _root_.GD.N0232.N0720.N1155.d008950).map
        _root_.GD.N0232.N0720.N1053.d014749 := by rw [_root_.GD.N0232.N0720.N1053.d014748 hp0 hp1]
    _ = _root_.GD.N0232.N0720.N1155.d008950.prod (gaussianReal 0 1) :=
      _root_.GD.N0232.N0720.N1053.d014751

end

end N1053
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1053.d014742
#print axioms _root_.GD.N0232.N0720.N1053.d014754
