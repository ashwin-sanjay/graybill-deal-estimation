import GD.Module0759
import GD.Module0949
import GD.Module1161
import GD.Module1179
import GD.Module0822















open MeasureTheory

namespace GD
namespace N0232
namespace N0720
namespace N1475

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1470
open _root_.GD.N0232.N0720.N1497
open _root_.GD.N0232.N0720.N1501
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1010
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229





theorem d018975
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (g : _root_.GD.N0232.N0719.N0946.d009229)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1467.d012542 m n (g • omega) = g • _root_.GD.N0232.N0720.N1467.d012542 m n omega := by
  have hsizes : ∀ i, 0 < _root_.GD.N0232.N0720.N1467.d012537 m n i := by
    intro i
    fin_cases i
    · simpa [_root_.GD.N0232.N0720.N1467.d012537] using hm
    · simpa [_root_.GD.N0232.N0720.N1467.d012537] using hn
  unfold _root_.GD.N0232.N0720.N1467.d012542
  rw [_root_.GD.N0232.N0720.N1214.d014259,
    _root_.GD.N0232.N0720.N1497.d012556]
  exact _root_.GD.N0232.N0719.N1010.d011418 hsizes g (_root_.GD.N0232.N0720.N1467.d012541 m n omega)



noncomputable def d018976 (m n : ℕ) :
    Measure (_root_.GD.N0232.N0719.N0900.d009096 2) :=
  (_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1467.d012542 m n)

instance d018977 (m n : ℕ) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1475.d018976 m n) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  unfold _root_.GD.N0232.N0720.N1475.d018976
  exact Measure.isProbabilityMeasure_map
    (_root_.GD.N0232.N0720.N1501.d016289 m n).aemeasurable

instance d018978 (m n : ℕ) :
    SFinite (_root_.GD.N0232.N0720.N1475.d018976 m n) := by
  infer_instance





theorem d018979
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value)
    (value : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
    (hrep : (fun omega ↦ s.value omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
          value (g • _root_.GD.N0232.N0720.N1467.d012542 m n omega)) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦ g • value (_root_.GD.N0232.N0720.N1467.d012542 m n omega) := by
  have hmem : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      MemLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n s.value)) 2
        (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    intro g
    exact _root_.GD.N0232.N0720.N1159.d014641 m n g s.value s.finiteRisk
  have hfixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n s.value))
          (hmem g) = s.value := by
    intro g
    simpa only [_root_.GD.N0232.N0720.N1159.d014642] using
      _root_.GD.N0232.N0720.N1409.d018606
        s hsTerminal g
  have hdecisionCov :=
    _root_.GD.N0232.N0720.N1214.d014270 m n s.value hmem hfixed
  have hdecisionRep :
      _root_.GD.N0232.N0720.N1214.d014265 m n s.value =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n :=
    (_root_.GD.N0232.N0720.N1214.d014267 m n s.value).trans hrep
  have hm0 : 0 < m := lt_of_lt_of_le (by omega) hm
  have hn0 : 0 < n := lt_of_lt_of_le (by omega) hn
  intro g
  have hdecisionRepAtG :=
    (_root_.GD.N0232.N0720.N1215.d014907 m n g).ae_eq_comp hdecisionRep
  filter_upwards [hdecisionRepAtG, hdecisionCov g, hdecisionRep] with
      omega hAtG hCov hAtOne
  simp only [Function.comp_apply] at hAtG hAtOne
  rw [_root_.GD.N0232.N0720.N1475.d018975 m n hm0 hn0 g omega] at hAtG
  calc
    value (g • _root_.GD.N0232.N0720.N1467.d012542 m n omega) =
        _root_.GD.N0232.N0720.N1214.d014265 m n s.value (g • omega) := hAtG.symm
    _ = g • _root_.GD.N0232.N0720.N1214.d014265 m n s.value omega := hCov
    _ = g • value (_root_.GD.N0232.N0720.N1467.d012542 m n omega) := congrArg (g • ·) hAtOne



theorem d018980
    (m n : ℕ)
    (value : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hvalue : Measurable value)
    (hcov : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
          value (g • _root_.GD.N0232.N0720.N1467.d012542 m n omega)) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦ g • value (_root_.GD.N0232.N0720.N1467.d012542 m n omega)) :
    ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun summary : _root_.GD.N0232.N0719.N0900.d009096 2 ↦ value (g • summary)) =ᵐ[
          _root_.GD.N0232.N0720.N1475.d018976 m n]
        fun summary ↦ g • value summary := by
  intro g
  let E : Set (_root_.GD.N0232.N0719.N0900.d009096 2) :=
    {summary | value (g • summary) = g • value summary}
  have hE : MeasurableSet E := by
    exact measurableSet_eq_fun
      (hvalue.comp (measurable_const.smul measurable_id))
      (measurable_const.smul hvalue)
  have hmap := (ae_map_iff
    (_root_.GD.N0232.N0720.N1501.d016289 m n).aemeasurable hE).2 (hcov g)
  change ∀ᵐ summary ∂_root_.GD.N0232.N0720.N1475.d018976 m n,
    value (g • summary) = g • value summary
  simpa only [_root_.GD.N0232.N0720.N1475.d018976] using hmap









theorem d018981
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value) :
    ∃ repaired : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        (repaired ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
          fun omega ↦ s.value omega) ∧
      _root_.GD.N0230.N0644.d000297
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (summary : _root_.GD.N0232.N0719.N0900.d009096 2) ↦ g • summary)
        (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) repaired := by
  obtain ⟨value, hvalue, hrep⟩ :=
    _root_.GD.N0232.N0720.N1470.d018970
      m n hm hn s.value hsTerminal
  have hcovRaw := _root_.GD.N0232.N0720.N1475.d018979
    m n hm hn s hsTerminal value hrep
  have hcovSummary :=
    _root_.GD.N0232.N0720.N1475.d018980
      m n value hvalue hcovRaw
  obtain ⟨repaired, hrepaired, hrepairedSummary, hequivariant⟩ :=
    _root_.GD.N0230.N0605.d000343
      (G := _root_.GD.N0232.N0719.N0946.d009229) (X := _root_.GD.N0232.N0719.N0900.d009096 2)
      (_root_.GD.N0232.N0720.N1475.d018976 m n) _root_.GD.N0232.N0719.N0946.d009229.d009254
      value _root_.GD.N0232.N0719.N0900.d009110 hvalue _root_.GD.N0232.N0719.N0900.d009121
      (_root_.GD.N0232.N0719.N1010.d011421 (by norm_num))
      hcovSummary _root_.GD.N0232.N0719.N0946.d009229.d009257
  refine ⟨repaired, hrepaired, ?_, hequivariant⟩
  intro theta
  have hset : MeasurableSet
      {summary : _root_.GD.N0232.N0719.N0900.d009096 2 | repaired summary = value summary} :=
    measurableSet_eq_fun hrepaired hvalue
  have href :
      (repaired ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n := by
    exact (ae_map_iff
      (_root_.GD.N0232.N0720.N1501.d016289 m n).aemeasurable hset).1
        hrepairedSummary
  have hall := (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
    (href.trans hrep.symm)
  exact hall

end
end N1475
end N0720
end N0232
end GD
