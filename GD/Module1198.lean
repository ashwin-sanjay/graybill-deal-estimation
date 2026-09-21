import GD.Module0818
import GD.Module1185
import GD.Module1180




















open MeasureTheory

namespace GD
namespace N0232
namespace N0720
namespace N1476

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0860
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0232.N0719.N1010
open _root_.GD.N0232.N0720.N1041
open _root_.GD.N0232.N0720.N1043
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1209
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1446
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1475




def d019350 (x : _root_.GD.N0232.N0719.N0900.d009096 2) : _root_.GD.N0232.N0719.N0900.d009096 2 :=
  _root_.GD.N0232.N0720.N1209.d012458 (-x.mean 0) (-x.mean 1)
    (x.meanVariance 0) (x.meanVariance 1)


def d019351 (x : _root_.GD.N0232.N0719.N0900.d009096 2) : _root_.GD.N0232.N0719.N0900.d009096 2 :=
  _root_.GD.N0232.N0720.N1209.d012458 (x.mean 1) (x.mean 0)
    (x.meanVariance 1) (x.meanVariance 0)

@[simp] theorem d019352
    (u v s t : ℝ) :
    _root_.GD.N0232.N0720.N1476.d019350 (_root_.GD.N0232.N0720.N1209.d012458 u v s t) =
      _root_.GD.N0232.N0720.N1209.d012458 (-u) (-v) s t := rfl

@[simp] theorem d019353
    (u v s t : ℝ) :
    _root_.GD.N0232.N0720.N1476.d019351 (_root_.GD.N0232.N0720.N1209.d012458 u v s t) =
      _root_.GD.N0232.N0720.N1209.d012458 v u t s := rfl

@[simp] theorem d019354 (x : _root_.GD.N0232.N0719.N0900.d009096 2) :
    _root_.GD.N0232.N0720.N1476.d019350 (_root_.GD.N0232.N0720.N1476.d019350 x) = x := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;>
    simp [_root_.GD.N0232.N0720.N1476.d019350, _root_.GD.N0232.N0720.N1209.d012458]

@[simp] theorem d019355 (x : _root_.GD.N0232.N0719.N0900.d009096 2) :
    _root_.GD.N0232.N0720.N1476.d019351 (_root_.GD.N0232.N0720.N1476.d019351 x) = x := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;> rfl

theorem d019356 (x : _root_.GD.N0232.N0719.N0900.d009096 2) :
    _root_.GD.N0232.N0720.N1476.d019350 (_root_.GD.N0232.N0720.N1476.d019351 x) = _root_.GD.N0232.N0720.N1476.d019351 (_root_.GD.N0232.N0720.N1476.d019350 x) := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;> rfl

theorem d019357 : Measurable _root_.GD.N0232.N0720.N1476.d019350 := by
  rw [measurable_comap_iff]
  change Measurable (fun x : _root_.GD.N0232.N0719.N0900.d009096 2 =>
    ((fun i : Fin 2 => ![-x.mean 0, -x.mean 1] i),
      fun i : Fin 2 => ![x.meanVariance 0, x.meanVariance 1] i))
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    fin_cases i <;> fun_prop
  · apply measurable_pi_lambda
    intro i
    fin_cases i <;> fun_prop

theorem d019358 : Measurable _root_.GD.N0232.N0720.N1476.d019351 := by
  rw [measurable_comap_iff]
  change Measurable (fun x : _root_.GD.N0232.N0719.N0900.d009096 2 =>
    ((fun i : Fin 2 => ![x.mean 1, x.mean 0] i),
      fun i : Fin 2 => ![x.meanVariance 1, x.meanVariance 0] i))
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    fin_cases i <;> fun_prop
  · apply measurable_pi_lambda
    intro i
    fin_cases i <;> fun_prop

theorem d019359
    (shift dilationFactor : ℝ) (x : _root_.GD.N0232.N0719.N0900.d009096 2) :
    _root_.GD.N0232.N0720.N1476.d019350 (_root_.GD.N0232.N0719.N0900.d009101 shift dilationFactor x) =
      _root_.GD.N0232.N0719.N0900.d009101 (-shift) dilationFactor (_root_.GD.N0232.N0720.N1476.d019350 x) := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;>
    simp [_root_.GD.N0232.N0720.N1476.d019350, _root_.GD.N0232.N0719.N0900.d009101, _root_.GD.N0232.N0720.N1209.d012458] <;> ring

theorem d019360
    (shift dilationFactor : ℝ) (x : _root_.GD.N0232.N0719.N0900.d009096 2) :
    _root_.GD.N0232.N0720.N1476.d019351 (_root_.GD.N0232.N0719.N0900.d009101 shift dilationFactor x) =
      _root_.GD.N0232.N0719.N0900.d009101 shift dilationFactor (_root_.GD.N0232.N0720.N1476.d019351 x) := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;>
    simp [_root_.GD.N0232.N0720.N1476.d019351, _root_.GD.N0232.N0719.N0900.d009101, _root_.GD.N0232.N0720.N1209.d012458]




def d019361 (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (x : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ :=
  (d x - d (_root_.GD.N0232.N0720.N1476.d019350 x)) / 2

theorem d019362
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hd : Measurable d) :
    Measurable (_root_.GD.N0232.N0720.N1476.d019361 d) := by
  unfold _root_.GD.N0232.N0720.N1476.d019361
  exact (hd.sub (hd.comp _root_.GD.N0232.N0720.N1476.d019357)).div_const 2

theorem d019363
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hd : _root_.GD.N0232.N0719.N0860.d011447 d) :
    _root_.GD.N0232.N0719.N0860.d011447 (_root_.GD.N0232.N0720.N1476.d019361 d) := by
  intro shift dilationFactor hdilation x
  unfold _root_.GD.N0232.N0720.N1476.d019361
  rw [_root_.GD.N0232.N0720.N1476.d019359, hd shift dilationFactor hdilation,
    hd (-shift) dilationFactor hdilation]
  ring

theorem d019364
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) :
    _root_.GD.N0232.N0720.N1209.d012478
      (_root_.GD.N0232.N0720.N1476.d019361 d) := by
  intro u v s t
  unfold _root_.GD.N0232.N0720.N1476.d019361
  simp only [_root_.GD.N0232.N0720.N1476.d019352, neg_neg]
  ring


def d019365 (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (x : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ :=
  (d x + d (_root_.GD.N0232.N0720.N1476.d019351 x)) / 2

theorem d019366
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hd : Measurable d) :
    Measurable (_root_.GD.N0232.N0720.N1476.d019365 d) := by
  unfold _root_.GD.N0232.N0720.N1476.d019365
  exact (hd.add (hd.comp _root_.GD.N0232.N0720.N1476.d019358)).div_const 2

theorem d019367
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hd : _root_.GD.N0232.N0719.N0860.d011447 d) :
    _root_.GD.N0232.N0719.N0860.d011447 (_root_.GD.N0232.N0720.N1476.d019365 d) := by
  intro shift dilationFactor hdilation x
  unfold _root_.GD.N0232.N0720.N1476.d019365
  rw [_root_.GD.N0232.N0720.N1476.d019360, hd shift dilationFactor hdilation,
    hd shift dilationFactor hdilation]
  ring

theorem d019368
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) :
    _root_.GD.N0232.N0720.N1209.d012479 (_root_.GD.N0232.N0720.N1476.d019365 d) := by
  intro u v s t
  unfold _root_.GD.N0232.N0720.N1476.d019365
  simp only [_root_.GD.N0232.N0720.N1476.d019353]
  ring

theorem d019369
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hd : _root_.GD.N0232.N0720.N1209.d012478 d) :
    _root_.GD.N0232.N0720.N1209.d012478 (_root_.GD.N0232.N0720.N1476.d019365 d) := by
  intro u v s t
  unfold _root_.GD.N0232.N0720.N1476.d019365
  simp only [_root_.GD.N0232.N0720.N1476.d019353]
  rw [hd u v s t, hd v u t s]
  ring


def d019370 (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (x : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ :=
  (d x - d (_root_.GD.N0232.N0720.N1476.d019350 x) + d (_root_.GD.N0232.N0720.N1476.d019351 x) -
      d (_root_.GD.N0232.N0720.N1476.d019350 (_root_.GD.N0232.N0720.N1476.d019351 x))) / 4

theorem d019371
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hd : Measurable d) :
    Measurable (_root_.GD.N0232.N0720.N1476.d019370 d) := by
  unfold _root_.GD.N0232.N0720.N1476.d019370
  exact (((hd.sub (hd.comp _root_.GD.N0232.N0720.N1476.d019357)).add
    (hd.comp _root_.GD.N0232.N0720.N1476.d019358)).sub
      (hd.comp (_root_.GD.N0232.N0720.N1476.d019357.comp _root_.GD.N0232.N0720.N1476.d019358))).div_const 4

theorem d019372
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hd : _root_.GD.N0232.N0719.N0860.d011447 d) :
    _root_.GD.N0232.N0719.N0860.d011447 (_root_.GD.N0232.N0720.N1476.d019370 d) := by
  intro shift dilationFactor hdilation x
  unfold _root_.GD.N0232.N0720.N1476.d019370
  rw [_root_.GD.N0232.N0720.N1476.d019359, _root_.GD.N0232.N0720.N1476.d019360,
    _root_.GD.N0232.N0720.N1476.d019359, hd shift dilationFactor hdilation,
    hd (-shift) dilationFactor hdilation, hd shift dilationFactor hdilation,
    hd (-shift) dilationFactor hdilation]
  ring

theorem d019373
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) :
    _root_.GD.N0232.N0720.N1209.d012478
      (_root_.GD.N0232.N0720.N1476.d019370 d) := by
  intro u v s t
  unfold _root_.GD.N0232.N0720.N1476.d019370
  simp only [_root_.GD.N0232.N0720.N1476.d019352, _root_.GD.N0232.N0720.N1476.d019353,
    neg_neg]
  ring

theorem d019374
    (d : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) :
    _root_.GD.N0232.N0720.N1209.d012479 (_root_.GD.N0232.N0720.N1476.d019370 d) := by
  intro u v s t
  unfold _root_.GD.N0232.N0720.N1476.d019370
  simp only [_root_.GD.N0232.N0720.N1476.d019352, _root_.GD.N0232.N0720.N1476.d019353]
  ring



theorem d019375
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1467.d012542 m n (_root_.GD.N0232.N0720.N1446.d019019 m n omega) =
      _root_.GD.N0232.N0720.N1476.d019350 (_root_.GD.N0232.N0720.N1467.d012542 m n omega) := by
  change
    _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0232.N0720.N1467.d012537 m n)
        (_root_.GD.N0232.N0720.N1467.d012541 m n (_root_.GD.N0232.N0720.N1446.d019019 m n omega)) = _
  have hmany :
      _root_.GD.N0232.N0720.N1467.d012541 m n (_root_.GD.N0232.N0720.N1446.d019019 m n omega) =
        _root_.GD.N0232.N0719.N0900.d009095 2 (_root_.GD.N0232.N0720.N1467.d012537 m n)
          0 (-1) (_root_.GD.N0232.N0720.N1467.d012541 m n omega) := by
    funext i
    fin_cases i <;> ext j <;>
      simp [_root_.GD.N0232.N0720.N1446.d019019, _root_.GD.N0232.N0719.N0900.d009095,
        _root_.GD.N0107.d009018]
  rw [hmany, _root_.GD.N0232.N0719.N0900.d009139]
  · change
      _root_.GD.N0232.N0719.N0900.d009101 0 (-1)
          (_root_.GD.N0232.N0720.N1467.d012542 m n omega) =
        _root_.GD.N0232.N0720.N1476.d019350 (_root_.GD.N0232.N0720.N1467.d012542 m n omega)
    apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;>
      simp [_root_.GD.N0232.N0720.N1476.d019350, _root_.GD.N0232.N0720.N1209.d012458,
        _root_.GD.N0232.N0719.N0900.d009101]
  · intro i
    fin_cases i
    · simpa [_root_.GD.N0232.N0720.N1467.d012537] using hm
    · simpa [_root_.GD.N0232.N0720.N1467.d012537] using hn

theorem d019376
    (n : ℕ) (omega : _root_.GD.N0232.N0720.N1080.d014170 n n) :
    _root_.GD.N0232.N0720.N1467.d012542 n n (_root_.GD.N0232.N0720.N1043.d019054 n omega) =
      _root_.GD.N0232.N0720.N1476.d019351 (_root_.GD.N0232.N0720.N1467.d012542 n n omega) := by
  apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;> rfl



theorem d019377
    (m n : ℕ) (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    (fun omega => (_root_.GD.N0232.N0720.N1446.d019032 m n x) omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun omega => -(x (_root_.GD.N0232.N0720.N1446.d019019 m n omega)) := by
  unfold _root_.GD.N0232.N0720.N1446.d019032
  filter_upwards
      [Lp.coeFn_neg
        (Lp.compMeasurePreserving (_root_.GD.N0232.N0720.N1446.d019019 m n)
          (_root_.GD.N0232.N0720.N1446.d019031 m n) x),
       Lp.coeFn_compMeasurePreserving x
        (_root_.GD.N0232.N0720.N1446.d019031 m n)] with omega hneg hcomp
  exact hneg.trans (congrArg Neg.neg hcomp)

theorem d019378
    (n : ℕ) (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 n n)) :
    (fun omega => (_root_.GD.N0232.N0720.N1043.d019067 n x) omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 n n]
      fun omega => x (_root_.GD.N0232.N0720.N1043.d019054 n omega) := by
  unfold _root_.GD.N0232.N0720.N1043.d019067
  exact Lp.coeFn_compMeasurePreserving x
    (_root_.GD.N0232.N0720.N1043.d019066 n)






theorem d019379
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value) :
    ∃ repaired : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        (repaired ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
          fun omega => s.value omega) ∧
      _root_.GD.N0232.N0719.N0860.d011447 repaired ∧
      _root_.GD.N0232.N0720.N1209.d012478 repaired := by
  obtain ⟨value, hvalue, hrep, hequivariant⟩ :=
    _root_.GD.N0232.N0720.N1475.d018981
      m n hm hn s hsTerminal
  have hvalueAffine : _root_.GD.N0232.N0719.N0860.d011447 value := by
    intro shift dilationFactor hdilation summary
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨shift, Real.log dilationFactor⟩
    have hg := hequivariant g summary
    simpa [g, _root_.GD.N0232.N0719.N0946.d009229.d009244, _root_.GD.N0232.N0719.N1010.d011416,
      _root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_log hdilation] using hg
  let repaired := _root_.GD.N0232.N0720.N1476.d019361 value
  refine ⟨repaired,
    _root_.GD.N0232.N0720.N1476.d019362 value hvalue, ?_,
    _root_.GD.N0232.N0720.N1476.d019363 value hvalueAffine,
    _root_.GD.N0232.N0720.N1476.d019364 value⟩
  have hfixed : _root_.GD.N0232.N0720.N1446.d019032 m n s.value = s.value :=
    _root_.GD.N0232.N0720.N1446.d019040
      m n s hsTerminal
  have hfixedAE :
      (fun omega => -(s.value (_root_.GD.N0232.N0720.N1446.d019019 m n omega))) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega => s.value omega := by
    have hcoe := _root_.GD.N0232.N0720.N1476.d019377 m n s.value
    rw [hfixed] at hcoe
    exact hcoe.symm
  have href :
      (value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega => s.value omega := by
    simpa [_root_.GD.N0232.N0720.N1080.d014172] using hrep _root_.GD.N0232.N0720.N1080.d014169
  have hrefNeg :=
    (_root_.GD.N0232.N0720.N1446.d019031 m n).quasiMeasurePreserving.ae_eq_comp href
  have hvalueReflect :
      (fun omega => -value (_root_.GD.N0232.N0720.N1476.d019350 (_root_.GD.N0232.N0720.N1467.d012542 m n omega))) =ᵐ[
        _root_.GD.N0232.N0720.N1080.d014172 m n] fun omega => s.value omega := by
    filter_upwards [hrefNeg, hfixedAE] with omega hrepAtNeg hfix
    rw [← _root_.GD.N0232.N0720.N1476.d019375 m n (by omega) (by omega) omega]
    exact (congrArg Neg.neg hrepAtNeg).trans hfix
  have hrepairedRef :
      (repaired ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega => s.value omega := by
    filter_upwards [href, hvalueReflect] with omega hone hreflected
    change (value (_root_.GD.N0232.N0720.N1467.d012542 m n omega) -
      value (_root_.GD.N0232.N0720.N1476.d019350 (_root_.GD.N0232.N0720.N1467.d012542 m n omega))) / 2 = s.value omega
    have hreflected' :
        value (_root_.GD.N0232.N0720.N1476.d019350 (_root_.GD.N0232.N0720.N1467.d012542 m n omega)) = -s.value omega := by
      linarith
    have hone' : value (_root_.GD.N0232.N0720.N1467.d012542 m n omega) = s.value omega := by
      simpa only [Function.comp_apply] using hone
    rw [hone', hreflected']
    ring
  intro theta
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le hrepairedRef





theorem d019380
    (n : ℕ) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 n n)
    (hsTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 n n) s.value)
    (hswapProfile : ∀ theta,
      _root_.GD.N0232.N0720.N1080.d014182 n n (_root_.GD.N0232.N0720.N1043.d019058 theta) s.value = _root_.GD.N0232.N0720.N1080.d014182 n n theta s.value) :
    ∃ repaired : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        (repaired ∘ _root_.GD.N0232.N0720.N1467.d012542 n n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 n n theta]
          fun omega => s.value omega) ∧
      _root_.GD.N0232.N0719.N0860.d011447 repaired ∧
      _root_.GD.N0232.N0720.N1209.d012478 repaired ∧
      _root_.GD.N0232.N0720.N1209.d012479 repaired := by
  obtain ⟨value, hvalue, hrep, haffine, hreflection⟩ :=
    _root_.GD.N0232.N0720.N1476.d019379
      n n hn hn s hsTerminal
  let repaired := _root_.GD.N0232.N0720.N1476.d019365 value
  refine ⟨repaired, _root_.GD.N0232.N0720.N1476.d019366 value hvalue,
    ?_, _root_.GD.N0232.N0720.N1476.d019367 value haffine,
    _root_.GD.N0232.N0720.N1476.d019369 value hreflection,
    _root_.GD.N0232.N0720.N1476.d019368 value⟩
  have hfixed : _root_.GD.N0232.N0720.N1043.d019067 n s.value = s.value :=
    _root_.GD.N0232.N0720.N1043.d019073 n s.value
      hswapProfile hsTerminal
  have hfixedAE :
      (fun omega => s.value (_root_.GD.N0232.N0720.N1043.d019054 n omega)) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 n n]
        fun omega => s.value omega := by
    have hcoe := _root_.GD.N0232.N0720.N1476.d019378 n s.value
    rw [hfixed] at hcoe
    exact hcoe.symm
  have href :
      (value ∘ _root_.GD.N0232.N0720.N1467.d012542 n n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 n n]
        fun omega => s.value omega := by
    simpa [_root_.GD.N0232.N0720.N1080.d014172] using hrep _root_.GD.N0232.N0720.N1080.d014169
  have hrefSwap :=
    (_root_.GD.N0232.N0720.N1043.d019066 n).quasiMeasurePreserving.ae_eq_comp href
  have hvalueSwap :
      (fun omega => value (_root_.GD.N0232.N0720.N1476.d019351 (_root_.GD.N0232.N0720.N1467.d012542 n n omega))) =ᵐ[
        _root_.GD.N0232.N0720.N1080.d014172 n n] fun omega => s.value omega := by
    filter_upwards [hrefSwap, hfixedAE] with omega hrepAtSwap hfix
    rw [← _root_.GD.N0232.N0720.N1476.d019376 n omega]
    exact hrepAtSwap.trans hfix
  have hrepairedRef :
      (repaired ∘ _root_.GD.N0232.N0720.N1467.d012542 n n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 n n]
        fun omega => s.value omega := by
    filter_upwards [href, hvalueSwap] with omega hone hswap
    change (value (_root_.GD.N0232.N0720.N1467.d012542 n n omega) +
      value (_root_.GD.N0232.N0720.N1476.d019351 (_root_.GD.N0232.N0720.N1467.d012542 n n omega))) / 2 = s.value omega
    have hone' : value (_root_.GD.N0232.N0720.N1467.d012542 n n omega) = s.value omega := by
      simpa only [Function.comp_apply] using hone
    rw [hone', hswap]
    ring
  intro theta
  exact (_root_.GD.N0232.N0720.N1080.d014173 n n theta).ae_le hrepairedRef



theorem d019381
    (n : ℕ) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 n n)
    (hsTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 n n) s.value)
    (hswapProfile : ∀ theta,
      _root_.GD.N0232.N0720.N1080.d014182 n n (_root_.GD.N0232.N0720.N1043.d019058 theta) s.value = _root_.GD.N0232.N0720.N1080.d014182 n n theta s.value) :
    ∃ repaired : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ, ∃ h : ℝ → ℝ → ℝ,
      Measurable repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        (repaired ∘ _root_.GD.N0232.N0720.N1467.d012542 n n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 n n theta]
          fun omega => s.value omega) ∧
      Measurable (fun p : ℝ × ℝ => h p.1 p.2) ∧
      (∀ r q, h (1 - r) q = 1 - h r q) ∧
      (∀ r, h r 0 = 1 / 2) ∧
      ∀ u v vx vy,
        0 ≤ vx → 0 ≤ vy →
        repaired (_root_.GD.N0232.N0720.N1209.d012458 u v vx vy) =
          _root_.GD.N0232.N0720.N1437.d003016
            h u v vx vy := by
  obtain ⟨repaired, hmeas, hrep, haffine, hreflect, hswap⟩ :=
    _root_.GD.N0232.N0720.N1476.d019380
      n hn s hsTerminal hswapProfile
  obtain ⟨h, hhmeas, hcomplement, hzero, hnormal⟩ :=
    _root_.GD.N0232.N0720.N1041.d012488
      repaired hmeas haffine hreflect hswap
  exact ⟨repaired, h, hmeas, hrep, hhmeas, hcomplement, hzero, hnormal⟩

end
end N1476
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1476.d019379
#print axioms _root_.GD.N0232.N0720.N1476.d019380
#print axioms _root_.GD.N0232.N0720.N1476.d019381
