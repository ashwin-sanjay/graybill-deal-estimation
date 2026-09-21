import GD.Module0848
import GD.Module0846

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0228.N0547.N0792

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0933
open _root_.GD.N0228.N0547.N0778
open _root_.GD.N0228.N0547.N0790
open _root_.GD.N0228.N0547.N0793
open _root_.GD.N0228.N0547.N0781

def d012996 (muX muY : ℝ) : Fin 2 → ℝ := ![muX, muY]

def d012997
    (r s : ℕ) (muX muY sigmaX sigmaY : ℝ) (y : Fin 2 → ℝ) : ℝ :=
  (y 0 - y 1 - (muX - muY)) /
    Real.sqrt (_root_.GD.N0228.N0547.N0793.d012958 r s sigmaX sigmaY)

@[fun_prop]
theorem d012998
    (r s : ℕ) (muX muY sigmaX sigmaY : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0792.d012997 r s muX muY sigmaX sigmaY) := by
  unfold _root_.GD.N0228.N0547.N0792.d012997
  fun_prop

def d012999
    (r s : ℕ) (muX muY sigmaX sigmaY : ℝ)
    (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ × (ℝ × ℝ) :=
  (_root_.GD.N0228.N0547.N0792.d012997 r s muX muY sigmaX sigmaY z.1,
    _root_.GD.N0228.N0547.N0793.d012960 r s sigmaX sigmaY z.2)

@[fun_prop]
theorem d013000
    (r s : ℕ) (muX muY sigmaX sigmaY : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0792.d012999 r s muX muY sigmaX sigmaY) := by
  unfold _root_.GD.N0228.N0547.N0792.d012999
  fun_prop

def d013001
    (r s : ℕ) (muX muY sigmaX sigmaY : ℝ)
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ × (ℝ × ℝ) :=
  (_root_.GD.N0228.N0547.N0792.d012997 r s muX muY sigmaX sigmaY u.mean,
    _root_.GD.N0228.N0547.N0793.d012960 r s sigmaX sigmaY u.meanVariance)

@[fun_prop]
theorem d013002
    (r s : ℕ) (muX muY sigmaX sigmaY : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0792.d013001 r s muX muY sigmaX sigmaY) := by
  unfold _root_.GD.N0228.N0547.N0792.d013001
  fun_prop



theorem d013003
    {muX muY : ℝ} {A B : ℝ≥0}
    (hAB : 0 < (A : ℝ) + (B : ℝ)) :
    ((gaussianReal muX A).prod (gaussianReal muY B)).map
        (fun z : ℝ × ℝ =>
          (z.1 - z.2 - (muX - muY)) /
            Real.sqrt ((A : ℝ) + (B : ℝ))) =
      gaussianReal 0 1 := by
  let P : Measure (ℝ × ℝ) :=
    (gaussianReal muX A).prod (gaussianReal muY B)
  let X : ℝ × ℝ → ℝ := fun z => z.1
  let Y : ℝ × ℝ → ℝ := fun z => -z.2
  have hXY : IndepFun X Y P := by
    exact indepFun_prod (X := id) (Y := fun y : ℝ => -y)
      measurable_id (by fun_prop)
  have hX : P.map X = gaussianReal muX A := by
    exact (MeasurePreserving.hasLaw measurePreserving_fst).map_eq
  have hY : P.map Y = gaussianReal (-muY) B := by
    calc
      P.map Y = (P.map Prod.snd).map (fun y : ℝ => -y) := by
        rw [Measure.map_map (by fun_prop) measurable_snd]
        rfl
      _ = (gaussianReal muY B).map (fun y : ℝ => -y) := by
        rw [measurePreserving_snd.map_eq]
      _ = gaussianReal (-muY) B := gaussianReal_map_neg
  have hdiff := gaussianReal_add_gaussianReal_of_indepFun hXY hX hY
  have hfun : X + Y = fun z : ℝ × ℝ => z.1 - z.2 := by
    funext z
    rfl
  rw [hfun] at hdiff
  have hsqrtSq : Real.sqrt ((A : ℝ) + (B : ℝ)) ^ 2 =
      (A : ℝ) + (B : ℝ) := Real.sq_sqrt hAB.le
  let delta := muX - muY
  let recenter : ℝ → ℝ := fun x => -delta + x
  let normalize : ℝ → ℝ := fun x =>
    x / Real.sqrt ((A : ℝ) + (B : ℝ))
  have hrecenter :
      (gaussianReal delta (A + B)).map recenter = gaussianReal 0 (A + B) := by
    simpa only [recenter, delta, add_neg_cancel] using
      (gaussianReal_map_const_add (μ := delta) (v := A + B) (-delta))
  have hdiff' :
      P.map (fun z : ℝ × ℝ => z.1 - z.2) =
        gaussianReal delta (A + B) := by
    simpa only [delta, sub_eq_add_neg] using hdiff
  have htarget :
      (fun z : ℝ × ℝ =>
        (z.1 - z.2 - (muX - muY)) /
          Real.sqrt ((A : ℝ) + (B : ℝ))) =
        (normalize ∘ recenter) ∘ (fun z : ℝ × ℝ => z.1 - z.2) := by
    funext z
    simp only [Function.comp_apply, normalize, recenter, delta]
    congr 1
    ring
  calc
    P.map (fun z : ℝ × ℝ =>
        (z.1 - z.2 - (muX - muY)) /
          Real.sqrt ((A : ℝ) + (B : ℝ))) =
      P.map ((normalize ∘ recenter) ∘
        (fun z : ℝ × ℝ => z.1 - z.2)) := by rw [htarget]
    _ = (P.map (fun z : ℝ × ℝ => z.1 - z.2)).map
        (normalize ∘ recenter) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = (gaussianReal delta (A + B)).map (normalize ∘ recenter) := by
      rw [hdiff']
    _ = ((gaussianReal delta (A + B)).map recenter).map normalize := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = (gaussianReal 0 (A + B)).map normalize := by rw [hrecenter]
    _ = gaussianReal
        (0 / Real.sqrt ((A : ℝ) + (B : ℝ)))
        ((A + B) /
          .mk (Real.sqrt ((A : ℝ) + (B : ℝ)) ^ 2) (sq_nonneg _)) := by
      simpa only [normalize] using
        (gaussianReal_map_div_const
          (μ := (0 : ℝ)) (v := A + B)
          (Real.sqrt ((A : ℝ) + (B : ℝ))))
    _ = gaussianReal 0 1 := by
      congr 2
      · simp
      · apply NNReal.eq
        simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_mk,
          NNReal.coe_one, hsqrtSq]
        exact div_self hAB.ne'



theorem d013004
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY) :
    (_root_.GD.N0232.N0719.N0897.d009336 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
        (_root_.GD.N0228.N0547.N0792.d012996 muX muY) (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
      (_root_.GD.N0228.N0547.N0792.d012997 r s muX muY sigmaX sigmaY) =
      gaussianReal 0 1 := by
  let lawX : Measure ℝ := _root_.GD.N0232.N0719.N0933.d009288 (r + 1) muX sigmaX
  let lawY : Measure ℝ := _root_.GD.N0232.N0719.N0933.d009288 (s + 1) muY sigmaY
  let e : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.finTwoArrow
  let pairMap : ℝ × ℝ → ℝ := fun z =>
    (z.1 - z.2 - (muX - muY)) /
      Real.sqrt (_root_.GD.N0228.N0547.N0793.d012958 r s sigmaX sigmaY)
  have hsource :
      _root_.GD.N0232.N0719.N0897.d009336 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
          (_root_.GD.N0228.N0547.N0792.d012996 muX muY) (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY) =
        Measure.pi ![lawX, lawY] := by
    unfold _root_.GD.N0232.N0719.N0897.d009336
    congr 1
    funext i
    fin_cases i <;> rfl
  have he : (Measure.pi ![lawX, lawY]).map e = lawX.prod lawY := by
    exact (measurePreserving_finTwoArrow_vec lawX lawY).map_eq
  have hfun : pairMap ∘ e =
      _root_.GD.N0228.N0547.N0792.d012997 r s muX muY sigmaX sigmaY := by
    funext y
    rfl
  have hfirst : 0 < _root_.GD.N0228.N0547.N0793.d012956 r sigmaX := by
    unfold _root_.GD.N0228.N0547.N0793.d012956
    positivity
  have hsecond : 0 < _root_.GD.N0228.N0547.N0793.d012957 s sigmaY := by
    unfold _root_.GD.N0228.N0547.N0793.d012957
    positivity
  let A : ℝ≥0 := ⟨_root_.GD.N0228.N0547.N0793.d012956 r sigmaX, hfirst.le⟩
  let B : ℝ≥0 := ⟨_root_.GD.N0228.N0547.N0793.d012957 s sigmaY, hsecond.le⟩
  have hlawX : lawX = gaussianReal muX A := by
    unfold lawX
    rw [_root_.GD.N0232.N0719.N0933.d009297 (n := r + 1) (by omega) muX sigmaX]
    congr 2
  have hlawY : lawY = gaussianReal muY B := by
    unfold lawY
    rw [_root_.GD.N0232.N0719.N0933.d009297 (n := s + 1) (by omega) muY sigmaY]
    congr 2
  have hAB : 0 < (A : ℝ) + (B : ℝ) := add_pos hfirst hsecond
  calc
    (_root_.GD.N0232.N0719.N0897.d009336 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
        (_root_.GD.N0228.N0547.N0792.d012996 muX muY) (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
      (_root_.GD.N0228.N0547.N0792.d012997 r s muX muY sigmaX sigmaY) =
      ((_root_.GD.N0232.N0719.N0897.d009336 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
        (_root_.GD.N0228.N0547.N0792.d012996 muX muY) (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map e).map pairMap := by
          rw [Measure.map_map (by fun_prop) e.measurable, hfun]
    _ = (lawX.prod lawY).map pairMap := by rw [hsource, he]
    _ = ((gaussianReal muX A).prod (gaussianReal muY B)).map pairMap := by
      rw [hlawX, hlawY]
    _ = gaussianReal 0 1 := by
      convert _root_.GD.N0228.N0547.N0792.d013003
        (muX := muX) (muY := muY) (A := A) (B := B) hAB using 1
      simp only [pairMap, _root_.GD.N0228.N0547.N0793.d012958, A, B]
      rfl



theorem d013005
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY) :
    (_root_.GD.N0232.N0719.N0897.d009340 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
        (_root_.GD.N0228.N0547.N0792.d012996 muX muY) (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
      (_root_.GD.N0228.N0547.N0792.d013001 r s muX muY sigmaX sigmaY) =
      _root_.GD.N0228.N0547.N0790.d012894 r s := by
  let meanLaw := _root_.GD.N0232.N0719.N0897.d009336 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
    (_root_.GD.N0228.N0547.N0792.d012996 muX muY) (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  let varianceLaw := _root_.GD.N0232.N0719.N0933.d009301 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
    (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  have hsizes := _root_.GD.N0228.N0547.N0793.d012972 hr hs
  letI : IsProbabilityMeasure meanLaw := by
    unfold meanLaw _root_.GD.N0232.N0719.N0897.d009336
    infer_instance
  letI (i : Fin 2) : IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0933.d009289 (_root_.GD.N0228.N0547.N0793.d012954 r s i)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY i)) := by
    have hshapeNat : 0 < _root_.GD.N0228.N0547.N0793.d012954 r s i - 1 := by
      have hi := hsizes i
      omega
    have hshapeReal :
        0 < (((_root_.GD.N0228.N0547.N0793.d012954 r s i - 1 : ℕ) : ℝ) / 2) := by
      have : 0 < ((_root_.GD.N0228.N0547.N0793.d012954 r s i - 1 : ℕ) : ℝ) := by
        exact_mod_cast hshapeNat
      positivity
    unfold _root_.GD.N0232.N0719.N0933.d009289
    letI : IsProbabilityMeasure
        (gammaMeasure (((_root_.GD.N0228.N0547.N0793.d012954 r s i - 1 : ℕ) : ℝ) / 2)
          (((_root_.GD.N0228.N0547.N0793.d012954 r s i - 1 : ℕ) : ℝ) / 2)) :=
      isProbabilityMeasure_gammaMeasure hshapeReal hshapeReal
    exact Measure.isProbabilityMeasure_map
      (_root_.GD.N0232.N0719.N0933.d009294 (_root_.GD.N0228.N0547.N0793.d012954 r s i)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY i)).aemeasurable
  letI : IsProbabilityMeasure varianceLaw := by
    unfold varianceLaw _root_.GD.N0232.N0719.N0933.d009301
    infer_instance
  have hmean := _root_.GD.N0228.N0547.N0792.d013004
    hr hs muX muY hsigmaX hsigmaY
  have hvariance := _root_.GD.N0228.N0547.N0793.d012975
    hr hs hsigmaX hsigmaY
  have hproduct :
      (meanLaw.prod varianceLaw).map
          (_root_.GD.N0228.N0547.N0792.d012999 r s muX muY sigmaX sigmaY) =
        _root_.GD.N0228.N0547.N0790.d012894 r s := by
    change (meanLaw.prod varianceLaw).map
      (Prod.map
        (_root_.GD.N0228.N0547.N0792.d012997 r s muX muY sigmaX sigmaY)
        (_root_.GD.N0228.N0547.N0793.d012960 r s sigmaX sigmaY)) = _
    rw [← Measure.map_prod_map meanLaw varianceLaw
      (_root_.GD.N0228.N0547.N0792.d012998 r s muX muY sigmaX sigmaY)
      (_root_.GD.N0228.N0547.N0793.d012964 r s sigmaX sigmaY)]
    rw [hmean, hvariance]
    rfl
  unfold _root_.GD.N0232.N0719.N0897.d009340
  calc
    ((meanLaw.prod varianceLaw).map (_root_.GD.N0232.N0719.N0933.d009305 2)).map
        (_root_.GD.N0228.N0547.N0792.d013001 r s muX muY sigmaX sigmaY) =
      (meanLaw.prod varianceLaw).map
        (_root_.GD.N0228.N0547.N0792.d013001 r s muX muY sigmaX sigmaY ∘
          _root_.GD.N0232.N0719.N0933.d009305 2) := by
        rw [Measure.map_map
          (_root_.GD.N0228.N0547.N0792.d013002 r s muX muY sigmaX sigmaY)
          (_root_.GD.N0232.N0719.N0933.d009306 2)]
    _ = (meanLaw.prod varianceLaw).map
        (_root_.GD.N0228.N0547.N0792.d012999 r s muX muY sigmaX sigmaY) := by
      congr 1
    _ = _root_.GD.N0228.N0547.N0790.d012894 r s := hproduct

def d013006
    (r s : ℕ) (muX muY sigmaX sigmaY : ℝ) (u : _root_.GD.N0232.N0719.N0900.d009096 2) : Fin 3 → ℝ :=
  _root_.GD.N0228.N0547.N0781.d012920
    (_root_.GD.N0228.N0547.N0792.d013001 r s muX muY sigmaX sigmaY u)

@[fun_prop]
theorem d013007
    (r s : ℕ) (muX muY sigmaX sigmaY : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0792.d013006 r s muX muY sigmaX sigmaY) := by
  unfold _root_.GD.N0228.N0547.N0792.d013006
  fun_prop




theorem d013008
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY) :
    (_root_.GD.N0232.N0719.N0897.d009340 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
        (_root_.GD.N0228.N0547.N0792.d012996 muX muY) (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
      (_root_.GD.N0228.N0547.N0792.d013006 r s muX muY sigmaX sigmaY) =
      _root_.GD.N0235.d004250
        (1 / 2) ((r : ℝ) / 2) ((s : ℝ) / 2) := by
  let summarySource := _root_.GD.N0232.N0719.N0897.d009340 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
    (_root_.GD.N0228.N0547.N0792.d012996 muX muY) (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  let baseMap := _root_.GD.N0228.N0547.N0792.d013001 r s muX muY sigmaX sigmaY
  have hbase : summarySource.map baseMap = _root_.GD.N0228.N0547.N0790.d012894 r s :=
    _root_.GD.N0228.N0547.N0792.d013005
      hr hs muX muY hsigmaX hsigmaY
  calc
    summarySource.map
        (_root_.GD.N0228.N0547.N0792.d013006 r s muX muY sigmaX sigmaY) =
      (summarySource.map baseMap).map _root_.GD.N0228.N0547.N0781.d012920 := by
        rw [Measure.map_map _root_.GD.N0228.N0547.N0781.d012921
          (_root_.GD.N0228.N0547.N0792.d013002
            r s muX muY sigmaX sigmaY)]
        rfl
    _ = (_root_.GD.N0228.N0547.N0781.d012916 r s).map _root_.GD.N0228.N0547.N0781.d012920 := by
      rw [hbase]
      rfl
    _ = _root_.GD.N0235.d004250
        (1 / 2) ((r : ℝ) / 2) ((s : ℝ) / 2) :=
      _root_.GD.N0228.N0547.N0781.d012922 hr hs





def d013009
    (r s : ℕ) (muX muY sigmaX sigmaY : ℝ)
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ × ℝ :=
  _root_.GD.N0228.N0547.N0787.d012939
    (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY)
    (_root_.GD.N0228.N0547.N0792.d013001 r s muX muY sigmaX sigmaY u)




def d013010
    (r s : ℕ) (delta : ℝ) (u : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ × ℝ :=
  let D := (r : ℝ) * u.meanVariance 0 +
    (s : ℝ) * u.meanVariance 1
  (((u.mean 0 - u.mean 1) - delta) ^ 2 / D,
    (r : ℝ) * u.meanVariance 0 / D)

@[fun_prop]
theorem d013011
    (r s : ℕ) (muX muY sigmaX sigmaY : ℝ) :
    Measurable
      (_root_.GD.N0228.N0547.N0792.d013009 r s muX muY sigmaX sigmaY) := by
  unfold _root_.GD.N0228.N0547.N0792.d013009
  fun_prop

@[fun_prop]
theorem d013012
    (r s : ℕ) (delta : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0792.d013010 r s delta) := by
  unfold _root_.GD.N0228.N0547.N0792.d013010
  fun_prop

private theorem d013013
    {x y c : ℝ} (hc : c ≠ 0) :
    (x / c) / (y / c) = x / y := by
  by_cases hy : y = 0
  · simp [hy]
  · field_simp




theorem d013014
    {r s : ℕ} {muX muY sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) :
    _root_.GD.N0228.N0547.N0792.d013009 r s muX muY sigmaX sigmaY u =
      _root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY) u := by
  let A := _root_.GD.N0228.N0547.N0793.d012956 r sigmaX
  let B := _root_.GD.N0228.N0547.N0793.d012957 s sigmaY
  let S := _root_.GD.N0228.N0547.N0793.d012958 r s sigmaX sigmaY
  let D := (r : ℝ) * u.meanVariance 0 +
    (s : ℝ) * u.meanVariance 1
  let X := u.mean 0 - u.mean 1 - (muX - muY)
  have hA : 0 < A := by
    unfold A _root_.GD.N0228.N0547.N0793.d012956
    positivity
  have hB : 0 < B := by
    unfold B _root_.GD.N0228.N0547.N0793.d012957
    positivity
  have hS : 0 < S := by
    unfold S _root_.GD.N0228.N0547.N0793.d012958
    exact add_pos hA hB
  have hSAB : S = A + B := by
    rfl
  have hsqrtSq : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS.le
  have hden :
      _root_.GD.N0228.N0547.N0787.d012938 (A / S)
        (X / Real.sqrt S,
          (((r : ℝ) / A) * u.meanVariance 0,
            ((s : ℝ) / B) * u.meanVariance 1)) = D / S := by
    unfold _root_.GD.N0228.N0547.N0787.d012938 D
    rw [hSAB]
    field_simp [hA.ne', hB.ne']
    ring
  have hnum :
      (A / S) * (((r : ℝ) / A) * u.meanVariance 0) =
        ((r : ℝ) * u.meanVariance 0) / S := by
    field_simp [hA.ne', hS.ne']
  have hzsq :
      (X / Real.sqrt S) ^ 2 = X ^ 2 / S := by
    rw [div_pow, hsqrtSq]
  change
    ((X / Real.sqrt S) ^ 2 /
        _root_.GD.N0228.N0547.N0787.d012938 (A / S)
          (X / Real.sqrt S,
            (((r : ℝ) / A) * u.meanVariance 0,
              ((s : ℝ) / B) * u.meanVariance 1)),
      (A / S) * (((r : ℝ) / A) * u.meanVariance 0) /
        _root_.GD.N0228.N0547.N0787.d012938 (A / S)
          (X / Real.sqrt S,
            (((r : ℝ) / A) * u.meanVariance 0,
              ((s : ℝ) / B) * u.meanVariance 1))) =
      (X ^ 2 / D,
        (r : ℝ) * u.meanVariance 0 / D)
  rw [hden, hnum, hzsq,
    _root_.GD.N0228.N0547.N0792.d013013 hS.ne', _root_.GD.N0228.N0547.N0792.d013013 hS.ne']



theorem d013015
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY) :
    (_root_.GD.N0232.N0719.N0897.d009340 2
        (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
      (_root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY)) =
      _root_.GD.N0228.N0547.N0787.d012941 r s
        (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY) := by
  let P := _root_.GD.N0232.N0719.N0897.d009340 2
    (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
    (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  let rho := _root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY
  let baseMap :=
    _root_.GD.N0228.N0547.N0792.d013001 r s muX muY sigmaX sigmaY
  have hbase : P.map baseMap = _root_.GD.N0228.N0547.N0790.d012894 r s :=
    _root_.GD.N0228.N0547.N0792.d013005
      hr hs muX muY hsigmaX hsigmaY
  have hfun :
      _root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY) =
        _root_.GD.N0228.N0547.N0787.d012939 rho ∘ baseMap := by
    funext u
    exact (_root_.GD.N0228.N0547.N0792.d013014
      hsigmaX hsigmaY u).symm
  change P.map (_root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY)) = _
  calc
    P.map (_root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY)) =
        P.map (_root_.GD.N0228.N0547.N0787.d012939 rho ∘ baseMap) := by
      rw [hfun]
    _ = (P.map baseMap).map
        (_root_.GD.N0228.N0547.N0787.d012939 rho) := by
      rw [Measure.map_map
        (_root_.GD.N0228.N0547.N0787.d012940 rho)
        (_root_.GD.N0228.N0547.N0792.d013002
          r s muX muY sigmaX sigmaY)]
    _ = (_root_.GD.N0228.N0547.N0790.d012894 r s).map
        (_root_.GD.N0228.N0547.N0787.d012939 rho) := by
      rw [hbase]
    _ = _root_.GD.N0228.N0547.N0787.d012941 r s rho := rfl




theorem d013016
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∫⁻ u, ENNReal.ofReal
        (_root_.GD.N0228.N0547.N0787.d012935
          r s p
          (_root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY) u))
      ∂(_root_.GD.N0232.N0719.N0897.d009340 2
        (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)) = ENNReal.ofReal p := by
  let P := _root_.GD.N0232.N0719.N0897.d009340 2
    (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
    (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  let rho := _root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY
  let g := _root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY)
  let f : ℝ × ℝ → ℝ≥0∞ := fun tx => ENNReal.ofReal
    (_root_.GD.N0228.N0547.N0787.d012935
      r s p tx)
  have hf : Measurable f :=
    (_root_.GD.N0228.N0547.N0787.d012936
      hr hs p).ennreal_ofReal
  have hg : Measurable g :=
    _root_.GD.N0228.N0547.N0792.d013012 r s (muX - muY)
  have hmap : P.map g =
      _root_.GD.N0228.N0547.N0787.d012941 r s rho :=
    _root_.GD.N0228.N0547.N0792.d013015
      hr hs muX muY hsigmaX hsigmaY
  have hrho0 : 0 < rho :=
    _root_.GD.N0228.N0547.N0793.d012979 (r := r) (s := s) hsigmaX hsigmaY
  have hrho1 : rho < 1 :=
    _root_.GD.N0228.N0547.N0793.d012980 (r := r) (s := s) hsigmaX hsigmaY
  change ∫⁻ u, f (g u) ∂P = ENNReal.ofReal p
  calc
    ∫⁻ u, f (g u) ∂P = ∫⁻ tx, f tx ∂(P.map g) := by
      exact (lintegral_map hf hg).symm
    _ = ∫⁻ tx, ENNReal.ofReal
        (_root_.GD.N0228.N0547.N0787.d012935
          r s p tx)
        ∂(_root_.GD.N0228.N0547.N0787.d012941 r s rho) := by
      rw [hmap]
    _ = ENNReal.ofReal p :=
      _root_.GD.N0228.N0547.N0787.d012953
        hr hs hrho0 hrho1 hp0 hp1



theorem d013017
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY) :
    (_root_.GD.N0232.N0719.N0897.d009332
        2 (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
      (_root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY) ∘
        _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)) =
      _root_.GD.N0228.N0547.N0787.d012941 r s
        (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY) := by
  let P :=
    _root_.GD.N0232.N0719.N0897.d009332
      2 (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
      (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  let g := _root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY)
  have hsizes := _root_.GD.N0228.N0547.N0793.d012972 hr hs
  calc
    P.map (g ∘ _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)) =
        (P.map (_root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s))).map g := by
      rw [Measure.map_map
        (_root_.GD.N0228.N0547.N0792.d013012
          r s (muX - muY))
        (_root_.GD.N0232.N0719.N0900.d009115 2 (_root_.GD.N0228.N0547.N0793.d012954 r s))]
    _ = (_root_.GD.N0232.N0719.N0897.d009340 2
          (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
          (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map g := by
      rw [_root_.GD.N0232.N0719.N0897.d009341
        2 (_root_.GD.N0228.N0547.N0793.d012954 r s) hsizes
        (_root_.GD.N0228.N0547.N0792.d012996 muX muY) (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)]
    _ = _root_.GD.N0228.N0547.N0787.d012941 r s
        (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY) :=
      _root_.GD.N0228.N0547.N0792.d013015
        hr hs muX muY hsigmaX hsigmaY



theorem d013018
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∫⁻ omega, ENNReal.ofReal
        (_root_.GD.N0228.N0547.N0787.d012935
          r s p
          (_root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY)
            (_root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) omega)))
      ∂(_root_.GD.N0232.N0719.N0897.d009332
        2 (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)) = ENNReal.ofReal p := by
  let P :=
    _root_.GD.N0232.N0719.N0897.d009332
      2 (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
      (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  let rho := _root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY
  let g := _root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY) ∘
    _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
  let f : ℝ × ℝ → ℝ≥0∞ := fun tx => ENNReal.ofReal
    (_root_.GD.N0228.N0547.N0787.d012935
      r s p tx)
  have hf : Measurable f :=
    (_root_.GD.N0228.N0547.N0787.d012936
      hr hs p).ennreal_ofReal
  have hg : Measurable g :=
    (_root_.GD.N0228.N0547.N0792.d013012 r s (muX - muY)).comp
      (_root_.GD.N0232.N0719.N0900.d009115 2 (_root_.GD.N0228.N0547.N0793.d012954 r s))
  have hmap : P.map g =
      _root_.GD.N0228.N0547.N0787.d012941 r s rho :=
    _root_.GD.N0228.N0547.N0792.d013017
      hr hs muX muY hsigmaX hsigmaY
  have hrho0 : 0 < rho :=
    _root_.GD.N0228.N0547.N0793.d012979 (r := r) (s := s) hsigmaX hsigmaY
  have hrho1 : rho < 1 :=
    _root_.GD.N0228.N0547.N0793.d012980 (r := r) (s := s) hsigmaX hsigmaY
  change ∫⁻ omega, f (g omega) ∂P = ENNReal.ofReal p
  calc
    ∫⁻ omega, f (g omega) ∂P = ∫⁻ tx, f tx ∂(P.map g) := by
      exact (lintegral_map hf hg).symm
    _ = ∫⁻ tx, ENNReal.ofReal
        (_root_.GD.N0228.N0547.N0787.d012935
          r s p tx)
        ∂(_root_.GD.N0228.N0547.N0787.d012941 r s rho) := by
      rw [hmap]
    _ = ENNReal.ofReal p :=
      _root_.GD.N0228.N0547.N0787.d012953
        hr hs hrho0 hrho1 hp0 hp1





def d013019 (b : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {tx | tx.1 ≤ b tx.2}

theorem d013020
    {b : ℝ → ℝ} (hb : Measurable b) :
    MeasurableSet (_root_.GD.N0228.N0547.N0792.d013019 b) := by
  exact measurableSet_le measurable_fst (hb.comp measurable_snd)




def d013021
    (r s : ℕ) (p : ℝ) (b : ℝ → ℝ) : Prop :=
  Measurable b ∧
    ∀ rho ∈ Set.Ioo (0 : ℝ) 1,
      _root_.GD.N0228.N0547.N0787.d012941 r s rho
        (_root_.GD.N0228.N0547.N0792.d013019 b) = ENNReal.ofReal p





theorem d013022
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    {p : ℝ} {b : ℝ → ℝ}
    (hcert : _root_.GD.N0228.N0547.N0792.d013021 r s p b) :
    (_root_.GD.N0232.N0719.N0897.d009340 2
      (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
      (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY))
      {u | _root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY) u ∈
        _root_.GD.N0228.N0547.N0792.d013019 b} = ENNReal.ofReal p := by
  let P := _root_.GD.N0232.N0719.N0897.d009340 2
    (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
    (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  let rho := _root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY
  let g := _root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY)
  let E := _root_.GD.N0228.N0547.N0792.d013019 b
  have hg : Measurable g :=
    _root_.GD.N0228.N0547.N0792.d013012 r s (muX - muY)
  have hE : MeasurableSet E :=
    _root_.GD.N0228.N0547.N0792.d013020 hcert.1
  have hmap : P.map g =
      _root_.GD.N0228.N0547.N0787.d012941 r s rho :=
    _root_.GD.N0228.N0547.N0792.d013015
      hr hs muX muY hsigmaX hsigmaY
  have hrho0 : 0 < rho :=
    _root_.GD.N0228.N0547.N0793.d012979 (r := r) (s := s) hsigmaX hsigmaY
  have hrho1 : rho < 1 :=
    _root_.GD.N0228.N0547.N0793.d012980 (r := r) (s := s) hsigmaX hsigmaY
  change P (g ⁻¹' E) = ENNReal.ofReal p
  calc
    P (g ⁻¹' E) = (P.map g) E :=
      (Measure.map_apply hg hE).symm
    _ = _root_.GD.N0228.N0547.N0787.d012941 r s rho E := by
      rw [hmap]
    _ = ENNReal.ofReal p := hcert.2 rho ⟨hrho0, hrho1⟩


theorem d013023
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    {p : ℝ} {b : ℝ → ℝ}
    (hcert : _root_.GD.N0228.N0547.N0792.d013021 r s p b) :
    (_root_.GD.N0232.N0719.N0897.d009332
      2 (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
      (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY))
      {omega |
        _root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY)
          (_root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) omega) ∈
            _root_.GD.N0228.N0547.N0792.d013019 b} = ENNReal.ofReal p := by
  let P :=
    _root_.GD.N0232.N0719.N0897.d009332
      2 (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
      (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  let rho := _root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY
  let g := _root_.GD.N0228.N0547.N0792.d013010 r s (muX - muY) ∘
    _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
  let E := _root_.GD.N0228.N0547.N0792.d013019 b
  have hg : Measurable g :=
    (_root_.GD.N0228.N0547.N0792.d013012 r s (muX - muY)).comp
      (_root_.GD.N0232.N0719.N0900.d009115 2 (_root_.GD.N0228.N0547.N0793.d012954 r s))
  have hE : MeasurableSet E :=
    _root_.GD.N0228.N0547.N0792.d013020 hcert.1
  have hmap : P.map g =
      _root_.GD.N0228.N0547.N0787.d012941 r s rho :=
    _root_.GD.N0228.N0547.N0792.d013017
      hr hs muX muY hsigmaX hsigmaY
  have hrho0 : 0 < rho :=
    _root_.GD.N0228.N0547.N0793.d012979 (r := r) (s := s) hsigmaX hsigmaY
  have hrho1 : rho < 1 :=
    _root_.GD.N0228.N0547.N0793.d012980 (r := r) (s := s) hsigmaX hsigmaY
  change P (g ⁻¹' E) = ENNReal.ofReal p
  calc
    P (g ⁻¹' E) = (P.map g) E :=
      (Measure.map_apply hg hE).symm
    _ = _root_.GD.N0228.N0547.N0787.d012941 r s rho E := by
      rw [hmap]
    _ = ENNReal.ofReal p := hcert.2 rho ⟨hrho0, hrho1⟩

end

end GD.N0228.N0547.N0792

#print axioms _root_.GD.N0228.N0547.N0792.d013003
#print axioms _root_.GD.N0228.N0547.N0792.d013005
#print axioms _root_.GD.N0228.N0547.N0792.d013008
#print axioms _root_.GD.N0228.N0547.N0792.d013014
#print axioms _root_.GD.N0228.N0547.N0792.d013015
#print axioms _root_.GD.N0228.N0547.N0792.d013016
#print axioms _root_.GD.N0228.N0547.N0792.d013017
#print axioms _root_.GD.N0228.N0547.N0792.d013018
#print axioms _root_.GD.N0228.N0547.N0792.d013022
#print axioms _root_.GD.N0228.N0547.N0792.d013023
