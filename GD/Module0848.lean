import GD.Module0639
import GD.Module0640
import GD.Module0847
import GD.Module0842

set_option autoImplicit false
set_option warningAsError true

















open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0228.N0547.N0793

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0933
open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0228.N0547.N0778
open _root_.GD.N0228.N0547.N0790
open _root_.GD.N0228.N0547.N0791
open _root_.GD.N0228.N0547.N0787




def d012954 (r s : ℕ) : Fin 2 → ℕ := ![r + 1, s + 1]


def d012955 (sigmaX sigmaY : ℝ) : Fin 2 → ℝ := ![sigmaX, sigmaY]


def d012956 (r : ℕ) (sigmaX : ℝ) : ℝ :=
  sigmaX ^ 2 / ((r + 1 : ℕ) : ℝ)


def d012957 (s : ℕ) (sigmaY : ℝ) : ℝ :=
  sigmaY ^ 2 / ((s + 1 : ℕ) : ℝ)


def d012958 (r s : ℕ) (sigmaX sigmaY : ℝ) : ℝ :=
  _root_.GD.N0228.N0547.N0793.d012956 r sigmaX + _root_.GD.N0228.N0547.N0793.d012957 s sigmaY


def d012959
    (r s : ℕ) (sigmaX sigmaY : ℝ) (y : Fin 2 → ℝ) : ℝ :=
  (y 0 - y 1) / Real.sqrt (_root_.GD.N0228.N0547.N0793.d012958 r s sigmaX sigmaY)



def d012960
    (r s : ℕ) (sigmaX sigmaY : ℝ) (t : Fin 2 → ℝ) : ℝ × ℝ :=
  (((r : ℝ) / _root_.GD.N0228.N0547.N0793.d012956 r sigmaX) * t 0,
    ((s : ℝ) / _root_.GD.N0228.N0547.N0793.d012957 s sigmaY) * t 1)



def d012961
    (r s : ℕ) (sigmaX sigmaY : ℝ)
    (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ × (ℝ × ℝ) :=
  (_root_.GD.N0228.N0547.N0793.d012959 r s sigmaX sigmaY z.1,
    _root_.GD.N0228.N0547.N0793.d012960 r s sigmaX sigmaY z.2)



def d012962
    (r s : ℕ) (sigmaX sigmaY : ℝ) (u : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ × (ℝ × ℝ) :=
  (_root_.GD.N0228.N0547.N0793.d012959 r s sigmaX sigmaY u.mean,
    _root_.GD.N0228.N0547.N0793.d012960 r s sigmaX sigmaY u.meanVariance)

@[fun_prop]
theorem d012963
    (r s : ℕ) (sigmaX sigmaY : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0793.d012959 r s sigmaX sigmaY) := by
  unfold _root_.GD.N0228.N0547.N0793.d012959
  fun_prop

@[fun_prop]
theorem d012964
    (r s : ℕ) (sigmaX sigmaY : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0793.d012960 r s sigmaX sigmaY) := by
  unfold _root_.GD.N0228.N0547.N0793.d012960
  fun_prop

@[fun_prop]
theorem d012965
    (r s : ℕ) (sigmaX sigmaY : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0793.d012961 r s sigmaX sigmaY) := by
  unfold _root_.GD.N0228.N0547.N0793.d012961
  fun_prop

@[fun_prop]
theorem d012966
    (r s : ℕ) (sigmaX sigmaY : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0793.d012962 r s sigmaX sigmaY) := by
  unfold _root_.GD.N0228.N0547.N0793.d012962
  fun_prop





theorem d012967
    {theta : ℝ} {A B : ℝ≥0}
    (hAB : 0 < (A : ℝ) + (B : ℝ)) :
    ((gaussianReal theta A).prod (gaussianReal theta B)).map
        (fun z : ℝ × ℝ =>
          (z.1 - z.2) / Real.sqrt ((A : ℝ) + (B : ℝ))) =
      gaussianReal 0 1 := by
  let P : Measure (ℝ × ℝ) :=
    (gaussianReal theta A).prod (gaussianReal theta B)
  let X : ℝ × ℝ → ℝ := fun z => z.1
  let Y : ℝ × ℝ → ℝ := fun z => -z.2
  have hXY : IndepFun X Y P := by
    exact indepFun_prod (X := id) (Y := fun y : ℝ => -y)
      measurable_id (by fun_prop)
  have hX : P.map X = gaussianReal theta A := by
    exact (MeasurePreserving.hasLaw measurePreserving_fst).map_eq
  have hY : P.map Y = gaussianReal (-theta) B := by
    calc
      P.map Y = (P.map Prod.snd).map (fun y : ℝ => -y) := by
        rw [Measure.map_map (by fun_prop) measurable_snd]
        rfl
      _ = (gaussianReal theta B).map (fun y : ℝ => -y) := by
        rw [measurePreserving_snd.map_eq]
      _ = gaussianReal (-theta) B := gaussianReal_map_neg
  have hdiff := gaussianReal_add_gaussianReal_of_indepFun hXY hX hY
  have hfun : X + Y = fun z : ℝ × ℝ => z.1 - z.2 := by
    funext z
    rfl
  rw [hfun] at hdiff
  have hsqrt : 0 < Real.sqrt ((A : ℝ) + (B : ℝ)) :=
    Real.sqrt_pos.2 hAB
  have hsqrtSq : Real.sqrt ((A : ℝ) + (B : ℝ)) ^ 2 =
      (A : ℝ) + (B : ℝ) := Real.sq_sqrt hAB.le
  calc
    P.map (fun z : ℝ × ℝ =>
        (z.1 - z.2) / Real.sqrt ((A : ℝ) + (B : ℝ))) =
      (P.map (fun z : ℝ × ℝ => z.1 - z.2)).map
        (fun x : ℝ => x / Real.sqrt ((A : ℝ) + (B : ℝ))) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = (gaussianReal 0 (A + B)).map
        (fun x : ℝ => x / Real.sqrt ((A : ℝ) + (B : ℝ))) := by
          rw [hdiff]
          simp only [add_neg_cancel]
    _ = gaussianReal
        (0 / Real.sqrt ((A : ℝ) + (B : ℝ)))
        ((A + B) /
          .mk (Real.sqrt ((A : ℝ) + (B : ℝ)) ^ 2) (sq_nonneg _)) := by
          simpa only [] using
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

@[simp]
theorem d012968 (r s : ℕ) : _root_.GD.N0228.N0547.N0793.d012954 r s 0 = r + 1 := by
  rfl

@[simp]
theorem d012969 (r s : ℕ) : _root_.GD.N0228.N0547.N0793.d012954 r s 1 = s + 1 := by
  rfl

@[simp]
theorem d012970 (sigmaX sigmaY : ℝ) :
    _root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY 0 = sigmaX := by
  rfl

@[simp]
theorem d012971 (sigmaX sigmaY : ℝ) :
    _root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY 1 = sigmaY := by
  rfl

theorem d012972
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ∀ i, 2 ≤ _root_.GD.N0228.N0547.N0793.d012954 r s i := by
  intro i
  fin_cases i <;> simp [_root_.GD.N0228.N0547.N0793.d012954] <;> omega



theorem d012973
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {sigmaX sigmaY : ℝ} (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    (theta : ℝ) :
    (_root_.GD.N0232.N0719.N0933.d009300 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
          (_root_.GD.N0228.N0547.N0793.d012959 r s sigmaX sigmaY) =
      gaussianReal 0 1 := by
  let muX : Measure ℝ := _root_.GD.N0232.N0719.N0933.d009288 (r + 1) theta sigmaX
  let muY : Measure ℝ := _root_.GD.N0232.N0719.N0933.d009288 (s + 1) theta sigmaY
  let e : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.finTwoArrow
  let pairDifference : ℝ × ℝ → ℝ := fun z =>
    (z.1 - z.2) / Real.sqrt (_root_.GD.N0228.N0547.N0793.d012958 r s sigmaX sigmaY)
  have hsource :
      _root_.GD.N0232.N0719.N0933.d009300 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
          (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY) =
        Measure.pi ![muX, muY] := by
    unfold _root_.GD.N0232.N0719.N0933.d009300
    congr 1
    funext i
    fin_cases i <;> rfl
  have he :
      (Measure.pi ![muX, muY]).map e = muX.prod muY := by
    exact (measurePreserving_finTwoArrow_vec muX muY).map_eq
  have hfun :
      pairDifference ∘ e =
        _root_.GD.N0228.N0547.N0793.d012959 r s sigmaX sigmaY := by
    funext y
    rfl
  have hfirstPos : 0 < _root_.GD.N0228.N0547.N0793.d012956 r sigmaX := by
    unfold _root_.GD.N0228.N0547.N0793.d012956
    positivity
  have hsecondPos : 0 < _root_.GD.N0228.N0547.N0793.d012957 s sigmaY := by
    unfold _root_.GD.N0228.N0547.N0793.d012957
    positivity
  let A : ℝ≥0 :=
    ⟨_root_.GD.N0228.N0547.N0793.d012956 r sigmaX, hfirstPos.le⟩
  let B : ℝ≥0 :=
    ⟨_root_.GD.N0228.N0547.N0793.d012957 s sigmaY, hsecondPos.le⟩
  have hmuX : muX = gaussianReal theta A := by
    unfold muX
    rw [_root_.GD.N0232.N0719.N0933.d009297
      (n := r + 1) (by omega) theta sigmaX]
    congr 2
  have hmuY : muY = gaussianReal theta B := by
    unfold muY
    rw [_root_.GD.N0232.N0719.N0933.d009297
      (n := s + 1) (by omega) theta sigmaY]
    congr 2
  have hAB : 0 < (A : ℝ) + (B : ℝ) := by
    exact add_pos hfirstPos hsecondPos
  calc
    (_root_.GD.N0232.N0719.N0933.d009300 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
          (_root_.GD.N0228.N0547.N0793.d012959 r s sigmaX sigmaY) =
      ((_root_.GD.N0232.N0719.N0933.d009300 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map e).map pairDifference := by
          rw [Measure.map_map (by fun_prop) e.measurable, hfun]
    _ = (muX.prod muY).map pairDifference := by
      rw [hsource, he]
    _ = ((gaussianReal theta A).prod
        (gaussianReal theta B)).map pairDifference := by
      rw [hmuX, hmuY]
    _ = gaussianReal 0 1 := by
      convert
        (_root_.GD.N0228.N0547.N0793.d012967
          (theta := theta) (A := A) (B := B) hAB) using 1
      simp only [pairDifference, _root_.GD.N0228.N0547.N0793.d012958, A, B]
      rfl





theorem d012974
    {d : ℕ} (hd : 0 < d) {sigma : ℝ} (hsigma : 0 < sigma) :
    (_root_.GD.N0232.N0719.N0933.d009289 (d + 1) sigma).map
        (fun t : ℝ =>
          ((d : ℝ) / _root_.GD.N0228.N0547.N0793.d012956 d sigma) * t) =
      _root_.GD.N0228.N0547.N0778.d009365 d := by
  have hvariance : 0 < _root_.GD.N0228.N0547.N0793.d012956 d sigma := by
    unfold _root_.GD.N0228.N0547.N0793.d012956
    positivity
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hshape : 0 < (d : ℝ) / 2 := by positivity
  have hfun :
      (fun t : ℝ => ((d : ℝ) / _root_.GD.N0228.N0547.N0793.d012956 d sigma) * t) ∘
          _root_.GD.N0232.N0719.N0933.d009287 (d + 1) sigma =
        fun q : ℝ => (d : ℝ) * q := by
    funext q
    change
      ((d : ℝ) / _root_.GD.N0228.N0547.N0793.d012956 d sigma) *
          ((sigma ^ 2 / ((d + 1 : ℕ) : ℝ)) * q) =
        (d : ℝ) * q
    unfold _root_.GD.N0228.N0547.N0793.d012956
    field_simp [hvariance.ne']
  calc
    (_root_.GD.N0232.N0719.N0933.d009289 (d + 1) sigma).map
        (fun t : ℝ =>
          ((d : ℝ) / _root_.GD.N0228.N0547.N0793.d012956 d sigma) * t) =
      (gammaMeasure ((((d + 1) - 1 : ℕ) : ℝ) / 2)
        ((((d + 1) - 1 : ℕ) : ℝ) / 2)).map
          ((fun t : ℝ =>
            ((d : ℝ) / _root_.GD.N0228.N0547.N0793.d012956 d sigma) * t) ∘
              _root_.GD.N0232.N0719.N0933.d009287 (d + 1) sigma) := by
        unfold _root_.GD.N0232.N0719.N0933.d009289
        rw [Measure.map_map (by fun_prop)
          (_root_.GD.N0232.N0719.N0933.d009294 (d + 1) sigma)]
    _ = (gammaMeasure ((d : ℝ) / 2) ((d : ℝ) / 2)).map
          (fun q : ℝ => (d : ℝ) * q) := by
      rw [hfun]
      simp only [Nat.add_sub_cancel]
    _ = gammaMeasure ((d : ℝ) / 2) (((d : ℝ) / 2) / (d : ℝ)) := by
      exact _root_.GD.N0232.N0719.N0954.d009354 hshape hshape hdR
    _ = _root_.GD.N0228.N0547.N0778.d009365 d := by
      have hrate : ((d : ℝ) / 2) / (d : ℝ) = 1 / 2 := by
        field_simp [hdR.ne']
      unfold _root_.GD.N0228.N0547.N0778.d009365
      rw [hrate]



theorem d012975
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {sigmaX sigmaY : ℝ} (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY) :
    (_root_.GD.N0232.N0719.N0933.d009301 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
          (_root_.GD.N0228.N0547.N0793.d012960 r s sigmaX sigmaY) =
      (_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s) := by
  let nuX : Measure ℝ := _root_.GD.N0232.N0719.N0933.d009289 (r + 1) sigmaX
  let nuY : Measure ℝ := _root_.GD.N0232.N0719.N0933.d009289 (s + 1) sigmaY
  let e : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.finTwoArrow
  let scaleX : ℝ → ℝ := fun t =>
    ((r : ℝ) / _root_.GD.N0228.N0547.N0793.d012956 r sigmaX) * t
  let scaleY : ℝ → ℝ := fun t =>
    ((s : ℝ) / _root_.GD.N0228.N0547.N0793.d012957 s sigmaY) * t
  letI : IsProbabilityMeasure nuX := by
    unfold nuX _root_.GD.N0232.N0719.N0933.d009289
    have hshape : 0 < (((r + 1 - 1 : ℕ) : ℝ) / 2) := by
      simp only [Nat.add_sub_cancel]
      positivity
    letI : IsProbabilityMeasure
        (gammaMeasure (((r + 1 - 1 : ℕ) : ℝ) / 2)
          (((r + 1 - 1 : ℕ) : ℝ) / 2)) :=
      isProbabilityMeasure_gammaMeasure hshape hshape
    exact Measure.isProbabilityMeasure_map
      (_root_.GD.N0232.N0719.N0933.d009294 (r + 1) sigmaX).aemeasurable
  letI : IsProbabilityMeasure nuY := by
    unfold nuY _root_.GD.N0232.N0719.N0933.d009289
    have hshape : 0 < (((s + 1 - 1 : ℕ) : ℝ) / 2) := by
      simp only [Nat.add_sub_cancel]
      positivity
    letI : IsProbabilityMeasure
        (gammaMeasure (((s + 1 - 1 : ℕ) : ℝ) / 2)
          (((s + 1 - 1 : ℕ) : ℝ) / 2)) :=
      isProbabilityMeasure_gammaMeasure hshape hshape
    exact Measure.isProbabilityMeasure_map
      (_root_.GD.N0232.N0719.N0933.d009294 (s + 1) sigmaY).aemeasurable
  have hsource :
      _root_.GD.N0232.N0719.N0933.d009301 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
          (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY) = Measure.pi ![nuX, nuY] := by
    unfold _root_.GD.N0232.N0719.N0933.d009301
    congr 1
    funext i
    fin_cases i <;> rfl
  have he : (Measure.pi ![nuX, nuY]).map e = nuX.prod nuY := by
    exact (measurePreserving_finTwoArrow_vec nuX nuY).map_eq
  have hfun :
      Prod.map scaleX scaleY ∘ e =
        _root_.GD.N0228.N0547.N0793.d012960 r s sigmaX sigmaY := by
    funext t
    rfl
  have hX : nuX.map scaleX = _root_.GD.N0228.N0547.N0778.d009365 r := by
    simpa only [nuX, scaleX] using
      (_root_.GD.N0228.N0547.N0793.d012974 hr hsigmaX)
  have hY : nuY.map scaleY = _root_.GD.N0228.N0547.N0778.d009365 s := by
    simpa only [nuY, scaleY, _root_.GD.N0228.N0547.N0793.d012956, _root_.GD.N0228.N0547.N0793.d012957] using
      (_root_.GD.N0228.N0547.N0793.d012974 hs hsigmaY)
  have hscaleXMeas : Measurable scaleX := by
    dsimp only [scaleX]
    fun_prop
  have hscaleYMeas : Measurable scaleY := by
    dsimp only [scaleY]
    fun_prop
  calc
    (_root_.GD.N0232.N0719.N0933.d009301 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
          (_root_.GD.N0228.N0547.N0793.d012960 r s sigmaX sigmaY) =
      ((_root_.GD.N0232.N0719.N0933.d009301 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map e).map
          (Prod.map scaleX scaleY) := by
            rw [Measure.map_map (by fun_prop) e.measurable, hfun]
    _ = (nuX.prod nuY).map (Prod.map scaleX scaleY) := by
      rw [hsource, he]
    _ = (nuX.map scaleX).prod (nuY.map scaleY) := by
      exact (Measure.map_prod_map nuX nuY hscaleXMeas hscaleYMeas).symm
    _ = (_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s) := by
      rw [hX, hY]






theorem d012976
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {sigmaX sigmaY : ℝ} (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    (theta : ℝ) :
    ((_root_.GD.N0232.N0719.N0933.d009300 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).prod
      (_root_.GD.N0232.N0719.N0933.d009301 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY))).map
          (_root_.GD.N0228.N0547.N0793.d012961 r s sigmaX sigmaY) =
      _root_.GD.N0228.N0547.N0790.d012894 r s := by
  have hmean := _root_.GD.N0228.N0547.N0793.d012973
    hr hs hsigmaX hsigmaY theta
  have hvariance := _root_.GD.N0228.N0547.N0793.d012975
    hr hs hsigmaX hsigmaY
  have hsizes := _root_.GD.N0228.N0547.N0793.d012972 hr hs
  letI : IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0933.d009300 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)) := by
    unfold _root_.GD.N0232.N0719.N0933.d009300
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
  letI : IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0933.d009301 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)) := by
    unfold _root_.GD.N0232.N0719.N0933.d009301
    infer_instance
  change
    ((_root_.GD.N0232.N0719.N0933.d009300 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).prod
      (_root_.GD.N0232.N0719.N0933.d009301 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY))).map
          (Prod.map
            (_root_.GD.N0228.N0547.N0793.d012959 r s sigmaX sigmaY)
            (_root_.GD.N0228.N0547.N0793.d012960 r s sigmaX sigmaY)) = _
  rw [← Measure.map_prod_map
    (_root_.GD.N0232.N0719.N0933.d009300 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
      (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY))
    (_root_.GD.N0232.N0719.N0933.d009301 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
      (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY))
    (_root_.GD.N0228.N0547.N0793.d012963 r s sigmaX sigmaY)
    (_root_.GD.N0228.N0547.N0793.d012964 r s sigmaX sigmaY)]
  rw [hmean, hvariance]
  rfl




theorem d012977
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {sigmaX sigmaY : ℝ} (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    (theta : ℝ) :
    (_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
      (_root_.GD.N0228.N0547.N0793.d012962 r s sigmaX sigmaY ∘
        _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)) =
      _root_.GD.N0228.N0547.N0790.d012894 r s := by
  have hsizes := _root_.GD.N0228.N0547.N0793.d012972 hr hs
  have hsplit := _root_.GD.N0232.N0719.N0933.d009309
    2 (_root_.GD.N0228.N0547.N0793.d012954 r s) hsizes theta (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  have hfun :
      _root_.GD.N0228.N0547.N0793.d012962 r s sigmaX sigmaY ∘
          _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) =
        _root_.GD.N0228.N0547.N0793.d012961 r s sigmaX sigmaY ∘
          _root_.GD.N0232.N0719.N0933.d009304 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) := by
    funext omega
    rfl
  rw [hfun]
  calc
    (_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
      (_root_.GD.N0228.N0547.N0793.d012961 r s sigmaX sigmaY ∘
        _root_.GD.N0232.N0719.N0933.d009304 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)) =
      ((_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
          (_root_.GD.N0232.N0719.N0933.d009304 2 (_root_.GD.N0228.N0547.N0793.d012954 r s))).map
            (_root_.GD.N0228.N0547.N0793.d012961 r s sigmaX sigmaY) := by
        rw [Measure.map_map
          (_root_.GD.N0228.N0547.N0793.d012965 r s sigmaX sigmaY)
          (_root_.GD.N0232.N0719.N0933.d009308 2 (_root_.GD.N0228.N0547.N0793.d012954 r s))]
    _ = ((_root_.GD.N0232.N0719.N0933.d009300 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
          (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).prod
        (_root_.GD.N0232.N0719.N0933.d009301 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
          (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY))).map
            (_root_.GD.N0228.N0547.N0793.d012961 r s sigmaX sigmaY) := by
      rw [hsplit]
    _ = _root_.GD.N0228.N0547.N0790.d012894 r s :=
      _root_.GD.N0228.N0547.N0793.d012976
        hr hs hsigmaX hsigmaY theta




def d012978
    (r s : ℕ) (sigmaX sigmaY : ℝ) : ℝ :=
  _root_.GD.N0228.N0547.N0793.d012956 r sigmaX / _root_.GD.N0228.N0547.N0793.d012958 r s sigmaX sigmaY

theorem d012979
    {r s : ℕ} {sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY) :
    0 < _root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY := by
  unfold _root_.GD.N0228.N0547.N0793.d012978 _root_.GD.N0228.N0547.N0793.d012958
  have hX : 0 < _root_.GD.N0228.N0547.N0793.d012956 r sigmaX := by
    unfold _root_.GD.N0228.N0547.N0793.d012956
    positivity
  have hY : 0 < _root_.GD.N0228.N0547.N0793.d012957 s sigmaY := by
    unfold _root_.GD.N0228.N0547.N0793.d012957
    positivity
  positivity

theorem d012980
    {r s : ℕ} {sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY) :
    _root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY < 1 := by
  unfold _root_.GD.N0228.N0547.N0793.d012978 _root_.GD.N0228.N0547.N0793.d012958
  have hX : 0 < _root_.GD.N0228.N0547.N0793.d012956 r sigmaX := by
    unfold _root_.GD.N0228.N0547.N0793.d012956
    positivity
  have hY : 0 < _root_.GD.N0228.N0547.N0793.d012957 s sigmaY := by
    unfold _root_.GD.N0228.N0547.N0793.d012957
    positivity
  exact (div_lt_one (add_pos hX hY)).2 (lt_add_of_pos_right _ hY)




def d012981
    (r s : ℕ) (sigmaX sigmaY : ℝ) (u : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ × ℝ :=
  _root_.GD.N0228.N0547.N0787.d012939 (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY)
    (_root_.GD.N0228.N0547.N0793.d012962 r s sigmaX sigmaY u)



def d012982 (r s : ℕ) (u : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ × ℝ :=
  let D := (r : ℝ) * u.meanVariance 0 +
    (s : ℝ) * u.meanVariance 1
  ((u.mean 0 - u.mean 1) ^ 2 / D,
    (r : ℝ) * u.meanVariance 0 / D)

@[fun_prop]
theorem d012983
    (r s : ℕ) (sigmaX sigmaY : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0793.d012981 r s sigmaX sigmaY) := by
  unfold _root_.GD.N0228.N0547.N0793.d012981
  fun_prop

@[fun_prop]
theorem d012984 (r s : ℕ) :
    Measurable (_root_.GD.N0228.N0547.N0793.d012982 r s) := by
  unfold _root_.GD.N0228.N0547.N0793.d012982
  fun_prop

private theorem d012985
    {x y c : ℝ} (hc : c ≠ 0) :
    (x / c) / (y / c) = x / y := by
  by_cases hy : y = 0
  · simp [hy]
  · field_simp



theorem d012986
    {r s : ℕ} {sigmaX sigmaY : ℝ}
    (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) :
    _root_.GD.N0228.N0547.N0793.d012981 r s sigmaX sigmaY u =
      _root_.GD.N0228.N0547.N0793.d012982 r s u := by
  let A := _root_.GD.N0228.N0547.N0793.d012956 r sigmaX
  let B := _root_.GD.N0228.N0547.N0793.d012957 s sigmaY
  let S := _root_.GD.N0228.N0547.N0793.d012958 r s sigmaX sigmaY
  let D := (r : ℝ) * u.meanVariance 0 +
    (s : ℝ) * u.meanVariance 1
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
        ((u.mean 0 - u.mean 1) / Real.sqrt S,
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
      ((u.mean 0 - u.mean 1) / Real.sqrt S) ^ 2 =
        (u.mean 0 - u.mean 1) ^ 2 / S := by
    rw [div_pow, hsqrtSq]
  change
    (((u.mean 0 - u.mean 1) / Real.sqrt S) ^ 2 /
        _root_.GD.N0228.N0547.N0787.d012938 (A / S)
          ((u.mean 0 - u.mean 1) / Real.sqrt S,
            (((r : ℝ) / A) * u.meanVariance 0,
              ((s : ℝ) / B) * u.meanVariance 1)),
      (A / S) * (((r : ℝ) / A) * u.meanVariance 0) /
        _root_.GD.N0228.N0547.N0787.d012938 (A / S)
          ((u.mean 0 - u.mean 1) / Real.sqrt S,
            (((r : ℝ) / A) * u.meanVariance 0,
              ((s : ℝ) / B) * u.meanVariance 1))) =
      ((u.mean 0 - u.mean 1) ^ 2 / D,
        (r : ℝ) * u.meanVariance 0 / D)
  rw [hden, hnum, hzsq,
    _root_.GD.N0228.N0547.N0793.d012985 hS.ne', _root_.GD.N0228.N0547.N0793.d012985 hS.ne']



theorem d012987
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {sigmaX sigmaY : ℝ} (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    (theta : ℝ) :
    (_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
      (_root_.GD.N0228.N0547.N0793.d012981 r s sigmaX sigmaY ∘
        _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)) =
      _root_.GD.N0228.N0547.N0787.d012941 r s
        (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY) := by
  let P := _root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
    (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  let rho := _root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY
  have hbase := _root_.GD.N0228.N0547.N0793.d012977
    hr hs hsigmaX hsigmaY theta
  calc
    P.map (_root_.GD.N0228.N0547.N0793.d012981 r s sigmaX sigmaY ∘
        _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)) =
      (P.map (_root_.GD.N0228.N0547.N0793.d012962 r s sigmaX sigmaY ∘
        _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s))).map (_root_.GD.N0228.N0547.N0787.d012939 rho) := by
          rw [Measure.map_map
            (_root_.GD.N0228.N0547.N0787.d012940 rho)
            ((_root_.GD.N0228.N0547.N0793.d012966 r s sigmaX sigmaY).comp
              (_root_.GD.N0232.N0719.N0900.d009115 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)))]
          rfl
    _ = (_root_.GD.N0228.N0547.N0790.d012894 r s).map (_root_.GD.N0228.N0547.N0787.d012939 rho) := by
      rw [hbase]
    _ = _root_.GD.N0228.N0547.N0787.d012941 r s rho := by
      rfl


theorem d012988
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {sigmaX sigmaY : ℝ} (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    (theta : ℝ) :
    (_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
      (_root_.GD.N0228.N0547.N0793.d012982 r s ∘
        _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)) =
      _root_.GD.N0228.N0547.N0787.d012941 r s
        (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY) := by
  have hfun :
      _root_.GD.N0228.N0547.N0793.d012982 r s ∘
          _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) =
        _root_.GD.N0228.N0547.N0793.d012981 r s sigmaX sigmaY ∘
          _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) := by
    funext omega
    exact (_root_.GD.N0228.N0547.N0793.d012986
      hsigmaX hsigmaY (_root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) omega)).symm
  rw [hfun]
  exact _root_.GD.N0228.N0547.N0793.d012987
    hr hs hsigmaX hsigmaY theta




theorem d012989
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {sigmaX sigmaY : ℝ} (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    (theta : ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∫⁻ omega, ENNReal.ofReal
        (_root_.GD.N0228.N0547.N0787.d012935 r s p
          (_root_.GD.N0228.N0547.N0793.d012981 r s sigmaX sigmaY
            (_root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) omega)))
      ∂(_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)) = ENNReal.ofReal p := by
  let P := _root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
    (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  let g := _root_.GD.N0228.N0547.N0793.d012981 r s sigmaX sigmaY ∘
    _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)
  let f : ℝ × ℝ → ℝ≥0∞ := fun tx => ENNReal.ofReal
    (_root_.GD.N0228.N0547.N0787.d012935 r s p tx)
  have hf : Measurable f :=
    (_root_.GD.N0228.N0547.N0787.d012936 hr hs p).ennreal_ofReal
  have hg : Measurable g :=
    (_root_.GD.N0228.N0547.N0793.d012983 r s sigmaX sigmaY).comp
      (_root_.GD.N0232.N0719.N0900.d009115 2 (_root_.GD.N0228.N0547.N0793.d012954 r s))
  have hmap := _root_.GD.N0228.N0547.N0793.d012987
    hr hs hsigmaX hsigmaY theta
  have hrho0 := _root_.GD.N0228.N0547.N0793.d012979
    (r := r) (s := s) hsigmaX hsigmaY
  have hrho1 := _root_.GD.N0228.N0547.N0793.d012980
    (r := r) (s := s) hsigmaX hsigmaY
  calc
    ∫⁻ omega, ENNReal.ofReal
        (_root_.GD.N0228.N0547.N0787.d012935 r s p
          (_root_.GD.N0228.N0547.N0793.d012981 r s sigmaX sigmaY
            (_root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) omega))) ∂P =
      ∫⁻ tx, f tx ∂(P.map g) := by
        exact (lintegral_map hf hg).symm
    _ = ∫⁻ tx, ENNReal.ofReal
        (_root_.GD.N0228.N0547.N0787.d012935 r s p tx)
          ∂(_root_.GD.N0228.N0547.N0787.d012941 r s
            (_root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY)) := by
      rw [hmap]
    _ = ENNReal.ofReal p :=
      _root_.GD.N0228.N0547.N0787.d012953
        hr hs hrho0 hrho1 hp0 hp1





theorem d012990
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {sigmaX sigmaY : ℝ} (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    (theta : ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∫⁻ omega, ENNReal.ofReal
        (_root_.GD.N0228.N0547.N0787.d012935 r s p
          (_root_.GD.N0228.N0547.N0793.d012982 r s
            (_root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) omega)))
      ∂(_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)) = ENNReal.ofReal p := by
  calc
    ∫⁻ omega, ENNReal.ofReal
        (_root_.GD.N0228.N0547.N0787.d012935 r s p
          (_root_.GD.N0228.N0547.N0793.d012982 r s
            (_root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) omega)))
      ∂(_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)) =
      ∫⁻ omega, ENNReal.ofReal
        (_root_.GD.N0228.N0547.N0787.d012935 r s p
          (_root_.GD.N0228.N0547.N0793.d012981 r s sigmaX sigmaY
            (_root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) omega)))
      ∂(_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)) := by
      apply lintegral_congr
      intro omega
      rw [_root_.GD.N0228.N0547.N0793.d012986 hsigmaX hsigmaY]
    _ = ENNReal.ofReal p :=
      _root_.GD.N0228.N0547.N0793.d012989
        hr hs hsigmaX hsigmaY theta hp0 hp1


theorem d012991
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (p : ℝ) (u : _root_.GD.N0232.N0719.N0900.d009096 2) :
    _root_.GD.N0228.N0547.N0787.d012935 r s p
        (_root_.GD.N0228.N0547.N0793.d012982 r s u) ∈ Set.Icc (0 : ℝ) 1 :=
  _root_.GD.N0228.N0547.N0787.d012937 hr hs p _





def d012992 (z : ℝ × (ℝ × ℝ)) : Fin 3 → ℝ :=
  _root_.GD.N0228.N0547.N0791.d012866 (z.1 ^ 2, z.2)

@[fun_prop]
theorem d012993 :
    Measurable _root_.GD.N0228.N0547.N0793.d012992 := by
  unfold _root_.GD.N0228.N0547.N0793.d012992
  fun_prop



theorem d012994
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (_root_.GD.N0228.N0547.N0790.d012894 r s).map _root_.GD.N0228.N0547.N0793.d012992 =
      _root_.GD.N0235.d004250
        (1 / 2) ((r : ℝ) / 2) ((s : ℝ) / 2) := by
  let squareNumerator : ℝ × (ℝ × ℝ) → ℝ × (ℝ × ℝ) :=
    fun z => (z.1 ^ 2, z.2)
  have hsquareMeas : Measurable squareNumerator := by
    dsimp only [squareNumerator]
    fun_prop
  have hsquareScalarMeas : Measurable (fun z : ℝ => z ^ 2) := by
    fun_prop
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 r) :=
    _root_.GD.N0228.N0547.N0790.d012889 hr
  letI : IsProbabilityMeasure (_root_.GD.N0228.N0547.N0778.d009365 s) :=
    _root_.GD.N0228.N0547.N0790.d012889 hs
  have hsquare :
      (_root_.GD.N0228.N0547.N0790.d012894 r s).map squareNumerator =
        (_root_.GD.N0228.N0547.N0778.d009365 1).prod
          ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s)) := by
    calc
      (_root_.GD.N0228.N0547.N0790.d012894 r s).map squareNumerator =
          ((gaussianReal 0 1).map (fun z : ℝ => z ^ 2)).prod
            (((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s)).map id) := by
        exact (Measure.map_prod_map (gaussianReal 0 1)
          ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s))
          hsquareScalarMeas measurable_id).symm
      _ = (_root_.GD.N0228.N0547.N0778.d009365 1).prod
          ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s)) := by
        rw [_root_.GD.N0121.d006355, Measure.map_id]
        rfl
  have hrR : 0 < (r : ℝ) / 2 := by positivity
  have hsR : 0 < (s : ℝ) / 2 := by positivity
  calc
    (_root_.GD.N0228.N0547.N0790.d012894 r s).map _root_.GD.N0228.N0547.N0793.d012992 =
        ((_root_.GD.N0228.N0547.N0790.d012894 r s).map squareNumerator).map
          _root_.GD.N0228.N0547.N0791.d012866 := by
      rw [Measure.map_map _root_.GD.N0228.N0547.N0791.d012867 hsquareMeas]
      rfl
    _ = ((_root_.GD.N0228.N0547.N0778.d009365 1).prod
          ((_root_.GD.N0228.N0547.N0778.d009365 r).prod (_root_.GD.N0228.N0547.N0778.d009365 s))).map
            _root_.GD.N0228.N0547.N0791.d012866 := by
      rw [hsquare]
    _ = _root_.GD.N0235.d004250
        (1 / 2) ((r : ℝ) / 2) ((s : ℝ) / 2) := by
      simpa only [_root_.GD.N0228.N0547.N0778.d009365, Nat.cast_one] using
        (_root_.GD.N0228.N0547.N0791.d012873
          (a := (1 / 2 : ℝ)) (b := (r : ℝ) / 2)
          (c := (s : ℝ) / 2) (r := (1 / 2 : ℝ))
          (by norm_num) hrR hsR (by norm_num))



theorem d012995
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {sigmaX sigmaY : ℝ} (hsigmaX : 0 < sigmaX) (hsigmaY : 0 < sigmaY)
    (theta : ℝ) :
    (_root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
      (_root_.GD.N0228.N0547.N0793.d012992 ∘
        _root_.GD.N0228.N0547.N0793.d012962 r s sigmaX sigmaY ∘
        _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)) =
      _root_.GD.N0235.d004250
        (1 / 2) ((r : ℝ) / 2) ((s : ℝ) / 2) := by
  let P := _root_.GD.N0232.N0719.d009176 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) theta
    (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)
  have hbase := _root_.GD.N0228.N0547.N0793.d012977
    hr hs hsigmaX hsigmaY theta
  calc
    P.map (_root_.GD.N0228.N0547.N0793.d012992 ∘
        _root_.GD.N0228.N0547.N0793.d012962 r s sigmaX sigmaY ∘
        _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)) =
      (P.map (_root_.GD.N0228.N0547.N0793.d012962 r s sigmaX sigmaY ∘
        _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s))).map
          _root_.GD.N0228.N0547.N0793.d012992 := by
      rw [Measure.map_map _root_.GD.N0228.N0547.N0793.d012993
        ((_root_.GD.N0228.N0547.N0793.d012966 r s sigmaX sigmaY).comp
          (_root_.GD.N0232.N0719.N0900.d009115 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)))]
    _ = (_root_.GD.N0228.N0547.N0790.d012894 r s).map _root_.GD.N0228.N0547.N0793.d012992 := by
      rw [hbase]
    _ = _root_.GD.N0235.d004250
        (1 / 2) ((r : ℝ) / 2) ((s : ℝ) / 2) :=
      _root_.GD.N0228.N0547.N0793.d012994 hr hs

end

end GD.N0228.N0547.N0793

#print axioms _root_.GD.N0228.N0547.N0793.d012967
#print axioms _root_.GD.N0228.N0547.N0793.d012977
#print axioms _root_.GD.N0228.N0547.N0793.d012986
#print axioms _root_.GD.N0228.N0547.N0793.d012988
#print axioms _root_.GD.N0228.N0547.N0793.d012990
#print axioms _root_.GD.N0228.N0547.N0793.d012995
