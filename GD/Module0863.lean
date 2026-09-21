import GD.Module0862
import GD.Module0283













open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1344

open _root_.GD.N0232.N0720.N1320 _root_.GD.N0232.N0720.N1415
open _root_.GD.N0232.N0720.N1414

noncomputable section

def d013333 (q : ℝ) (hq : 3 / 2 ≤ q) (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) : Measure (Icc a b) :=
  Measure.map (_root_.GD.N0232.N0720.N1414.d004198 a b center r hr ha hb) (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)

instance d013334 (q : ℝ) (hq : 3 / 2 ≤ q) (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1344.d013333 q hq a b center r hr ha hb) :=
  Measure.isProbabilityMeasure_map
    (_root_.GD.N0232.N0720.N1414.d004199 a b center r hr ha hb).measurable.aemeasurable


theorem d013335 (q : ℝ) (hq : 3 / 2 ≤ q) (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) (n : ℕ) :
    _root_.GD.N0232.N0720.N1415.d004091 a b center (_root_.GD.N0232.N0720.N1344.d013333 q hq a b center r hr ha hb) n =
      r ^ n * _root_.GD.N0232.N0720.N1415.d004091 (-1) 1 0 (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309) n := by
  unfold _root_.GD.N0232.N0720.N1415.d004091 _root_.GD.N0232.N0720.N1344.d013333
  have hfun : Continuous (fun x : Icc a b ↦ ((x : ℝ) - center) ^ n) := by fun_prop
  rw [integral_map
    (_root_.GD.N0232.N0720.N1414.d004199 a b center r hr ha hb).measurable.aemeasurable
    hfun.aestronglyMeasurable]
  simp only [_root_.GD.N0232.N0720.N1414.d004198, add_sub_cancel_left, sub_zero, mul_pow, integral_const_mul]

theorem d013336 (q : ℝ) (hq : 3 / 2 ≤ q) (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) :
    _root_.GD.N0232.N0720.N1415.d004091 a b center (_root_.GD.N0232.N0720.N1344.d013333 q hq a b center r hr ha hb) 1 = 0 := by
  rw [_root_.GD.N0232.N0720.N1344.d013335]
  simp [_root_.GD.N0232.N0720.N1415.d004091, _root_.GD.N0232.N0720.N1320.d013327 q hq]

theorem d013337 (q : ℝ) (hq : 3 / 2 ≤ q) (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) :
    _root_.GD.N0232.N0720.N1415.d004091 a b center (_root_.GD.N0232.N0720.N1344.d013333 q hq a b center r hr ha hb) 2 = r ^ 2 / (2 * q) := by
  rw [_root_.GD.N0232.N0720.N1344.d013335]
  simp only [_root_.GD.N0232.N0720.N1415.d004091, sub_zero, _root_.GD.N0232.N0720.N1320.d013330 q hq]
  ring


theorem d013338 (q : ℝ) (hq : 3 / 2 ≤ q) (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) :
    _root_.GD.N0232.N0720.N1415.d004078 q
      (_root_.GD.N0232.N0720.N1415.d004091 a b center (_root_.GD.N0232.N0720.N1344.d013333 q hq a b center r hr ha hb)) = 0 := by
  have hm : _root_.GD.N0232.N0720.N1415.d004091 a b center (_root_.GD.N0232.N0720.N1344.d013333 q hq a b center r hr ha hb) =
      _root_.GD.N0232.N0720.N1414.d004194 r (_root_.GD.N0232.N0720.N1415.d004091 (-1) 1 0 (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) := by
    funext n
    exact _root_.GD.N0232.N0720.N1344.d013335 q hq a b center r hr ha hb n
  rw [hm, _root_.GD.N0232.N0720.N1414.d004197, _root_.GD.N0232.N0720.N1320.d013332 q hq, map_zero, mul_zero]



def d013339 (q : ℝ) (hq : 3 / 2 ≤ q) (center r : ℝ) : Measure ℝ :=
  Measure.map (fun x : _root_.GD.N0232.N0720.N1320.d013309 ↦ center + r * (x : ℝ)) (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)

@[simp] theorem d013340 (q : ℝ) (hq : 3 / 2 ≤ q) (center : ℝ) :
    _root_.GD.N0232.N0720.N1344.d013339 q hq center 0 = Measure.dirac center := by
  simp [_root_.GD.N0232.N0720.N1344.d013339, Measure.map_const]




theorem d013341 (q : ℝ) (hq : 3 / 2 ≤ q)
    (a b center r : ℝ) (hr : 0 ≤ r)
    (mu : Measure (Icc a b)) [IsProbabilityMeasure mu]
    (hfirst : _root_.GD.N0232.N0720.N1415.d004091 a b center mu 1 = 0)
    (hsecond : r ^ 2 = (2 * q) * _root_.GD.N0232.N0720.N1415.d004091 a b center mu 2)
    (hcubic : _root_.GD.N0232.N0720.N1415.d004078 q (_root_.GD.N0232.N0720.N1415.d004091 a b center mu) = 0) :
    Measure.map (fun x : Icc a b ↦ (x : ℝ)) mu = _root_.GD.N0232.N0720.N1344.d013339 q hq center r := by
  let A := min a (center - r)
  let B := max b (center + r)
  have hAa : A ≤ a := min_le_left _ _
  have hbB : b ≤ B := le_max_left _ _
  have hAc : A ≤ center - r := min_le_right _ _
  have hcB : center + r ≤ B := le_max_right _ _
  let inc := _root_.GD.N0232.N0720.N1414.d004206 a b A B hAa hbB
  let candidate := Measure.map inc mu
  let ref := _root_.GD.N0232.N0720.N1344.d013333 q hq A B center r hr hAc hcB
  have hinc : Measurable inc := (_root_.GD.N0232.N0720.N1414.d004207 a b A B hAa hbB).measurable
  letI : IsProbabilityMeasure candidate := Measure.isProbabilityMeasure_map hinc.aemeasurable
  have hmom : _root_.GD.N0232.N0720.N1415.d004091 A B center candidate = _root_.GD.N0232.N0720.N1415.d004091 a b center mu := by
    funext n
    exact _root_.GD.N0232.N0720.N1414.d004208 a b A B center hAa hbB mu n
  have hfirstEq : _root_.GD.N0232.N0720.N1415.d004091 A B center candidate 1 = _root_.GD.N0232.N0720.N1415.d004091 A B center ref 1 := by
    rw [hmom, hfirst, _root_.GD.N0232.N0720.N1344.d013336]
  have hsecondEq : _root_.GD.N0232.N0720.N1415.d004091 A B center candidate 2 = _root_.GD.N0232.N0720.N1415.d004091 A B center ref 2 := by
    rw [hmom, _root_.GD.N0232.N0720.N1344.d013337]
    exact (eq_div_iff (by linarith : 2 * q ≠ 0)).2 (by nlinarith [hsecond])
  have hcandidate : _root_.GD.N0232.N0720.N1415.d004078 q (_root_.GD.N0232.N0720.N1415.d004091 A B center candidate) = 0 := by
    rw [hmom]
    exact hcubic
  have href : _root_.GD.N0232.N0720.N1415.d004078 q (_root_.GD.N0232.N0720.N1415.d004091 A B center ref) = 0 :=
    _root_.GD.N0232.N0720.N1344.d013338 q hq A B center r hr hAc hcB
  have heq : candidate = ref :=
    _root_.GD.N0232.N0720.N1415.d004094 A B center (q := q) (by linarith)
      candidate ref hfirstEq hsecondEq hcandidate href
  have hmap := congrArg (Measure.map (fun x : Icc A B ↦ (x : ℝ))) heq
  change Measure.map (fun x : Icc A B ↦ (x : ℝ)) (Measure.map inc mu) =
    Measure.map (fun x : Icc A B ↦ (x : ℝ))
      (Measure.map (_root_.GD.N0232.N0720.N1414.d004198 A B center r hr hAc hcB) (_root_.GD.N0232.N0720.N1320.d013321 q hq : Measure _root_.GD.N0232.N0720.N1320.d013309)) at hmap
  rw [Measure.map_map measurable_subtype_coe hinc,
    Measure.map_map measurable_subtype_coe
      (_root_.GD.N0232.N0720.N1414.d004199 A B center r hr hAc hcB).measurable] at hmap
  exact hmap

def d013342 (q : ℝ) (_hq : 3 / 2 ≤ q) (a b : ℝ) (mu : Measure (Icc a b)) : ℝ :=
  Real.sqrt ((2 * q) * _root_.GD.N0232.N0720.N1415.d004091 a b (_root_.GD.N0232.N0720.N1414.d004212 a b mu) mu 2)



theorem d013343 (q : ℝ) (hq : 3 / 2 ≤ q)
    (a b : ℝ) (mu : Measure (Icc a b)) [IsProbabilityMeasure mu]
    (hcubic : _root_.GD.N0232.N0720.N1415.d004078 q
      (_root_.GD.N0232.N0720.N1415.d004091 a b (_root_.GD.N0232.N0720.N1414.d004212 a b mu) mu) = 0) :
    Measure.map (fun x : Icc a b ↦ (x : ℝ)) mu =
      _root_.GD.N0232.N0720.N1344.d013339 q hq (_root_.GD.N0232.N0720.N1414.d004212 a b mu) (_root_.GD.N0232.N0720.N1344.d013342 q hq a b mu) := by
  apply _root_.GD.N0232.N0720.N1344.d013341 q hq a b
    (_root_.GD.N0232.N0720.N1414.d004212 a b mu) (_root_.GD.N0232.N0720.N1344.d013342 q hq a b mu) (Real.sqrt_nonneg _) mu
    (_root_.GD.N0232.N0720.N1414.d004213 a b mu) ?_ hcubic
  exact Real.sq_sqrt (mul_nonneg (by linarith) (_root_.GD.N0232.N0720.N1414.d004214 a b _ mu))

open _root_.GD.N0232.N0720.N1290




theorem d013344 (q : ℝ) (hq : 3 / 2 ≤ q)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hF : ∀ᶠ epsilon in 𝓝 (0 : ℝ),
      _root_.GD.N0232.N0720.N1290.d004143 q (_root_.GD.N0232.N0720.N1290.d004147 (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) epsilon) mu = 0) :
    Measure.map (fun x : _root_.GD.N0232.N0720.N1290.d004131 ↦ (x : ℝ)) mu =
      _root_.GD.N0232.N0720.N1344.d013339 q hq (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) (_root_.GD.N0232.N0720.N1344.d013342 q hq 0 1 mu) := by
  apply _root_.GD.N0232.N0720.N1344.d013343 q hq 0 1 mu
  exact _root_.GD.N0232.N0720.N1290.d004150
    (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) q (by linarith) mu hF

end
end GD.N0232.N0720.N1344

#print axioms _root_.GD.N0232.N0720.N1344.d013338
#print axioms _root_.GD.N0232.N0720.N1344.d013341
#print axioms _root_.GD.N0232.N0720.N1344.d013344
