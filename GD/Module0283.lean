import GD.Module0282
import GD.Module0279
















open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1414

open _root_.GD.N0232.N0720.N1353 _root_.GD.N0232.N0720.N1415

noncomputable section

def d004194 (r : ℝ) (mu : ℕ → ℝ) (n : ℕ) : ℝ := r ^ n * mu n

theorem d004195 (r c : ℝ) :
    PowerSeries.rescale r (PowerSeries.C c) = PowerSeries.C c := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · simp [PowerSeries.coeff_C, hn]

theorem d004196 (q r : ℝ) (j : ℕ) (mu : ℕ → ℝ) :
    _root_.GD.N0232.N0720.N1415.d004075 q j (_root_.GD.N0232.N0720.N1414.d004194 r mu) =
      PowerSeries.C (r ^ j) * PowerSeries.rescale r (_root_.GD.N0232.N0720.N1415.d004075 q j mu) := by
  ext n
  simp only [_root_.GD.N0232.N0720.N1415.d004076, _root_.GD.N0232.N0720.N1414.d004194, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale, pow_add]
  ring


theorem d004197 (q r : ℝ) (mu : ℕ → ℝ) :
    _root_.GD.N0232.N0720.N1415.d004078 q (_root_.GD.N0232.N0720.N1414.d004194 r mu) =
      PowerSeries.C (r ^ 3) * PowerSeries.rescale r (_root_.GD.N0232.N0720.N1415.d004078 q mu) := by
  simp only [_root_.GD.N0232.N0720.N1415.d004078, _root_.GD.N0232.N0720.N1414.d004196, map_sub, map_add,
    map_mul, map_pow, _root_.GD.N0232.N0720.N1414.d004195, pow_zero, pow_one, map_one, one_mul]
  ring


def d004198 (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b)
    (x : _root_.GD.N0232.N0720.N1353.d004179) : Icc a b :=
  ⟨center + r * (x : ℝ), by
    constructor
    · have hx := mul_le_mul_of_nonneg_left x.2.1 hr
      linarith
    · have hx := mul_le_mul_of_nonneg_left x.2.2 hr
      linarith⟩

theorem d004199 (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) :
    Continuous (_root_.GD.N0232.N0720.N1414.d004198 a b center r hr ha hb) := by
  unfold _root_.GD.N0232.N0720.N1414.d004198
  fun_prop

def d004200 (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) : Measure (Icc a b) :=
  Measure.map (_root_.GD.N0232.N0720.N1414.d004198 a b center r hr ha hb) _root_.GD.N0232.N0720.N1353.d004182

instance d004201 (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1414.d004200 a b center r hr ha hb) :=
  Measure.isProbabilityMeasure_map
    (_root_.GD.N0232.N0720.N1414.d004199 a b center r hr ha hb).measurable.aemeasurable


theorem d004202 (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) (n : ℕ) :
    _root_.GD.N0232.N0720.N1415.d004091 a b center (_root_.GD.N0232.N0720.N1414.d004200 a b center r hr ha hb) n =
      r ^ n * _root_.GD.N0232.N0720.N1415.d004091 (-1) 1 0 _root_.GD.N0232.N0720.N1353.d004182 n := by
  unfold _root_.GD.N0232.N0720.N1415.d004091 _root_.GD.N0232.N0720.N1414.d004200
  have hfun : Continuous (fun x : Icc a b ↦ ((x : ℝ) - center) ^ n) := by fun_prop
  rw [integral_map
    (_root_.GD.N0232.N0720.N1414.d004199 a b center r hr ha hb).measurable.aemeasurable
    hfun.aestronglyMeasurable]
  simp only [_root_.GD.N0232.N0720.N1414.d004198, add_sub_cancel_left, sub_zero, mul_pow, integral_const_mul]

theorem d004203 (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) :
    _root_.GD.N0232.N0720.N1415.d004091 a b center (_root_.GD.N0232.N0720.N1414.d004200 a b center r hr ha hb) 1 = 0 := by
  rw [_root_.GD.N0232.N0720.N1414.d004202]
  simp [_root_.GD.N0232.N0720.N1415.d004091, _root_.GD.N0232.N0720.N1353.d004186]

theorem d004204 (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) :
    _root_.GD.N0232.N0720.N1415.d004091 a b center (_root_.GD.N0232.N0720.N1414.d004200 a b center r hr ha hb) 2 = r ^ 2 / 5 := by
  rw [_root_.GD.N0232.N0720.N1414.d004202]
  simp only [_root_.GD.N0232.N0720.N1415.d004091, sub_zero, _root_.GD.N0232.N0720.N1353.d004187]
  ring


theorem d004205 (a b center r : ℝ) (hr : 0 ≤ r)
    (ha : a ≤ center - r) (hb : center + r ≤ b) :
    _root_.GD.N0232.N0720.N1415.d004078 (5 / 2 : ℝ)
      (_root_.GD.N0232.N0720.N1415.d004091 a b center (_root_.GD.N0232.N0720.N1414.d004200 a b center r hr ha hb)) = 0 := by
  have hm : _root_.GD.N0232.N0720.N1415.d004091 a b center (_root_.GD.N0232.N0720.N1414.d004200 a b center r hr ha hb) =
      _root_.GD.N0232.N0720.N1414.d004194 r (_root_.GD.N0232.N0720.N1415.d004091 (-1) 1 0 _root_.GD.N0232.N0720.N1353.d004182) := by
    funext n
    exact _root_.GD.N0232.N0720.N1414.d004202 a b center r hr ha hb n
  rw [hm, _root_.GD.N0232.N0720.N1414.d004197, _root_.GD.N0232.N0720.N1353.d004193, map_zero, mul_zero]


def d004206 (a b A B : ℝ) (hA : A ≤ a) (hB : b ≤ B)
    (x : Icc a b) : Icc A B :=
  ⟨(x : ℝ), ⟨hA.trans x.2.1, x.2.2.trans hB⟩⟩

theorem d004207 (a b A B : ℝ) (hA : A ≤ a) (hB : b ≤ B) :
    Continuous (_root_.GD.N0232.N0720.N1414.d004206 a b A B hA hB) := by
  unfold _root_.GD.N0232.N0720.N1414.d004206
  fun_prop

theorem d004208 (a b A B center : ℝ)
    (hA : A ≤ a) (hB : b ≤ B) (mu : Measure (Icc a b)) (n : ℕ) :
    _root_.GD.N0232.N0720.N1415.d004091 A B center (Measure.map (_root_.GD.N0232.N0720.N1414.d004206 a b A B hA hB) mu) n =
      _root_.GD.N0232.N0720.N1415.d004091 a b center mu n := by
  unfold _root_.GD.N0232.N0720.N1415.d004091
  have hfun : Continuous (fun x : Icc A B ↦ ((x : ℝ) - center) ^ n) := by fun_prop
  rw [integral_map (_root_.GD.N0232.N0720.N1414.d004207 a b A B hA hB).measurable.aemeasurable
    hfun.aestronglyMeasurable]
  rfl



def d004209 (center r : ℝ) : Measure ℝ :=
  Measure.map (fun x : _root_.GD.N0232.N0720.N1353.d004179 ↦ center + r * (x : ℝ)) _root_.GD.N0232.N0720.N1353.d004182

@[simp] theorem d004210 (center : ℝ) :
    _root_.GD.N0232.N0720.N1414.d004209 center 0 = Measure.dirac center := by
  simp [_root_.GD.N0232.N0720.N1414.d004209, Measure.map_const]




theorem d004211
    (a b center r : ℝ) (hr : 0 ≤ r)
    (mu : Measure (Icc a b)) [IsProbabilityMeasure mu]
    (hfirst : _root_.GD.N0232.N0720.N1415.d004091 a b center mu 1 = 0)
    (hsecond : r ^ 2 = 5 * _root_.GD.N0232.N0720.N1415.d004091 a b center mu 2)
    (hcubic : _root_.GD.N0232.N0720.N1415.d004078 (5 / 2 : ℝ) (_root_.GD.N0232.N0720.N1415.d004091 a b center mu) = 0) :
    Measure.map (fun x : Icc a b ↦ (x : ℝ)) mu = _root_.GD.N0232.N0720.N1414.d004209 center r := by
  let A := min a (center - r)
  let B := max b (center + r)
  have hAa : A ≤ a := min_le_left _ _
  have hbB : b ≤ B := le_max_left _ _
  have hAc : A ≤ center - r := min_le_right _ _
  have hcB : center + r ≤ B := le_max_right _ _
  let inc := _root_.GD.N0232.N0720.N1414.d004206 a b A B hAa hbB
  let candidate := Measure.map inc mu
  let ref := _root_.GD.N0232.N0720.N1414.d004200 A B center r hr hAc hcB
  have hinc : Measurable inc := (_root_.GD.N0232.N0720.N1414.d004207 a b A B hAa hbB).measurable
  letI : IsProbabilityMeasure candidate := Measure.isProbabilityMeasure_map hinc.aemeasurable
  have hmom : _root_.GD.N0232.N0720.N1415.d004091 A B center candidate = _root_.GD.N0232.N0720.N1415.d004091 a b center mu := by
    funext n
    exact _root_.GD.N0232.N0720.N1414.d004208 a b A B center hAa hbB mu n
  have hfirstEq : _root_.GD.N0232.N0720.N1415.d004091 A B center candidate 1 = _root_.GD.N0232.N0720.N1415.d004091 A B center ref 1 := by
    rw [hmom, hfirst, _root_.GD.N0232.N0720.N1414.d004203]
  have hsecondEq : _root_.GD.N0232.N0720.N1415.d004091 A B center candidate 2 = _root_.GD.N0232.N0720.N1415.d004091 A B center ref 2 := by
    rw [hmom, _root_.GD.N0232.N0720.N1414.d004204]
    linarith
  have hcandidate : _root_.GD.N0232.N0720.N1415.d004078 (5 / 2 : ℝ) (_root_.GD.N0232.N0720.N1415.d004091 A B center candidate) = 0 := by
    rw [hmom]
    exact hcubic
  have href : _root_.GD.N0232.N0720.N1415.d004078 (5 / 2 : ℝ) (_root_.GD.N0232.N0720.N1415.d004091 A B center ref) = 0 :=
    _root_.GD.N0232.N0720.N1414.d004205 A B center r hr hAc hcB
  have heq : candidate = ref :=
    _root_.GD.N0232.N0720.N1415.d004094 A B center (q := (5 / 2 : ℝ)) (by norm_num)
      candidate ref hfirstEq hsecondEq hcandidate href
  have hmap := congrArg (Measure.map (fun x : Icc A B ↦ (x : ℝ))) heq
  change Measure.map (fun x : Icc A B ↦ (x : ℝ)) (Measure.map inc mu) =
    Measure.map (fun x : Icc A B ↦ (x : ℝ))
      (Measure.map (_root_.GD.N0232.N0720.N1414.d004198 A B center r hr hAc hcB) _root_.GD.N0232.N0720.N1353.d004182) at hmap
  rw [Measure.map_map measurable_subtype_coe hinc,
    Measure.map_map measurable_subtype_coe
      (_root_.GD.N0232.N0720.N1414.d004199 A B center r hr hAc hcB).measurable] at hmap
  exact hmap

def d004212 (a b : ℝ) (mu : Measure (Icc a b)) : ℝ := ∫ x, (x : ℝ) ∂mu

theorem d004213 (a b : ℝ)
    (mu : Measure (Icc a b)) [IsProbabilityMeasure mu] :
    _root_.GD.N0232.N0720.N1415.d004091 a b (_root_.GD.N0232.N0720.N1414.d004212 a b mu) mu 1 = 0 := by
  have hid : Integrable (fun x : Icc a b ↦ (x : ℝ)) mu :=
    continuous_subtype_val.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  unfold _root_.GD.N0232.N0720.N1415.d004091
  simp only [pow_one]
  rw [integral_sub hid (integrable_const _)]
  simp [_root_.GD.N0232.N0720.N1414.d004212]

theorem d004214 (a b center : ℝ) (mu : Measure (Icc a b)) :
    0 ≤ _root_.GD.N0232.N0720.N1415.d004091 a b center mu 2 :=
  integral_nonneg fun _ ↦ sq_nonneg _


def d004215 (a b : ℝ) (mu : Measure (Icc a b)) : ℝ :=
  Real.sqrt (5 * _root_.GD.N0232.N0720.N1415.d004091 a b (_root_.GD.N0232.N0720.N1414.d004212 a b mu) mu 2)



theorem d004216
    (a b : ℝ) (mu : Measure (Icc a b)) [IsProbabilityMeasure mu]
    (hcubic : _root_.GD.N0232.N0720.N1415.d004078 (5 / 2 : ℝ)
      (_root_.GD.N0232.N0720.N1415.d004091 a b (_root_.GD.N0232.N0720.N1414.d004212 a b mu) mu) = 0) :
    Measure.map (fun x : Icc a b ↦ (x : ℝ)) mu =
      _root_.GD.N0232.N0720.N1414.d004209 (_root_.GD.N0232.N0720.N1414.d004212 a b mu) (_root_.GD.N0232.N0720.N1414.d004215 a b mu) := by
  apply _root_.GD.N0232.N0720.N1414.d004211 a b
    (_root_.GD.N0232.N0720.N1414.d004212 a b mu) (_root_.GD.N0232.N0720.N1414.d004215 a b mu) (Real.sqrt_nonneg _) mu
    (_root_.GD.N0232.N0720.N1414.d004213 a b mu) ?_ hcubic
  exact Real.sq_sqrt (mul_nonneg (by norm_num) (_root_.GD.N0232.N0720.N1414.d004214 a b _ mu))

open _root_.GD.N0232.N0720.N1290




theorem d004217
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hF : ∀ᶠ epsilon in 𝓝 (0 : ℝ),
      _root_.GD.N0232.N0720.N1290.d004143 (5 / 2) (_root_.GD.N0232.N0720.N1290.d004147 (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) epsilon) mu = 0) :
    Measure.map (fun x : _root_.GD.N0232.N0720.N1290.d004131 ↦ (x : ℝ)) mu =
      _root_.GD.N0232.N0720.N1414.d004209 (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) (_root_.GD.N0232.N0720.N1414.d004215 0 1 mu) := by
  apply _root_.GD.N0232.N0720.N1414.d004216 0 1 mu
  exact _root_.GD.N0232.N0720.N1290.d004150
    (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) (5 / 2) (by norm_num) mu hF

end

end GD.N0232.N0720.N1414

#print axioms _root_.GD.N0232.N0720.N1414.d004197
#print axioms _root_.GD.N0232.N0720.N1414.d004205
#print axioms _root_.GD.N0232.N0720.N1414.d004211
#print axioms _root_.GD.N0232.N0720.N1414.d004217
