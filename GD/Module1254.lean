import GD.Module1253











open MeasureTheory Set
open scoped ContDiff

namespace GD.N0232.N0720.N1308

noncomputable section

open _root_.GD.N0232.N0720.N1290 _root_.GD.N0232.N0720.N1368
open _root_.GD.N0232.N0720.N1352 _root_.GD.N0232.N0720.N1351
open _root_.GD.N0232.N0720.N1270 _root_.GD.N0232.N0720.N1292
open _root_.GD.N0232.N0720.N1264

def d020280 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)
    (p : _root_.GD.N0232.N0720.N1351.d002812) : ℝ :=
  1 - _root_.GD.N0232.N0720.N1292.d004162 ((D : ℝ) / 2) (fun t ↦ (t : ℝ)) mu (_root_.GD.N0232.N0720.N1264.d020244 p) /
    _root_.GD.N0232.N0720.N1292.d004162 ((D : ℝ) / 2) (fun _ ↦ 1) mu (_root_.GD.N0232.N0720.N1264.d020244 p)

theorem d020281 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1308.d020280 D mu) _root_.GD.N0232.N0720.N1292.d004155 := by
  have hD := (_root_.GD.N0232.N0720.N1292.d004173 ((D : ℝ) / 2) continuous_const mu
    (phi := fun _ ↦ 1)).comp _root_.GD.N0232.N0720.N1264.d020245.contDiffOn (fun _ hp ↦ _root_.GD.N0232.N0720.N1264.d020246 hp)
  have hT := (_root_.GD.N0232.N0720.N1292.d004173 ((D : ℝ) / 2) continuous_subtype_val mu).comp
    _root_.GD.N0232.N0720.N1264.d020245.contDiffOn (fun _ hp ↦ _root_.GD.N0232.N0720.N1264.d020246 hp)
  exact contDiffOn_const.sub (hT.div hD (fun p hp ↦
    ne_of_gt (_root_.GD.N0232.N0720.N1264.d020248 ((D : ℝ) / 2) mu (_root_.GD.N0232.N0720.N1264.d020246 hp))))

def d020282 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) : _root_.GD.N0232.N0720.N1352.d002739 → ℝ := _root_.GD.N0232.N0720.N1264.d020260 ((D : ℝ) / 2) (fun _ ↦ 1) mu

def d020283 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) : _root_.GD.N0232.N0720.N1352.d002739 → ℝ :=
  _root_.GD.N0232.N0720.N1264.d020260 ((D : ℝ) / 2) (fun t ↦ 1 - (t : ℝ)) mu

def d020284 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (x : _root_.GD.N0232.N0720.N1352.d002739) : ℝ :=
  x 0 * _root_.GD.N0232.N0720.N1308.d020282 D mu x + _root_.GD.N0232.N0720.N1352.d002742 x * _root_.GD.N0232.N0720.N1308.d020283 D mu x

theorem d020285 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) : 0 < _root_.GD.N0232.N0720.N1308.d020282 D mu x :=
  _root_.GD.N0232.N0720.N1264.d020248 ((D : ℝ) / 2) mu (_root_.GD.N0232.N0720.N1264.d020257 hx)

theorem d020286 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    _root_.GD.N0232.N0720.N1308.d020284 D mu x = _root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1308.d020280 D mu ∘ _root_.GD.N0232.N0720.N1351.d002814) x * _root_.GD.N0232.N0720.N1308.d020282 D mu x := by
  have hD := ne_of_gt (_root_.GD.N0232.N0720.N1308.d020285 D mu hx)
  have hC := _root_.GD.N0232.N0720.N1264.d020266 ((D : ℝ) / 2) continuous_const continuous_subtype_val mu hx
    (phi := fun _ ↦ 1)
  unfold _root_.GD.N0232.N0720.N1308.d020284 _root_.GD.N0232.N0720.N1308.d020283
  rw [hC]
  simp only [_root_.GD.N0232.N0720.N1352.d002804, Function.comp_apply, _root_.GD.N0232.N0720.N1308.d020280,
    ← _root_.GD.N0232.N0720.N1264.d020256]
  change x 0 * _root_.GD.N0232.N0720.N1308.d020282 D mu x + _root_.GD.N0232.N0720.N1352.d002742 x *
      (_root_.GD.N0232.N0720.N1308.d020282 D mu x - _root_.GD.N0232.N0720.N1264.d020260 ((D : ℝ) / 2) (fun t ↦ (t : ℝ)) mu x) =
    (x 0 + _root_.GD.N0232.N0720.N1352.d002742 x * (1 - _root_.GD.N0232.N0720.N1264.d020260 ((D : ℝ) / 2) (fun t ↦ (t : ℝ)) mu x / _root_.GD.N0232.N0720.N1308.d020282 D mu x)) * _root_.GD.N0232.N0720.N1308.d020282 D mu x
  field_simp [hD]

def d020287 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (x : _root_.GD.N0232.N0720.N1352.d002739) : _root_.GD.N0232.N0720.N1352.d002739 →L[ℝ] ℝ :=
  _root_.GD.N0232.N0720.N1308.d020282 D mu x • _root_.GD.N0232.N0720.N1352.d002741 0 + x 0 • _root_.GD.N0232.N0720.N1264.d020261 ((D : ℝ) / 2) (fun _ ↦ 1) mu x +
    _root_.GD.N0232.N0720.N1308.d020283 D mu x • _root_.GD.N0232.N0720.N1352.d002743 +
      _root_.GD.N0232.N0720.N1352.d002742 x • _root_.GD.N0232.N0720.N1264.d020261 ((D : ℝ) / 2) (fun t ↦ 1 - (t : ℝ)) mu x

theorem d020288 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu]
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    HasFDerivAt (_root_.GD.N0232.N0720.N1308.d020284 D mu) (_root_.GD.N0232.N0720.N1308.d020287 D mu x) x := by
  have hM := _root_.GD.N0232.N0720.N1264.d020262 ((D : ℝ) / 2) continuous_const mu hx (phi := fun _ ↦ 1)
  have hC := _root_.GD.N0232.N0720.N1264.d020262 ((D : ℝ) / 2) (by fun_prop) mu hx
    (phi := fun t ↦ 1 - (t : ℝ))
  apply (((hasFDerivAt_apply (0 : Fin 4) x).fun_mul hM).fun_add
    ((_root_.GD.N0232.N0720.N1352.d002746 x).fun_mul hC)).congr_fderiv
  ext v
  simp only [_root_.GD.N0232.N0720.N1308.d020287, _root_.GD.N0232.N0720.N1308.d020282, _root_.GD.N0232.N0720.N1308.d020283, _root_.GD.N0232.N0720.N1352.d002741,
    add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

private theorem d020289 (q : ℝ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)
    [IsFiniteMeasure mu] {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    _root_.GD.N0232.N0720.N1264.d020260 q (fun t ↦ (1 - (t : ℝ)) * (1 - (t : ℝ))) mu x =
      _root_.GD.N0232.N0720.N1264.d020260 q (fun t ↦ 1 - (t : ℝ)) mu x -
        _root_.GD.N0232.N0720.N1264.d020260 q (fun t ↦ (t : ℝ) * (1 - (t : ℝ))) mu x := by
  rw [← _root_.GD.N0232.N0720.N1264.d020266 q (by fun_prop) (by fun_prop) mu hx]
  congr 1
  funext t
  ring


theorem d020290 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsFiniteMeasure mu]
    {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    fderiv ℝ (_root_.GD.N0232.N0720.N1308.d020284 D mu) x (_root_.GD.N0232.N0720.N1352.d002740 2) =
        x 0 * fderiv ℝ (_root_.GD.N0232.N0720.N1308.d020282 D mu) x (_root_.GD.N0232.N0720.N1352.d002740 2) - fderiv ℝ (_root_.GD.N0232.N0720.N1308.d020282 D mu) x (_root_.GD.N0232.N0720.N1352.d002740 0) ∧
      fderiv ℝ (_root_.GD.N0232.N0720.N1308.d020284 D mu) x (_root_.GD.N0232.N0720.N1352.d002740 3) =
        x 1 * fderiv ℝ (_root_.GD.N0232.N0720.N1308.d020282 D mu) x (_root_.GD.N0232.N0720.N1352.d002740 3) - fderiv ℝ (_root_.GD.N0232.N0720.N1308.d020282 D mu) x (_root_.GD.N0232.N0720.N1352.d002740 1) := by
  have hM := _root_.GD.N0232.N0720.N1264.d020264 ((D : ℝ) / 2) continuous_const mu hx (phi := fun _ ↦ 1)
  have hN := (_root_.GD.N0232.N0720.N1308.d020288 D mu hx).fderiv
  have hcomm : (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (1 - (t : ℝ)) * (t : ℝ)) =
      (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ) * (1 - (t : ℝ))) := by funext t; ring
  rw [hN]
  change _ = x 0 * fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020260 ((D : ℝ) / 2) (fun _ ↦ 1) mu) x (_root_.GD.N0232.N0720.N1352.d002740 2) -
      fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020260 ((D : ℝ) / 2) (fun _ ↦ 1) mu) x (_root_.GD.N0232.N0720.N1352.d002740 0) ∧
    _ = x 1 * fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020260 ((D : ℝ) / 2) (fun _ ↦ 1) mu) x (_root_.GD.N0232.N0720.N1352.d002740 3) -
      fderiv ℝ (_root_.GD.N0232.N0720.N1264.d020260 ((D : ℝ) / 2) (fun _ ↦ 1) mu) x (_root_.GD.N0232.N0720.N1352.d002740 1)
  rw [hM]
  simp only [_root_.GD.N0232.N0720.N1308.d020287, add_apply, smul_apply,
    _root_.GD.N0232.N0720.N1352.d002744, _root_.GD.N0232.N0720.N1352.d002745, _root_.GD.N0232.N0720.N1264.d020265,
    smul_eq_mul, one_mul, hcomm]
  rw [_root_.GD.N0232.N0720.N1308.d020289 ((D : ℝ) / 2 + 1) mu hx]
  simp only [_root_.GD.N0232.N0720.N1352.d002740, _root_.GD.N0232.N0720.N1352.d002742, Pi.single_apply]
  norm_num [Fin.ext_iff]
  constructor <;> ring


theorem d020291 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) {x : _root_.GD.N0232.N0720.N1352.d002739} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224)
    {a : ℝ} (ha : 0 < a) : a ^ D * _root_.GD.N0232.N0720.N1308.d020282 D mu (_root_.GD.N0232.N0720.N1352.d002795 x a) = _root_.GD.N0232.N0720.N1308.d020282 D mu x := by
  have hpow : (a ^ 2) ^ (-((D : ℝ) / 2)) = (a ^ D)⁻¹ := by
    simpa only [neg_div, Real.sqrt_sq ha.le] using
      _root_.GD.N0232.N0720.N1358.d004012 (a ^ 2) (sq_nonneg a) D
  have hkernel : ∀ t : _root_.GD.N0232.N0720.N1290.d004131,
      _root_.GD.N0232.N0720.N1292.d004161 ((D : ℝ) / 2) (fun _ ↦ 1) (_root_.GD.N0232.N0720.N1264.d020254 (_root_.GD.N0232.N0720.N1352.d002795 x a)) t =
        (a ^ D)⁻¹ * _root_.GD.N0232.N0720.N1292.d004161 ((D : ℝ) / 2) (fun _ ↦ 1) (_root_.GD.N0232.N0720.N1264.d020254 x) t := by
    intro t
    simp only [_root_.GD.N0232.N0720.N1292.d004161, one_mul, _root_.GD.N0232.N0720.N1264.d020276]
    rw [Real.mul_rpow (sq_nonneg a) (_root_.GD.N0232.N0720.N1292.d004159 (_root_.GD.N0232.N0720.N1264.d020257 hx) t).le, hpow]
  unfold _root_.GD.N0232.N0720.N1308.d020282 _root_.GD.N0232.N0720.N1264.d020260 _root_.GD.N0232.N0720.N1292.d004162
  simp_rw [hkernel]
  rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero D (ne_of_gt ha)), one_mul]

def d020292 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    _root_.GD.N0232.N0720.N1270.d020238 D (_root_.GD.N0232.N0720.N1308.d020280 D mu) where
  M := _root_.GD.N0232.N0720.N1308.d020282 D mu
  N := _root_.GD.N0232.N0720.N1308.d020284 D mu
  smooth_M := _root_.GD.N0232.N0720.N1264.d020263 ((D : ℝ) / 2) continuous_const mu
  positive_M := fun _ hx ↦ _root_.GD.N0232.N0720.N1308.d020285 D mu hx
  numerator := fun _ hx ↦ _root_.GD.N0232.N0720.N1308.d020286 D mu hx
  pde := fun _ hx ↦ _root_.GD.N0232.N0720.N1308.d020290 D mu hx
  homogeneous := fun _ hx _ ha ↦ _root_.GD.N0232.N0720.N1308.d020291 D mu hx ha


end
end GD.N0232.N0720.N1308

#print axioms _root_.GD.N0232.N0720.N1308.d020281
#print axioms _root_.GD.N0232.N0720.N1308.d020290
#print axioms _root_.GD.N0232.N0720.N1308.d020292
