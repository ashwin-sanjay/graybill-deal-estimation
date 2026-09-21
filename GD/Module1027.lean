import GD.Module1025
import GD.Module0617











open MeasureTheory ProbabilityTheory

namespace GD
namespace N0232
namespace N0720
namespace N1502

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0107
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0720.N1467



abbrev d016357 (m n : ℕ) (e : ℝ) :
    Measure _root_.GD.N0124.d006387 :=
  (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008935 m n e)


def d016358 (m n : ℕ) (e : ℝ) :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) →
      ℝ × _root_.GD.N0124.d006387 :=
  fun omega ↦
    (_root_.GD.N0137.d008931 m n e omega, _root_.GD.N0137.d008935 m n e omega)

@[fun_prop]
theorem d016359 (m n : ℕ) (e : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1502.d016358 m n e) := by
  unfold _root_.GD.N0232.N0720.N1502.d016358
  fun_prop


theorem d016360
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0232.N0720.N1502.d016358 m n e) =
      (gaussianReal 0 1).prod (_root_.GD.N0232.N0720.N1502.d016357 m n e) := by
  have hOracle : HasLaw (_root_.GD.N0137.d008931 m n e) (gaussianReal 0 1)
      (_root_.GD.N0137.d008914 m n) :=
    ⟨(_root_.GD.N0137.d008936 m n e).aemeasurable,
      _root_.GD.N0137.d008939 m n hm hn he0 he1⟩
  have hRaw : HasLaw (_root_.GD.N0137.d008935 m n e) (_root_.GD.N0232.N0720.N1502.d016357 m n e)
      (_root_.GD.N0137.d008914 m n) :=
    ⟨(_root_.GD.N0137.d008937 m n e).aemeasurable, rfl⟩
  have hIndep := _root_.GD.N0137.d008940
    m n hm hn he0 he1
  have hJoint := hIndep.hasLaw_prod hOracle hRaw
  change (_root_.GD.N0137.d008914 m n).map
      (fun omega ↦
        (_root_.GD.N0137.d008931 m n e omega, _root_.GD.N0137.d008935 m n e omega)) =
    (gaussianReal 0 1).prod (_root_.GD.N0232.N0720.N1502.d016357 m n e)
  exact hJoint.map_eq



def d016361
    (m n : ℕ) (sigma tau s : ℝ)
    (q : _root_.GD.N0124.d006387) : _root_.GD.N0232.N0719.N0900.d009096 2 where
  mean := ![
    s + (1 - _root_.GD.N0107.d009046 m n sigma tau) *
      Real.sqrt (_root_.GD.N0107.d009045 m n sigma tau) * q.1,
    s - _root_.GD.N0107.d009046 m n sigma tau *
      Real.sqrt (_root_.GD.N0107.d009045 m n sigma tau) * q.1]
  meanVariance := ![
    _root_.GD.N0107.d009043 m sigma * q.2.1,
    _root_.GD.N0107.d009044 n tau * q.2.2]

@[fun_prop]
theorem d016362
    (m n : ℕ) (sigma tau : ℝ) :
    Measurable (fun p : ℝ × _root_.GD.N0124.d006387 ↦
      _root_.GD.N0232.N0720.N1502.d016361 m n sigma tau p.1 p.2) := by
  rw [measurable_comap_iff]
  change Measurable (fun p : ℝ × _root_.GD.N0124.d006387 ↦
    ((_root_.GD.N0232.N0720.N1502.d016361 m n sigma tau p.1 p.2).mean,
      (_root_.GD.N0232.N0720.N1502.d016361 m n sigma tau p.1 p.2).meanVariance))
  unfold _root_.GD.N0232.N0720.N1502.d016361
  fun_prop



theorem d016363
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0720.N1467.d012542 m n
        (_root_.GD.N0107.d009024 m n mu sigma tau omega) =
      _root_.GD.N0232.N0720.N1502.d016361 m n sigma tau
        (mu + _root_.GD.N0137.d008945 m n
          (_root_.GD.N0107.d009046 m n sigma tau)
          (_root_.GD.N0107.d009045 m n sigma tau) omega)
        (_root_.GD.N0137.d008935 m n (_root_.GD.N0107.d009046 m n sigma tau) omega) := by
  let observed := _root_.GD.N0107.d009024 m n mu sigma tau omega
  let e := _root_.GD.N0107.d009046 m n sigma tau
  let Sigma := _root_.GD.N0107.d009045 m n sigma tau
  have hstandardize :
      _root_.GD.N0107.d009025 m n mu sigma tau observed = omega := by
    exact _root_.GD.N0107.d009028
      m n mu sigma tau hsigma.ne' htau.ne' omega
  have hOracle := _root_.GD.N0107.d012740
    m n hm hn mu sigma tau hsigma htau observed
  have hContrast := _root_.GD.N0107.d012724
    m n hm hn mu sigma tau hsigma htau observed
  simp only [_root_.GD.N0107.d012738, _root_.GD.N0107.d009038,
    Function.comp_apply, hstandardize] at hOracle hContrast
  ext i
  · fin_cases i
    · simp only [_root_.GD.N0232.N0720.N1467.d012545, _root_.GD.N0232.N0720.N1502.d016361,
        Matrix.cons_val_zero]
      change _root_.GD.N0107.d009084 observed.1 = _
      unfold _root_.GD.N0107.d012732 at hOracle
      unfold _root_.GD.N0107.d009090 at hOracle hContrast
      unfold _root_.GD.N0137.d008942 at hContrast
      unfold _root_.GD.N0137.d008935
      dsimp [e, Sigma] at hOracle hContrast ⊢
      rw [mul_assoc, hContrast, hOracle]
      ring
    · simp only [_root_.GD.N0232.N0720.N1467.d012546, _root_.GD.N0232.N0720.N1502.d016361,
        Matrix.cons_val_one]
      change _root_.GD.N0107.d009084 observed.2 = _
      unfold _root_.GD.N0107.d012732 at hOracle
      unfold _root_.GD.N0107.d009090 at hOracle hContrast
      unfold _root_.GD.N0137.d008942 at hContrast
      unfold _root_.GD.N0137.d008935
      dsimp [e, Sigma] at hOracle hContrast ⊢
      rw [mul_assoc, hContrast, hOracle]
      ring
  · fin_cases i
    · simp only [_root_.GD.N0232.N0720.N1467.d012547,
        _root_.GD.N0232.N0720.N1502.d016361, Matrix.cons_val_zero]
      change _root_.GD.N0107.d009085 observed.1 / (m : ℝ) = _
      rw [show observed.1 = _root_.GD.N0107.d009018 m mu sigma omega.1 by rfl,
        _root_.GD.N0117.d014148 hm]
      simp only [_root_.GD.N0137.d008935,
        _root_.GD.N0137.d008933, _root_.GD.N0107.d009043,
        Matrix.cons_val_zero]
      unfold _root_.GD.N0137.d008897 _root_.GD.N0107.d009085
      ring_nf
      simp
    · simp only [_root_.GD.N0232.N0720.N1467.d012548,
        _root_.GD.N0232.N0720.N1502.d016361, Matrix.cons_val_one]
      change _root_.GD.N0107.d009085 observed.2 / (n : ℝ) = _
      rw [show observed.2 = _root_.GD.N0107.d009018 n mu tau omega.2 by rfl,
        _root_.GD.N0117.d014148 hn]
      simp only [_root_.GD.N0137.d008935,
        _root_.GD.N0137.d008934, _root_.GD.N0107.d009044,
        Matrix.cons_val_one]
      unfold _root_.GD.N0137.d008897 _root_.GD.N0107.d009085
      ring_nf
      simp


def d016364 (m n : ℕ) (sigma tau : ℝ) : ℝ :=
  _root_.GD.N0107.d009045 m n sigma tau *
    _root_.GD.N0107.d009046 m n sigma tau *
    (1 - _root_.GD.N0107.d009046 m n sigma tau)

theorem d016365
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau) :
    0 < _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau := by
  unfold _root_.GD.N0232.N0720.N1502.d016364
  exact mul_pos
    (mul_pos
      (_root_.GD.N0107.d009049 (by omega) (by omega) hsigma htau)
      (_root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau))
    (sub_pos.mpr
      (_root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau))


def d016366
    (m n : ℕ) (sigma tau : ℝ)
    (g : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) :
    ℝ × _root_.GD.N0124.d006387 → ℝ :=
  fun p ↦
    g (_root_.GD.N0232.N0720.N1502.d016361 m n sigma tau
      (Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau) * p.1) p.2) /
      Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau)

@[fun_prop]
theorem d016367
    (m n : ℕ) (sigma tau : ℝ)
    {g : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ} (hg : Measurable g) :
    Measurable (_root_.GD.N0232.N0720.N1502.d016366 m n sigma tau g) := by
  unfold _root_.GD.N0232.N0720.N1502.d016366
  exact ((hg.comp
    ((_root_.GD.N0232.N0720.N1502.d016362 m n sigma tau).comp
      ((measurable_const.mul measurable_fst).prodMk measurable_snd)))).div_const _


theorem d016368
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (g : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (mu noise : ℝ)
    (q : _root_.GD.N0124.d006387) :
    _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau *
        (_root_.GD.N0232.N0720.N1502.d016366 m n sigma tau g
            (mu / Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau) + noise, q) -
          mu / Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau)) ^ 2 =
      (g (_root_.GD.N0232.N0720.N1502.d016361 m n sigma tau
          (mu + Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau) * noise) q) -
        mu) ^ 2 := by
  have hv := _root_.GD.N0232.N0720.N1502.d016365 m n hm hn hsigma htau
  have hsqrt : 0 < Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau) :=
    Real.sqrt_pos.2 hv
  have hsqrtSq :
      Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau) ^ 2 =
        _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau :=
    Real.sq_sqrt hv.le
  unfold _root_.GD.N0232.N0720.N1502.d016366
  have harg :
      Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau) *
          (mu / Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau) + noise) =
        mu + Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau) * noise := by
    field_simp [hsqrt.ne']
  rw [harg]
  field_simp [hsqrt.ne']
  nlinarith




theorem d016369
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (g : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hg : Measurable g) (lambda : ℝ)
    (hint : Integrable
      (fun omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n ↦
        (g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) -
          Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau) * lambda) ^ 2)
      (_root_.GD.N0107.d009030 m n
        (Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau) * lambda)
        sigma tau)) :
    Integrable (fun z : ℝ × _root_.GD.N0124.d006387 ↦
      (_root_.GD.N0232.N0720.N1502.d016366 m n sigma tau g
          (lambda + z.1, z.2) - lambda) ^ 2)
      ((gaussianReal 0 1).prod
        (_root_.GD.N0232.N0720.N1502.d016357 m n (_root_.GD.N0107.d009046 m n sigma tau))) := by
  let e := _root_.GD.N0107.d009046 m n sigma tau
  let v := _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau
  let mu := Real.sqrt v * lambda
  let affine := _root_.GD.N0107.d009024 m n mu sigma tau
  let coord := _root_.GD.N0232.N0720.N1502.d016358 m n e
  let physicalLoss : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n → ℝ :=
    fun omega ↦ (g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) ^ 2
  let sourceLoss : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n → ℝ :=
    fun omega ↦ physicalLoss (affine omega)
  let coordinateLoss : ℝ × _root_.GD.N0124.d006387 → ℝ :=
    fun p ↦
      (g (_root_.GD.N0232.N0720.N1502.d016361 m n sigma tau
        (mu + Real.sqrt v * p.1) p.2) - mu) ^ 2
  let unitLoss : ℝ × _root_.GD.N0124.d006387 → ℝ :=
    fun p ↦
      (_root_.GD.N0232.N0720.N1502.d016366 m n sigma tau g
        (lambda + p.1, p.2) - lambda) ^ 2
  have hv : 0 < v :=
    _root_.GD.N0232.N0720.N1502.d016365 m n hm hn hsigma htau
  have hsqrt : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hphysicalMeas : Measurable physicalLoss := by
    unfold physicalLoss
    fun_prop
  have hsourceInt : Integrable sourceLoss (_root_.GD.N0137.d008914 m n) := by
    apply (integrable_map_measure hphysicalMeas.aestronglyMeasurable
      (_root_.GD.N0107.d009026 m n mu sigma tau).aemeasurable).mp
    simpa only [physicalLoss, mu, v, _root_.GD.N0107.d009030] using hint
  have hsourceEq : ∀ omega,
      sourceLoss omega = coordinateLoss (coord omega) := by
    intro omega
    unfold sourceLoss physicalLoss coordinateLoss coord
    rw [_root_.GD.N0232.N0720.N1502.d016363
      m n hm hn mu sigma tau hsigma htau omega]
    unfold _root_.GD.N0137.d008945 v _root_.GD.N0232.N0720.N1502.d016364 e
    rfl
  have hcoordinateMeas : Measurable coordinateLoss := by
    unfold coordinateLoss
    fun_prop
  have hcoordinateInt : Integrable coordinateLoss
      ((gaussianReal 0 1).prod (_root_.GD.N0232.N0720.N1502.d016357 m n e)) := by
    rw [← _root_.GD.N0232.N0720.N1502.d016360 m n hm hn
      (_root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau).le
      (_root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau).le]
    apply (integrable_map_measure hcoordinateMeas.aestronglyMeasurable
      (_root_.GD.N0232.N0720.N1502.d016359 m n e).aemeasurable).2
    exact hsourceInt.congr
      (Filter.Eventually.of_forall hsourceEq)
  have hmuquot : mu / Real.sqrt v = lambda := by
    unfold mu
    field_simp [hsqrt.ne']
  have hpoint : ∀ p, unitLoss p = v⁻¹ * coordinateLoss p := by
    intro p
    have hloss := _root_.GD.N0232.N0720.N1502.d016368
      m n hm hn sigma tau hsigma htau g mu p.1 p.2
    have hloss' : v * unitLoss p = coordinateLoss p := by
      simpa only [unitLoss, coordinateLoss, mu, hmuquot, mul_add,
        v] using hloss
    calc
      unitLoss p = v⁻¹ * (v * unitLoss p) := by
        field_simp [hv.ne']
      _ = v⁻¹ * coordinateLoss p := by rw [hloss']
  have hscaled : Integrable (fun p ↦ v⁻¹ * coordinateLoss p)
      ((gaussianReal 0 1).prod (_root_.GD.N0232.N0720.N1502.d016357 m n e)) :=
    hcoordinateInt.const_mul v⁻¹
  exact hscaled.congr
    (Filter.Eventually.of_forall fun p ↦ (hpoint p).symm)



theorem d016370
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (g : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hg : Measurable g) (mu : ℝ)
    (hint : Integrable (fun omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n ↦
      (g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) ^ 2)
      (_root_.GD.N0107.d009030 m n mu sigma tau)) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) =
      _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau *
        _root_.GD.N0232.N0720.N1040.d008975
          (_root_.GD.N0232.N0720.N1502.d016357 m n (_root_.GD.N0107.d009046 m n sigma tau))
          (_root_.GD.N0232.N0720.N1502.d016366 m n sigma tau g)
          (mu / Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau)) := by
  let e := _root_.GD.N0107.d009046 m n sigma tau
  let v := _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau
  let affine := _root_.GD.N0107.d009024 m n mu sigma tau
  let coord := _root_.GD.N0232.N0720.N1502.d016358 m n e
  let physicalLoss : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n → ℝ :=
    fun omega ↦ (g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) ^ 2
  let sourceLoss : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n → ℝ :=
    fun omega ↦ physicalLoss (affine omega)
  let coordinateLoss : ℝ × _root_.GD.N0124.d006387 → ℝ :=
    fun p ↦
      (g (_root_.GD.N0232.N0720.N1502.d016361 m n sigma tau
        (mu + Real.sqrt v * p.1) p.2) - mu) ^ 2
  have hv : 0 < v := by
    exact _root_.GD.N0232.N0720.N1502.d016365 m n hm hn hsigma htau
  have hphysicalMeas : Measurable physicalLoss := by
    unfold physicalLoss
    fun_prop
  have hsourceInt : Integrable sourceLoss (_root_.GD.N0137.d008914 m n) := by
    exact (integrable_map_measure hphysicalMeas.aestronglyMeasurable
      (_root_.GD.N0107.d009026 m n mu sigma tau).aemeasurable).mp hint
  have hsourceEq : ∀ omega,
      sourceLoss omega = coordinateLoss (coord omega) := by
    intro omega
    unfold sourceLoss physicalLoss coordinateLoss coord
    rw [_root_.GD.N0232.N0720.N1502.d016363
      m n hm hn mu sigma tau hsigma htau omega]
    unfold _root_.GD.N0137.d008945 v _root_.GD.N0232.N0720.N1502.d016364 e
    rfl
  have hcoordinateMeas : Measurable coordinateLoss := by
    unfold coordinateLoss
    fun_prop
  have hcoordinateInt : Integrable coordinateLoss
      ((gaussianReal 0 1).prod (_root_.GD.N0232.N0720.N1502.d016357 m n e)) := by
    rw [← _root_.GD.N0232.N0720.N1502.d016360 m n hm hn
      (_root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau).le
      (_root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau).le]
    apply (integrable_map_measure hcoordinateMeas.aestronglyMeasurable
      (_root_.GD.N0232.N0720.N1502.d016359 m n e).aemeasurable).2
    exact hsourceInt.congr
      (Filter.Eventually.of_forall hsourceEq)
  have hproduct := integral_prod
    (μ := gaussianReal 0 1) (ν := _root_.GD.N0232.N0720.N1502.d016357 m n e)
    coordinateLoss hcoordinateInt
  calc
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) =
        ∫ omega, sourceLoss omega ∂_root_.GD.N0137.d008914 m n := by
      unfold _root_.GD.N0141.d006684 sourceLoss physicalLoss
        _root_.GD.N0107.d009030 affine
      exact integral_map
        (_root_.GD.N0107.d009026 m n mu sigma tau).aemeasurable
        hphysicalMeas.aestronglyMeasurable
    _ = ∫ omega, coordinateLoss (coord omega) ∂_root_.GD.N0137.d008914 m n := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hsourceEq
    _ = ∫ p, coordinateLoss p
        ∂(_root_.GD.N0137.d008914 m n).map coord := by
      exact (integral_map
        (_root_.GD.N0232.N0720.N1502.d016359 m n e).aemeasurable
        hcoordinateMeas.aestronglyMeasurable).symm
    _ = ∫ p, coordinateLoss p
        ∂(gaussianReal 0 1).prod (_root_.GD.N0232.N0720.N1502.d016357 m n e) := by
      rw [_root_.GD.N0232.N0720.N1502.d016360 m n hm hn
        (_root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau).le
        (_root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau).le]
    _ = ∫ noise, (∫ q, coordinateLoss (noise, q)
        ∂_root_.GD.N0232.N0720.N1502.d016357 m n e) ∂gaussianReal 0 1 := hproduct
    _ = v *
        _root_.GD.N0232.N0720.N1040.d008975
          (_root_.GD.N0232.N0720.N1502.d016357 m n e)
          (_root_.GD.N0232.N0720.N1502.d016366 m n sigma tau g)
          (mu / Real.sqrt v) := by
      unfold _root_.GD.N0232.N0720.N1040.d008975
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with noise
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with q
      exact (_root_.GD.N0232.N0720.N1502.d016368
        m n hm hn sigma tau hsigma htau g mu noise q).symm
    _ = _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau *
        _root_.GD.N0232.N0720.N1040.d008975
          (_root_.GD.N0232.N0720.N1502.d016357 m n (_root_.GD.N0107.d009046 m n sigma tau))
          (_root_.GD.N0232.N0720.N1502.d016366 m n sigma tau g)
          (mu / Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau)) := rfl





theorem d016371
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (g : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ) (hg : Measurable g)
    (hint : ∀ mu, Integrable
      (fun omega : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n ↦
        (g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) ^ 2)
      (_root_.GD.N0107.d009030 m n mu sigma tau))
    (hbounded : BddAbove (Set.range
      (_root_.GD.N0232.N0720.N1040.d008975
        (_root_.GD.N0232.N0720.N1502.d016357 m n (_root_.GD.N0107.d009046 m n sigma tau))
        (_root_.GD.N0232.N0720.N1502.d016366 m n sigma tau g)))) :
    _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau ≤
      ⨆ mu : ℝ,
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) := by
  let v := _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau
  let R := _root_.GD.N0232.N0720.N1040.d008975
    (_root_.GD.N0232.N0720.N1502.d016357 m n (_root_.GD.N0107.d009046 m n sigma tau))
    (_root_.GD.N0232.N0720.N1502.d016366 m n sigma tau g)
  let P : ℝ → ℝ := fun mu ↦
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
      (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu)
  have hv : 0 < v := _root_.GD.N0232.N0720.N1502.d016365
    m n hm hn hsigma htau
  letI : IsProbabilityMeasure
      (_root_.GD.N0232.N0720.N1502.d016357 m n (_root_.GD.N0107.d009046 m n sigma tau)) := by
    unfold _root_.GD.N0232.N0720.N1502.d016357
    exact Measure.isProbabilityMeasure_map
      (_root_.GD.N0137.d008937 m n
        (_root_.GD.N0107.d009046 m n sigma tau)).aemeasurable
  have hmin : 1 ≤ ⨆ lambda : ℝ, R lambda := by
    exact _root_.GD.N0232.N0720.N1040.d008979
      (_root_.GD.N0232.N0720.N1502.d016357 m n (_root_.GD.N0107.d009046 m n sigma tau))
      (_root_.GD.N0232.N0720.N1502.d016366 m n sigma tau g)
      (_root_.GD.N0232.N0720.N1502.d016367 m n sigma tau hg)
      (fun lambda ↦
        _root_.GD.N0232.N0720.N1502.d016369
          m n hm hn sigma tau hsigma htau g hg lambda
          (hint (Real.sqrt v * lambda)))
      hbounded
  obtain ⟨U, hU⟩ := hbounded
  have hPbounded : BddAbove (Set.range P) := by
    refine ⟨v * U, ?_⟩
    rintro y ⟨mu, rfl⟩
    rw [show P mu = v * R (mu / Real.sqrt v) by
      exact _root_.GD.N0232.N0720.N1502.d016370
        m n hm hn sigma tau hsigma htau g hg mu (hint mu)]
    exact mul_le_mul_of_nonneg_left
      (hU ⟨mu / Real.sqrt v, rfl⟩) hv.le
  have hRtoP : ∀ lambda : ℝ,
      v * R lambda ≤ ⨆ mu : ℝ, P mu := by
    intro lambda
    have hsqrt : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
    have heq : P (Real.sqrt v * lambda) = v * R lambda := by
      rw [show P (Real.sqrt v * lambda) =
          v * R ((Real.sqrt v * lambda) / Real.sqrt v) by
        exact _root_.GD.N0232.N0720.N1502.d016370
          m n hm hn sigma tau hsigma htau g hg
          (Real.sqrt v * lambda) (hint _)]
      have hquot : (Real.sqrt v * lambda) / Real.sqrt v = lambda := by
        field_simp [hsqrt.ne']
      rw [hquot]
    rw [← heq]
    exact le_ciSup hPbounded (Real.sqrt v * lambda)
  have hsupR : (⨆ lambda : ℝ, R lambda) ≤
      (⨆ mu : ℝ, P mu) / v := by
    apply ciSup_le
    intro lambda
    exact (le_div_iff₀ hv).2 (by
      simpa [mul_comm] using hRtoP lambda)
  calc
    v = v * 1 := by ring
    _ ≤ v * (⨆ lambda : ℝ, R lambda) :=
      mul_le_mul_of_nonneg_left hmin hv.le
    _ ≤ ⨆ mu : ℝ, P mu := by
      simpa [mul_comm] using (le_div_iff₀ hv).1 hsupR
    _ = ⨆ mu : ℝ,
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) := rfl

end

end N1502
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1502.d016363
#print axioms _root_.GD.N0232.N0720.N1502.d016369
#print axioms _root_.GD.N0232.N0720.N1502.d016371
