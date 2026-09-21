import GD.Module1565














set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0106.N0428.N0770.N1724
noncomputable section

open _root_.GD.N0137 _root_.GD.N0107 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1207
open _root_.GD.N0106.N0428.N0770.N1725

abbrev d024295 := _root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2

def d024296 (sigma zeta : ℝ) : ℝ := _root_.GD.N0107.d009046 2 2 sigma zeta

def d024297 (sigma zeta : ℝ) : ℝ :=
  sigma ^ 2 * zeta ^ 2 / (2 * (sigma ^ 2 + zeta ^ 2))

def d024298 (w : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ × (ℝ × ℝ) :=
  (_root_.GD.N0107.d009090 2 2 w,
    (_root_.GD.N0107.d009085 w.1, _root_.GD.N0107.d009085 w.2))

def d024299 (b : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  if b.2.1 + b.2.2 = 0 then (1 / 2, 0)
  else (b.2.2 / (b.2.1 + b.2.2), 2 * b.1 ^ 2 / (b.2.1 + b.2.2))

def d024300 (w : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ × ℝ := _root_.GD.N0106.N0428.N0770.N1724.d024299 (_root_.GD.N0106.N0428.N0770.N1724.d024298 w)

def d024301 : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Ici 0

def d024302 (h : (ℝ × ℝ) → ℝ) (w : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ :=
  _root_.GD.N0107.d009084 w.2 + _root_.GD.N0107.d009090 2 2 w * h (_root_.GD.N0106.N0428.N0770.N1724.d024300 w)

def d024303 (sigma zeta : ℝ) (w : _root_.GD.N0106.N0428.N0770.N1724.d024295) : ℝ :=
  _root_.GD.N0107.d009084 w.2 + _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta * _root_.GD.N0107.d009090 2 2 w

def d024304 (mu sigma zeta : ℝ) : _root_.GD.N0106.N0428.N0770.N1724.d024295 → ℝ :=
  _root_.GD.N0107.d012732 2 2 mu (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)

theorem d024305 (sigma zeta : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta = zeta ^ 2 / (sigma ^ 2 + zeta ^ 2) := by
  unfold _root_.GD.N0106.N0428.N0770.N1724.d024296 _root_.GD.N0107.d009046 _root_.GD.N0107.d009045 _root_.GD.N0107.d009043 _root_.GD.N0107.d009044
  norm_num only [Nat.cast_ofNat]
  rw [← add_div]
  by_cases h : sigma ^ 2 + zeta ^ 2 = 0
  · simp [h]
  · field_simp [h]
    <;> ring

theorem d024306 (sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0107.d009045 2 2 sigma zeta * _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta * (1 - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) =
      _root_.GD.N0106.N0428.N0770.N1724.d024297 sigma zeta := by
  rw [_root_.GD.N0106.N0428.N0770.N1724.d024305]
  have h : sigma ^ 2 + zeta ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold _root_.GD.N0107.d009045 _root_.GD.N0107.d009043 _root_.GD.N0107.d009044 _root_.GD.N0106.N0428.N0770.N1724.d024297
  norm_num only [Nat.cast_ofNat]
  field_simp [h]
  <;> ring

theorem d024307 (w : _root_.GD.N0106.N0428.N0770.N1724.d024295) :
    _root_.GD.N0106.N0428.N0770.N1724.d024300 w = _root_.GD.N0106.N0428.N0770.N1725.d024155 (_root_.GD.N0107.d009084 w.1)
      (_root_.GD.N0107.d009084 w.2) (_root_.GD.N0107.d009085 w.1)
      (_root_.GD.N0107.d009085 w.2) := by
  rfl

@[fun_prop] theorem d024308 : Measurable _root_.GD.N0106.N0428.N0770.N1724.d024298 := by
  unfold _root_.GD.N0106.N0428.N0770.N1724.d024298 _root_.GD.N0107.d009090 _root_.GD.N0107.d009084 _root_.GD.N0107.d009085
    _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
    _root_.GD.N0126.d006420
  fun_prop

@[fun_prop] theorem d024309 : Measurable _root_.GD.N0106.N0428.N0770.N1724.d024299 := by
  classical
  have hz : MeasurableSet {b : ℝ × (ℝ × ℝ) | b.2.1 + b.2.2 = 0} :=
    measurableSet_eq_fun (measurable_snd.fst.add measurable_snd.snd) measurable_const
  unfold _root_.GD.N0106.N0428.N0770.N1724.d024299
  apply Measurable.ite hz
  · exact measurable_const
  · fun_prop

@[fun_prop] theorem d024310 : Measurable _root_.GD.N0106.N0428.N0770.N1724.d024300 :=
  _root_.GD.N0106.N0428.N0770.N1724.d024309.comp _root_.GD.N0106.N0428.N0770.N1724.d024308

theorem d024311 (w : _root_.GD.N0106.N0428.N0770.N1724.d024295) : _root_.GD.N0106.N0428.N0770.N1724.d024300 w ∈ _root_.GD.N0106.N0428.N0770.N1724.d024301 := by
  have hvar (x : _root_.GD.N0137.d008894 2) : 0 ≤ _root_.GD.N0107.d009085 x := by
    unfold _root_.GD.N0107.d009085 _root_.GD.N0126.d006422
    positivity
  have hx := hvar w.1
  have hy := hvar w.2
  unfold _root_.GD.N0106.N0428.N0770.N1724.d024300 _root_.GD.N0106.N0428.N0770.N1724.d024299 _root_.GD.N0106.N0428.N0770.N1724.d024298 _root_.GD.N0106.N0428.N0770.N1724.d024301
  dsimp only
  split_ifs with hz
  · norm_num
  · have hp : 0 < _root_.GD.N0107.d009085 w.1 + _root_.GD.N0107.d009085 w.2 :=
      lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hz)
    exact ⟨⟨div_nonneg hy hp.le, (div_le_one hp).mpr (by linarith)⟩,
      div_nonneg (by positivity) hp.le⟩



theorem d024312 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    IndepFun (_root_.GD.N0106.N0428.N0770.N1724.d024304 mu sigma zeta) _root_.GD.N0106.N0428.N0770.N1724.d024298 (_root_.GD.N0107.d009030 2 2 mu sigma zeta) := by
  let e := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta
  let V := _root_.GD.N0107.d009045 2 2 sigma zeta
  let S := _root_.GD.N0107.d009025 2 2 mu sigma zeta
  have he0 : 0 < e := _root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta
  have he1 : e < 1 := _root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta
  have hi := _root_.GD.N0107.d012741
    (P := _root_.GD.N0107.d009030 2 2 mu sigma zeta) (Q := _root_.GD.N0137.d008914 2 2)
    (S := S) (f := _root_.GD.N0137.d008931 2 2 e) (g := _root_.GD.N0137.d008935 2 2 e)
    (_root_.GD.N0107.d009027 2 2 mu sigma zeta)
    (_root_.GD.N0137.d008936 2 2 e) (_root_.GD.N0137.d008937 2 2 e)
    (_root_.GD.N0107.d009031 2 2 mu sigma zeta hsigma.ne' hzeta.ne')
    (_root_.GD.N0137.d008940 2 2 (by norm_num) (by norm_num) he0.le he1.le)
  have hi' := hi.comp
    (show Measurable (fun u : ℝ => Real.sqrt (V * e * (1 - e)) * u) by fun_prop)
    (show Measurable (fun b : ℝ × (ℝ × ℝ) =>
      (Real.sqrt V * b.1, (sigma ^ 2 * b.2.1, zeta ^ 2 * b.2.2))) by fun_prop)
  change IndepFun
    (fun w => Real.sqrt (V * e * (1 - e)) * _root_.GD.N0137.d008931 2 2 e (S w))
    (fun w => (Real.sqrt V * _root_.GD.N0137.d008932 2 2 e (S w),
      (sigma ^ 2 * _root_.GD.N0137.d008933 2 2 (S w), zeta ^ 2 * _root_.GD.N0137.d008934 2 2 (S w))))
    (_root_.GD.N0107.d009030 2 2 mu sigma zeta) at hi'
  have hu : (fun w => Real.sqrt (V * e * (1 - e)) * _root_.GD.N0137.d008931 2 2 e (S w)) =
      _root_.GD.N0106.N0428.N0770.N1724.d024304 mu sigma zeta := by
    funext w
    exact _root_.GD.N0107.d012740 2 2 (by norm_num) (by norm_num)
      mu sigma zeta hsigma hzeta w
  have hb : (fun w => (Real.sqrt V * _root_.GD.N0137.d008932 2 2 e (S w),
      (sigma ^ 2 * _root_.GD.N0137.d008933 2 2 (S w), zeta ^ 2 * _root_.GD.N0137.d008934 2 2 (S w)))) = _root_.GD.N0106.N0428.N0770.N1724.d024298 := by
    funext w
    apply Prod.ext
    · exact _root_.GD.N0107.d012724 2 2 (by norm_num) (by norm_num)
        mu sigma zeta hsigma hzeta w
    · apply Prod.ext
      · change sigma ^ 2 * _root_.GD.N0107.d009033 2 2 mu sigma zeta w = _root_.GD.N0107.d009085 w.1
        rw [_root_.GD.N0107.d012725 2 2 (by norm_num)]
        field_simp [hsigma.ne']
      · change zeta ^ 2 * _root_.GD.N0107.d009034 2 2 mu sigma zeta w = _root_.GD.N0107.d009085 w.2
        rw [_root_.GD.N0107.d012726 2 2 (by norm_num)]
        field_simp [hzeta.ne']
  rw [hu, hb] at hi'
  exact hi'

theorem d024313 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    MemLp (_root_.GD.N0106.N0428.N0770.N1724.d024304 mu sigma zeta) 2 (_root_.GD.N0107.d009030 2 2 mu sigma zeta) :=
  _root_.GD.N0107.d012747 2 2 (by norm_num) (by norm_num) mu sigma zeta hsigma hzeta

theorem d024314 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    ∫ w, _root_.GD.N0106.N0428.N0770.N1724.d024304 mu sigma zeta w ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta = 0 :=
  _root_.GD.N0107.d012746 2 2 (by norm_num) (by norm_num)
    mu sigma zeta hsigma hzeta

theorem d024315 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta) (_root_.GD.N0106.N0428.N0770.N1724.d024304 mu sigma zeta) =
      _root_.GD.N0106.N0428.N0770.N1724.d024297 sigma zeta := by
  let e := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta
  let V := _root_.GD.N0107.d009045 2 2 sigma zeta
  have he0 : 0 < e := _root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta
  have he1 : e < 1 := _root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta
  have hV : 0 < V := _root_.GD.N0107.d009049 (by norm_num) (by norm_num) hsigma hzeta
  have hLaw : HasLaw (_root_.GD.N0137.d008931 2 2 e) (gaussianReal 0 1) (_root_.GD.N0137.d008914 2 2) :=
    ⟨(_root_.GD.N0137.d008936 2 2 e).aemeasurable,
      _root_.GD.N0137.d008939 2 2 (by norm_num) (by norm_num) he0.le he1.le⟩
  have hstandard : (∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
    simpa only [sub_zero, NNReal.coe_one] using h
  have hsq : (∫ w, _root_.GD.N0137.d008931 2 2 e w ^ 2 ∂_root_.GD.N0137.d008914 2 2) = 1 := by
    calc
      _ = ∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1 := by
        simpa only [Function.comp_def] using
          hLaw.integral_comp (show AEStronglyMeasurable (fun z : ℝ => z ^ 2)
            (gaussianReal 0 1) by fun_prop)
      _ = 1 := hstandard
  have hp (w : _root_.GD.N0106.N0428.N0770.N1724.d024295) : _root_.GD.N0106.N0428.N0770.N1724.d024304 mu sigma zeta w =
      _root_.GD.N0137.d008945 2 2 e V (_root_.GD.N0107.d009025 2 2 mu sigma zeta w) :=
    (_root_.GD.N0107.d012740 2 2 (by norm_num) (by norm_num)
      mu sigma zeta hsigma hzeta w).symm
  unfold _root_.GD.N0141.d006684
  simp_rw [hp]
  rw [_root_.GD.N0107.d012742
    (_root_.GD.N0107.d009027 2 2 mu sigma zeta)
    (show Measurable (fun w => _root_.GD.N0137.d008945 2 2 e V w ^ 2) by
      unfold _root_.GD.N0137.d008945
      exact (measurable_const.mul (_root_.GD.N0137.d008936 2 2 e)).pow_const 2)
    (_root_.GD.N0107.d009031 2 2 mu sigma zeta hsigma.ne' hzeta.ne')]
  simp_rw [_root_.GD.N0137.d008945, mul_pow]
  rw [integral_const_mul, hsq, mul_one,
    Real.sq_sqrt (mul_nonneg (mul_nonneg hV.le he0.le) (sub_nonneg.mpr he1.le))]
  exact _root_.GD.N0106.N0428.N0770.N1724.d024306 sigma zeta hsigma hzeta

theorem d024316 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    IndepFun (_root_.GD.N0106.N0428.N0770.N1724.d024303 sigma zeta) _root_.GD.N0106.N0428.N0770.N1724.d024298 (_root_.GD.N0107.d009030 2 2 mu sigma zeta) := by
  have hi := (_root_.GD.N0106.N0428.N0770.N1724.d024312 mu sigma zeta hsigma hzeta).comp
    (show Measurable (fun x : ℝ => x + mu) by fun_prop) measurable_id
  have heq : (fun w => _root_.GD.N0106.N0428.N0770.N1724.d024304 mu sigma zeta w + mu) = _root_.GD.N0106.N0428.N0770.N1724.d024303 sigma zeta := by
    funext w
    unfold _root_.GD.N0106.N0428.N0770.N1724.d024304 _root_.GD.N0107.d012732 _root_.GD.N0106.N0428.N0770.N1724.d024303
    ring
  simpa only [Function.comp_def, id_eq, heq] using hi

theorem d024317 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    ∫ w, _root_.GD.N0106.N0428.N0770.N1724.d024303 sigma zeta w ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta = mu := by
  have heq : _root_.GD.N0106.N0428.N0770.N1724.d024303 sigma zeta = fun w => _root_.GD.N0106.N0428.N0770.N1724.d024304 mu sigma zeta w + mu := by
    funext w
    unfold _root_.GD.N0106.N0428.N0770.N1724.d024304 _root_.GD.N0107.d012732 _root_.GD.N0106.N0428.N0770.N1724.d024303
    ring
  rw [heq, integral_add
    ((_root_.GD.N0106.N0428.N0770.N1724.d024313 mu sigma zeta hsigma hzeta).integrable (by norm_num))
    (integrable_const mu), _root_.GD.N0106.N0428.N0770.N1724.d024314 mu sigma zeta hsigma hzeta,
    integral_const]
  simp

theorem d024318 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    Var[_root_.GD.N0106.N0428.N0770.N1724.d024303 sigma zeta; _root_.GD.N0107.d009030 2 2 mu sigma zeta] =
      _root_.GD.N0106.N0428.N0770.N1724.d024297 sigma zeta := by
  have hm : Measurable (_root_.GD.N0106.N0428.N0770.N1724.d024303 sigma zeta) := by
    unfold _root_.GD.N0106.N0428.N0770.N1724.d024303 _root_.GD.N0107.d009090 _root_.GD.N0107.d009084 _root_.GD.N0126.d006420
    fun_prop
  rw [variance_eq_integral hm.aemeasurable, _root_.GD.N0106.N0428.N0770.N1724.d024317 mu sigma zeta hsigma hzeta]
  exact _root_.GD.N0106.N0428.N0770.N1724.d024315 mu sigma zeta hsigma hzeta

theorem d024319 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    MemLp (_root_.GD.N0107.d009090 2 2) 2 (_root_.GD.N0107.d009030 2 2 mu sigma zeta) := by
  simpa only [mul_one] using
    (_root_.GD.N0107.d012749 2 2 (by norm_num) (by norm_num)
      mu sigma zeta hsigma hzeta (fun _ => 1) measurable_const
      (B := 1) (by norm_num) (by intro p; norm_num)).2


theorem d024320 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (h : (ℝ × ℝ) → ℝ) (hh : Measurable h)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ p ∈ _root_.GD.N0106.N0428.N0770.N1724.d024301, |h p| ≤ B) :
    MemLp (fun w => _root_.GD.N0107.d009090 2 2 w *
      (h (_root_.GD.N0106.N0428.N0770.N1724.d024300 w) - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)) 2
      (_root_.GD.N0107.d009030 2 2 mu sigma zeta) := by
  have he0 : 0 < _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta :=
    _root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta
  have he1 : _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta < 1 :=
    _root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta
  have hc : Measurable (fun w => _root_.GD.N0107.d009090 2 2 w *
      (h (_root_.GD.N0106.N0428.N0770.N1724.d024300 w) - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)) :=
    _root_.GD.N0106.N0428.N0770.N1724.d024308.fst.mul ((hh.comp _root_.GD.N0106.N0428.N0770.N1724.d024310).sub measurable_const)
  have hB1 : 0 ≤ B + 1 := by linarith
  apply ((_root_.GD.N0106.N0428.N0770.N1724.d024319 mu sigma zeta hsigma hzeta).norm.const_mul (B + 1)).mono
    hc.aestronglyMeasurable
  filter_upwards [] with w
  have hb : |h (_root_.GD.N0106.N0428.N0770.N1724.d024300 w) - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta| ≤ B + 1 :=
    (abs_sub _ _).trans (add_le_add (hbound _ (_root_.GD.N0106.N0428.N0770.N1724.d024311 w))
      (by rw [abs_of_pos he0]; exact he1.le))
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hB1, abs_abs]
  calc
    _ ≤ |_root_.GD.N0107.d009090 2 2 w| * (B + 1) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

theorem d024321 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (h : (ℝ × ℝ) → ℝ) (hh : Measurable h)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ p ∈ _root_.GD.N0106.N0428.N0770.N1724.d024301, |h p| ≤ B) :
    MemLp (fun w => _root_.GD.N0106.N0428.N0770.N1724.d024302 h w - mu) 2 (_root_.GD.N0107.d009030 2 2 mu sigma zeta) ∧
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta) (fun w => _root_.GD.N0106.N0428.N0770.N1724.d024302 h w - mu) =
        _root_.GD.N0106.N0428.N0770.N1724.d024297 sigma zeta +
          ∫ w, _root_.GD.N0107.d009090 2 2 w ^ 2 *
            (h (_root_.GD.N0106.N0428.N0770.N1724.d024300 w) - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2
            ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta := by
  let U := _root_.GD.N0106.N0428.N0770.N1724.d024304 mu sigma zeta
  let D := _root_.GD.N0107.d009090 2 2
  let L := fun w => h (_root_.GD.N0106.N0428.N0770.N1724.d024300 w)
  let q := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta
  have hU := _root_.GD.N0106.N0428.N0770.N1724.d024313 mu sigma zeta hsigma hzeta
  have hc := _root_.GD.N0106.N0428.N0770.N1724.d024320 mu sigma zeta hsigma hzeta h hh hB hbound
  have hi := (_root_.GD.N0106.N0428.N0770.N1724.d024312 mu sigma zeta hsigma hzeta).comp
    measurable_id (show Measurable (fun b : ℝ × (ℝ × ℝ) =>
      b.1 * (h (_root_.GD.N0106.N0428.N0770.N1724.d024299 b) - q)) from
      measurable_fst.mul ((hh.comp _root_.GD.N0106.N0428.N0770.N1724.d024309).sub measurable_const))
  have horth : (∫ w, U w * (D w * (L w - q))
      ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta) = 0 :=
    _root_.GD.N0141.d006692 hi hU.aestronglyMeasurable
      hc.aestronglyMeasurable (_root_.GD.N0106.N0428.N0770.N1724.d024314 mu sigma zeta hsigma hzeta)
  have heq : (fun w => _root_.GD.N0106.N0428.N0770.N1724.d024302 h w - mu) = _root_.GD.N0141.d006685 U D L q := by
    funext w
    unfold _root_.GD.N0106.N0428.N0770.N1724.d024302 _root_.GD.N0141.d006685 U D L q _root_.GD.N0106.N0428.N0770.N1724.d024304 _root_.GD.N0107.d012732
    ring
  constructor
  · rw [heq]
    exact hU.add hc
  · have hr := _root_.GD.N0232.N0720.N1207.d012751 hU hc horth
    rw [← heq] at hr
    have hv := _root_.GD.N0106.N0428.N0770.N1724.d024315 mu sigma zeta hsigma hzeta
    change _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta) U = _root_.GD.N0106.N0428.N0770.N1724.d024297 sigma zeta at hv
    linarith



def d024322 (p : ℝ × ℝ) : _root_.GD.N0106.N0428.N0770.N1724.d024301 :=
  ⟨(max 0 (min 1 p.1), max 0 p.2), by
    change (0 ≤ max (0 : ℝ) (min 1 p.1) ∧ max (0 : ℝ) (min 1 p.1) ≤ 1) ∧
      0 ≤ max (0 : ℝ) p.2
    exact ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩,
      le_max_left (0 : ℝ) p.2⟩⟩

def d024323 (w : _root_.GD.N0106.N0428.N0770.N1724.d024295) : _root_.GD.N0106.N0428.N0770.N1724.d024301 :=
  ⟨_root_.GD.N0106.N0428.N0770.N1724.d024300 w, _root_.GD.N0106.N0428.N0770.N1724.d024311 w⟩

theorem d024324 : Measurable _root_.GD.N0106.N0428.N0770.N1724.d024322 :=
  (show Measurable (fun p : ℝ × ℝ => (max 0 (min 1 p.1), max 0 p.2)) by
    fun_prop).subtype_mk

theorem d024325 (w : _root_.GD.N0106.N0428.N0770.N1724.d024295) :
    _root_.GD.N0106.N0428.N0770.N1724.d024322 (_root_.GD.N0106.N0428.N0770.N1724.d024300 w) = _root_.GD.N0106.N0428.N0770.N1724.d024323 w := by
  apply Subtype.ext
  have hp := _root_.GD.N0106.N0428.N0770.N1724.d024311 w
  apply Prod.ext
  · change max 0 (min 1 (_root_.GD.N0106.N0428.N0770.N1724.d024300 w).1) = (_root_.GD.N0106.N0428.N0770.N1724.d024300 w).1
    rw [min_eq_right hp.1.2, max_eq_right hp.1.1]
  · change max 0 (_root_.GD.N0106.N0428.N0770.N1724.d024300 w).2 = (_root_.GD.N0106.N0428.N0770.N1724.d024300 w).2
    exact max_eq_right hp.2



theorem d024326 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta)
    (h : _root_.GD.N0106.N0428.N0770.N1724.d024301 → ℝ) (hh : Measurable h)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ p, |h p| ≤ B) :
    MemLp (fun w => _root_.GD.N0107.d009084 w.2 + _root_.GD.N0107.d009090 2 2 w *
      h (_root_.GD.N0106.N0428.N0770.N1724.d024323 w) - mu) 2 (_root_.GD.N0107.d009030 2 2 mu sigma zeta) ∧
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w => _root_.GD.N0107.d009084 w.2 + _root_.GD.N0107.d009090 2 2 w *
          h (_root_.GD.N0106.N0428.N0770.N1724.d024323 w) - mu) =
        _root_.GD.N0106.N0428.N0770.N1724.d024297 sigma zeta +
          ∫ w, _root_.GD.N0107.d009090 2 2 w ^ 2 *
            (h (_root_.GD.N0106.N0428.N0770.N1724.d024323 w) - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2
            ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta := by
  have hresult := _root_.GD.N0106.N0428.N0770.N1724.d024321 mu sigma zeta hsigma hzeta
    (fun p => h (_root_.GD.N0106.N0428.N0770.N1724.d024322 p)) (hh.comp _root_.GD.N0106.N0428.N0770.N1724.d024324)
    hB (fun p _ => hbound (_root_.GD.N0106.N0428.N0770.N1724.d024322 p))
  simpa only [_root_.GD.N0106.N0428.N0770.N1724.d024302, _root_.GD.N0106.N0428.N0770.N1724.d024325] using hresult



theorem d024327 (a t : ℝ) (p : ℝ × ℝ) (hp : p ∈ _root_.GD.N0106.N0428.N0770.N1724.d024301) :
    |_root_.GD.N0106.N0428.N0770.N1725.d024154 a t p| ≤ 1 + |a| + 7 * |t| := by
  have hfirst : |p.1| ≤ 1 := by rw [abs_of_nonneg hp.1.1]; exact hp.1.2
  have hQ := (_root_.GD.N0106.N0428.N0770.N1725.d024142 p).le
  have hJ := _root_.GD.N0106.N0428.N0770.N1725.d024143 p
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024154
  calc
    _ ≤ (|p.1| + |a * _root_.GD.N0106.N0428.N0770.N1725.d024130 p|) + |t * _root_.GD.N0106.N0428.N0770.N1725.d024131 p| := by
      have h1 := abs_add_le (p.1 + a * _root_.GD.N0106.N0428.N0770.N1725.d024130 p) (t * _root_.GD.N0106.N0428.N0770.N1725.d024131 p)
      have h2 := abs_add_le p.1 (a * _root_.GD.N0106.N0428.N0770.N1725.d024130 p)
      linarith only [h1, h2]
    _ ≤ (1 + |a| * 1) + |t| * 7 := by
      rw [abs_mul, abs_mul]
      exact add_le_add (add_le_add hfirst (mul_le_mul_of_nonneg_left hQ (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hJ (abs_nonneg _))
    _ = _ := by ring

theorem d024328 (mu sigma zeta a t : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    MemLp (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024156 a t (_root_.GD.N0107.d009084 w.1)
      (_root_.GD.N0107.d009084 w.2) (_root_.GD.N0107.d009085 w.1)
      (_root_.GD.N0107.d009085 w.2) - mu) 2 (_root_.GD.N0107.d009030 2 2 mu sigma zeta) ∧
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024156 a t (_root_.GD.N0107.d009084 w.1)
          (_root_.GD.N0107.d009084 w.2) (_root_.GD.N0107.d009085 w.1)
          (_root_.GD.N0107.d009085 w.2) - mu) =
        _root_.GD.N0106.N0428.N0770.N1724.d024297 sigma zeta +
          ∫ w, _root_.GD.N0107.d009090 2 2 w ^ 2 *
            (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t (_root_.GD.N0106.N0428.N0770.N1724.d024300 w) - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2
            ∂_root_.GD.N0107.d009030 2 2 mu sigma zeta := by
  have hresult := _root_.GD.N0106.N0428.N0770.N1724.d024321 mu sigma zeta hsigma hzeta
    (_root_.GD.N0106.N0428.N0770.N1725.d024154 a t) (_root_.GD.N0106.N0428.N0770.N1725.d024167 a t)
    (B := 1 + |a| + 7 * |t|) (by positivity) (_root_.GD.N0106.N0428.N0770.N1724.d024327 a t)
  simpa only [_root_.GD.N0106.N0428.N0770.N1724.d024302, _root_.GD.N0106.N0428.N0770.N1724.d024307, _root_.GD.N0106.N0428.N0770.N1725.d024162,
    _root_.GD.N0107.d009090] using hresult

end
end GD.N0106.N0428.N0770.N1724

#print axioms _root_.GD.N0106.N0428.N0770.N1724.d024312
#print axioms _root_.GD.N0106.N0428.N0770.N1724.d024316
#print axioms _root_.GD.N0106.N0428.N0770.N1724.d024315
#print axioms _root_.GD.N0106.N0428.N0770.N1724.d024318
#print axioms _root_.GD.N0106.N0428.N0770.N1724.d024320
#print axioms _root_.GD.N0106.N0428.N0770.N1724.d024321
#print axioms _root_.GD.N0106.N0428.N0770.N1724.d024326
#print axioms _root_.GD.N0106.N0428.N0770.N1724.d024327
#print axioms _root_.GD.N0106.N0428.N0770.N1724.d024328
