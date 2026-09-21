import GD.Module0618
import GD.Module0085























open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GD
namespace N0232
namespace N0720
namespace N1157

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0232.N0720.N1155
open _root_.GD.N0232.N0720.N1156
open _root_.GD.N0230.N0702



def d008992 (z : ℝ) : ℝ × ℝ → ℝ :=
  _root_.GD.N0137.d008919 (1 - z)


def d008993 (z : ℝ) : ℝ × ℝ → ℝ :=
  fun x ↦ Real.sqrt (z * (1 - z)) * _root_.GD.N0137.d008918 (1 - z) x



def d008994 (z : ℝ) (phi : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun x ↦ Real.sqrt (1 - z) * x.2 + phi (_root_.GD.N0232.N0720.N1157.d008992 z x)


def d008995 (z : ℝ) (phi : ℝ → ℝ) : ℝ → ℝ :=
  fun w ↦ phi w - (1 - z) * w



def d008996 (z : ℝ) (phi : ℝ → ℝ) : ℝ :=
  ∫ w, _root_.GD.N0232.N0720.N1157.d008995 z phi w ^ 2 ∂gaussianReal 0 1


def d008997 (z : ℝ) (phi : ℝ → ℝ) : ℝ :=
  ∫ x, _root_.GD.N0232.N0720.N1157.d008994 z phi x ^ 2 ∂_root_.GD.N0232.N0720.N1155.d008950



theorem d008998
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (phi : ℝ → ℝ) (x : ℝ × ℝ) :
    _root_.GD.N0232.N0720.N1157.d008994 z phi x =
      _root_.GD.N0232.N0720.N1157.d008993 z x +
        _root_.GD.N0232.N0720.N1157.d008995 z phi (_root_.GD.N0232.N0720.N1157.d008992 z x) := by
  unfold _root_.GD.N0232.N0720.N1157.d008994 _root_.GD.N0232.N0720.N1157.d008993 _root_.GD.N0232.N0720.N1157.d008995
    _root_.GD.N0232.N0720.N1157.d008992 _root_.GD.N0137.d008918 _root_.GD.N0137.d008919
  have hz : 1 - (1 - z) = z := by ring
  have hcomp : 0 ≤ 1 - z := sub_nonneg.mpr hz1
  have hsqrtMul : Real.sqrt (z * (1 - z)) =
      Real.sqrt z * Real.sqrt (1 - z) := Real.sqrt_mul hz0 _
  have hzSq : Real.sqrt z ^ 2 = z := Real.sq_sqrt hz0
  have hcompSq : Real.sqrt (1 - z) ^ 2 = 1 - z := Real.sq_sqrt hcomp
  rw [hz, hsqrtMul]
  calc
    Real.sqrt (1 - z) * x.2 +
        phi (Real.sqrt z * x.1 - Real.sqrt (1 - z) * x.2) =
      Real.sqrt z * Real.sqrt (1 - z) *
          (Real.sqrt (1 - z) * x.1 + Real.sqrt z * x.2) +
        (phi (Real.sqrt z * x.1 - Real.sqrt (1 - z) * x.2) -
          (1 - z) * (Real.sqrt z * x.1 - Real.sqrt (1 - z) * x.2)) := by
      rw [show Real.sqrt z * Real.sqrt (1 - z) *
              (Real.sqrt (1 - z) * x.1 + Real.sqrt z * x.2) =
            z * Real.sqrt (1 - z) * x.2 +
              (1 - z) * Real.sqrt z * x.1 by
        calc
          _ = Real.sqrt (1 - z) * x.2 * Real.sqrt z ^ 2 +
              Real.sqrt z * x.1 * Real.sqrt (1 - z) ^ 2 := by ring
          _ = _ := by rw [hzSq, hcompSq]; ring
        ]
      ring



theorem d008999
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    _root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0232.N0720.N1157.d008992 z) = gaussianReal 0 1 := by
  unfold _root_.GD.N0232.N0720.N1157.d008992
  exact _root_.GD.N0232.N0720.N1155.d008953
    (sub_nonneg.mpr hz1) (by linarith)


theorem d009000
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∫ x, _root_.GD.N0232.N0720.N1157.d008993 z x ∂_root_.GD.N0232.N0720.N1155.d008950) = 0 := by
  unfold _root_.GD.N0232.N0720.N1157.d008993
  rw [integral_const_mul]
  have hLaw : HasLaw (_root_.GD.N0137.d008918 (1 - z)) (gaussianReal 0 1)
      _root_.GD.N0232.N0720.N1155.d008950 :=
    ⟨(_root_.GD.N0137.d008921 (1 - z)).fst.aemeasurable,
      _root_.GD.N0232.N0720.N1155.d008952
        (sub_nonneg.mpr hz1) (by linarith)⟩
  rw [hLaw.integral_eq, integral_id_gaussianReal, mul_zero]


theorem d009001
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (∫ x, _root_.GD.N0232.N0720.N1157.d008993 z x ^ 2 ∂_root_.GD.N0232.N0720.N1155.d008950) =
      z * (1 - z) := by
  have hzprod : 0 ≤ z * (1 - z) :=
    mul_nonneg hz0 (sub_nonneg.mpr hz1)
  have hLaw : HasLaw (_root_.GD.N0137.d008918 (1 - z)) (gaussianReal 0 1)
      _root_.GD.N0232.N0720.N1155.d008950 :=
    ⟨(_root_.GD.N0137.d008921 (1 - z)).fst.aemeasurable,
      _root_.GD.N0232.N0720.N1155.d008952
        (sub_nonneg.mpr hz1) (by linarith)⟩
  have hsecond :
      (∫ x, _root_.GD.N0137.d008918 (1 - z) x ^ 2
          ∂_root_.GD.N0232.N0720.N1155.d008950) = 1 := by
    have hmeas : AEStronglyMeasurable (fun x : ℝ ↦ x ^ 2)
        (gaussianReal 0 1) :=
      (measurable_id.pow_const 2).aestronglyMeasurable
    have hcomp := hLaw.integral_comp hmeas
    have hvar := variance_fun_id_gaussianReal
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    rw [variance_eq_integral measurable_id'.aemeasurable] at hvar
    rw [integral_id_gaussianReal] at hvar
    have hvar' : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
      simpa using hvar
    exact hcomp.trans hvar'
  unfold _root_.GD.N0232.N0720.N1157.d008993
  rw [show (fun x : ℝ × ℝ ↦
      (Real.sqrt (z * (1 - z)) * _root_.GD.N0137.d008918 (1 - z) x) ^ 2) =
        fun x ↦ (z * (1 - z)) * _root_.GD.N0137.d008918 (1 - z) x ^ 2 by
      funext x
      rw [mul_pow, Real.sq_sqrt hzprod],
    integral_const_mul, hsecond, mul_one]


theorem d009002
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (phi : ℝ → ℝ) (hphiMeas : Measurable phi)
    (hphi : MemLp phi 2 (gaussianReal 0 1)) :
    _root_.GD.N0232.N0720.N1157.d008997 z phi =
      z * (1 - z) + _root_.GD.N0232.N0720.N1157.d008996 z phi := by
  let O : ℝ × ℝ → ℝ := _root_.GD.N0232.N0720.N1157.d008993 z
  let W : ℝ × ℝ → ℝ := _root_.GD.N0232.N0720.N1157.d008992 z
  let C : ℝ × ℝ → ℝ := fun x ↦ _root_.GD.N0232.N0720.N1157.d008995 z phi (W x)
  have hO : MemLp O 2 _root_.GD.N0232.N0720.N1155.d008950 := by
    unfold O _root_.GD.N0232.N0720.N1157.d008993
    exact (_root_.GD.N0232.N0720.N1155.d008954
      (sub_nonneg.mpr hz1.le) (by linarith)).const_mul _
  have hWmap : _root_.GD.N0232.N0720.N1155.d008950.map W = gaussianReal 0 1 := by
    exact _root_.GD.N0232.N0720.N1157.d008999 hz0.le hz1.le
  have hWmeas : AEMeasurable W _root_.GD.N0232.N0720.N1155.d008950 := by
    unfold W _root_.GD.N0232.N0720.N1157.d008992
    exact (_root_.GD.N0137.d008921 (1 - z)).snd.aemeasurable
  have hId : MemLp (fun w : ℝ ↦ w) 2 (gaussianReal 0 1) :=
    memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
  have hFiber : MemLp (_root_.GD.N0232.N0720.N1157.d008995 z phi) 2 (gaussianReal 0 1) := by
    unfold _root_.GD.N0232.N0720.N1157.d008995
    exact hphi.sub (hId.const_mul (1 - z))
  have hC : MemLp C 2 _root_.GD.N0232.N0720.N1155.d008950 := by
    have hmeasMap : AEStronglyMeasurable (_root_.GD.N0232.N0720.N1157.d008995 z phi)
        (_root_.GD.N0232.N0720.N1155.d008950.map W) := by
      rw [hWmap]
      exact hFiber.aestronglyMeasurable
    have hcomp : MemLp ((_root_.GD.N0232.N0720.N1157.d008995 z phi) ∘ W) 2
        _root_.GD.N0232.N0720.N1155.d008950 :=
      (memLp_map_measure_iff hmeasMap hWmeas).mp (by
        rw [hWmap]
        exact hFiber)
    simpa [C, Function.comp_def] using hcomp
  have hindepBase :=
    _root_.GD.N0232.N0720.N1155.d008951
      (sub_nonneg.mpr hz1.le) (by linarith : 1 - z ≤ 1)
  have hindep : IndepFun (fun x ↦ -O x) C _root_.GD.N0232.N0720.N1155.d008950 := by
    have h := hindepBase.comp
      (show Measurable (fun u : ℝ ↦
        -(Real.sqrt (z * (1 - z)) * u)) by fun_prop)
      (show Measurable (_root_.GD.N0232.N0720.N1157.d008995 z phi) by
        unfold _root_.GD.N0232.N0720.N1157.d008995
        fun_prop)
    simpa [O, W, C, _root_.GD.N0232.N0720.N1157.d008993, _root_.GD.N0232.N0720.N1157.d008992,
      Function.comp_def] using h
  have hcentered : (∫ x, -O x ∂_root_.GD.N0232.N0720.N1155.d008950) = 0 := by
    rw [integral_neg, show (∫ x, O x ∂_root_.GD.N0232.N0720.N1155.d008950) = 0 by
      exact _root_.GD.N0232.N0720.N1157.d009000 hz0.le hz1.le,
      neg_zero]
  have hpyth := _root_.GD.N0232.N0720.N1156.d008980
    hO.neg hC hindep hcentered
  have herror : (fun x ↦ (C x - -O x) ^ 2) =
      fun x ↦ _root_.GD.N0232.N0720.N1157.d008994 z phi x ^ 2 := by
    funext x
    rw [_root_.GD.N0232.N0720.N1157.d008998 hz0.le hz1.le]
    simp only [C, W, O]
    ring
  have htax : (∫ x, C x ^ 2 ∂_root_.GD.N0232.N0720.N1155.d008950) =
      _root_.GD.N0232.N0720.N1157.d008996 z phi := by
    have hLaw : HasLaw W (gaussianReal 0 1) _root_.GD.N0232.N0720.N1155.d008950 :=
      ⟨hWmeas, hWmap⟩
    have hsqMeas : AEStronglyMeasurable
        (fun w ↦ _root_.GD.N0232.N0720.N1157.d008995 z phi w ^ 2) (gaussianReal 0 1) :=
      hFiber.integrable_sq.aestronglyMeasurable
    have hmap := hLaw.integral_comp hsqMeas
    simpa [C, W, _root_.GD.N0232.N0720.N1157.d008996, Function.comp_def] using hmap
  have hnegSq : (fun x : ℝ × ℝ ↦ (-O) x ^ 2) =
      fun x ↦ O x ^ 2 := by
    funext x
    simp
  rw [show (fun x ↦ (C x - (-O) x) ^ 2) =
      fun x ↦ _root_.GD.N0232.N0720.N1157.d008994 z phi x ^ 2 by
        simpa only [Pi.neg_apply] using herror,
    hnegSq,
    _root_.GD.N0232.N0720.N1157.d009001 hz0.le hz1.le,
    htax] at hpyth
  exact hpyth




def d009003 (a b z₁ z₂ : ℝ) : ℝ :=
  (a * z₁ + b * z₂) / (a + b)


def d009004 (a b z₁ z₂ : ℝ) : ℝ → ℝ :=
  fun w ↦ (1 - _root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) * w


def d009005 (a b z₁ z₂ : ℝ) : ℝ :=
  a * b / (a + b) * (z₁ - z₂) ^ 2


theorem d009006
    {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (phi : ℝ → ℝ) (w : ℝ) :
    a * _root_.GD.N0232.N0720.N1157.d008995 z₁ phi w ^ 2 +
        b * _root_.GD.N0232.N0720.N1157.d008995 z₂ phi w ^ 2 =
      (a + b) *
          _root_.GD.N0232.N0720.N1157.d008995 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi w ^ 2 +
        _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ * w ^ 2 := by
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  unfold _root_.GD.N0232.N0720.N1157.d008995 _root_.GD.N0232.N0720.N1157.d009003 _root_.GD.N0232.N0720.N1157.d009005
  field_simp [hab]
  ring



theorem d009007
    {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (phi : ℝ → ℝ) (hphi : MemLp phi 2 (gaussianReal 0 1)) :
    a * _root_.GD.N0232.N0720.N1157.d008996 z₁ phi + b * _root_.GD.N0232.N0720.N1157.d008996 z₂ phi =
      (a + b) * _root_.GD.N0232.N0720.N1157.d008996 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi +
        _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ := by
  have hId : MemLp (fun w : ℝ ↦ w) 2 (gaussianReal 0 1) :=
    memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2
  have hE (z : ℝ) : Integrable
      (fun w ↦ _root_.GD.N0232.N0720.N1157.d008995 z phi w ^ 2) (gaussianReal 0 1) := by
    apply MemLp.integrable_sq
    unfold _root_.GD.N0232.N0720.N1157.d008995
    exact hphi.sub (hId.const_mul (1 - z))
  have hW2 : Integrable (fun w : ℝ ↦ w ^ 2) (gaussianReal 0 1) :=
    hId.integrable_sq
  have hsecond : (∫ w : ℝ, w ^ 2 ∂gaussianReal 0 1) = 1 := by
    have hvar := variance_fun_id_gaussianReal
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    rw [variance_eq_integral measurable_id'.aemeasurable] at hvar
    rw [integral_id_gaussianReal] at hvar
    simpa using hvar
  unfold _root_.GD.N0232.N0720.N1157.d008996
  calc
    a * (∫ w, _root_.GD.N0232.N0720.N1157.d008995 z₁ phi w ^ 2 ∂gaussianReal 0 1) +
        b * (∫ w, _root_.GD.N0232.N0720.N1157.d008995 z₂ phi w ^ 2 ∂gaussianReal 0 1) =
      (∫ w, a * _root_.GD.N0232.N0720.N1157.d008995 z₁ phi w ^ 2 +
        b * _root_.GD.N0232.N0720.N1157.d008995 z₂ phi w ^ 2 ∂gaussianReal 0 1) := by
      rw [integral_add ((hE z₁).const_mul a) ((hE z₂).const_mul b),
        integral_const_mul, integral_const_mul]
    _ =
      ∫ w, (a + b) *
          _root_.GD.N0232.N0720.N1157.d008995 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi w ^ 2 +
        _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ * w ^ 2
          ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w ↦
        _root_.GD.N0232.N0720.N1157.d009006 ha hb phi w
    _ = (∫ w, (a + b) *
          _root_.GD.N0232.N0720.N1157.d008995 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi w ^ 2
          ∂gaussianReal 0 1) +
        ∫ w, _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ * w ^ 2
          ∂gaussianReal 0 1 := by
      rw [integral_add
        ((hE (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂)).const_mul (a + b))
        (hW2.const_mul (_root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂))]
    _ = (∫ w, (a + b) *
          _root_.GD.N0232.N0720.N1157.d008995 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi w ^ 2
          ∂gaussianReal 0 1) + _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ := by
      rw [integral_const_mul, integral_const_mul, hsecond, mul_one]
    _ = (a + b) *
          (∫ w, _root_.GD.N0232.N0720.N1157.d008995 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi w ^ 2
            ∂gaussianReal 0 1) + _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ := by
      rw [integral_const_mul]


theorem d009008
    {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ := by
  unfold _root_.GD.N0232.N0720.N1157.d009005
  exact mul_nonneg (div_nonneg (mul_nonneg ha.le hb.le) (add_pos ha hb).le)
    (sq_nonneg _)



theorem d009009
    {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 < _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ ↔ z₁ ≠ z₂ := by
  have hcoef : 0 < a * b / (a + b) :=
    div_pos (mul_pos ha hb) (add_pos ha hb)
  unfold _root_.GD.N0232.N0720.N1157.d009005
  rw [mul_pos_iff_of_pos_left hcoef, sq_pos_iff, sub_ne_zero]



theorem d009010
    {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (phi : ℝ → ℝ) (hphi : MemLp phi 2 (gaussianReal 0 1)) :
    _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ ≤
      a * _root_.GD.N0232.N0720.N1157.d008996 z₁ phi + b * _root_.GD.N0232.N0720.N1157.d008996 z₂ phi := by
  rw [_root_.GD.N0232.N0720.N1157.d009007
    ha hb phi hphi]
  have hnonneg : 0 ≤ _root_.GD.N0232.N0720.N1157.d008996
      (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi :=
    integral_nonneg fun w ↦ sq_nonneg _
  nlinarith [add_pos ha hb]




theorem d009011
    {a b z₁ z₂ epsilon : ℝ} (ha : 0 < a) (hb : 0 < b)
    (phi : ℝ → ℝ) (hphi : MemLp phi 2 (gaussianReal 0 1))
    (hnear : a * _root_.GD.N0232.N0720.N1157.d008996 z₁ phi + b * _root_.GD.N0232.N0720.N1157.d008996 z₂ phi ≤
      _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ + epsilon) :
    _root_.GD.N0232.N0720.N1157.d008996 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi ≤
      epsilon / (a + b) := by
  rw [_root_.GD.N0232.N0720.N1157.d009007
    ha hb phi hphi] at hnear
  exact (le_div_iff₀ (add_pos ha hb)).2 (by linarith)



theorem d009012
    {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (phi : ℝ → ℝ) (hphi : MemLp phi 2 (gaussianReal 0 1)) :
    a * _root_.GD.N0232.N0720.N1157.d008996 z₁ phi + b * _root_.GD.N0232.N0720.N1157.d008996 z₂ phi =
        _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ ↔
      phi =ᵐ[gaussianReal 0 1] _root_.GD.N0232.N0720.N1157.d009004 a b z₁ z₂ := by
  have hdecomp := _root_.GD.N0232.N0720.N1157.d009007
    (z₁ := z₁) (z₂ := z₂) ha hb phi hphi
  have hCenter : MemLp (_root_.GD.N0232.N0720.N1157.d009004 a b z₁ z₂) 2
      (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2).const_mul _
  have hFiber : MemLp
      (_root_.GD.N0232.N0720.N1157.d008995 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi) 2
      (gaussianReal 0 1) := by
    unfold _root_.GD.N0232.N0720.N1157.d008995
    exact hphi.sub hCenter
  have hab : 0 < a + b := add_pos ha hb
  constructor
  · intro h
    have henergy : _root_.GD.N0232.N0720.N1157.d008996 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi = 0 := by
      rw [h] at hdecomp
      nlinarith
    have hsq :
        (fun w ↦ _root_.GD.N0232.N0720.N1157.d008995 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi w ^ 2)
            =ᵐ[gaussianReal 0 1] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun w ↦ sq_nonneg
          (_root_.GD.N0232.N0720.N1157.d008995 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi w))
        hFiber.integrable_sq).1 (by simpa [_root_.GD.N0232.N0720.N1157.d008996] using henergy)
    filter_upwards [hsq] with w hw
    have hzero : _root_.GD.N0232.N0720.N1157.d008995 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi w = 0 :=
      sq_eq_zero_iff.mp (by simpa using hw)
    dsimp [_root_.GD.N0232.N0720.N1157.d008995] at hzero
    dsimp [_root_.GD.N0232.N0720.N1157.d009004]
    linarith
  · intro hae
    have hzero : _root_.GD.N0232.N0720.N1157.d008996 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi = 0 := by
      unfold _root_.GD.N0232.N0720.N1157.d008996
      have hsq :
          (fun w ↦ _root_.GD.N0232.N0720.N1157.d008995 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi w ^ 2)
              =ᵐ[gaussianReal 0 1] 0 := by
        filter_upwards [hae] with w hw
        simp [_root_.GD.N0232.N0720.N1157.d008995, _root_.GD.N0232.N0720.N1157.d009004, hw]
      rw [integral_congr_ae hsq]
      simp
    rw [hdecomp, hzero]
    ring


theorem d009013
    {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * _root_.GD.N0232.N0720.N1157.d008996 z₁ (_root_.GD.N0232.N0720.N1157.d009004 a b z₁ z₂) +
        b * _root_.GD.N0232.N0720.N1157.d008996 z₂ (_root_.GD.N0232.N0720.N1157.d009004 a b z₁ z₂) =
      _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ := by
  have hopt : MemLp (_root_.GD.N0232.N0720.N1157.d009004 a b z₁ z₂) 2
      (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2).const_mul _
  rw [_root_.GD.N0232.N0720.N1157.d009007
    ha hb _ hopt]
  have hzero : _root_.GD.N0232.N0720.N1157.d008996 (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂)
      (_root_.GD.N0232.N0720.N1157.d009004 a b z₁ z₂) = 0 := by
    unfold _root_.GD.N0232.N0720.N1157.d008996 _root_.GD.N0232.N0720.N1157.d009004 _root_.GD.N0232.N0720.N1157.d008995
    simp
  rw [hzero]
  ring



theorem d009014
    {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsLeast
      {x : ℝ | ∃ phi : ℝ → ℝ,
        Measurable phi ∧ MemLp phi 2 (gaussianReal 0 1) ∧
          x = a * _root_.GD.N0232.N0720.N1157.d008996 z₁ phi + b * _root_.GD.N0232.N0720.N1157.d008996 z₂ phi}
      (_root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂) := by
  constructor
  · refine ⟨_root_.GD.N0232.N0720.N1157.d009004 a b z₁ z₂, ?_, ?_, ?_⟩
    · unfold _root_.GD.N0232.N0720.N1157.d009004
      fun_prop
    · exact (memLp_id_gaussianReal
        (μ := (0 : ℝ)) (v := 1) 2).const_mul _
    · exact (_root_.GD.N0232.N0720.N1157.d009013 ha hb).symm
  · rintro x ⟨phi, _hphiMeas, hphi, rfl⟩
    exact _root_.GD.N0232.N0720.N1157.d009010 ha hb phi hphi



theorem d009015
    {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * (z₁ * (1 - z₁)) + b * (z₂ * (1 - z₂)) +
        _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ =
      (a + b) *
        (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂ *
          (1 - _root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂)) := by
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  unfold _root_.GD.N0232.N0720.N1157.d009005 _root_.GD.N0232.N0720.N1157.d009003
  field_simp [hab]
  ring


theorem d009016
    {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hz₁0 : 0 < z₁) (hz₁1 : z₁ < 1)
    (hz₂0 : 0 < z₂) (hz₂1 : z₂ < 1)
    (phi : ℝ → ℝ) (hphiMeas : Measurable phi)
    (hphi : MemLp phi 2 (gaussianReal 0 1)) :
    a * _root_.GD.N0232.N0720.N1157.d008997 z₁ phi +
        b * _root_.GD.N0232.N0720.N1157.d008997 z₂ phi =
      (a + b) *
          (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂ *
            (1 - _root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂)) +
        (a + b) * _root_.GD.N0232.N0720.N1157.d008996
          (_root_.GD.N0232.N0720.N1157.d009003 a b z₁ z₂) phi := by
  rw [_root_.GD.N0232.N0720.N1157.d009002
      hz₁0 hz₁1 phi hphiMeas hphi,
    _root_.GD.N0232.N0720.N1157.d009002
      hz₂0 hz₂1 phi hphiMeas hphi]
  have hE := _root_.GD.N0232.N0720.N1157.d009007
    (z₁ := z₁) (z₂ := z₂) ha hb phi hphi
  have hF := _root_.GD.N0232.N0720.N1157.d009015
    (z₁ := z₁) (z₂ := z₂) ha hb
  nlinarith



theorem d009017
    {a b z₁ z₂ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    _root_.GD.N0232.N0720.N1157.d009005 a b z₁ z₂ =
      _root_.GD.N0230.N0702.d001136 a b (a * (1 - z₁)) (b * (1 - z₂)) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  unfold _root_.GD.N0232.N0720.N1157.d009005 _root_.GD.N0230.N0702.d001136 _root_.GD.N0230.N0702.d001134 _root_.GD.N0230.N0702.d001123
  field_simp [ha0, hb0]
  ring

end

end N1157
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1157.d009002
#print axioms _root_.GD.N0232.N0720.N1157.d009007
#print axioms _root_.GD.N0232.N0720.N1157.d009012
#print axioms _root_.GD.N0232.N0720.N1157.d009014
#print axioms _root_.GD.N0232.N0720.N1157.d009016
#print axioms _root_.GD.N0232.N0720.N1157.d009017
