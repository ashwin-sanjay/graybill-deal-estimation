import GD.Module0787
import GD.Module0963
























open Filter Function MeasureTheory Set Topology
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1146

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N0834
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)

noncomputable local instance d015196 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance




theorem d015197
    (b r x : ℝ) (hr : 1 < r) :
    x ^ 2 / 2 - (r * x + b) ^ 2 / 2 ≤
      b ^ 2 / (2 * (r ^ 2 - 1)) := by
  have hr2 : 0 < r ^ 2 - 1 := by
    nlinarith [sq_nonneg (r - 1)]
  have hidentity :
      b ^ 2 / (2 * (r ^ 2 - 1)) -
          (x ^ 2 / 2 - (r * x + b) ^ 2 / 2) =
        (((r ^ 2 - 1) * x + r * b) ^ 2) /
          (2 * (r ^ 2 - 1)) := by
    field_simp [hr2.ne']
    ring
  apply sub_nonneg.mp
  rw [hidentity]
  positivity



theorem d015198
    (b r x : ℝ) (hr : 1 < r) :
    _root_.GD.N0232.N0719.N0932.d009204 (-(b / r)) r⁻¹ x ≤
      r * Real.exp (b ^ 2 / (2 * (r ^ 2 - 1))) := by
  rw [_root_.GD.N0232.N0719.N0834.d011965 b r x (by linarith)]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (_root_.GD.N0232.N0720.N1146.d015197 b r x hr))
    (by linarith)


theorem d015199
    (sampleSize : ℕ) (b r : ℝ) (hr : 1 < r)
    (x : _root_.GD.N0137.d008894 sampleSize) :
    _root_.GD.N0232.N0719.N0932.d009213 sampleSize (-(b / r)) r⁻¹ x ≤
      (r * Real.exp (b ^ 2 / (2 * (r ^ 2 - 1)))) ^ sampleSize := by
  unfold _root_.GD.N0232.N0719.N0932.d009213 _root_.GD.N0232.N0719.N0932.d009190
  calc
    (∏ i : Fin sampleSize,
        _root_.GD.N0232.N0719.N0932.d009204 (-(b / r)) r⁻¹ (x i)) ≤
        ∏ _i : Fin sampleSize,
          (r * Real.exp (b ^ 2 / (2 * (r ^ 2 - 1)))) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact _root_.GD.N0232.N0719.N0932.d009205 (-(b / r)) r⁻¹ (x i)
      · intro i hi
        exact _root_.GD.N0232.N0720.N1146.d015198 b r (x i) hr
    _ = (r * Real.exp (b ^ 2 / (2 * (r ^ 2 - 1)))) ^ sampleSize := by
      simp



def d015200
    (g : _root_.GD.N0232.N0720.N1482.d015118) : ℝ :=
  (g.d009239 * Real.exp
    (g.shift ^ 2 / (2 * (g.d009239 ^ 2 - 1)))) ^ (m + n)


def d015201
    (g : _root_.GD.N0232.N0720.N1482.d015118) : ℝ≥0∞ :=
  ENNReal.ofReal (_root_.GD.N0232.N0720.N1146.d015200 m n g)

theorem d015202
    (g : _root_.GD.N0232.N0720.N1482.d015118) :
    0 ≤ _root_.GD.N0232.N0720.N1146.d015200 m n g := by
  unfold _root_.GD.N0232.N0720.N1146.d015200
  exact pow_nonneg
    (mul_nonneg g.d009240.le (Real.exp_pos _).le) _

theorem d015203
    (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1146.d015201 m n g ≠ ∞ := by
  exact ENNReal.ofReal_ne_top

theorem d015204 (g : _root_.GD.N0232.N0720.N1482.d015118) :
    g⁻¹.d009239 = g.d009239⁻¹ := by
  change Real.exp (-g.logScale) = (Real.exp g.logScale)⁻¹
  exact Real.exp_neg g.logScale

theorem d015205 (g : _root_.GD.N0232.N0720.N1482.d015118) :
    g⁻¹.shift = -(g.shift / g.d009239) := by
  change -(Real.exp (-g.logScale) * g.shift) =
    -(g.shift / Real.exp g.logScale)
  rw [Real.exp_neg, div_eq_mul_inv, mul_comm]



theorem d015206
    (g : _root_.GD.N0232.N0720.N1482.d015118) (hr : 1 < g.d009239)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1484.d015099 g) omega ≤
      _root_.GD.N0232.N0720.N1146.d015200 m n g := by
  have hlocation :
      (_root_.GD.N0232.N0720.N1484.d015099 g).location =
        -(g.shift / g.d009239) := by
    change g⁻¹.shift + g⁻¹.d009239 * 0 = _
    rw [mul_zero, add_zero, _root_.GD.N0232.N0720.N1146.d015205]
  have hscale₁ :
      (_root_.GD.N0232.N0720.N1484.d015099 g).scale₁ = g.d009239⁻¹ := by
    change g⁻¹.d009239 * 1 = _
    rw [mul_one, _root_.GD.N0232.N0720.N1146.d015204]
  have hscale₂ :
      (_root_.GD.N0232.N0720.N1484.d015099 g).scale₂ = g.d009239⁻¹ := by
    change g⁻¹.d009239 * 1 = _
    rw [mul_one, _root_.GD.N0232.N0720.N1146.d015204]
  unfold _root_.GD.N0232.N0720.N1499.d015001 _root_.GD.N0232.N0720.N1146.d015200
  rw [hlocation, hscale₁, hscale₂, pow_add]
  exact mul_le_mul
    (_root_.GD.N0232.N0720.N1146.d015199
      m g.shift g.d009239 hr omega.1)
    (_root_.GD.N0232.N0720.N1146.d015199
      n g.shift g.d009239 hr omega.2)
    (_root_.GD.N0232.N0719.N0932.d009215
      n (-(g.shift / g.d009239)) g.d009239⁻¹ omega.2)
    (pow_nonneg
      (mul_nonneg g.d009240.le (Real.exp_pos _).le) m)


theorem d015207
    (g : _root_.GD.N0232.N0720.N1482.d015118) :
    _root_.GD.N0232.N0720.N1146.d015200 m n g =
      g.d009239 ^ (m + n) *
        Real.exp
          (((m + n : ℕ) : ℝ) *
            (g.shift ^ 2 / (2 * (g.d009239 ^ 2 - 1)))) := by
  unfold _root_.GD.N0232.N0720.N1146.d015200
  rw [mul_pow, ← Real.exp_nat_mul]





structure d015208 (g : _root_.GD.N0232.N0720.N1482.d015118) where
  densityBound : ℝ≥0∞
  densityBound_ne_top : densityBound ≠ ∞
  pullback_le :
    (_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1484.d015094 m n g) ≤
      densityBound • _root_.GD.N0232.N0720.N1080.d014172 m n



def d015209
    (g : _root_.GD.N0232.N0720.N1482.d015118) (hr : 1 < g.d009239) :
    _root_.GD.N0232.N0720.N1146.d015208 m n g where
  densityBound := _root_.GD.N0232.N0720.N1146.d015201 m n g
  densityBound_ne_top := _root_.GD.N0232.N0720.N1146.d015203 m n g
  pullback_le := by
    rw [_root_.GD.N0232.N0720.N1484.d015102]
    calc
      (_root_.GD.N0232.N0720.N1080.d014172 m n).withDensity
          (fun omega ↦ ENNReal.ofReal
            (_root_.GD.N0232.N0720.N1499.d015001 m n
              (_root_.GD.N0232.N0720.N1484.d015099 g) omega)) ≤
          (_root_.GD.N0232.N0720.N1080.d014172 m n).withDensity
            (fun _ ↦ _root_.GD.N0232.N0720.N1146.d015201 m n g) := by
        apply withDensity_mono
        exact ae_of_all _ fun omega ↦
          ENNReal.ofReal_le_ofReal
            (_root_.GD.N0232.N0720.N1146.d015206 m n g hr omega)
      _ = _root_.GD.N0232.N0720.N1146.d015201 m n g •
          _root_.GD.N0232.N0720.N1080.d014172 m n := by rw [withDensity_const]





theorem d015210
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    MemLp (_root_.GD.N0232.N0720.N1214.d014265 m n p) 2
      ((_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1484.d015094 m n g)) := by
  exact (_root_.GD.N0232.N0720.N1214.d014268 m n p).of_measure_le_smul
    certificate.densityBound_ne_top certificate.pullback_le



theorem d015211
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    MemLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hpull : MemLp
      (_root_.GD.N0232.N0720.N1214.d014265 m n p ∘ _root_.GD.N0232.N0720.N1484.d015094 m n g) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (memLp_map_measure_iff
      (_root_.GD.N0232.N0720.N1214.d014266 m n p).aestronglyMeasurable
      (_root_.GD.N0232.N0720.N1484.d015095 m n g).aemeasurable).1
      (_root_.GD.N0232.N0720.N1146.d015210 m n certificate p)
  have hscaled : MemLp
      (fun omega ↦ g.d009239 *
        _root_.GD.N0232.N0720.N1214.d014265 m n p (_root_.GD.N0232.N0720.N1484.d015094 m n g omega)) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    simpa [Function.comp_def] using hpull.const_mul g.d009239
  have hshift : MemLp
      (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g.shift) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := memLp_const g.shift
  have hraw : _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) =
      (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g.shift) +
        (fun omega ↦ g.d009239 *
          _root_.GD.N0232.N0720.N1214.d014265 m n p (_root_.GD.N0232.N0720.N1484.d015094 m n g omega)) := by
    funext omega
    simp [_root_.GD.N0232.N0720.N1214.d014261, _root_.GD.N0232.N0720.N1484.d015094, _root_.GD.N0232.N0719.N0946.d009229.d009244, Pi.add_apply]
  exact (hshift.add hscaled).congr_norm
    (_root_.GD.N0232.N0720.N1214.d014262 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)
      (_root_.GD.N0232.N0720.N1214.d014266 m n p)).aestronglyMeasurable
    (ae_of_all _ fun omega ↦
      congrArg norm (congrFun hraw omega).symm)



def d015212
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))
    (_root_.GD.N0232.N0720.N1146.d015211 m n certificate p)


def d015213
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g) : ℝ :=
  g.d009239 * Real.sqrt certificate.densityBound.toReal

theorem d015214
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g) :
    0 ≤ _root_.GD.N0232.N0720.N1146.d015213 m n certificate := by
  unfold _root_.GD.N0232.N0720.N1146.d015213
  exact mul_nonneg g.d009240.le (Real.sqrt_nonneg _)



theorem d015215
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate p -
        _root_.GD.N0232.N0720.N1146.d015212 m n certificate q‖ ≤
      _root_.GD.N0232.N0720.N1146.d015213 m n certificate * ‖p - q‖ := by
  let fp := _root_.GD.N0232.N0720.N1214.d014265 m n p
  let fq := _root_.GD.N0232.N0720.N1214.d014265 m n q
  let diff : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := fun omega ↦ fp omega - fq omega
  let outp := _root_.GD.N0232.N0720.N1214.d014261 m n g fp
  let outq := _root_.GD.N0232.N0720.N1214.d014261 m n g fq
  let houtp : MemLp outp 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1146.d015211 m n certificate p
  let houtq : MemLp outq 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1146.d015211 m n certificate q
  let hfp : MemLp fp 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := _root_.GD.N0232.N0720.N1214.d014268 m n p
  let hfq : MemLp fq 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := _root_.GD.N0232.N0720.N1214.d014268 m n q
  let hdiff : MemLp diff 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := hfp.sub hfq
  have hdiffPull : MemLp diff 2
      ((_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1484.d015094 m n g)) :=
    hdiff.of_measure_le_smul certificate.densityBound_ne_top
      certificate.pullback_le
  have hcomp : MemLp (diff ∘ _root_.GD.N0232.N0720.N1484.d015094 m n g) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (memLp_map_measure_iff hdiffPull.aestronglyMeasurable
      (_root_.GD.N0232.N0720.N1484.d015095 m n g).aemeasurable).1 hdiffPull
  have hraw : outp - outq =
      g.d009239 • (diff ∘ _root_.GD.N0232.N0720.N1484.d015094 m n g) := by
    funext omega
    change
      (g.shift + g.d009239 * fp (_root_.GD.N0232.N0720.N1484.d015094 m n g omega)) -
          (g.shift + g.d009239 * fq (_root_.GD.N0232.N0720.N1484.d015094 m n g omega)) =
        g.d009239 *
          (fp (_root_.GD.N0232.N0720.N1484.d015094 m n g omega) -
            fq (_root_.GD.N0232.N0720.N1484.d015094 m n g omega))
    ring
  have hcompNorm :
      eLpNorm (diff ∘ _root_.GD.N0232.N0720.N1484.d015094 m n g) 2
          (_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
        certificate.densityBound ^ (1 / 2 : ℝ) *
          eLpNorm diff 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    rw [← eLpNorm_map_measure hdiffPull.aestronglyMeasurable
      (_root_.GD.N0232.N0720.N1484.d015095 m n g).aemeasurable]
    calc
      eLpNorm diff 2
          ((_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1484.d015094 m n g)) ≤
          eLpNorm diff 2
            (certificate.densityBound • _root_.GD.N0232.N0720.N1080.d014172 m n) :=
        eLpNorm_mono_measure diff certificate.pullback_le
      _ = certificate.densityBound ^ (1 / 2 : ℝ) *
          eLpNorm diff 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
        rw [eLpNorm_smul_measure_of_ne_top (by norm_num)]
        norm_num
  have houtNorm :
      eLpNorm (outp - outq) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
        ‖g.d009239‖ₑ *
          (certificate.densityBound ^ (1 / 2 : ℝ) *
            eLpNorm diff 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)) := by
    rw [hraw, eLpNorm_const_smul]
    exact mul_le_mul_right hcompNorm ‖g.d009239‖ₑ
  have hright_ne_top :
      ‖g.d009239‖ₑ *
          (certificate.densityBound ^ (1 / 2 : ℝ) *
            eLpNorm diff 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)) ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          certificate.densityBound_ne_top)
        hdiff.2.ne)
  have htoReal := ENNReal.toReal_mono hright_ne_top houtNorm
  have hdiffToLp : MemLp.toLp diff hdiff = p - q := by
    calc
      MemLp.toLp diff hdiff =
          MemLp.toLp fp hfp - MemLp.toLp fq hfq :=
        MemLp.toLp_sub hfp hfq
      _ = p - q := by
        rw [_root_.GD.N0232.N0720.N1214.d014269 m n p, _root_.GD.N0232.N0720.N1214.d014269 m n q]
  change ‖MemLp.toLp outp houtp - MemLp.toLp outq houtq‖ ≤ _
  rw [← MemLp.toLp_sub houtp houtq, Lp.norm_toLp]
  have hdensityToReal :
      (certificate.densityBound ^ (1 / 2 : ℝ)).toReal =
        Real.sqrt certificate.densityBound.toReal := by
    rw [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  have hdiffToReal :
      (eLpNorm diff 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)).toReal = ‖p - q‖ := by
    rw [← Lp.norm_toLp diff hdiff, hdiffToLp]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at htoReal
  rw [hdensityToReal, hdiffToReal] at htoReal
  simpa [_root_.GD.N0232.N0720.N1146.d015213,
    Real.norm_eq_abs, abs_of_pos g.d009240, mul_assoc] using htoReal


theorem d015216
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g) :
    LipschitzWith
      ⟨_root_.GD.N0232.N0720.N1146.d015213 m n certificate,
        _root_.GD.N0232.N0720.N1146.d015214 m n certificate⟩
      (_root_.GD.N0232.N0720.N1146.d015212 m n certificate) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change dist (_root_.GD.N0232.N0720.N1146.d015212 m n certificate p)
      (_root_.GD.N0232.N0720.N1146.d015212 m n certificate q) ≤
    _root_.GD.N0232.N0720.N1146.d015213 m n certificate * dist p q
  simpa [dist_eq_norm] using
    _root_.GD.N0232.N0720.N1146.d015215 m n certificate p q





theorem d015217
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (q r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hclose : Tendsto (fun j ↦ ‖q j - r j‖) atTop (nhds 0))
    (hfixed : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (r j) - r j‖)
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (q j) - q j‖)
      atTop (nhds 0) := by
  let C := _root_.GD.N0232.N0720.N1146.d015213 m n certificate
  have hreverse : Tendsto (fun j ↦ ‖r j - q j‖) atTop (nhds 0) := by
    simpa only [norm_sub_rev] using hclose
  have hupper : ∀ j,
      ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (q j) - q j‖ ≤
        C * ‖q j - r j‖ +
          (‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (r j) - r j‖ +
            ‖r j - q j‖) := by
    intro j
    have hid :
        _root_.GD.N0232.N0720.N1146.d015212 m n certificate (q j) - q j =
          (_root_.GD.N0232.N0720.N1146.d015212 m n certificate (q j) -
              _root_.GD.N0232.N0720.N1146.d015212 m n certificate (r j)) +
            ((_root_.GD.N0232.N0720.N1146.d015212 m n certificate (r j) - r j) +
              (r j - q j)) := by
      abel
    rw [hid]
    calc
      ‖(_root_.GD.N0232.N0720.N1146.d015212 m n certificate (q j) -
            _root_.GD.N0232.N0720.N1146.d015212 m n certificate (r j)) +
          ((_root_.GD.N0232.N0720.N1146.d015212 m n certificate (r j) - r j) +
            (r j - q j))‖ ≤
          ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (q j) -
            _root_.GD.N0232.N0720.N1146.d015212 m n certificate (r j)‖ +
            ‖(_root_.GD.N0232.N0720.N1146.d015212 m n certificate (r j) - r j) +
              (r j - q j)‖ := norm_add_le _ _
      _ ≤ ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (q j) -
            _root_.GD.N0232.N0720.N1146.d015212 m n certificate (r j)‖ +
          (‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (r j) - r j‖ +
            ‖r j - q j‖) := by
        gcongr
        exact norm_add_le _ _
      _ ≤ C * ‖q j - r j‖ +
          (‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (r j) - r j‖ +
            ‖r j - q j‖) := by
        gcongr
        exact _root_.GD.N0232.N0720.N1146.d015215
          m n certificate (q j) (r j)
  have hmajor : Tendsto
      (fun j ↦ C * ‖q j - r j‖ +
        (‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (r j) - r j‖ +
          ‖r j - q j‖)) atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      (hclose.const_mul C).add (hfixed.add hreverse)
  exact squeeze_zero
    (fun j ↦ norm_nonneg
      (_root_.GD.N0232.N0720.N1146.d015212 m n certificate (q j) - q j))
    hupper hmajor



theorem d015218
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1146.d015212 m n certificate p =
      _root_.GD.N0232.N0720.N1159.d014642 m n g p hp := by
  unfold _root_.GD.N0232.N0720.N1146.d015212 _root_.GD.N0232.N0720.N1159.d014642
  apply MemLp.toLp_congr
  exact Filter.EventuallyEq.rfl



theorem d015219 : _root_.GD.N0232.N0720.N1482.d015130.d009239 = 2 := by
  simp [_root_.GD.N0232.N0720.N1482.d015130, _root_.GD.N0232.N0720.N1482.d015129, _root_.GD.N0232.N0719.N0946.d009229.d009239,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem d015220 :
    _root_.GD.N0232.N0720.N1482.d015131.d009239 = 3 := by
  simp [_root_.GD.N0232.N0720.N1482.d015131, _root_.GD.N0232.N0719.N0946.d009229.d009239,
    Real.exp_log (by norm_num : (0 : ℝ) < 3)]

def d015221 :
    _root_.GD.N0232.N0720.N1146.d015208 m n _root_.GD.N0232.N0720.N1482.d015130 :=
  _root_.GD.N0232.N0720.N1146.d015209 m n _root_.GD.N0232.N0720.N1482.d015130 (by
    rw [_root_.GD.N0232.N0720.N1146.d015219]
    norm_num)

def d015222 :
    _root_.GD.N0232.N0720.N1146.d015208 m n _root_.GD.N0232.N0720.N1482.d015131 :=
  _root_.GD.N0232.N0720.N1146.d015209 m n _root_.GD.N0232.N0720.N1482.d015131 (by
    rw [_root_.GD.N0232.N0720.N1146.d015220]
    norm_num)


theorem d015223 :
    (_root_.GD.N0232.N0720.N1146.d015221 m n).densityBound =
      ENNReal.ofReal ((2 : ℝ) ^ (m + n)) := by
  change _root_.GD.N0232.N0720.N1146.d015201 m n _root_.GD.N0232.N0720.N1482.d015130 = _
  unfold _root_.GD.N0232.N0720.N1146.d015201 _root_.GD.N0232.N0720.N1146.d015200
  rw [_root_.GD.N0232.N0720.N1146.d015219]
  change ENNReal.ofReal
    ((2 * Real.exp (0 ^ 2 / (2 * (2 ^ 2 - 1)))) ^ (m + n)) = _
  norm_num


theorem d015224 :
    (_root_.GD.N0232.N0720.N1146.d015222 m n).densityBound =
      ENNReal.ofReal
        ((3 * Real.exp (1 / 16 : ℝ)) ^ (m + n)) := by
  change _root_.GD.N0232.N0720.N1146.d015201 m n _root_.GD.N0232.N0720.N1482.d015131 = _
  unfold _root_.GD.N0232.N0720.N1146.d015201 _root_.GD.N0232.N0720.N1146.d015200
  rw [_root_.GD.N0232.N0720.N1146.d015220]
  change ENNReal.ofReal
    ((3 * Real.exp (1 ^ 2 / (2 * (3 ^ 2 - 1)))) ^ (m + n)) = _
  norm_num



theorem d015225 :
    (_root_.GD.N0232.N0720.N1146.d015222 m n).densityBound =
      ENNReal.ofReal
        ((3 : ℝ) ^ (m + n) *
          Real.exp (((m + n : ℕ) : ℝ) / 16)) := by
  rw [_root_.GD.N0232.N0720.N1146.d015224]
  apply congrArg ENNReal.ofReal
  calc
    (3 * Real.exp (1 / 16 : ℝ)) ^ (m + n) =
        (3 : ℝ) ^ (m + n) * Real.exp (1 / 16 : ℝ) ^ (m + n) :=
      mul_pow _ _ _
    _ = (3 : ℝ) ^ (m + n) *
        Real.exp (((m + n : ℕ) : ℝ) * (1 / 16 : ℝ)) := by
      rw [Real.exp_nat_mul]
    _ = (3 : ℝ) ^ (m + n) *
        Real.exp (((m + n : ℕ) : ℝ) / 16) := by
      congr 2
      ring

theorem d015226 :
    _root_.GD.N0232.N0720.N1146.d015213 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) =
      2 * Real.sqrt ((2 : ℝ) ^ (m + n)) := by
  unfold _root_.GD.N0232.N0720.N1146.d015213
  rw [_root_.GD.N0232.N0720.N1146.d015219, _root_.GD.N0232.N0720.N1146.d015223]
  rw [ENNReal.toReal_ofReal (pow_nonneg (by norm_num) (m + n))]

theorem d015227 :
    _root_.GD.N0232.N0720.N1146.d015213 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) =
      3 * Real.sqrt
        ((3 * Real.exp (1 / 16 : ℝ)) ^ (m + n)) := by
  unfold _root_.GD.N0232.N0720.N1146.d015213
  rw [_root_.GD.N0232.N0720.N1146.d015220,
    _root_.GD.N0232.N0720.N1146.d015224]
  rw [ENNReal.toReal_ofReal
    (pow_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Real.exp_pos _).le)
      (m + n))]


def d015228 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1146.d015212 m n (_root_.GD.N0232.N0720.N1146.d015221 m n)


def d015229 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1146.d015212 m n
    (_root_.GD.N0232.N0720.N1146.d015222 m n)


theorem d015230
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖_root_.GD.N0232.N0720.N1146.d015228 m n p -
        _root_.GD.N0232.N0720.N1146.d015228 m n q‖ ≤
      2 * Real.sqrt ((2 : ℝ) ^ (m + n)) * ‖p - q‖ := by
  change ‖_root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) p -
      _root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) q‖ ≤ _
  rw [← _root_.GD.N0232.N0720.N1146.d015226 m n]
  exact _root_.GD.N0232.N0720.N1146.d015215 m n
    (_root_.GD.N0232.N0720.N1146.d015221 m n) p q



theorem d015231
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖_root_.GD.N0232.N0720.N1146.d015229 m n p -
        _root_.GD.N0232.N0720.N1146.d015229 m n q‖ ≤
      3 * Real.sqrt
        ((3 * Real.exp (1 / 16 : ℝ)) ^ (m + n)) * ‖p - q‖ := by
  change ‖_root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) p -
      _root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) q‖ ≤ _
  rw [← _root_.GD.N0232.N0720.N1146.d015227 m n]
  exact _root_.GD.N0232.N0720.N1146.d015215 m n
    (_root_.GD.N0232.N0720.N1146.d015222 m n) p q



theorem d015232
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q) :
    ‖_root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp -
        _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 q hq‖ ≤
      2 * Real.sqrt ((2 : ℝ) ^ (m + n)) * ‖p - q‖ := by
  rw [← _root_.GD.N0232.N0720.N1146.d015218 m n
      (_root_.GD.N0232.N0720.N1146.d015221 m n) p hp,
    ← _root_.GD.N0232.N0720.N1146.d015218 m n
      (_root_.GD.N0232.N0720.N1146.d015221 m n) q hq]
  exact _root_.GD.N0232.N0720.N1146.d015230 m n p q



theorem d015233
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q) :
    ‖_root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp -
        _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 q hq‖ ≤
      3 * Real.sqrt
        ((3 * Real.exp (1 / 16 : ℝ)) ^ (m + n)) * ‖p - q‖ := by
  rw [← _root_.GD.N0232.N0720.N1146.d015218 m n
      (_root_.GD.N0232.N0720.N1146.d015222 m n) p hp,
    ← _root_.GD.N0232.N0720.N1146.d015218 m n
      (_root_.GD.N0232.N0720.N1146.d015222 m n) q hq]
  exact _root_.GD.N0232.N0720.N1146.d015231 m n p q












end

end N1146
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1146.d015197
#print axioms _root_.GD.N0232.N0720.N1146.d015206
#print axioms _root_.GD.N0232.N0720.N1146.d015209
#print axioms _root_.GD.N0232.N0720.N1146.d015215
#print axioms _root_.GD.N0232.N0720.N1146.d015217
#print axioms _root_.GD.N0232.N0720.N1146.d015218
#print axioms _root_.GD.N0232.N0720.N1146.d015232
#print axioms _root_.GD.N0232.N0720.N1146.d015233
