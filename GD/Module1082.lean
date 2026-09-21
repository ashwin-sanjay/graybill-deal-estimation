import GD.Module1067
import GD.Module1025


























open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1469

noncomputable section

open _root_.GD.N0232.N0720.N1028
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1105
open _root_.GD.N0232.N0720.N1128
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1501
open _root_.GD.N0232.N0720.N1482

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)


noncomputable def d017316 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1501.d016291 m n s.value



noncomputable def d017317
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (theta : _root_.GD.N0232.N0720.N1080.d014168) : ENNReal :=
  _root_.GD.N0232.N0720.N1028.d015328 m n theta (_root_.GD.N0232.N0720.N1469.d017316 m n s) s.value



def d017318
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ (g : _root_.GD.N0232.N0720.N1482.d015118) (theta : _root_.GD.N0232.N0720.N1080.d014168),
    _root_.GD.N0232.N0720.N1469.d017317 m n s (_root_.GD.N0232.N0720.N1215.d014272 g theta) =
      ENNReal.ofReal (g.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1469.d017317 m n s theta



theorem d017319
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1469.d017316 m n s) := by
  intro theta
  exact ne_top_of_le_ne_top (s.finiteRisk theta)
    (_root_.GD.N0232.N0720.N1501.d016299 m n hm hn theta s.value)

theorem d017320
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1469.d017316 m n s ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value := by
  intro theta
  exact _root_.GD.N0232.N0720.N1501.d016299 m n hm hn theta s.value






theorem d017321
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1128.d017098 m n theta
        (_root_.GD.N0232.N0720.N1469.d017316 m n s) s.value =
      ∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
        (s.value omega - _root_.GD.N0232.N0720.N1469.d017316 m n s omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  have hpFinite := _root_.GD.N0232.N0720.N1469.d017319 m n hm hn s
  rw [_root_.GD.N0232.N0720.N1128.d017101
    m n theta (_root_.GD.N0232.N0720.N1469.d017316 m n s) s.value hpFinite s.finiteRisk]
  let rho : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ≥0∞ :=
    fun omega ↦ ENNReal.ofReal (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega)
  have hrhoMeas : Measurable rho := by
    simpa only [rho] using
      (_root_.GD.N0232.N0720.N1499.d015002 m n theta).ennreal_ofReal
  have hrhoFinite : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n, rho omega < ∞ := by
    filter_upwards with omega
    exact ENNReal.ofReal_lt_top
  rw [_root_.GD.N0232.N0720.N1499.d015006 m n theta]
  change
    (∫ omega,
      (_root_.GD.N0232.N0720.N1469.d017316 m n s omega - s.value omega) ^ 2
        ∂(_root_.GD.N0232.N0720.N1080.d014172 m n).withDensity rho) = _
  have hdensityIntegral :=
    integral_withDensity_eq_integral_toReal_smul
      (μ := _root_.GD.N0232.N0720.N1080.d014172 m n) hrhoMeas hrhoFinite
      (fun omega ↦
        (_root_.GD.N0232.N0720.N1469.d017316 m n s omega - s.value omega) ^ 2)
  rw [hdensityIntegral]
  apply integral_congr_ae
  filter_upwards with omega
  rw [ENNReal.toReal_ofReal
    (_root_.GD.N0232.N0720.N1499.d015003 m n theta omega)]
  simp only [smul_eq_mul]
  ring





theorem d017322
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal =
      (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1469.d017316 m n s)).toReal +
        (_root_.GD.N0232.N0720.N1469.d017317 m n s theta).toReal := by
  have hsInt := _root_.GD.N0232.N0720.N1078.d016376
    m n theta s.value (s.finiteRisk theta)
  have hpyth := _root_.GD.N0232.N0720.N1501.d016301
    m n hm hn theta s.value hsInt
  have hpFinite := _root_.GD.N0232.N0720.N1469.d017319 m n hm hn s
  rw [_root_.GD.N0232.N0720.N1128.d017097 m n theta s.value (s.finiteRisk theta),
    _root_.GD.N0232.N0720.N1128.d017097 m n theta
      (_root_.GD.N0232.N0720.N1469.d017316 m n s) (hpFinite theta)]
  change
    (∫ omega, (s.value omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
      (∫ omega,
        (_root_.GD.N0232.N0720.N1469.d017316 m n s omega - theta.location) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) +
        _root_.GD.N0232.N0720.N1128.d017098 m n theta
          (_root_.GD.N0232.N0720.N1469.d017316 m n s) s.value
  rw [_root_.GD.N0232.N0720.N1469.d017321
    m n hm hn s theta]
  simpa only [_root_.GD.N0232.N0720.N1469.d017316] using hpyth


theorem d017323
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value =
      _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1469.d017316 m n s) +
        _root_.GD.N0232.N0720.N1469.d017317 m n s theta := by
  have hpFinite := _root_.GD.N0232.N0720.N1469.d017319 m n hm hn s
  have hresFinite : _root_.GD.N0232.N0720.N1469.d017317 m n s theta ≠ ⊤ := by
    exact _root_.GD.N0232.N0720.N1128.d017100
      m n theta (_root_.GD.N0232.N0720.N1469.d017316 m n s) s.value hpFinite s.finiteRisk
  calc
    _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value =
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal :=
      (ENNReal.ofReal_toReal (s.finiteRisk theta)).symm
    _ = ENNReal.ofReal
          ((_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1469.d017316 m n s)).toReal +
            (_root_.GD.N0232.N0720.N1469.d017317 m n s theta).toReal) := by
      rw [_root_.GD.N0232.N0720.N1469.d017322
        m n hm hn s theta]
    _ = ENNReal.ofReal
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1469.d017316 m n s)).toReal +
        ENNReal.ofReal (_root_.GD.N0232.N0720.N1469.d017317 m n s theta).toReal := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
    _ = _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1469.d017316 m n s) +
        _root_.GD.N0232.N0720.N1469.d017317 m n s theta := by
      rw [ENNReal.ofReal_toReal (hpFinite theta),
        ENNReal.ofReal_toReal hresFinite]





theorem d017324
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hres : _root_.GD.N0232.N0720.N1469.d017318 m n s) :
    _root_.GD.N0232.N0720.N1105.d017112 m n (_root_.GD.N0232.N0720.N1469.d017316 m n s) s.value := by
  intro g theta
  change _root_.GD.N0232.N0720.N1469.d017317 m n s (_root_.GD.N0232.N0720.N1215.d014272 g theta) =
    ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1469.d017317 m n s theta
  exact hres g theta



theorem d017325
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hres : _root_.GD.N0232.N0720.N1469.d017318 m n s) :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1469.d017316 m n s) := by
  intro g theta
  have hpFinite := _root_.GD.N0232.N0720.N1469.d017319 m n hm hn s
  have hseedReal :
      (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) s.value).toReal =
        g.d009239 ^ 2 * (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal := by
    rw [s.riskCharacter g theta, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg _)]
  have hresReal :
      (_root_.GD.N0232.N0720.N1469.d017317 m n s (_root_.GD.N0232.N0720.N1215.d014272 g theta)).toReal =
        g.d009239 ^ 2 * (_root_.GD.N0232.N0720.N1469.d017317 m n s theta).toReal := by
    rw [hres g theta, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg _)]
  have hpythAffine := _root_.GD.N0232.N0720.N1469.d017322
    m n hm hn s (_root_.GD.N0232.N0720.N1215.d014272 g theta)
  have hpyth := _root_.GD.N0232.N0720.N1469.d017322
    m n hm hn s theta
  have hcombine :
      (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
          (_root_.GD.N0232.N0720.N1469.d017316 m n s)).toReal =
        g.d009239 ^ 2 *
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1469.d017316 m n s)).toReal := by
    linear_combination -hpythAffine + hseedReal - hresReal +
      (g.d009239 ^ 2) * hpyth
  calc
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) (_root_.GD.N0232.N0720.N1469.d017316 m n s) =
        ENNReal.ofReal
          (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta)
            (_root_.GD.N0232.N0720.N1469.d017316 m n s)).toReal :=
      (ENNReal.ofReal_toReal (hpFinite (_root_.GD.N0232.N0720.N1215.d014272 g theta))).symm
    _ = ENNReal.ofReal (g.d009239 ^ 2 *
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1469.d017316 m n s)).toReal) := by
      rw [hcombine]
    _ = ENNReal.ofReal (g.d009239 ^ 2) *
        ENNReal.ofReal
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1469.d017316 m n s)).toReal :=
      ENNReal.ofReal_mul (sq_nonneg _)
    _ = ENNReal.ofReal (g.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1469.d017316 m n s) := by
      rw [ENNReal.ofReal_toReal (hpFinite theta)]





theorem d017326
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    ‖_root_.GD.N0232.N0720.N1469.d017316 m n s‖ ^ 2 +
        _root_.GD.N0232.N0720.N1128.d017098 m n _root_.GD.N0232.N0720.N1080.d014169
          (_root_.GD.N0232.N0720.N1469.d017316 m n s) s.value =
      ‖s.value‖ ^ 2 := by
  have hpyth := _root_.GD.N0232.N0720.N1469.d017322
    m n hm hn s _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at hpyth
  simp only [zero_sub, norm_neg,
    ENNReal.toReal_ofReal (sq_nonneg _)] at hpyth
  change ‖_root_.GD.N0232.N0720.N1469.d017316 m n s‖ ^ 2 +
      (_root_.GD.N0232.N0720.N1028.d015328 m n _root_.GD.N0232.N0720.N1080.d014169
        (_root_.GD.N0232.N0720.N1469.d017316 m n s) s.value).toReal = ‖s.value‖ ^ 2
  change ‖s.value‖ ^ 2 = ‖_root_.GD.N0232.N0720.N1469.d017316 m n s‖ ^ 2 +
    (_root_.GD.N0232.N0720.N1028.d015328 m n _root_.GD.N0232.N0720.N1080.d014169
      (_root_.GD.N0232.N0720.N1469.d017316 m n s) s.value).toReal at hpyth
  exact hpyth.symm



theorem d017327
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (kappa : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hres : _root_.GD.N0232.N0720.N1469.d017318 m n s)
    (hcapture : kappa * _root_.GD.N0232.N0720.N1201.d015333 m n s ≤
      _root_.GD.N0232.N0720.N1128.d017098 m n _root_.GD.N0232.N0720.N1080.d014169
        (_root_.GD.N0232.N0720.N1469.d017316 m n s) s.value) :
    _root_.GD.N0232.N0720.N1105.d017120 m n kappa s := by
  refine ⟨_root_.GD.N0232.N0720.N1469.d017316 m n s,
    _root_.GD.N0232.N0720.N1469.d017320 m n hm hn s,
    _root_.GD.N0232.N0720.N1469.d017325 m n hm hn s hres,
    _root_.GD.N0232.N0720.N1469.d017324 m n s hres, ?_⟩
  have hnorm := _root_.GD.N0232.N0720.N1469.d017326
    m n hm hn s
  linarith

end

end N1469
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1469.d017323
#print axioms _root_.GD.N0232.N0720.N1469.d017325
#print axioms _root_.GD.N0232.N0720.N1469.d017327
