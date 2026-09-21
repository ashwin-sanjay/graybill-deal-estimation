import GD.Module0923
import GD.Module0901
import GD.Module0893

















open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1071

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1433
open _root_.GD.N0232.N0720.N1442
open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1092
open _root_.GD.N0107
open _root_.GD.N0137
open _root_.GD.N0141
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)




theorem d014425
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp₀ : 0 < p) (hp₁ : p < 1) :
    _root_.GD.N0232.N0720.N1091.d012790 alpha beta p ≤ 1 := by
  letI : IsProbabilityMeasure (betaMeasure alpha beta) :=
    isProbabilityMeasureBeta halpha hbeta
  let f : ℝ → ℝ := fun u ↦
    (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p) ^ 2
  have hfMeas : AEStronglyMeasurable f (betaMeasure alpha beta) :=
    (((_root_.GD.N0232.N0720.N1091.d012771 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p)).sub
      measurable_const).pow_const 2).aestronglyMeasurable
  have hsupport := _root_.GD.N0232.N0720.N1092.d013031 alpha beta
  have hnorm : ∀ᵐ u ∂betaMeasure alpha beta, ‖f u‖ ≤ (1 : ℝ) := by
    filter_upwards [hsupport] with u hu
    have hw := _root_.GD.N0232.N0720.N1091.d012780
      (_root_.GD.N0232.N0720.N1091.d012778 halpha hbeta hp₀ hp₁) hu.1 hu.2
    have herrAbs :
        |_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hw.1, hw.2]
    have herrSq :
        |_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p| ^ 2 ≤ 1 := by
      nlinarith [abs_nonneg
        (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p)]
    simpa only [f, Real.norm_eq_abs, abs_pow, norm_one] using herrSq
  have hfInt : Integrable f (betaMeasure alpha beta) :=
    (integrable_const (1 : ℝ)).mono' hfMeas hnorm
  have hpoint : ∀ᵐ u ∂betaMeasure alpha beta, f u ≤ 1 := by
    filter_upwards [hsupport] with u hu
    have hw := _root_.GD.N0232.N0720.N1091.d012780
      (_root_.GD.N0232.N0720.N1091.d012778 halpha hbeta hp₀ hp₁) hu.1 hu.2
    have herrAbs :
        |_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hw.1, hw.2]
    dsimp only [f]
    nlinarith [sq_abs
      (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p),
      abs_nonneg (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta p) u - p)]
  unfold _root_.GD.N0232.N0720.N1091.d012790
  calc
    (∫ u, f u ∂betaMeasure alpha beta) ≤
        ∫ _u, (1 : ℝ) ∂betaMeasure alpha beta :=
      integral_mono_ae hfInt (integrable_const (1 : ℝ)) hpoint
    _ = 1 := by simp

include hm hn in


theorem d014426
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (_root_.GD.N0107.d012732 m n theta.location
          (_root_.GD.N0232.N0720.N1067.d014408 m n theta)) =
      _root_.GD.N0107.d009045
          m n theta.scale₁ theta.scale₂ *
        _root_.GD.N0232.N0720.N1442.d013866 (_root_.GD.N0232.N0720.N1067.d014408 m n theta) := by
  let e := _root_.GD.N0232.N0720.N1067.d014408 m n theta
  let Sigma := _root_.GD.N0107.d009045
    m n theta.scale₁ theta.scale₂
  have he₀ : 0 < e := _root_.GD.N0232.N0720.N1067.d014409 m n hm hn theta
  have he₁ : e < 1 := _root_.GD.N0232.N0720.N1067.d014410 m n hm hn theta
  have hSigma : 0 < Sigma :=
    _root_.GD.N0107.d009049
      (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos
  have hOracleLaw : HasLaw (_root_.GD.N0137.d008931 m n e) (gaussianReal 0 1)
      (_root_.GD.N0137.d008914 m n) := ⟨
    (_root_.GD.N0137.d008936 m n e).aemeasurable,
    _root_.GD.N0137.d008939 m n hm hn he₀.le he₁.le⟩
  have hOracleSecond :
      (∫ omega, (_root_.GD.N0137.d008931 m n e omega) ^ 2
        ∂_root_.GD.N0137.d008914 m n) = 1 := by
    have hvar : Var[_root_.GD.N0137.d008931 m n e; _root_.GD.N0137.d008914 m n] = 1 := by
      simpa using hOracleLaw.variance_eq
    rw [variance_eq_integral
      (_root_.GD.N0137.d008936 m n e).aemeasurable,
      _root_.GD.N0137.d008941 m n hm hn he₀.le he₁.le] at hvar
    simpa only [sub_zero] using hvar
  have hPhysicalOracleSecond :
      (∫ omega, (_root_.GD.N0137.d008945 m n e Sigma omega) ^ 2
        ∂_root_.GD.N0137.d008914 m n) = Sigma * e * (1 - e) := by
    calc
      (∫ omega, (_root_.GD.N0137.d008945 m n e Sigma omega) ^ 2
          ∂_root_.GD.N0137.d008914 m n) =
          ∫ omega, (Sigma * e * (1 - e)) *
            (_root_.GD.N0137.d008931 m n e omega) ^ 2 ∂_root_.GD.N0137.d008914 m n := by
        apply integral_congr_ae
        filter_upwards with omega
        unfold _root_.GD.N0137.d008945
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      _ = Sigma * e * (1 - e) := by
        rw [integral_const_mul, hOracleSecond, mul_one]
  let f : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n → ℝ := fun omega ↦
    (_root_.GD.N0137.d008945 m n e Sigma omega) ^ 2
  have htransport := _root_.GD.N0107.d012742
    (P := _root_.GD.N0107.d009030 m n theta.location theta.scale₁ theta.scale₂)
    (Q := _root_.GD.N0137.d008914 m n)
    (S := _root_.GD.N0107.d009025 m n
      theta.location theta.scale₁ theta.scale₂)
    (f := f)
    (_root_.GD.N0107.d009027 m n
      theta.location theta.scale₁ theta.scale₂)
    (show Measurable f by
      unfold f _root_.GD.N0137.d008945
      fun_prop)
    (_root_.GD.N0107.d009031
      m n theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos.ne' theta.scale₂_pos.ne')
  rw [hPhysicalOracleSecond] at htransport
  have hOracle :
      _root_.GD.N0107.d012738 m n theta.location theta.scale₁ theta.scale₂
          e Sigma =
        _root_.GD.N0107.d012732 m n theta.location e := by
    funext omega
    exact _root_.GD.N0107.d012740
      m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos omega
  unfold _root_.GD.N0141.d006684 _root_.GD.N0232.N0720.N1080.d014171
  rw [← hOracle]
  simpa only [_root_.GD.N0107.d012738, Function.comp_apply, f,
    _root_.GD.N0232.N0720.N1442.d013866, e, Sigma, _root_.GD.N0232.N0720.N1067.d014408,
    mul_assoc] using htransport



theorem d014427
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal =
      _root_.GD.N0107.d009045
          m n theta.scale₁ theta.scale₂ *
        _root_.GD.N0232.N0720.N1442.d013867
          (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n)
          (_root_.GD.N0232.N0720.N1067.d014408 m n theta) := by
  have hbaseNonnegative : 0 ≤
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - theta.location) := by
    unfold _root_.GD.N0141.d006684
    exact integral_nonneg fun _ ↦ sq_nonneg _
  have hcap : (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal =
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (fun omega ↦ _root_.GD.N0107.d012733 m n omega - theta.location) := by
    unfold _root_.GD.N0232.N0720.N1066.d014320
    rw [_root_.GD.N0232.N0720.N1080.d014184 m n hm hn theta,
      ENNReal.toReal_ofReal hbaseNonnegative]
    rfl
  have hOracle :
      _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 m n
            theta.location theta.scale₁ theta.scale₂)
          (_root_.GD.N0107.d012732 m n theta.location
            (_root_.GD.N0107.d009046
              m n theta.scale₁ theta.scale₂)) =
        _root_.GD.N0107.d009045
            m n theta.scale₁ theta.scale₂ *
          _root_.GD.N0232.N0720.N1442.d013866
            (_root_.GD.N0107.d009046
              m n theta.scale₁ theta.scale₂) := by
    simpa only [_root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0232.N0720.N1067.d014408] using
      _root_.GD.N0232.N0720.N1071.d014426
        m n hm hn theta
  have hExcess :
      _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 m n
            theta.location theta.scale₁ theta.scale₂)
          (fun omega ↦ _root_.GD.N0107.d012733 m n omega - theta.location) -
        _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 m n
            theta.location theta.scale₁ theta.scale₂)
          (_root_.GD.N0107.d012732 m n theta.location
            (_root_.GD.N0107.d009046
              m n theta.scale₁ theta.scale₂)) =
        _root_.GD.N0107.d009045
            m n theta.scale₁ theta.scale₂ *
          _root_.GD.N0232.N0720.N1091.d012790
            (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n)
            (_root_.GD.N0107.d009046
              m n theta.scale₁ theta.scale₂) := by
    rw [_root_.GD.N0232.N0720.N1433.d014030
      m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos]
    rw [← _root_.GD.N0232.N0720.N1091.d012800
      (_root_.GD.N0232.N0720.N1433.d014026 hm) (_root_.GD.N0232.N0720.N1433.d014027 hn)
      (_root_.GD.N0107.d009050
        (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos)
      (_root_.GD.N0107.d009051
        (by omega) (by omega) theta.scale₁_pos theta.scale₂_pos)]
  rw [hcap]
  unfold _root_.GD.N0232.N0720.N1080.d014171 _root_.GD.N0232.N0720.N1067.d014408 _root_.GD.N0232.N0720.N1442.d013867
  linarith [hOracle, hExcess]




theorem d014428
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta)).toReal ≤ 2 := by
  let eta := _root_.GD.N0232.N0720.N1067.d014402 theta
  let Sigma := _root_.GD.N0107.d009045
    m n eta.scale₁ eta.scale₂
  let p := _root_.GD.N0232.N0720.N1067.d014408 m n eta
  have hsum : eta.scale₁ + eta.scale₂ = 1 := by
    simpa only [eta, _root_.GD.N0232.N0720.N1067.d014398] using
      _root_.GD.N0232.N0720.N1067.d014406 theta
  have hSigmaLe : Sigma ≤ 1 := by
    have hmR : (1 : ℝ) ≤ m := by
      exact_mod_cast (show 1 ≤ m by omega)
    have hnR : (1 : ℝ) ≤ n := by
      exact_mod_cast (show 1 ≤ n by omega)
    have hfirst : eta.scale₁ ^ 2 / (m : ℝ) ≤ eta.scale₁ ^ 2 :=
      div_le_self (sq_nonneg eta.scale₁) hmR
    have hsecond : eta.scale₂ ^ 2 / (n : ℝ) ≤ eta.scale₂ ^ 2 :=
      div_le_self (sq_nonneg eta.scale₂) hnR
    unfold Sigma _root_.GD.N0107.d009045
      _root_.GD.N0107.d009043
      _root_.GD.N0107.d009044
    nlinarith [mul_nonneg eta.scale₁_pos.le eta.scale₂_pos.le]
  have hp₀ : 0 < p := _root_.GD.N0232.N0720.N1067.d014409 m n hm hn eta
  have hp₁ : p < 1 := _root_.GD.N0232.N0720.N1067.d014410 m n hm hn eta
  have hregret := _root_.GD.N0232.N0720.N1071.d014425
    (_root_.GD.N0232.N0720.N1433.d014026 hm) (_root_.GD.N0232.N0720.N1433.d014027 hn) hp₀ hp₁
  have htotalNonnegative : 0 ≤
      _root_.GD.N0232.N0720.N1442.d013867
        (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n) p :=
    (_root_.GD.N0232.N0720.N1442.d013871 hp₀ hp₁).le
  have htotalLe :
      _root_.GD.N0232.N0720.N1442.d013867
        (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n) p ≤ 2 := by
    unfold _root_.GD.N0232.N0720.N1442.d013867 _root_.GD.N0232.N0720.N1442.d013866
    nlinarith [mul_nonneg hp₀.le (sub_nonneg.mpr hp₁.le)]
  rw [_root_.GD.N0232.N0720.N1071.d014427
    m n hm hn eta]
  change Sigma *
      _root_.GD.N0232.N0720.N1442.d013867
        (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n) p ≤ 2
  calc
    Sigma * _root_.GD.N0232.N0720.N1442.d013867
        (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n) p ≤
        1 * 2 := mul_le_mul hSigmaLe htotalLe htotalNonnegative (by norm_num)
    _ = 2 := by norm_num



theorem d014429
    (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) :
    ∃ C : ℝ, ∀ j,
      (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn
        (_root_.GD.N0232.N0720.N1067.d014402 (thetaSeq j))).toReal ≤ C :=
  ⟨2, fun j ↦
    _root_.GD.N0232.N0720.N1071.d014428
      m n hm hn (thetaSeq j)⟩




theorem d014430
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1066.d014320 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta) =
      ENNReal.ofReal ((_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹.d009239 ^ 2) *
        _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta := by
  unfold _root_.GD.N0232.N0720.N1066.d014320 _root_.GD.N0232.N0720.N1067.d014402
  exact _root_.GD.N0232.N0720.N1215.d014293 m n hm hn (_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹ theta



theorem d014431
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1066.d014320 m n hm hn (_root_.GD.N0232.N0720.N1067.d014402 theta) =
      ENNReal.ofReal ((_root_.GD.N0232.N0720.N1067.d014398 theta)⁻¹ ^ 2) *
        _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta := by
  rw [_root_.GD.N0232.N0720.N1071.d014430 m n hm hn theta]
  have hdilation : (_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹.d009239 =
      (_root_.GD.N0232.N0720.N1067.d014398 theta)⁻¹ := by
    unfold _root_.GD.N0232.N0719.N0946.d009229.d009239 _root_.GD.N0232.N0720.N1067.d014400
    simp only [_root_.GD.N0232.N0719.N0946.d009229.d009238, Real.exp_neg,
      Real.exp_log (_root_.GD.N0232.N0720.N1067.d014399 theta)]
  rw [hdilation]

end

end N1071
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1071.d014425
#print axioms _root_.GD.N0232.N0720.N1071.d014426
#print axioms _root_.GD.N0232.N0720.N1071.d014427
#print axioms _root_.GD.N0232.N0720.N1071.d014428
#print axioms _root_.GD.N0232.N0720.N1071.d014431
