import GD.Module1073
import GD.Module1120
import GD.Module0963









































open MeasureTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1136

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1085
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1128
open _root_.GD.N0232.N0720.N1129
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1144
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482






private theorem d018010
    (x y epsilon : ℝ) (hepsilon : 0 < epsilon) :
    (x - y) ^ 2 <=
      (1 + epsilon) * x ^ 2 + (1 + epsilon⁻¹) * y ^ 2 := by
  have hnonneg :
      0 <= epsilon⁻¹ * (epsilon * x + y) ^ 2 :=
    mul_nonneg (inv_nonneg.mpr hepsilon.le) (sq_nonneg _)
  have hidentity :
      (1 + epsilon) * x ^ 2 + (1 + epsilon⁻¹) * y ^ 2 -
          (x - y) ^ 2 =
        epsilon⁻¹ * (epsilon * x + y) ^ 2 := by
    field_simp [hepsilon.ne']
    ring
  linarith






theorem d018011
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (lambda : ℝ) (hlambda0 : 0 <= lambda) (hlambda1 : lambda < 1) :
    ∃ theta : _root_.GD.N0232.N0720.N1080.d014168,
      lambda * _root_.GD.N0232.N0720.N1128.d017098 m n theta
          (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) s.value <
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1130.d017075 m n candidate)).toReal -
          (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal := by
  let r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1130.d017075 m n candidate
  let B : ℝ := _root_.GD.N0232.N0720.N1126.d016418 candidate.packet
  let S : ℝ := (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 s.value).toReal
  let epsilon : ℝ := (1 - lambda) / (2 * (lambda + 1))
  let alpha : ℝ := 1 + epsilon
  let beta : ℝ := 1 + epsilon⁻¹
  let c : ℝ := 1 - lambda * alpha
  let D : ℝ := 1 + lambda * beta
  let H : ℝ := D * S
  let M : ℝ := H / c + 2
  let a : ℝ := B + M
  let theta : _root_.GD.N0232.N0720.N1080.d014168 :=
    _root_.GD.N0232.N0720.N1215.d014272 (_root_.GD.N0232.N0720.N1482.d015128 a) _root_.GD.N0232.N0720.N1080.d014169

  have hlambdaAdd : 0 < lambda + 1 := by linarith
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact div_pos (sub_pos.mpr hlambda1) (mul_pos (by norm_num) hlambdaAdd)
  have hcIdentity :
      c = (1 - lambda) * (lambda + 2) / (2 * (lambda + 1)) := by
    dsimp [c, alpha, epsilon]
    field_simp [hlambdaAdd.ne']
    ring
  have hc : 0 < c := by
    rw [hcIdentity]
    positivity
  have hbeta : 0 <= beta := by
    dsimp [beta]
    positivity
  have hD : 0 <= D := by
    dsimp [D]
    positivity
  have hS : 0 <= S := ENNReal.toReal_nonneg
  have hH : 0 <= H := mul_nonneg hD hS
  have hMtwo : 2 <= M := by
    dsimp [M]
    have : 0 <= H / c := div_nonneg hH hc.le
    linarith
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hMtwo
  have hcM : H < c * M := by
    have hidentity : c * M = H + 2 * c := by
      dsimp [M]
      field_simp [hc.ne']
    rw [hidentity]
    linarith
  have hcMsq : H < c * M ^ 2 := by
    have hcmNonneg : 0 <= c * M := mul_nonneg hc.le hMpos.le
    have hgrowth : c * M <= c * M ^ 2 := by
      have hprod : 0 <= (c * M) * (M - 1) :=
        mul_nonneg hcmNonneg (sub_nonneg.mpr (by linarith [hMtwo]))
      nlinarith
    exact hcM.trans_le hgrowth
  have hB : 0 <= B := by
    dsimp [B, _root_.GD.N0232.N0720.N1126.d016418]
    exact Real.sqrt_nonneg _

  have hthetaLocation : theta.location = a := by
    simp [theta, a, _root_.GD.N0232.N0720.N1215.d014272, _root_.GD.N0232.N0720.N1080.d014169]

  have hsRisk : _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value =
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 s.value := by
    have hcharacter := s.riskCharacter
      (_root_.GD.N0232.N0720.N1482.d015128 a) _root_.GD.N0232.N0720.N1080.d014169
    simpa [theta, _root_.GD.N0232.N0720.N1482.d015128,
      _root_.GD.N0232.N0719.N0946.d009229.d009239]
      using hcharacter
  have hsRiskReal : (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal = S := by
    rw [hsRisk]

  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    unfold _root_.GD.N0232.N0720.N1080.d014171
    infer_instance

  have hrFinite : _root_.GD.N0232.N0720.N1159.d014637 m n r := by
    simpa only [r] using _root_.GD.N0232.N0720.N1128.d017106 m n candidate
  have hrIntegrable : Integrable
      (fun omega => (r omega - theta.location) ^ 2) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    _root_.GD.N0232.N0720.N1078.d016376 m n theta r (hrFinite theta)
  have hsIntegrable : Integrable
      (fun omega => (s.value omega - theta.location) ^ 2) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    _root_.GD.N0232.N0720.N1078.d016376 m n theta s.value (s.finiteRisk theta)

  have hcompletionReference :
      (fun omega => r omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1126.d016416 candidate.packet candidate.weight := by
    simpa only [r, _root_.GD.N0232.N0720.N1130.d017075] using
      (_root_.GD.N0232.N0720.N1126.d016427
        (m := m) (n := n) candidate.packet candidate.weight
          candidate.weight_nonneg)
  have hcompletion :
      (fun omega => r omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
        _root_.GD.N0232.N0720.N1126.d016416 candidate.packet candidate.weight :=
    (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq
      hcompletionReference

  have hrLower : M ^ 2 <= (_root_.GD.N0232.N0720.N1080.d014182 m n theta r).toReal := by
    rw [_root_.GD.N0232.N0720.N1128.d017097 m n theta r (hrFinite theta)]
    have hconst : Integrable (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n => M ^ 2)
        (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := integrable_const _
    have hpoint : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta,
        M ^ 2 <= (r omega - theta.location) ^ 2 := by
      filter_upwards [hcompletion] with omega hcompletionOmega
      rw [hcompletionOmega, hthetaLocation]
      have hpacket := _root_.GD.N0232.N0720.N1126.d016424
        candidate.packet candidate.weight candidate.weight_nonneg omega
      have hpacketUpper :
          _root_.GD.N0232.N0720.N1126.d016416 candidate.packet candidate.weight omega <= B :=
        (abs_le.mp hpacket).2
      have hdiff : M <=
          a - _root_.GD.N0232.N0720.N1126.d016416
            candidate.packet candidate.weight omega := by
        dsimp [a]
        linarith
      have hprod : 0 <=
          (a - _root_.GD.N0232.N0720.N1126.d016416
              candidate.packet candidate.weight omega - M) *
            (a - _root_.GD.N0232.N0720.N1126.d016416
              candidate.packet candidate.weight omega + M) :=
        mul_nonneg (sub_nonneg.mpr hdiff)
          (add_nonneg (le_trans hMpos.le hdiff) hMpos.le)
      nlinarith
    have hintegral := integral_mono_ae hconst hrIntegrable hpoint
    simpa using hintegral

  have hcrossIntegrable : Integrable
      (fun omega => (r omega - s.value omega) ^ 2) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    have hright : Integrable (fun omega =>
        alpha * (r omega - theta.location) ^ 2 +
          beta * (s.value omega - theta.location) ^ 2) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
      (hrIntegrable.const_mul alpha).add (hsIntegrable.const_mul beta)
    apply hright.mono'
    · exact
        (((AEStronglyMeasurable.mono_ac
            (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
            (Lp.aestronglyMeasurable r)).aemeasurable.sub
          (AEStronglyMeasurable.mono_ac
            (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
            (Lp.aestronglyMeasurable s.value)).aemeasurable).pow_const 2).aestronglyMeasurable
    · filter_upwards with omega
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hweighted := _root_.GD.N0232.N0720.N1136.d018010
        (r omega - theta.location) (s.value omega - theta.location)
          epsilon hepsilon
      dsimp [alpha, beta]
      simpa only [sub_sub_sub_cancel_right] using hweighted

  have hcrossUpper :
      _root_.GD.N0232.N0720.N1128.d017098 m n theta r s.value <=
        alpha * (_root_.GD.N0232.N0720.N1080.d014182 m n theta r).toReal +
          beta * (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value).toReal := by
    rw [_root_.GD.N0232.N0720.N1128.d017101
        m n theta r s.value hrFinite s.finiteRisk,
      _root_.GD.N0232.N0720.N1128.d017097 m n theta r (hrFinite theta),
      _root_.GD.N0232.N0720.N1128.d017097 m n theta s.value (s.finiteRisk theta)]
    have hright : Integrable (fun omega =>
        alpha * (r omega - theta.location) ^ 2 +
          beta * (s.value omega - theta.location) ^ 2) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
      (hrIntegrable.const_mul alpha).add (hsIntegrable.const_mul beta)
    calc
      (∫ omega, (r omega - s.value omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) <=
          ∫ omega,
            (alpha * (r omega - theta.location) ^ 2 +
              beta * (s.value omega - theta.location) ^ 2)
            ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
              apply integral_mono hcrossIntegrable hright
              intro omega
              have hweighted := _root_.GD.N0232.N0720.N1136.d018010
                (r omega - theta.location) (s.value omega - theta.location)
                  epsilon hepsilon
              dsimp [alpha, beta]
              simpa only [sub_sub_sub_cancel_right] using hweighted
      _ = alpha *
            ∫ omega, (r omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta +
          beta *
            ∫ omega, (s.value omega - theta.location) ^ 2
              ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
            rw [integral_add (hrIntegrable.const_mul alpha)
                (hsIntegrable.const_mul beta),
              integral_const_mul, integral_const_mul]

  refine ⟨theta, ?_⟩
  have hradial :
      D * S < c * (_root_.GD.N0232.N0720.N1080.d014182 m n theta r).toReal := by
    calc
      D * S = H := rfl
      _ < c * M ^ 2 := hcMsq
      _ <= c * (_root_.GD.N0232.N0720.N1080.d014182 m n theta r).toReal :=
        mul_le_mul_of_nonneg_left hrLower hc.le
  have hlambdaCross :
      lambda * _root_.GD.N0232.N0720.N1128.d017098 m n theta r s.value <=
        lambda * (alpha * (_root_.GD.N0232.N0720.N1080.d014182 m n theta r).toReal + beta * S) := by
    rw [← hsRiskReal]
    exact mul_le_mul_of_nonneg_left hcrossUpper hlambda0
  dsimp [D, c] at hradial
  rw [hsRiskReal]
  nlinarith





theorem d018012
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (lambda : ℝ) (hlambda1 : lambda < 1) :
    ¬ _root_.GD.N0232.N0720.N1128.d017105
      m n s candidate lambda := by
  intro hcertificate
  obtain ⟨theta, hviolate⟩ :=
    _root_.GD.N0232.N0720.N1136.d018011
      m n s candidate lambda hcertificate.1.1 hlambda1
  exact (not_lt_of_ge (hcertificate.2 theta)) hviolate



theorem d018013
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (lambda : ℝ)
    (hcertificate : _root_.GD.N0232.N0720.N1128.d017105
      m n s candidate lambda) :
    lambda = 1 := by
  apply le_antisymm hcertificate.1.2
  apply not_lt.mp
  exact fun hlambda =>
    _root_.GD.N0232.N0720.N1136.d018012
      m n s candidate lambda hlambda hcertificate





theorem d018014
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    ‖s.value‖ ^ 2 - ‖q‖ ^ 2 <=
      _root_.GD.N0232.N0720.N1129.d017187 m n s candidate := by
  have hreserve :=
    _root_.GD.N0232.N0720.N1126.d016436
      s candidate.packet candidate.weight candidate.weight_nonneg q hq
  unfold _root_.GD.N0232.N0720.N1129.d017187
  nlinarith [sq_nonneg
    ‖q - _root_.GD.N0232.N0720.N1126.d016426 candidate.packet candidate.weight
      candidate.weight_nonneg‖]





theorem d018015
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (lambda : ℝ)
    (hcertificate : _root_.GD.N0232.N0720.N1128.d017105
      m n s candidate lambda)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    ‖s.value‖ ^ 2 - ‖q‖ ^ 2 <=
      _root_.GD.N0232.N0720.N1129.d017191
        m n s candidate lambda := by
  have hlambda := _root_.GD.N0232.N0720.N1136.d018013
    m n s candidate lambda hcertificate
  subst lambda
  rw [_root_.GD.N0232.N0720.N1129.d017195]
  have hgap := _root_.GD.N0232.N0720.N1136.d018014
    m n s candidate q hq
  linarith [_root_.GD.N0232.N0720.N1130.d017083 m n candidate,
    _root_.GD.N0232.N0720.N1130.d017084 m n candidate]






theorem d018016
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsmall : _root_.GD.N0232.N0720.N1129.d017196
      m n s) :
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value := by
  let p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  have hp : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value := by
    simpa [p, _root_.GD.N0232.N0720.N1159.d014630] using
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hself : s.value ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
  have htax := _root_.GD.N0232.N0720.N1159.d014648
    m n s.value s.value hself
  have hgapNonpos : ‖s.value‖ ^ 2 - ‖p‖ ^ 2 <= 0 := by
    by_contra hpositive
    have hgapPos : 0 < ‖s.value‖ ^ 2 - ‖p‖ ^ 2 :=
      lt_of_not_ge hpositive
    obtain ⟨candidate, lambda, hcertificate, hmerit⟩ :=
      hsmall (‖s.value‖ ^ 2 - ‖p‖ ^ 2) hgapPos
    have hlower :=
      _root_.GD.N0232.N0720.N1136.d018015
        m n s candidate lambda hcertificate p hp
    exact (not_lt_of_ge hlower) hmerit
  have hdistanceSq : ‖s.value - p‖ ^ 2 = 0 := by
    apply le_antisymm
    · exact htax.trans hgapNonpos
    · exact sq_nonneg _
  have hdistance : ‖s.value - p‖ = 0 := by
    nlinarith [norm_nonneg (s.value - p)]
  have hseedEq : s.value = p := sub_eq_zero.mp (norm_eq_zero.mp hdistance)
  exact hseedEq.symm




theorem d018017
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsmall : _root_.GD.N0232.N0720.N1129.d017196
      m n s) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value := by
  exact (_root_.GD.N0232.N0720.N1159.d014635 m n s.value).1
    (_root_.GD.N0232.N0720.N1136.d018016
      m n s hsmall)



theorem d018018
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hstrictReference : ‖q‖ ^ 2 < ‖s.value‖ ^ 2) :
    ¬ _root_.GD.N0232.N0720.N1129.d017196 m n s := by
  intro hsmall
  let gap : ℝ := ‖s.value‖ ^ 2 - ‖q‖ ^ 2
  have hgap : 0 < gap := sub_pos.mpr hstrictReference
  obtain ⟨candidate, lambda, hcertificate, hmerit⟩ :=
    hsmall gap hgap
  have hlower :=
    _root_.GD.N0232.N0720.N1136.d018015
      m n s candidate lambda hcertificate q hq
  exact (not_lt_of_ge hlower) hmerit





theorem d018019
    (m n : ℕ) (hm : 2 <= m) (hn : 2 <= n)
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    ‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2 <
      ‖(_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U).value‖ ^ 2 := by
  have hstrict := _root_.GD.N0232.N0720.N1085.d015417
    m n hm hn U _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at hstrict
  have hstrict' :
      ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2) <
        ENNReal.ofReal
          (‖(_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U).value‖ ^ 2) := by
    change
      ENNReal.ofReal
          (‖_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (5 / 4)‖ ^ 2) <
        ENNReal.ofReal
          (‖_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U 1‖ ^ 2)
    simpa only [zero_sub, norm_neg] using hstrict
  have hlowerNonneg :
      (0 : ENNReal) ≤
        ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U‖ ^ 2) :=
    bot_le
  have hupperPos :
      0 < ENNReal.ofReal (‖(_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U).value‖ ^ 2) :=
    lt_of_le_of_lt hlowerNonneg hstrict'
  have hupperReal :
      0 < ‖(_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U).value‖ ^ 2 :=
    ENNReal.ofReal_pos.mp hupperPos
  exact (ENNReal.ofReal_lt_ofReal_iff hupperReal).mp hstrict'




theorem d018020
    (m n : ℕ) (hm : 2 <= m) (hn : 2 <= n)
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    ¬ _root_.GD.N0232.N0720.N1129.d017196
      m n (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U) := by
  exact
    _root_.GD.N0232.N0720.N1136.d018018
      m n (_root_.GD.N0232.N0720.N1144.d017995 m n hm hn U)
      (_root_.GD.N0232.N0720.N1144.d017996 m n hm hn U)
      (_root_.GD.N0232.N0720.N1144.d017997 m n hm hn U)
      (_root_.GD.N0232.N0720.N1136.d018019
        m n hm hn U)

end

end N1136
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1136.d018011
#print axioms _root_.GD.N0232.N0720.N1136.d018013
#print axioms _root_.GD.N0232.N0720.N1136.d018015
#print axioms _root_.GD.N0232.N0720.N1136.d018016
#print axioms _root_.GD.N0232.N0720.N1136.d018017
#print axioms _root_.GD.N0232.N0720.N1136.d018018
#print axioms _root_.GD.N0232.N0720.N1136.d018020
