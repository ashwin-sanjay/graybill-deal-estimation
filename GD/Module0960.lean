import GD.Module0959
import GD.Module0797





























open Filter MeasureTheory Set Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1068

noncomputable section

open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1073
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0646
open _root_.GD.N0232.N0719.N0826
open _root_.GD.N0238.N0750
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)


def d015070 (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) : _root_.GD.N0232.N0720.N1025.d014302 m n :=
  (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm p.1


theorem d015071
    {u : ℕ → _root_.GD.N0232.N0720.N1025.d014302 m n} {x y : _root_.GD.N0232.N0720.N1025.d014302 m n}
    (hx : _root_.GD.N0230.N0646.d000537 u x) (hy : _root_.GD.N0230.N0646.d000537 u y) :
    x = y := by
  have hpair : ⟪x, x - y⟫_ℝ = ⟪y, x - y⟫_ℝ :=
    tendsto_nhds_unique (hx (x - y)) (hy (x - y))
  have hself : ⟪x - y, x - y⟫_ℝ = 0 := by
    rw [inner_sub_left, hpair, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)



theorem d015072
    (u p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) u.1 p.1) :
    ‖_root_.GD.N0232.N0720.N1068.d015070 m n hm hn u‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1068.d015070 m n hm hn p‖ ^ 2 := by
  have href := hdom _root_.GD.N0232.N0720.N1080.d014169
  unfold _root_.GD.N0232.N0720.N1025.d014305 at href
  unfold _root_.GD.N0232.N0720.N1068.d015070
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  exact (ENNReal.ofReal_le_ofReal_iff
    (sq_nonneg ‖(toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm p.1‖)).mp href







theorem d015073
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) (u : ℕ → _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    (hdom : ∀ j, _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) (u j).1 p.1)
    (hweak : _root_.GD.N0230.N0646.d000537
      (fun j ↦ _root_.GD.N0232.N0720.N1068.d015070 m n hm hn (u j))
      (_root_.GD.N0232.N0720.N1068.d015070 m n hm hn p)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1068.d015070 m n hm hn (u j)) atTop
      (nhds (_root_.GD.N0232.N0720.N1068.d015070 m n hm hn p)) := by
  let P : _root_.GD.N0232.N0720.N1025.d014302 m n := _root_.GD.N0232.N0720.N1068.d015070 m n hm hn p
  let U : ℕ → _root_.GD.N0232.N0720.N1025.d014302 m n := fun j ↦ _root_.GD.N0232.N0720.N1068.d015070 m n hm hn (u j)
  have hinner : Tendsto (fun j ↦ ⟪U j, P⟫_ℝ) atTop (nhds ⟪P, P⟫_ℝ) :=
    hweak P
  have hupper : Tendsto
      (fun j ↦ 2 * (‖P‖ ^ 2 - ⟪U j, P⟫_ℝ)) atTop (nhds 0) := by
    have hconstant : Tendsto (fun _ : ℕ ↦ ‖P‖ ^ 2) atTop
        (nhds (‖P‖ ^ 2)) := tendsto_const_nhds
    have h := (hconstant.sub hinner).const_mul 2
    simpa [real_inner_self_eq_norm_sq] using h
  have hsq : Tendsto (fun j ↦ ‖U j - P‖ ^ 2) atTop (nhds 0) := by
    refine squeeze_zero (fun j ↦ sq_nonneg ‖U j - P‖) ?_ hupper
    intro j
    have hnorm : ‖U j‖ ^ 2 ≤ ‖P‖ ^ 2 := by
      exact _root_.GD.N0232.N0720.N1068.d015072
        m n hm hn (u j) p (hdom j)
    rw [norm_sub_sq_real]
    linarith
  have hnorm : Tendsto (fun j ↦ ‖U j - P‖) atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    change Tendsto (fun j ↦ Real.sqrt (‖U j - P‖ ^ 2)) atTop
      (nhds (Real.sqrt 0)) at hsqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm




theorem d015074
    (p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1)
    (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n)
      (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g q).1 p.1 := by
  let P : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p
  let Q : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q
  have hdomStrong : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) Q.1 P.1 := by
    exact (_root_.GD.N0232.N0720.N1025.d014313 m n q.1 p.1).1 hdom
  have hfixedStrong : _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g P = P :=
    _root_.GD.N0232.N0720.N1025.d014318
      m n hm hn p hfixed g
  have htransport : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g Q).1 P.1 := by
    intro eta
    let theta : _root_.GD.N0232.N0720.N1080.d014168 := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta
    have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by
      simp [theta]
    calc
      _root_.GD.N0232.N0720.N1080.d014182 m n eta (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g Q).1 =
          ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n theta Q.1 := by
        simpa [_root_.GD.N0232.N0720.N1215.d014298, heta] using
          _root_.GD.N0232.N0720.N1215.d014290 m n hm hn g theta Q.1 Q.2
      _ ≤ ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n theta P.1 :=
        mul_le_mul_left' (hdomStrong theta) _
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n eta (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g P).1 := by
        symm
        simpa [_root_.GD.N0232.N0720.N1215.d014298, heta] using
          _root_.GD.N0232.N0720.N1215.d014290 m n hm hn g theta P.1 P.2
      _ = _root_.GD.N0232.N0720.N1080.d014182 m n eta P.1 := by rw [hfixedStrong]
  apply (_root_.GD.N0232.N0720.N1025.d014313 m n
    (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g q).1 p.1).2
  simpa [P, Q, _root_.GD.N0232.N0720.N1025.d014316] using htransport



theorem d015075
    (p : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1073.d015043 m n hm hn theta p =
      _root_.GD.N0232.N0720.N1068.d015070 m n hm hn p := by
  unfold _root_.GD.N0232.N0720.N1073.d015043 _root_.GD.N0232.N0720.N1068.d015070
  rw [show _root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta p = p by
    exact hfixed (_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹]



theorem d015076
    (p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n)
      (_root_.GD.N0232.N0720.N1067.d014414 m n hm hn theta q).1 p.1 := by
  exact _root_.GD.N0232.N0720.N1068.d015074
    m n hm hn p q hfixed hdom (_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹



theorem d015077
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) :
    _root_.GD.N0232.N0720.N1073.d015043 m n hm hn theta q =
      _root_.GD.N0232.N0720.N1215.d014289 m n hm hn (_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).2 := by
  simp [_root_.GD.N0232.N0720.N1073.d015043, _root_.GD.N0232.N0720.N1067.d014414,
    _root_.GD.N0232.N0720.N1025.d014316, _root_.GD.N0232.N0720.N1215.d014298]






theorem N1755.d015078
    {p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn}
    (packet : _root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1073.d015043 m n hm hn (packet.thetaSeq j) q)
      atTop (nhds (_root_.GD.N0232.N0720.N1068.d015070 m n hm hn p)) := by
  have hpconst :
      (fun j ↦ _root_.GD.N0232.N0720.N1073.d015043 m n hm hn (packet.thetaSeq j) p) =
        fun _ : ℕ ↦ _root_.GD.N0232.N0720.N1068.d015070 m n hm hn p := by
    funext j
    exact _root_.GD.N0232.N0720.N1068.d015075
      m n hm hn p hfixed (packet.thetaSeq j)
  have hpconstWeak : _root_.GD.N0230.N0646.d000537
      (fun j ↦ _root_.GD.N0232.N0720.N1073.d015043 m n hm hn (packet.thetaSeq j) p)
      (_root_.GD.N0232.N0720.N1068.d015070 m n hm hn p) := by
    rw [hpconst]
    exact _root_.GD.N0230.N0646.d000539 tendsto_const_nhds
  have hpLimit : packet.pLimit = _root_.GD.N0232.N0720.N1068.d015070 m n hm hn p :=
    _root_.GD.N0232.N0720.N1068.d015071 m n packet.p_weak hpconstWeak
  have hqWeak : _root_.GD.N0230.N0646.d000537
      (fun j ↦ _root_.GD.N0232.N0720.N1073.d015043 m n hm hn (packet.thetaSeq j) q)
      (_root_.GD.N0232.N0720.N1068.d015070 m n hm hn p) := by
    rw [← hpLimit, packet.d015046 m n hm hn]
    exact packet.q_weak
  let u : ℕ → _root_.GD.N0232.N0720.N1073.d015042 m n hm hn := fun j ↦
    _root_.GD.N0232.N0720.N1067.d014414 m n hm hn (packet.thetaSeq j) q
  have huDom : ∀ j, _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) (u j).1 p.1 := by
    intro j
    exact _root_.GD.N0232.N0720.N1068.d015076
      m n hm hn p q hfixed hdom (packet.thetaSeq j)
  have huWeak : _root_.GD.N0230.N0646.d000537
      (fun j ↦ _root_.GD.N0232.N0720.N1068.d015070 m n hm hn (u j))
      (_root_.GD.N0232.N0720.N1068.d015070 m n hm hn p) := by
    simpa [u, _root_.GD.N0232.N0720.N1068.d015070, _root_.GD.N0232.N0720.N1073.d015043] using hqWeak
  simpa [u, _root_.GD.N0232.N0720.N1068.d015070, _root_.GD.N0232.N0720.N1073.d015043] using
    (_root_.GD.N0232.N0720.N1068.d015073
      m n hm hn p u huDom huWeak)






def d015079 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ × ℝ :=
  (((_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹).shift,
    ((_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹).logScale)



@[simp] theorem d015080 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    ((_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹).d009239 =
      (_root_.GD.N0232.N0720.N1067.d014398 theta)⁻¹ := by
  simp [_root_.GD.N0232.N0719.N0946.d009229.d009239, _root_.GD.N0232.N0720.N1067.d014400, Real.exp_neg,
    Real.exp_log (_root_.GD.N0232.N0720.N1067.d014399 theta)]



@[simp] theorem d015081 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    ((_root_.GD.N0232.N0720.N1067.d014400 theta)⁻¹).shift =
      -((_root_.GD.N0232.N0720.N1067.d014398 theta)⁻¹ * theta.location) := by
  simp [_root_.GD.N0232.N0720.N1067.d014400, Real.exp_neg,
    Real.exp_log (_root_.GD.N0232.N0720.N1067.d014399 theta)]








def d015082
    (q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) : Prop :=
  ∀ (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (limit : ℝ × ℝ),
    Tendsto (fun j ↦ ((gSeq j).shift, (gSeq j).logScale))
      atTop (nhds limit) →
    TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j)
        (_root_.GD.N0232.N0720.N1214.d014265 m n
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1))
      atTop
      (_root_.GD.N0232.N0720.N1214.d014261 m n ⟨limit.1, limit.2⟩
        (_root_.GD.N0232.N0720.N1214.d014265 m n
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1))



theorem d015083
    (g : _root_.GD.N0232.N0720.N1025.d014301) :
    Measure.QuasiMeasurePreserving
      (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g • omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  refine ⟨?_, ?_⟩
  · simpa only [_root_.GD.N0232.N0720.N1214.d014259] using
      _root_.GD.N0107.d009026
        m n g.shift g.d009239 g.d009239
  · change
      (_root_.GD.N0232.N0720.N1080.d014171 m n _root_.GD.N0232.N0720.N1080.d014169).map
          (_root_.GD.N0107.d009024
            m n g.shift g.d009239 g.d009239) ≪
        _root_.GD.N0232.N0720.N1080.d014172 m n
    rw [_root_.GD.N0232.N0720.N1215.d014282 m n g _root_.GD.N0232.N0720.N1080.d014169]
    exact _root_.GD.N0232.N0720.N1080.d014173
      m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)




theorem d015084
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    {a b : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (htransport : _root_.GD.N0232.N0720.N1214.d014261 m n g a =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014261 m n g b) :
    a =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] b := by
  have hpull :=
    (_root_.GD.N0232.N0720.N1068.d015083 m n g).ae_eq htransport
  filter_upwards [hpull] with omega homega
  change _root_.GD.N0232.N0720.N1214.d014261 m n g a (g • omega) =
    _root_.GD.N0232.N0720.N1214.d014261 m n g b (g • omega) at homega
  rw [show g • omega =
        _root_.GD.N0107.d009024
          m n g.shift g.d009239 g.d009239 omega by rfl,
    _root_.GD.N0232.N0720.N1215.d014283 m n g a omega,
    _root_.GD.N0232.N0720.N1215.d014283 m n g b omega] at homega
  change g.shift + g.d009239 * a omega =
    g.shift + g.d009239 * b omega at homega
  have hmul : g.d009239 * a omega = g.d009239 * b omega := by
    linarith
  exact mul_left_cancel₀ g.d009241 hmul









def d015085
    (p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) : Prop :=
  ∀ (thetaSeq : ℕ → _root_.GD.N0232.N0720.N1080.d014168) (extraction : ℕ → ℕ)
      (limit : ℝ × ℝ),
    Tendsto extraction atTop atTop →
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1068.d015079 (thetaSeq (extraction j)))
      atTop (nhds limit) →
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1073.d015043 m n hm hn
        (thetaSeq (extraction j)) q)
      atTop (nhds (_root_.GD.N0232.N0720.N1068.d015070 m n hm hn p)) →
    q = p





theorem d015086
    (p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p)
    (hcontinuous : _root_.GD.N0232.N0720.N1068.d015082
      m n hm hn q) :
    _root_.GD.N0232.N0720.N1068.d015085 m n hm hn p q := by
  intro thetaSeq extraction limit hextraction hcoordinate hstrong
  let P : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm p
  let Q : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q
  let gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301 := fun j ↦
    (_root_.GD.N0232.N0720.N1067.d014400 (thetaSeq (extraction j)))⁻¹
  let gLimit : _root_.GD.N0232.N0720.N1025.d014301 := ⟨limit.1, limit.2⟩
  have hcoordinate' : Tendsto
      (fun j ↦ ((gSeq j).shift, (gSeq j).logScale))
      atTop (nhds limit) := by
    simpa [gSeq, _root_.GD.N0232.N0720.N1068.d015079] using hcoordinate
  have hLp : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1215.d014289 m n hm hn (gSeq j) Q.1 Q.2)
      atTop (nhds P.1) := by
    simpa [gSeq, P, Q, _root_.GD.N0232.N0720.N1068.d015070,
      _root_.GD.N0232.N0720.N1068.d015077] using hstrong
  have hmeasureClass : TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun j ↦ _root_.GD.N0232.N0720.N1215.d014289 m n hm hn (gSeq j) Q.1 Q.2)
      atTop P.1 :=
    tendstoInMeasure_of_tendsto_Lp hLp
  have hmeasureRaw : TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j)
        (_root_.GD.N0232.N0720.N1214.d014265 m n Q.1))
      atTop (_root_.GD.N0232.N0720.N1214.d014265 m n P.1) := by
    exact TendstoInMeasure.congr
      (fun j ↦
        (_root_.GD.N0232.N0720.N1215.d014288 m n hm hn (gSeq j) Q.1 Q.2).coeFn_toLp)
      (_root_.GD.N0232.N0720.N1214.d014267 m n P.1).symm hmeasureClass
  have hmeasureContinuous : TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j)
        (_root_.GD.N0232.N0720.N1214.d014265 m n Q.1))
      atTop (_root_.GD.N0232.N0720.N1214.d014261 m n gLimit (_root_.GD.N0232.N0720.N1214.d014265 m n Q.1)) := by
    simpa [gLimit, Q] using hcontinuous gSeq limit hcoordinate'
  have hlimit :
      _root_.GD.N0232.N0720.N1214.d014261 m n gLimit (_root_.GD.N0232.N0720.N1214.d014265 m n Q.1) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n P.1 :=
    tendstoInMeasure_ae_unique hmeasureContinuous hmeasureRaw
  have hfixedStrong : _root_.GD.N0232.N0720.N1215.d014298 m n hm hn gLimit P = P :=
    _root_.GD.N0232.N0720.N1025.d014318
      m n hm hn p hfixed gLimit
  have hpRawFixed :
      _root_.GD.N0232.N0720.N1214.d014261 m n gLimit (_root_.GD.N0232.N0720.N1214.d014265 m n P.1) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n P.1 := by
    apply (MemLp.toLp_eq_toLp_iff
      (_root_.GD.N0232.N0720.N1215.d014288 m n hm hn gLimit P.1 P.2)
      (_root_.GD.N0232.N0720.N1214.d014268 m n P.1)).mp
    rw [_root_.GD.N0232.N0720.N1214.d014269]
    have hvalue := congrArg Subtype.val hfixedStrong
    change _root_.GD.N0232.N0720.N1215.d014289 m n hm hn gLimit P.1 P.2 = P.1 at hvalue
    exact hvalue
  have htransport :
      _root_.GD.N0232.N0720.N1214.d014261 m n gLimit (_root_.GD.N0232.N0720.N1214.d014265 m n Q.1) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014261 m n gLimit (_root_.GD.N0232.N0720.N1214.d014265 m n P.1) :=
    hlimit.trans hpRawFixed.symm
  have hQPraw : _root_.GD.N0232.N0720.N1214.d014265 m n Q.1 =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014265 m n P.1 :=
    _root_.GD.N0232.N0720.N1068.d015084 m n gLimit htransport
  have hQP : Q.1 = P.1 := by
    calc
      Q.1 = MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n Q.1)
          (_root_.GD.N0232.N0720.N1214.d014268 m n Q.1) :=
        (_root_.GD.N0232.N0720.N1214.d014269 m n Q.1).symm
      _ = MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n P.1)
          (_root_.GD.N0232.N0720.N1214.d014268 m n P.1) :=
        MemLp.toLp_congr
          (_root_.GD.N0232.N0720.N1214.d014268 m n Q.1)
          (_root_.GD.N0232.N0720.N1214.d014268 m n P.1) hQPraw
      _ = P.1 := _root_.GD.N0232.N0720.N1214.d014269 m n P.1
  apply (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm.injective
  exact Subtype.ext hQP



structure d015087
    {p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn}
    (packet : _root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q) where
  extraction : ℕ → ℕ
  extraction_tendsto : Tendsto extraction atTop atTop
  end_alternative :
    Tendsto
        (fun j ↦ ((_root_.GD.N0232.N0720.N1067.d014400
          (packet.thetaSeq (extraction j)))⁻¹).shift) atTop atTop ∨
      Tendsto
        (fun j ↦ ((_root_.GD.N0232.N0720.N1067.d014400
          (packet.thetaSeq (extraction j)))⁻¹).shift) atTop atBot ∨
      Tendsto
        (fun j ↦ ((_root_.GD.N0232.N0720.N1067.d014400
          (packet.thetaSeq (extraction j)))⁻¹).d009239) atTop atTop ∨
      Tendsto
        (fun j ↦ ((_root_.GD.N0232.N0720.N1067.d014400
          (packet.thetaSeq (extraction j)))⁻¹).d009239) atTop (nhds 0)




theorem d015087.d015088
    {p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn}
    {packet : _root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q}
    (certificate : _root_.GD.N0232.N0720.N1068.d015087 m n hm hn packet) :
    Tendsto
        (fun j ↦ -((_root_.GD.N0232.N0720.N1067.d014398
          (packet.thetaSeq (certificate.extraction j)))⁻¹ *
            (packet.thetaSeq (certificate.extraction j)).location))
        atTop atTop ∨
      Tendsto
        (fun j ↦ -((_root_.GD.N0232.N0720.N1067.d014398
          (packet.thetaSeq (certificate.extraction j)))⁻¹ *
            (packet.thetaSeq (certificate.extraction j)).location))
        atTop atBot ∨
      Tendsto
        (fun j ↦ (_root_.GD.N0232.N0720.N1067.d014398
          (packet.thetaSeq (certificate.extraction j)))⁻¹)
        atTop atTop ∨
      Tendsto
        (fun j ↦ (_root_.GD.N0232.N0720.N1067.d014398
          (packet.thetaSeq (certificate.extraction j)))⁻¹)
        atTop (nhds 0) := by
  simpa only [_root_.GD.N0232.N0720.N1068.d015081,
    _root_.GD.N0232.N0720.N1068.d015080] using certificate.end_alternative



theorem d015089
    {p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn}
    (packet : _root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1)
    (hproper : _root_.GD.N0232.N0720.N1068.d015085 m n hm hn p q)
    (hne : q ≠ p) :
    ¬ _root_.GD.N0238.N0750.d004292
      (fun j ↦ _root_.GD.N0232.N0720.N1068.d015079 (packet.thetaSeq j)) := by
  rintro ⟨extraction, hextraction, limit, hlimit⟩
  apply hne
  apply hproper packet.thetaSeq extraction limit hextraction hlimit
  exact
    (_root_.GD.N0232.N0720.N1068.N1755.d015078
        m n hm hn packet hfixed hdom).comp hextraction



theorem d015090
    {p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn}
    (packet : _root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1)
    (hproper : _root_.GD.N0232.N0720.N1068.d015085 m n hm hn p q)
    (hne : q ≠ p) :
    Nonempty (_root_.GD.N0232.N0720.N1068.d015087 m n hm hn packet) := by
  have hnoCluster : ¬ _root_.GD.N0238.N0750.d004292
      (fun j ↦ _root_.GD.N0232.N0720.N1068.d015079 (packet.thetaSeq j)) :=
    _root_.GD.N0232.N0720.N1068.d015089
      m n hm hn packet hfixed hdom hproper hne
  have hescape : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1068.d015079 (packet.thetaSeq j)‖)
      atTop atTop := by
    have hdist := _root_.GD.N0238.N0750.d004295
      (0 : ℝ × ℝ)
      (fun j ↦ _root_.GD.N0232.N0720.N1068.d015079 (packet.thetaSeq j)) hnoCluster
    simpa [dist_eq_norm] using hdist
  obtain ⟨extraction, hextraction, hend⟩ :=
    _root_.GD.N0232.N0719.N0826.d012089
      (fun j ↦ ((_root_.GD.N0232.N0720.N1067.d014400 (packet.thetaSeq j))⁻¹).shift)
      (fun j ↦ ((_root_.GD.N0232.N0720.N1067.d014400 (packet.thetaSeq j))⁻¹).logScale)
      (by simpa [_root_.GD.N0232.N0720.N1068.d015079] using hescape)
  refine ⟨⟨extraction, hextraction, ?_⟩⟩
  rcases hend with hshiftTop | hshiftBot | hlogTop | hlogBot
  · exact Or.inl (by simpa [Function.comp_def] using hshiftTop)
  · exact Or.inr (Or.inl
      (by simpa [Function.comp_def] using hshiftBot))
  · right
    right
    left
    have hexp := Real.tendsto_exp_atTop.comp hlogTop
    simpa [Function.comp_def, _root_.GD.N0232.N0719.N0946.d009229.d009239] using hexp
  · right
    right
    right
    have hexp := Real.tendsto_exp_atBot.comp hlogBot
    simpa [Function.comp_def, _root_.GD.N0232.N0719.N0946.d009229.d009239] using hexp







theorem d015091
    {p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn}
    (packet : _root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1)
    (hproper : _root_.GD.N0232.N0720.N1068.d015085 m n hm hn p q) :
    q = p ∨
      Nonempty (_root_.GD.N0232.N0720.N1068.d015087 m n hm hn packet) := by
  by_cases hqp : q = p
  · exact Or.inl hqp
  · exact Or.inr
      (_root_.GD.N0232.N0720.N1068.d015090
        m n hm hn packet hfixed hdom hproper hqp)

end

end N1068
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1068.d015073
#print axioms _root_.GD.N0232.N0720.N1068.N1755.d015078
#print axioms _root_.GD.N0232.N0720.N1068.d015087.d015088
#print axioms _root_.GD.N0232.N0720.N1068.d015091
