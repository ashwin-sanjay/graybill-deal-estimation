import GD.Module0132
import GD.Module0962
import GD.Module0951
import GD.Module1040


































open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Topology

namespace GD
namespace N0232
namespace N0720
namespace N1199

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1483
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1133
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1261
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0238
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0571
open _root_.GD.N0230.N0559
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0635
open _root_.GD.N0230.N0708
open _root_.GD.N0232.N0719.N0945
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

instance d016684 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance



instance d016685 :
    FirstCountableTopology _root_.GD.N0232.N0720.N1025.d014301 :=
  _root_.GD.N0232.N0719.N0945.d009264.isInducing.firstCountableTopology


abbrev d016686 (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g q)).1

theorem d016687
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
  ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g q)).2


theorem d016688
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) (g : _root_.GD.N0232.N0720.N1025.d014301) :
    ‖_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g‖ ≤ _root_.GD.N0232.N0720.N1080.d014248 m n hm hn :=
  _root_.GD.N0232.N0720.N1080.d014250 m n hm hn _
    (_root_.GD.N0232.N0720.N1199.d016687 m n hm hn q g)


theorem d016689
    {gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301} {g : _root_.GD.N0232.N0720.N1025.d014301}
    (hg : Tendsto gSeq atTop (𝓝 g)) :
    Tendsto (fun j ↦ ((gSeq j).shift, (gSeq j).logScale)) atTop
      (𝓝 (g.shift, g.logScale)) :=
  ((_root_.GD.N0232.N0719.N0945.d009267.tendsto g).comp hg).prodMk_nhds
    ((_root_.GD.N0232.N0719.N0945.d009266.tendsto g).comp hg)





theorem d016690
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (hcoordinate : Tendsto
      (fun j ↦ ((gSeq j).shift, (gSeq j).logScale))
      atTop (𝓝 (g.shift, g.logScale))) :
    _root_.GD.N0230.N0708.d001170 ℝ (fun j ↦ _root_.GD.N0232.N0720.N1199.d016686 m n hm hn q (gSeq j)) atTop
      (_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g) := by
  exact _root_.GD.N0230.N0635.d001526
    (fun j ↦ _root_.GD.N0232.N0720.N1199.d016686 m n hm hn q (gSeq j))
    (_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g)
    (_root_.GD.N0232.N0720.N1080.d014248 m n hm hn)
    (fun j ↦ _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q (gSeq j)))
    (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g))
    (fun j ↦ _root_.GD.N0232.N0720.N1214.d014267 m n _)
    (_root_.GD.N0232.N0720.N1214.d014267 m n _)
    (fun j ↦ _root_.GD.N0232.N0720.N1199.d016688 m n hm hn q (gSeq j))
    (_root_.GD.N0232.N0720.N1215.d015117 m n hm hn q gSeq g hcoordinate)


theorem d016691
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (hg : Tendsto gSeq atTop (𝓝 g)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1025.d014316 m n hm hn (gSeq j) q) atTop
      (𝓝 (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g q)) := by
  rw [tendsto_subtype_rng]
  have hweak := _root_.GD.N0232.N0720.N1199.d016690 m n hm hn q gSeq g
    (_root_.GD.N0232.N0720.N1199.d016689 hg)
  unfold _root_.GD.N0230.N0708.d001170 at hweak
  have hval : ∀ h : _root_.GD.N0232.N0720.N1025.d014301,
      (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn h q).1 =
        toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) (_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q h) := by
    intro h
    rw [_root_.GD.N0232.N0720.N1199.d016686, _root_.GD.N0232.N0720.N1025.d014309]
    simp
  simpa only [hval] using hweak



theorem d016692 (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦ _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g q) := by
  rw [continuous_iff_seqContinuous]
  intro gSeq g hg
  exact _root_.GD.N0232.N0720.N1199.d016691 m n hm hn q gSeq g hg


theorem d016693 (d : _root_.GD.N0232.N0720.N1261.d014958 m n hm hn) :
    Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦
      _root_.GD.N0232.N0720.N1261.d014959 m n hm hn g d) := by
  apply Continuous.subtype_mk (_root_.GD.N0232.N0720.N1199.d016692 m n hm hn d.1)





theorem d016694
    (stage : ℕ → Finset _root_.GD.N0232.N0719.N0945.d009269)
    (hstage : _root_.GD.N0238.d004327 stage)
    (hmono : Monotone stage)
    (energy : _root_.GD.N0232.N0719.N0945.d009269 →
      _root_.GD.N0232.N0720.N1261.d014958 m n hm hn → ℝ)
    (point : ℕ → _root_.GD.N0232.N0720.N1261.d014958 m n hm hn)
    (henergy : ∀ N, ∀ i ∈ stage N,
      dist
          (_root_.GD.N0232.N0720.N1261.d014959 m n hm hn (_root_.GD.N0232.N0719.N0945.d009270 i) (point N))
          (point N) ^ 2 ≤
        energy i (point N))
    (hvanish : _root_.GD.N0230.N0559.d004363 stage energy point)
    (control : _root_.GD.N0232.N0720.N1261.d014958 m n hm hn → ℝ)
    (hcompact : _root_.GD.N0238.d004342 control)
    (hbounded : _root_.GD.N0238.d004344 control point) :
    ∃ p : _root_.GD.N0232.N0720.N1261.d014926 m n hm hn,
      _root_.GD.N0230.N0571.d000684 (_root_.GD.N0232.N0720.N1261.d014949 m n hm hn) (_root_.GD.N0232.N0720.N1261.d014950 m n hm hn) p ∧
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1261.d014927 m n)).symm p.1) ∧
      ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
        _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p :=
  _root_.GD.N0232.N0720.N1261.d014961 m n hm hn
    (_root_.GD.N0232.N0720.N1199.d016693 m n hm hn)
    stage hstage hmono energy point henergy hvanish control hcompact hbounded




theorem d016695
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1159.d014637 m n p := by
  intro theta
  have := _root_.GD.N0232.N0720.N1215.d014287 m n hm hn p hp theta
  rwa [_root_.GD.N0232.N0720.N1215.d014286] at this


theorem d016696
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g =
      _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1
        ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).2 := by
  rfl




theorem d016697
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) (g : _root_.GD.N0232.N0720.N1025.d014301) :
    ‖_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g‖ ^ 2 =
      g.d009239 ^ 2 *
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1).toReal := by
  have hrisk := _root_.GD.N0232.N0720.N1215.d014290 m n hm hn g
    (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).2
  rw [_root_.GD.N0232.N0720.N1215.d014279, ← _root_.GD.N0232.N0720.N1199.d016696,
    _root_.GD.N0232.N0720.N1080.d014190] at hrisk
  have hfin : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
      ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1 ≠ ⊤ :=
    _root_.GD.N0232.N0720.N1199.d016695 m n hm hn _
      ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).2 _
  have := congrArg ENNReal.toReal hrisk
  rw [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _)] at this
  simpa only [zero_sub, norm_neg] using this


theorem d016698 :
    Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦ g⁻¹) := by
  rw [← _root_.GD.N0232.N0719.N0945.d009264.comp_continuous_iff]
  change Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦
    (-g.logScale, -(Real.exp (-g.logScale) * g.shift)))
  exact _root_.GD.N0232.N0719.N0945.d009266.neg.prodMk
    ((Real.continuous_exp.comp _root_.GD.N0232.N0719.N0945.d009266.neg).mul
      _root_.GD.N0232.N0719.N0945.d009267).neg



theorem d016699 :
    Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦
      _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) := by
  apply (_root_.GD.N0232.N0720.N1499.d014996.comp_continuous_iff).mp
  change Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦
    (g⁻¹.shift + g⁻¹.d009239 * (0 : ℝ),
      (g⁻¹.d009239 * (1 : ℝ), g⁻¹.d009239 * (1 : ℝ))))
  have hinv := _root_.GD.N0232.N0720.N1199.d016698
  have hshift : Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦ g⁻¹.shift) :=
    _root_.GD.N0232.N0719.N0945.d009267.comp hinv
  have hdil : Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦ g⁻¹.d009239) :=
    _root_.GD.N0232.N0719.N0945.d009268.comp hinv
  exact (hshift.add (hdil.mul continuous_const)).prodMk
    ((hdil.mul continuous_const).prodMk (hdil.mul continuous_const))


theorem d016700 (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦ ‖_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g‖) := by
  have hsq : Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦
      ‖_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g‖ ^ 2) := by
    simp_rw [_root_.GD.N0232.N0720.N1199.d016697]
    exact (_root_.GD.N0232.N0719.N0945.d009268.pow 2).mul
      ((_root_.GD.N0232.N0720.N1111.d016606 m n _
        (_root_.GD.N0232.N0720.N1199.d016695 m n hm hn _
          ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).2)).comp
        _root_.GD.N0232.N0720.N1199.d016699)
  have : (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦ ‖_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g‖) =
      fun g ↦ Real.sqrt (‖_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g‖ ^ 2) := by
    funext g
    rw [Real.sqrt_sq (norm_nonneg _)]
  rw [this]
  exact Real.continuous_sqrt.comp hsq



theorem d016701
    (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (hg : Tendsto gSeq atTop (𝓝 g)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1199.d016686 m n hm hn q (gSeq j)) atTop
      (𝓝 (_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g)) := by
  exact _root_.GD.N0230.N0635.d001527
    (fun j ↦ _root_.GD.N0232.N0720.N1199.d016686 m n hm hn q (gSeq j))
    (_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g)
    (_root_.GD.N0232.N0720.N1080.d014248 m n hm hn)
    (fun j ↦ _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q (gSeq j)))
    (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g))
    (fun j ↦ _root_.GD.N0232.N0720.N1214.d014267 m n _)
    (_root_.GD.N0232.N0720.N1214.d014267 m n _)
    (fun j ↦ _root_.GD.N0232.N0720.N1199.d016688 m n hm hn q (gSeq j))
    (_root_.GD.N0232.N0720.N1215.d015117 m n hm hn q gSeq g
      (_root_.GD.N0232.N0720.N1199.d016689 hg))
    (((_root_.GD.N0232.N0720.N1199.d016700 m n hm hn q).tendsto g).comp hg)




theorem d016702 (q : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦ _root_.GD.N0232.N0720.N1199.d016686 m n hm hn q g) := by
  rw [continuous_iff_seqContinuous]
  intro gSeq g hg
  exact _root_.GD.N0232.N0720.N1199.d016701 m n hm hn q gSeq g hg


theorem d016703 (p : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    Continuous (fun g : _root_.GD.N0232.N0720.N1025.d014301 ↦
      (_root_.GD.N0232.N0720.N1215.d014298 m n hm hn g p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))) := by
  have := _root_.GD.N0232.N0720.N1199.d016702 m n hm hn (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn p)
  simpa only [_root_.GD.N0232.N0720.N1199.d016686, _root_.GD.N0232.N0720.N1025.d014317, Equiv.symm_apply_apply] using this

end

end N1199
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1199.d016692
#print axioms _root_.GD.N0232.N0720.N1199.d016694
#print axioms _root_.GD.N0232.N0720.N1199.d016702
#print axioms _root_.GD.N0232.N0720.N1199.d016703
