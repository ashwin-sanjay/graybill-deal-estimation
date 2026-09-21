import GD.Module0010
import GD.Module0016
import GD.Module0960
import GD.Module0955


















open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1484

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1073
open _root_.GD.N0232.N0720.N1068
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0562
open _root_.GD.N0230.N0590
open _root_.GD.N0230.N0569
open _root_.GD.N0230.N0580
open _root_.GD.N0230.N0583
open _root_.GD.N0230.N0596
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

noncomputable local instance d015092 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171
  infer_instance

noncomputable local instance d015093 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172
  infer_instance



def d015094 (g : _root_.GD.N0232.N0720.N1025.d014301)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : _root_.GD.N0232.N0720.N1080.d014170 m n :=
  g⁻¹ • omega

theorem d015095 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    Measurable (_root_.GD.N0232.N0720.N1484.d015094 m n g) := by
  unfold _root_.GD.N0232.N0720.N1484.d015094
  change Measurable
    (_root_.GD.N0107.d009024
      m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239)
  exact _root_.GD.N0107.d009026
    m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239



theorem d015096
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    Continuous (fun z : ℝ × ℝ ↦
      _root_.GD.N0232.N0720.N1484.d015094 m n (⟨z.1, z.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) omega) := by
  unfold _root_.GD.N0232.N0720.N1484.d015094
  simp only [_root_.GD.N0232.N0720.N1214.d014259,
    _root_.GD.N0232.N0719.N0946.d009229.d009237, _root_.GD.N0232.N0719.N0946.d009229.d009238, _root_.GD.N0232.N0719.N0946.d009229.d009239]
  unfold _root_.GD.N0107.d009024
    _root_.GD.N0107.d009018
  fun_prop



theorem d015097
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Continuous d)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    Continuous (fun z : ℝ × ℝ ↦
      _root_.GD.N0232.N0720.N1214.d014261 m n (⟨z.1, z.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) d omega) := by
  unfold _root_.GD.N0232.N0720.N1214.d014261
  change Continuous (fun z : ℝ × ℝ ↦
    z.1 + Real.exp z.2 *
      d (_root_.GD.N0232.N0720.N1484.d015094 m n
        (⟨z.1, z.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) omega))
  exact continuous_fst.add
    ((Real.continuous_exp.comp continuous_snd).mul
      (hd.comp (_root_.GD.N0232.N0720.N1484.d015096 m n omega)))



theorem d015098
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (limit : ℝ × ℝ)
    (hcoordinate : Tendsto
      (fun j ↦ ((gSeq j).shift, (gSeq j).logScale))
      atTop (nhds limit))
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Continuous d) :
    TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) d) atTop
      (_root_.GD.N0232.N0720.N1214.d014261 m n (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) d) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro j
    exact (_root_.GD.N0232.N0720.N1214.d014262 m n (gSeq j) d hd.measurable).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega ↦
      (_root_.GD.N0232.N0720.N1484.d015097 m n d hd omega).continuousAt.tendsto.comp
        hcoordinate



def d015099 (g : _root_.GD.N0232.N0720.N1025.d014301) : _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169



theorem d015100
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (limit : ℝ × ℝ)
    (hcoordinate : Tendsto
      (fun j ↦ ((gSeq j).shift, (gSeq j).logScale))
      atTop (nhds limit)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1484.d015099 (gSeq j)) atTop
      (nhds (_root_.GD.N0232.N0720.N1484.d015099
        (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301))) := by
  have hshift : Tendsto (fun j ↦ (gSeq j).shift) atTop
      (nhds limit.1) :=
    (continuous_fst.tendsto limit).comp hcoordinate
  have hlog : Tendsto (fun j ↦ (gSeq j).logScale) atTop
      (nhds limit.2) :=
    (continuous_snd.tendsto limit).comp hcoordinate
  have hscale : Tendsto (fun j ↦ Real.exp (-(gSeq j).logScale)) atTop
      (nhds (Real.exp (-limit.2))) :=
    (Real.continuous_exp.tendsto (-limit.2)).comp hlog.neg
  have hlocation : Tendsto
      (fun j ↦ -(Real.exp (-(gSeq j).logScale) * (gSeq j).shift)) atTop
      (nhds (-(Real.exp (-limit.2) * limit.1))) :=
    (hscale.mul hshift).neg
  rw [_root_.GD.N0232.N0720.N1499.d014996.tendsto_nhds_iff]
  change Tendsto
    (fun j ↦ _root_.GD.N0232.N0720.N1499.d014993
      (_root_.GD.N0232.N0720.N1484.d015099 (gSeq j))) atTop
    (nhds (_root_.GD.N0232.N0720.N1499.d014993 (_root_.GD.N0232.N0720.N1484.d015099
      (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301))))
  simpa [_root_.GD.N0232.N0720.N1484.d015099, _root_.GD.N0232.N0720.N1499.d014993, _root_.GD.N0232.N0720.N1215.d014272,
    _root_.GD.N0232.N0720.N1080.d014169, _root_.GD.N0232.N0719.N0946.d009229.d009237, _root_.GD.N0232.N0719.N0946.d009229.d009238, _root_.GD.N0232.N0719.N0946.d009229.d009239] using
    hlocation.prodMk_nhds (hscale.prodMk_nhds hscale)


theorem d015101
    (g : _root_.GD.N0232.N0720.N1025.d014301) :
    (_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1484.d015094 m n g) =
      _root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1484.d015099 g) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1484.d015094 _root_.GD.N0232.N0720.N1484.d015099
  change
    (_root_.GD.N0232.N0720.N1080.d014171 m n _root_.GD.N0232.N0720.N1080.d014169).map
        (_root_.GD.N0107.d009024
          m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239) =
      _root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)
  exact _root_.GD.N0232.N0720.N1215.d014282 m n g⁻¹ _root_.GD.N0232.N0720.N1080.d014169



theorem d015102
    (g : _root_.GD.N0232.N0720.N1025.d014301) :
    (_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1484.d015094 m n g) =
      (_root_.GD.N0232.N0720.N1080.d014172 m n).withDensity
        (fun omega ↦ ENNReal.ofReal
          (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1484.d015099 g) omega)) := by
  rw [_root_.GD.N0232.N0720.N1484.d015101 m n g]
  exact _root_.GD.N0232.N0720.N1499.d015006 m n (_root_.GD.N0232.N0720.N1484.d015099 g)



theorem d015103
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Integrable (_root_.GD.N0232.N0720.N1499.d015001 m n theta) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hmeasure := congrArg
    (fun mu : Measure (_root_.GD.N0232.N0720.N1080.d014170 m n) ↦ mu Set.univ)
    (_root_.GD.N0232.N0720.N1499.d015006 m n theta)
  have hlintegral :
      (∫⁻ omega, ENNReal.ofReal (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega)
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ] at hmeasure
    simpa only [measure_univ, Measure.restrict_univ] using hmeasure.symm
  have hint := integrable_toReal_of_lintegral_ne_top
    (_root_.GD.N0232.N0720.N1499.d015002 m n theta |>.ennreal_ofReal.aemeasurable)
    (by rw [hlintegral]; exact ENNReal.one_ne_top)
  simpa only [ENNReal.toReal_ofReal
    (_root_.GD.N0232.N0720.N1499.d015003 m n theta _)] using hint


theorem d015104
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n theta omega
      ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 1 := by
  have hmeasure := congrArg
    (fun mu : Measure (_root_.GD.N0232.N0720.N1080.d014170 m n) ↦ mu Set.univ)
    (_root_.GD.N0232.N0720.N1499.d015006 m n theta)
  have hlintegral :
      (∫⁻ omega, ENNReal.ofReal (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega)
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ] at hmeasure
    simpa only [measure_univ, Measure.restrict_univ] using hmeasure.symm
  have hofReal : ENNReal.ofReal
      (∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n theta omega
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 1 := by
    rw [ofReal_integral_eq_lintegral_ofReal
      (_root_.GD.N0232.N0720.N1484.d015103 m n theta)
      (ae_of_all (_root_.GD.N0232.N0720.N1080.d014172 m n) fun omega ↦
        _root_.GD.N0232.N0720.N1499.d015003 m n theta omega)]
    exact hlintegral
  exact ENNReal.ofReal_eq_one.mp hofReal



theorem d015105
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (limit : ℝ × ℝ)
    (hcoordinate : Tendsto
      (fun j ↦ ((gSeq j).shift, (gSeq j).logScale))
      atTop (nhds limit))
    (s : Set (_root_.GD.N0232.N0720.N1080.d014170 m n)) (hs : MeasurableSet s)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ j in atTop,
      (_root_.GD.N0232.N0720.N1080.d014172 m n).real (_root_.GD.N0232.N0720.N1484.d015094 m n (gSeq j) ⁻¹' s) <
        (_root_.GD.N0232.N0720.N1080.d014172 m n).real
          (_root_.GD.N0232.N0720.N1484.d015094 m n
            (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) ⁻¹' s) + delta := by
  let gLimit : _root_.GD.N0232.N0720.N1025.d014301 := ⟨limit.1, limit.2⟩
  have htheta := _root_.GD.N0232.N0720.N1484.d015100
    gSeq limit hcoordinate
  have hmap (g : _root_.GD.N0232.N0720.N1025.d014301) :
      (_root_.GD.N0232.N0720.N1080.d014172 m n).real (_root_.GD.N0232.N0720.N1484.d015094 m n g ⁻¹' s) =
        ((_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1484.d015094 m n g)).real s := by
    change ((_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1484.d015094 m n g ⁻¹' s)).toReal =
      (((_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1484.d015094 m n g)) s).toReal
    rw [Measure.map_apply (_root_.GD.N0232.N0720.N1484.d015095 m n g) hs]
  simp_rw [hmap, _root_.GD.N0232.N0720.N1484.d015102]
  apply _root_.GD.N0230.N0590.d000145
  · intro j
    exact _root_.GD.N0232.N0720.N1499.d015002 m n
      (_root_.GD.N0232.N0720.N1484.d015099 (gSeq j))
  · exact _root_.GD.N0232.N0720.N1499.d015002 m n
      (_root_.GD.N0232.N0720.N1484.d015099 gLimit)
  · intro j
    exact _root_.GD.N0232.N0720.N1484.d015103 m n
      (_root_.GD.N0232.N0720.N1484.d015099 (gSeq j))
  · exact _root_.GD.N0232.N0720.N1484.d015103 m n
      (_root_.GD.N0232.N0720.N1484.d015099 gLimit)
  · intro j omega
    exact _root_.GD.N0232.N0720.N1499.d015003 m n
      (_root_.GD.N0232.N0720.N1484.d015099 (gSeq j)) omega
  · exact _root_.GD.N0232.N0720.N1499.d015003 m n
      (_root_.GD.N0232.N0720.N1484.d015099 gLimit)
  · intro omega
    exact (_root_.GD.N0232.N0720.N1499.d015007 m n omega).continuousAt.tendsto.comp
      htheta
  · simpa only [_root_.GD.N0232.N0720.N1484.d015104]
      using (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) from
        tendsto_const_nhds)
  · exact hs
  · exact hdelta




theorem d015106
    (q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) (g : _root_.GD.N0232.N0720.N1025.d014301) :
    MemLp
      (_root_.GD.N0232.N0720.N1214.d014265 m n ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1)
      2 ((_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1484.d015094 m n g)) := by
  let Q : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
    (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q
  let d := _root_.GD.N0232.N0720.N1214.d014265 m n Q.1
  have horbit : MemLp (_root_.GD.N0232.N0720.N1214.d014261 m n g d) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    exact _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g Q.1 Q.2
  have hcentered : MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1214.d014261 m n g d omega - g.shift)
      2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    horbit.sub (memLp_const g.shift)
  have hscaled : MemLp
      (fun omega ↦ g.d009239⁻¹ *
        (_root_.GD.N0232.N0720.N1214.d014261 m n g d omega - g.shift))
      2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    hcentered.const_mul g.d009239⁻¹
  have hcomp : MemLp (d ∘ _root_.GD.N0232.N0720.N1484.d015094 m n g)
      2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    simpa [d, _root_.GD.N0232.N0720.N1484.d015094, _root_.GD.N0232.N0720.N1214.d014261, Function.comp_def,
      _root_.GD.N0232.N0719.N0946.d009229.d009244, g.d009241] using hscaled
  exact (memLp_map_measure_iff
    (_root_.GD.N0232.N0720.N1214.d014266 m n Q.1).aestronglyMeasurable
    (_root_.GD.N0232.N0720.N1484.d015095 m n g).aemeasurable).2 hcomp



theorem d015107
    (g : _root_.GD.N0232.N0720.N1025.d014301) (a b : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    dist (_root_.GD.N0232.N0720.N1214.d014261 m n g a omega) (_root_.GD.N0232.N0720.N1214.d014261 m n g b omega) =
      g.d009239 * dist
        (a (_root_.GD.N0232.N0720.N1484.d015094 m n g omega))
        (b (_root_.GD.N0232.N0720.N1484.d015094 m n g omega)) := by
  rw [Real.dist_eq]
  unfold _root_.GD.N0232.N0720.N1214.d014261 _root_.GD.N0232.N0720.N1484.d015094
  simp only [_root_.GD.N0232.N0719.N0946.d009229.d009244]
  rw [show
    (g.shift + g.d009239 * a (g⁻¹ • omega)) -
        (g.shift + g.d009239 * b (g⁻¹ • omega)) =
      g.d009239 * (a (g⁻¹ • omega) - b (g⁻¹ • omega)) by ring]
  rw [abs_mul, abs_of_pos g.d009240, Real.dist_eq]



theorem d015108
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (limit : ℝ × ℝ)
    (hcoordinate : Tendsto
      (fun j ↦ ((gSeq j).shift, (gSeq j).logScale))
      atTop (nhds limit))
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (huniformApproximation : ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
      ∃ h : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Continuous h ∧
        (∀ᶠ j in atTop,
          (_root_.GD.N0232.N0720.N1080.d014172 m n).real
            {omega |
              ε ≤ dist
                (_root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) d omega)
                (_root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) h omega)} < δ) ∧
        (_root_.GD.N0232.N0720.N1080.d014172 m n).real
          {omega |
            ε ≤ dist
              (_root_.GD.N0232.N0720.N1214.d014261 m n
                (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) h omega)
              (_root_.GD.N0232.N0720.N1214.d014261 m n
                (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) d omega)} < δ) :
    TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) d) atTop
      (_root_.GD.N0232.N0720.N1214.d014261 m n
        (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) d) := by
  apply _root_.GD.N0230.N0562.d000067
  intro ε hε δ hδ
  obtain ⟨h, hh, hmoving, hlimit⟩ :=
    huniformApproximation ε hε δ hδ
  exact ⟨
    (fun j ↦ _root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) h),
    _root_.GD.N0232.N0720.N1214.d014261 m n
      (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) h,
    _root_.GD.N0232.N0720.N1484.d015098
      m n gSeq limit hcoordinate h hh,
    hmoving, hlimit⟩



theorem d015109
    (gSeq : ℕ → _root_.GD.N0232.N0720.N1025.d014301) (limit : ℝ × ℝ)
    (hcoordinate : Tendsto
      (fun j ↦ ((gSeq j).shift, (gSeq j).logScale))
      atTop (nhds limit))
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hdMeasurable : Measurable d)
    {p : ENNReal} (hpTop : p ≠ ⊤) (hpZero : p ≠ 0)
    (hdLp : MemLp d p
      ((_root_.GD.N0232.N0720.N1080.d014172 m n).map
        (_root_.GD.N0232.N0720.N1484.d015094 m n
          (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301))))
    (hregular :
      ((_root_.GD.N0232.N0720.N1080.d014172 m n).map
        (_root_.GD.N0232.N0720.N1484.d015094 m n
          (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301))).WeaklyRegular)
    (hsetwiseUpper : ∀ s : Set (_root_.GD.N0232.N0720.N1080.d014170 m n), MeasurableSet s →
      ∀ δ : ℝ, 0 < δ →
        ∀ᶠ j in atTop,
          (_root_.GD.N0232.N0720.N1080.d014172 m n).real
              (_root_.GD.N0232.N0720.N1484.d015094 m n (gSeq j) ⁻¹' s) <
            (_root_.GD.N0232.N0720.N1080.d014172 m n).real
              (_root_.GD.N0232.N0720.N1484.d015094 m n
                (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) ⁻¹' s) + δ) :
    TendstoInMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun j ↦ _root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) d) atTop
      (_root_.GD.N0232.N0720.N1214.d014261 m n
        (⟨limit.1, limit.2⟩ : _root_.GD.N0232.N0720.N1025.d014301) d) := by
  let gLimit : _root_.GD.N0232.N0720.N1025.d014301 := ⟨limit.1, limit.2⟩
  let nu : Measure (_root_.GD.N0232.N0720.N1080.d014170 m n) :=
    (_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit)
  letI : IsFiniteMeasure nu := by
    dsimp [nu]
    exact Measure.isFiniteMeasure_map _ _
  letI : nu.WeaklyRegular := hregular
  have hlog : Tendsto (fun j ↦ (gSeq j).logScale) atTop
      (nhds limit.2) :=
    (continuous_snd.tendsto limit).comp hcoordinate
  have hscaleTendsto : Tendsto (fun j ↦ (gSeq j).d009239) atTop
      (nhds gLimit.d009239) := by
    have hexp := (Real.continuous_exp.tendsto limit.2).comp hlog
    change Tendsto (fun j ↦ Real.exp (gSeq j).logScale) atTop
      (nhds (Real.exp limit.2)) at hexp
    simpa [gLimit, _root_.GD.N0232.N0719.N0946.d009229.d009239] using hexp
  let B : ℝ := 2 * gLimit.d009239
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos (by norm_num) gLimit.d009240
  have hlimitScaleB : gLimit.d009239 < B := by
    dsimp [B]
    linarith [gLimit.d009240]
  have hscaleBound : ∀ᶠ j in atTop, (gSeq j).d009239 < B :=
    hscaleTendsto.eventually (Iio_mem_nhds hlimitScaleB)
  apply _root_.GD.N0232.N0720.N1484.d015108
    m n gSeq limit hcoordinate d
  intro ε hε δ hδ
  have hεB : 0 < ε / B := div_pos hε hB
  have hδtwo : 0 < δ / 2 := by positivity
  obtain ⟨h, hh, hsmall⟩ :=
    _root_.GD.N0230.N0588.d000066
      nu hpTop hpZero d hdLp (ε / B) (δ / 2) hεB hδtwo
  let s : Set (_root_.GD.N0232.N0720.N1080.d014170 m n) :=
    {y | ε / B ≤ dist (d y) (h y)}
  have hs : MeasurableSet s := by
    exact measurableSet_le measurable_const (hdMeasurable.dist hh.measurable)
  have hmapReal :
      nu.real s =
        (_root_.GD.N0232.N0720.N1080.d014172 m n).real
          (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit ⁻¹' s) := by
    dsimp [nu]
    change
      (((_root_.GD.N0232.N0720.N1080.d014172 m n).map (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit)) s).toReal =
        ((_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit ⁻¹' s)).toReal
    rw [Measure.map_apply (_root_.GD.N0232.N0720.N1484.d015095 m n gLimit) hs]
  have hsmallLimit :
      (_root_.GD.N0232.N0720.N1080.d014172 m n).real
          (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit ⁻¹' s) < δ / 2 := by
    rw [← hmapReal]
    exact hsmall
  have hupper := hsetwiseUpper s hs (δ / 2) hδtwo
  refine ⟨h, hh, ?_, ?_⟩
  · filter_upwards [hscaleBound, hupper] with j hjScale hjUpper
    have hsubset :
        {omega |
          ε ≤ dist
            (_root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) d omega)
            (_root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) h omega)} ⊆
          _root_.GD.N0232.N0720.N1484.d015094 m n (gSeq j) ⁻¹' s := by
      intro omega homega
      change ε ≤ dist
        (_root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) d omega)
        (_root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) h omega) at homega
      rw [_root_.GD.N0232.N0720.N1484.d015107 m n (gSeq j) d h omega] at homega
      change ε / B ≤ dist
        (d (_root_.GD.N0232.N0720.N1484.d015094 m n (gSeq j) omega))
        (h (_root_.GD.N0232.N0720.N1484.d015094 m n (gSeq j) omega))
      apply (div_le_iff₀ hB).2
      calc
        ε ≤ (gSeq j).d009239 *
            dist (d (_root_.GD.N0232.N0720.N1484.d015094 m n (gSeq j) omega))
              (h (_root_.GD.N0232.N0720.N1484.d015094 m n (gSeq j) omega)) := homega
        _ ≤ B * dist (d (_root_.GD.N0232.N0720.N1484.d015094 m n (gSeq j) omega))
              (h (_root_.GD.N0232.N0720.N1484.d015094 m n (gSeq j) omega)) :=
          mul_le_mul_of_nonneg_right (le_of_lt hjScale) dist_nonneg
        _ = dist (d (_root_.GD.N0232.N0720.N1484.d015094 m n (gSeq j) omega))
              (h (_root_.GD.N0232.N0720.N1484.d015094 m n (gSeq j) omega)) * B := mul_comm _ _
    have hmeasure := measureReal_mono
      (μ := _root_.GD.N0232.N0720.N1080.d014172 m n) hsubset
    calc
      (_root_.GD.N0232.N0720.N1080.d014172 m n).real
          {omega |
            ε ≤ dist
              (_root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) d omega)
              (_root_.GD.N0232.N0720.N1214.d014261 m n (gSeq j) h omega)} ≤
          (_root_.GD.N0232.N0720.N1080.d014172 m n).real
            (_root_.GD.N0232.N0720.N1484.d015094 m n (gSeq j) ⁻¹' s) := hmeasure
      _ < (_root_.GD.N0232.N0720.N1080.d014172 m n).real
            (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit ⁻¹' s) + δ / 2 := by
        simpa [gLimit] using hjUpper
      _ < δ := by linarith
  · have hsubset :
        {omega |
          ε ≤ dist
            (_root_.GD.N0232.N0720.N1214.d014261 m n gLimit h omega)
            (_root_.GD.N0232.N0720.N1214.d014261 m n gLimit d omega)} ⊆
          _root_.GD.N0232.N0720.N1484.d015094 m n gLimit ⁻¹' s := by
      intro omega homega
      change ε ≤ dist
        (_root_.GD.N0232.N0720.N1214.d014261 m n gLimit h omega)
        (_root_.GD.N0232.N0720.N1214.d014261 m n gLimit d omega) at homega
      rw [dist_comm, _root_.GD.N0232.N0720.N1484.d015107 m n gLimit d h omega] at homega
      change ε / B ≤ dist
        (d (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit omega))
        (h (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit omega))
      apply (div_le_iff₀ hB).2
      calc
        ε ≤ gLimit.d009239 *
            dist (d (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit omega))
              (h (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit omega)) := homega
        _ ≤ B * dist (d (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit omega))
              (h (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit omega)) :=
          mul_le_mul_of_nonneg_right (le_of_lt hlimitScaleB) dist_nonneg
        _ = dist (d (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit omega))
              (h (_root_.GD.N0232.N0720.N1484.d015094 m n gLimit omega)) * B := mul_comm _ _
    exact (measureReal_mono (μ := _root_.GD.N0232.N0720.N1080.d014172 m n) hsubset).trans_lt
      (hsmallLimit.trans (half_lt_self hδ))





theorem d015110
    (q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn) :
    _root_.GD.N0232.N0720.N1068.d015082 m n hm hn q := by
  intro gSeq limit hcoordinate
  let gLimit : _root_.GD.N0232.N0720.N1025.d014301 := ⟨limit.1, limit.2⟩
  apply _root_.GD.N0232.N0720.N1484.d015109
    (p := (2 : ENNReal)) m n gSeq limit hcoordinate
    (_root_.GD.N0232.N0720.N1214.d014265 m n ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1)
    (_root_.GD.N0232.N0720.N1214.d014266 m n
      ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm q).1)
    (by norm_num) (by norm_num)
    (by
      simpa [gLimit] using
        _root_.GD.N0232.N0720.N1484.d015106 m n hm hn q gLimit)
    (by
      rw [_root_.GD.N0232.N0720.N1484.d015101 m n gLimit]
      infer_instance)
  intro s hs δ hδ
  exact _root_.GD.N0232.N0720.N1484.d015105
    m n gSeq limit hcoordinate s hs δ hδ



theorem d015111
    (p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p) :
    _root_.GD.N0232.N0720.N1068.d015085 m n hm hn p q := by
  exact _root_.GD.N0232.N0720.N1068.d015086
    m n hm hn p q hfixed
      (_root_.GD.N0232.N0720.N1484.d015110 m n hm hn q)



theorem d015112
    {p q : _root_.GD.N0232.N0720.N1073.d015042 m n hm hn}
    (packet : _root_.GD.N0232.N0720.N1073.d015045 m n hm hn p q)
    (hfixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1025.d014305 m n) q.1 p.1) :
    q = p ∨ Nonempty
      (_root_.GD.N0232.N0720.N1068.d015087 m n hm hn packet) := by
  exact _root_.GD.N0232.N0720.N1068.d015091
    m n hm hn packet hfixed hdom
      (_root_.GD.N0232.N0720.N1484.d015111 m n hm hn p q hfixed)

end

end N1484
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1484.d015105
#print axioms _root_.GD.N0232.N0720.N1484.d015106
#print axioms _root_.GD.N0232.N0720.N1484.d015110
#print axioms _root_.GD.N0232.N0720.N1484.d015112
