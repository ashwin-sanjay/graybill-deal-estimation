import GD.Module1029
import GD.Module0981









set_option autoImplicit false
set_option warningAsError true

open Filter MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0720.N1228
noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1069
open _root_.GD.N0232.N0720.N1071
open _root_.GD.N0232.N0720.N1075
open _root_.GD.N0232.N0720.N1433
open _root_.GD.N0232.N0720.N1442
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1501
open _root_.GD.N0232.N0720.N1502
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0633


open _root_.GD.N0232.N0720.N1078 _root_.GD.N0232.N0720.N1074
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0230.N0611

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn



theorem d016741
    (sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (cap : ℝ) (hcap : 0 ≤ cap)
    (hpLeCap : ∀ mu : ℝ,
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) p ≤
        ENNReal.ofReal cap) :
    _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau ≤ cap := by
  let pSummary := _root_.GD.N0232.N0720.N1501.d016291 m n p
  obtain ⟨g, hgmem, hg, hgae, hgclass⟩ :=
    _root_.GD.N0232.N0720.N1501.d016307 m n p
  let v := _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau
  have hv : 0 < v :=
    _root_.GD.N0232.N0720.N1502.d016365 m n hm hn hsigma htau
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hpFinite : ∀ mu : ℝ,
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) p ≠ ⊤ := by
    intro mu
    exact ne_top_of_le_ne_top
      ENNReal.ofReal_ne_top (hpLeCap mu)
  have hsummaryLe : ∀ mu : ℝ,
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) pSummary ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) p := by
    intro mu
    exact _root_.GD.N0232.N0720.N1501.d016299 m n hm hn
      (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) p
  have hsummaryFinite : ∀ mu : ℝ,
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau)
        pSummary ≠ ⊤ := by
    intro mu
    exact ne_top_of_le_ne_top (hpFinite mu) (hsummaryLe mu)
  have hint : ∀ mu : ℝ,
      Integrable (fun omega : _root_.GD.N0137.d008894 m ×
          _root_.GD.N0137.d008894 n ↦
        (g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) ^ 2)
      (_root_.GD.N0107.d009030 m n mu sigma tau) := by
    intro mu
    let theta := _root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau
    have hpInt := _root_.GD.N0232.N0720.N1078.d016376
      m n theta pSummary (hsummaryFinite mu)
    have haePhysical :
        (fun omega ↦ pSummary omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
          g ∘ _root_.GD.N0232.N0720.N1467.d012542 m n :=
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq
        (by simpa only [pSummary] using hgae)
    have hpInt' : Integrable
        (fun omega ↦ (g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) ^ 2)
        (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
      refine hpInt.congr <| haePhysical.mono fun omega homega ↦ ?_
      have hvalue : pSummary omega =
          g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) := by
        simpa only [Function.comp_apply] using homega
      simpa only [theta, _root_.GD.N0232.N0720.N1078.d016373] using
        congrArg (fun x : ℝ ↦ (x - mu) ^ 2) hvalue
    simpa only [_root_.GD.N0232.N0720.N1080.d014171, theta, _root_.GD.N0232.N0720.N1078.d016373,
      _root_.GD.N0232.N0720.N1078.d016374, _root_.GD.N0232.N0720.N1078.d016375] using hpInt'
  have hsummaryRiskEq : ∀ mu : ℝ,
      _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) =
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau)
          pSummary).toReal := by
    intro mu
    let theta := _root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau
    have herrorMeas : AEStronglyMeasurable
        (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu)
        (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
      ((hg.comp (_root_.GD.N0232.N0720.N1501.d016289 m n)).sub
        measurable_const).aestronglyMeasurable
    have hgmu : MemLp
        (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) 2
        (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
      (memLp_two_iff_integrable_sq herrorMeas).2 (by
        simpa only [_root_.GD.N0232.N0720.N1080.d014171, theta, _root_.GD.N0232.N0720.N1078.d016373,
          _root_.GD.N0232.N0720.N1078.d016374, _root_.GD.N0232.N0720.N1078.d016375] using
            hint mu)
    have hrisk : _root_.GD.N0232.N0720.N1080.d014182 m n theta pSummary = ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu)) := by
      dsimp only [pSummary]
      rw [← hgclass]
      exact _root_.GD.N0232.N0720.N1080.d014183
        m n (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
        mu (g ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) hgmem hgmu
    have hnonneg : 0 ≤ _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) := by
      unfold _root_.GD.N0141.d006684
      exact integral_nonneg fun _ ↦ sq_nonneg _
    rw [hrisk, ENNReal.toReal_ofReal hnonneg]
    rfl
  have hsummaryLeRaw : ∀ mu : ℝ,
      _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) ≤
        (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) p).toReal := by
    intro mu
    rw [hsummaryRiskEq mu]
    exact ENNReal.toReal_mono (hpFinite mu) (hsummaryLe mu)
  have hancillaryBounded : BddAbove (Set.range
      (_root_.GD.N0232.N0720.N1040.d008975
        (_root_.GD.N0232.N0720.N1502.d016357 m n (_root_.GD.N0107.d009046
          m n sigma tau))
        (_root_.GD.N0232.N0720.N1502.d016366 m n sigma tau g))) := by
    refine ⟨cap / v, ?_⟩
    rintro y ⟨lambda, rfl⟩
    let mu := Real.sqrt v * lambda
    have heq := _root_.GD.N0232.N0720.N1502.d016370
      m n hm hn sigma tau hsigma htau g hg mu (hint mu)
    have hle : _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) ≤ cap := by
      calc
        _ ≤ (_root_.GD.N0232.N0720.N1080.d014182 m n
            (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) p).toReal :=
          hsummaryLeRaw mu
        _ ≤ cap := ENNReal.toReal_le_of_le_ofReal hcap (hpLeCap mu)
    rw [heq] at hle
    have hquot :
        mu / Real.sqrt (_root_.GD.N0232.N0720.N1502.d016364 m n sigma tau) =
          lambda := by
      dsimp only [mu]
      change (Real.sqrt v * lambda) / Real.sqrt v = lambda
      field_simp [hsv.ne']
    exact (le_div_iff₀ hv).2 (by
      simpa only [v, hquot, mul_comm] using hle)
  have hsummaryMinimax : v ≤
      ⨆ mu : ℝ,
        _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu) := by
    exact _root_.GD.N0232.N0720.N1502.d016371
      m n hm hn sigma tau hsigma htau g hg hint hancillaryBounded
  exact hsummaryMinimax.trans (ciSup_le fun mu =>
    (hsummaryLeRaw mu).trans (ENNReal.toReal_le_of_le_ofReal hcap (hpLeCap mu)))




theorem d016742
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≤
      ENNReal.ofReal (c * (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal))
    (sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1075.d014487 m n
      (_root_.GD.N0232.N0720.N1078.d016372 0 sigma tau hsigma htau) ≤ c := by
  let beta := (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn
    (_root_.GD.N0232.N0720.N1078.d016372 0 sigma tau hsigma htau)).toReal
  have hbeta : 0 < beta := ENNReal.toReal_pos
    (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn _)
    (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn _)
  have hv := _root_.GD.N0232.N0720.N1228.d016741 m n hm hn
    sigma tau hsigma htau p (c * beta) (mul_nonneg hc hbeta.le) (fun mu => by
      simpa only [_root_.GD.N0232.N0720.N1078.d016378 m n hm hn, beta] using
        hb (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau))
  rw [_root_.GD.N0232.N0720.N1078.d016377 m n hm hn]
  exact (div_le_iff₀ hbeta).2 hv



theorem d016743
    (hdesign : 4 ≤ m ∨ 4 ≤ n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≤
      ENNReal.ofReal (c * (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal)) :
    1 ≤ c := by
  rcases hdesign with hm4 | hn4
  · apply le_of_tendsto (_root_.GD.N0232.N0720.N1074.d016393 m n hm hn hm4)
    exact Filter.Eventually.of_forall fun j =>
      _root_.GD.N0232.N0720.N1228.d016742 m n hm hn p c hc hb
        (_root_.GD.N0232.N0720.N1074.d016387 m j) (_root_.GD.N0232.N0720.N1074.d016388 n j)
        (_root_.GD.N0232.N0720.N1074.d016389 m hm j) (_root_.GD.N0232.N0720.N1074.d016390 n hn j)
  · apply le_of_tendsto (_root_.GD.N0232.N0720.N1074.d016401 m n hm hn hn4)
    exact Filter.Eventually.of_forall fun j =>
      _root_.GD.N0232.N0720.N1228.d016742 m n hm hn p c hc hb
        (_root_.GD.N0232.N0720.N1074.d016395 m j) (_root_.GD.N0232.N0720.N1074.d016396 n j)
        (_root_.GD.N0232.N0720.N1074.d016397 m hm j) (_root_.GD.N0232.N0720.N1074.d016398 n hn j)


def d016744 (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0232.N0720.N1080.d014197 m n theta d / _root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta

def d016745 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn) d

theorem d016746
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    _root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d ≤ ENNReal.ofReal c ↔
    _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (c * (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal) := by
  unfold _root_.GD.N0232.N0720.N1228.d016744
  rw [ENNReal.div_le_iff (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn theta)
    (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn theta), ENNReal.ofReal_mul hc,
    ENNReal.ofReal_toReal (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn theta)]



theorem d016747
    (hdesign : 4 ≤ m ∨ 4 ≤ n)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d) :
    1 ≤ _root_.GD.N0232.N0720.N1228.d016745 m n hm hn d := by
  by_contra h
  have hlt : _root_.GD.N0232.N0720.N1228.d016745 m n hm hn d < 1 := lt_of_not_ge h
  have htop : _root_.GD.N0232.N0720.N1228.d016745 m n hm hn d ≠ ⊤ :=
    ne_top_of_lt hlt
  let c := (_root_.GD.N0232.N0720.N1228.d016745 m n hm hn d).toReal
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hc1 : c < 1 := by
    have h' := (ENNReal.toReal_lt_toReal htop (by simp : (1 : ℝ≥0∞) ≠ ⊤)).2 hlt
    simpa only [ENNReal.toReal_one, c] using h'
  have hb : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (c * (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal) := by
    intro theta
    apply (_root_.GD.N0232.N0720.N1228.d016746 m n hm hn theta d c hc).1
    rw [ENNReal.ofReal_toReal htop]
    exact le_iSup (fun theta => _root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d) theta
  have hmem := _root_.GD.N0232.N0720.N1215.d014285
    m n d hd (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb _root_.GD.N0232.N0720.N1080.d014169))
  have hcge := _root_.GD.N0232.N0720.N1228.d016743 m n hm hn hdesign
    (hmem.toLp d) c hc (fun theta => by
      rw [← _root_.GD.N0232.N0720.N1080.d014198 m n theta d hmem]
      exact hb theta)
  linarith



theorem d016748
    (hdesign : 4 ≤ m ∨ 4 ≤ n) :
    _root_.GD.N0232.N0720.N1228.d016745 m n hm hn (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) = 1 := by
  have hlegal := _root_.GD.N0232.N0720.N1221.d015562
    m n hm hn
  apply le_antisymm _ (_root_.GD.N0232.N0720.N1228.d016747 m n hm hn hdesign _ hlegal.1.1)
  apply iSup_le
  intro theta
  unfold _root_.GD.N0232.N0720.N1228.d016744
  rw [ENNReal.div_le_iff (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn theta)
    (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn theta), one_mul]
  have hmem : MemLp (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
      _root_.GD.N0232.N0720.N1080.d014179 m n hm hn _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014198 m n theta _ hmem]
  exact (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn theta).le



theorem d016749
    (hdesign : 4 ≤ m ∨ 4 ≤ n) (C : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ))
    (hC : ∀ d ∈ C, Measurable d) (hseed : _root_.GD.N0232.N0720.N1080.d014176 m n hm hn ∈ C) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn) C = 1 := by
  apply le_antisymm
  · exact (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn) hseed).trans
      (le_of_eq (_root_.GD.N0232.N0720.N1228.d016748 m n hm hn hdesign))
  · exact le_iInf fun d => le_iInf fun hd =>
      _root_.GD.N0232.N0720.N1228.d016747 m n hm hn hdesign d (hC d hd)



theorem d016750
    (hdesign : 4 ≤ m ∨ 4 ≤ n) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn) (_root_.GD.N0232.N0720.N1256.d015551 m n) = 1 ∧
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn) (_root_.GD.N0232.N0720.N1256.d015552 m n) = 1 := by
  have hs := _root_.GD.N0232.N0720.N1221.d015562
    m n hm hn
  exact ⟨_root_.GD.N0232.N0720.N1228.d016749 m n hm hn hdesign _ (fun _ h => h.1) ⟨hs.1.1, hs.2⟩,
    _root_.GD.N0232.N0720.N1228.d016749 m n hm hn hdesign _ (fun _ h => h.1.1) hs⟩



theorem d016751
    (hdesign : 4 ≤ m ∨ 4 ≤ n) :
    ¬ ∃ (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ), Measurable d ∧
      ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ theta,
        _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
          ENNReal.ofReal (c * (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal) := by
  rintro ⟨d, hd, c, hc, hc1, hb⟩
  have hlow := _root_.GD.N0232.N0720.N1228.d016747 m n hm hn hdesign d hd
  have hupper : _root_.GD.N0232.N0720.N1228.d016745 m n hm hn d ≤ ENNReal.ofReal c :=
    iSup_le fun theta => (_root_.GD.N0232.N0720.N1228.d016746 m n hm hn theta d c hc).2 (hb theta)
  have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal c := hlow.trans hupper
  have : (1 : ℝ) ≤ c := ENNReal.one_le_ofReal.1 this
  linarith




def d016752 (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : EReal :=
  ⨅ theta, (1 : EReal) - (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d : EReal)

def d016753 (C : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)) : EReal :=
  ⨆ d ∈ C, _root_.GD.N0232.N0720.N1228.d016752 m n hm hn d



theorem d016754
    (hdesign : 4 ≤ m ∨ 4 ≤ n)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n) :
    _root_.GD.N0232.N0720.N1228.d016752 m n hm hn d ≤ 0 := by
  by_contra h
  obtain ⟨epsilon, heps0, heps⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have hepsilon : 0 < epsilon := by exact_mod_cast heps0
  have hpoint : ∀ theta,
      (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d).toReal ≤ 1 - epsilon := by
    intro theta
    have hrfinite : _root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d ≠ ⊤ :=
      ENNReal.div_ne_top (hd.2 theta) (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn theta)
    have hcoe : (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d : EReal) =
        ((_root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d).toReal : EReal) := by
      calc
        _ = (ENNReal.ofReal (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d).toReal : EReal) :=
          congrArg (fun x : ℝ≥0∞ => (x : EReal)) (ENNReal.ofReal_toReal hrfinite).symm
        _ = _ := by simp only [EReal.coe_ennreal_ofReal,
          max_eq_left ENNReal.toReal_nonneg]
    have hpt := heps.le.trans (iInf_le
      (fun theta => (1 : EReal) - (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d : EReal)) theta)
    rw [hcoe, ← EReal.coe_one, ← EReal.coe_sub] at hpt
    have hptR : epsilon ≤ 1 - (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d).toReal := by
      exact_mod_cast hpt
    linarith
  have hc : 0 ≤ 1 - epsilon :=
    ENNReal.toReal_nonneg.trans (hpoint _root_.GD.N0232.N0720.N1080.d014169)
  apply _root_.GD.N0232.N0720.N1228.d016751 m n hm hn hdesign
  refine ⟨d, hd.1, 1 - epsilon, hc, by linarith, ?_⟩
  intro theta
  apply (_root_.GD.N0232.N0720.N1228.d016746 m n hm hn theta d _ hc).1
  have hrfinite : _root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d ≠ ⊤ :=
    ENNReal.div_ne_top (hd.2 theta) (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn theta)
  rw [← ENNReal.ofReal_toReal hrfinite]
  exact ENNReal.ofReal_le_ofReal (hpoint theta)



theorem d016755
    (hdesign : 4 ≤ m ∨ 4 ≤ n) :
    _root_.GD.N0232.N0720.N1228.d016752 m n hm hn (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) = 0 := by
  have hs := _root_.GD.N0232.N0720.N1221.d015562
    m n hm hn
  apply le_antisymm (_root_.GD.N0232.N0720.N1228.d016754 m n hm hn hdesign _ ⟨hs.1.1, hs.2⟩)
  apply le_iInf
  intro theta
  have hle : _root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) ≤ 1 := by
    exact (le_iSup (fun theta => _root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta
      (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn)) theta).trans
      (le_of_eq (_root_.GD.N0232.N0720.N1228.d016748 m n hm hn hdesign))
  apply (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top 1))
    (Or.inl (EReal.coe_ne_bot 1))).2
  simpa only [EReal.coe_ennreal_one, EReal.coe_one] using
    EReal.coe_ennreal_le_coe_ennreal_iff.2 hle



theorem d016756
    (hdesign : 4 ≤ m ∨ 4 ≤ n) :
    _root_.GD.N0232.N0720.N1228.d016753 m n hm hn (_root_.GD.N0232.N0720.N1256.d015551 m n) = 0 ∧
    _root_.GD.N0232.N0720.N1228.d016753 m n hm hn (_root_.GD.N0232.N0720.N1256.d015552 m n) = 0 := by
  have hs := _root_.GD.N0232.N0720.N1221.d015562
    m n hm hn
  have hzero := _root_.GD.N0232.N0720.N1228.d016755 m n hm hn hdesign
  have hclass : ∀ C : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ),
      (∀ d ∈ C, d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n) →
      _root_.GD.N0232.N0720.N1080.d014176 m n hm hn ∈ C →
      _root_.GD.N0232.N0720.N1228.d016753 m n hm hn C = 0 := by
    intro C hC hseed
    apply le_antisymm
    · exact iSup_le fun d => iSup_le fun hd =>
        _root_.GD.N0232.N0720.N1228.d016754 m n hm hn hdesign d (hC d hd)
    · rw [← hzero]
      exact le_iSup_of_le (_root_.GD.N0232.N0720.N1080.d014176 m n hm hn) (le_iSup_of_le hseed le_rfl)
  exact ⟨hclass _ (fun _ h => h) ⟨hs.1.1, hs.2⟩,
    hclass _ (fun _ h => ⟨h.1.1, h.2⟩) hs⟩



theorem d016757 :
    _root_.GD.N0232.N0720.N1502.d016364 m n 1 1 = ((m : ℝ) + (n : ℝ))⁻¹ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsum : (1 : ℝ) / m + 1 / n ≠ 0 := ne_of_gt (by positivity)
  simp only [_root_.GD.N0232.N0720.N1502.d016364, _root_.GD.N0107.d009045,
    _root_.GD.N0107.d009046, _root_.GD.N0107.d009043,
    _root_.GD.N0107.d009044]
  norm_num
  field_simp [hmR.ne', hnR.ne', hsum, ne_of_gt (add_pos hmR hnR)]
  ring



theorem d016758
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d) :
    1 ≤ _root_.GD.N0232.N0720.N1256.d015548 m n d := by
  by_contra h
  have hlt : _root_.GD.N0232.N0720.N1256.d015548 m n d < 1 := lt_of_not_ge h
  have htop : _root_.GD.N0232.N0720.N1256.d015548 m n d ≠ ⊤ := ne_top_of_lt hlt
  let c := (_root_.GD.N0232.N0720.N1256.d015548 m n d).toReal
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hc1 : c < 1 := by
    simpa only [ENNReal.toReal_one, c] using
      (ENNReal.toReal_lt_toReal htop (by simp : (1 : ℝ≥0∞) ≠ ⊤)).2 hlt
  have hb : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (c * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := by
    intro theta
    apply (_root_.GD.N0232.N0720.N1256.d015553 m n (by omega) c hc theta d).1
    rw [ENNReal.ofReal_toReal htop]
    exact le_iSup (fun theta => _root_.GD.N0232.N0720.N1256.d015547 m n theta d) theta
  have hmem := _root_.GD.N0232.N0720.N1215.d014285
    m n d hd (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb _root_.GD.N0232.N0720.N1080.d014169))
  let v : ℝ := ((m : ℝ) + (n : ℝ))⁻¹
  have hv : 0 < v := by
    dsimp only [v]
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hvbound := _root_.GD.N0232.N0720.N1228.d016741 m n hm hn
    1 1 (by norm_num) (by norm_num) (hmem.toLp d) (c * v) (mul_nonneg hc hv.le)
    (fun mu => by
      rw [← _root_.GD.N0232.N0720.N1080.d014198 m n _ d hmem]
      simpa only [_root_.GD.N0232.N0720.N1257.d015508, _root_.GD.N0232.N0720.N1078.d016372,
        one_pow, div_one, v] using
        hb (_root_.GD.N0232.N0720.N1078.d016372 mu 1 1 (by norm_num) (by norm_num)))
  rw [_root_.GD.N0232.N0720.N1228.d016757 m n hm hn] at hvbound
  have : (1 : ℝ) ≤ c := by
    change v ≤ c * v at hvbound
    nlinarith
  linarith



theorem d016759 :
    1 ≤ _root_.GD.N0232.N0720.N1256.d015549 m n ∧
    1 ≤ _root_.GD.N0232.N0720.N1256.d015550 m n ∧
    1 ≤ _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015551 m n) ∧
    1 ≤ _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) (_root_.GD.N0232.N0720.N1256.d015552 m n) := by
  have hclass : ∀ C : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ), (∀ d ∈ C, Measurable d) →
      1 ≤ _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1256.d015547 m n) C :=
    fun C hC => le_iInf fun d => le_iInf fun hd =>
      _root_.GD.N0232.N0720.N1228.d016758 m n hm hn d (hC d hd)
  exact ⟨hclass _ (fun _ h => h), hclass _ (fun _ h => h.1),
    hclass _ (fun _ h => h.1), hclass _ (fun _ h => h.1.1)⟩




theorem d016760
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≠ ⊤) :
    (1 : EReal) - (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d : EReal) =
      (((_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal - (_root_.GD.N0232.N0720.N1080.d014197 m n theta d).toReal) /
        (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal : ℝ) := by
  have hrfinite : _root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d ≠ ⊤ :=
    ENNReal.div_ne_top hfinite (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn theta)
  have hcoe : (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d : EReal) =
      ((_root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d).toReal : EReal) := by
    calc
      _ = (ENNReal.ofReal (_root_.GD.N0232.N0720.N1228.d016744 m n hm hn theta d).toReal : EReal) :=
        congrArg (fun x : ℝ≥0∞ => (x : EReal)) (ENNReal.ofReal_toReal hrfinite).symm
      _ = _ := by simp only [EReal.coe_ennreal_ofReal,
        max_eq_left ENNReal.toReal_nonneg]
  rw [hcoe, ← EReal.coe_one, ← EReal.coe_sub]
  congr 1
  unfold _root_.GD.N0232.N0720.N1228.d016744
  rw [ENNReal.toReal_div]
  have hbeta : (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn theta).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn theta)
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn theta))
  field_simp [hbeta]

end
end GD.N0232.N0720.N1228

#print axioms _root_.GD.N0232.N0720.N1228.d016741
#print axioms _root_.GD.N0232.N0720.N1228.d016742
#print axioms _root_.GD.N0232.N0720.N1228.d016743
#print axioms _root_.GD.N0232.N0720.N1228.d016747
#print axioms _root_.GD.N0232.N0720.N1228.d016748
#print axioms _root_.GD.N0232.N0720.N1228.d016749
#print axioms _root_.GD.N0232.N0720.N1228.d016750
#print axioms _root_.GD.N0232.N0720.N1228.d016751
#print axioms _root_.GD.N0232.N0720.N1228.d016754
#print axioms _root_.GD.N0232.N0720.N1228.d016755
#print axioms _root_.GD.N0232.N0720.N1228.d016756
#print axioms _root_.GD.N0232.N0720.N1228.d016758
#print axioms _root_.GD.N0232.N0720.N1228.d016759
#print axioms _root_.GD.N0232.N0720.N1228.d016760
