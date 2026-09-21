import GD.Module1027
import GD.Module0928
import GD.Module0924
















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1078

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

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



def d016372 (mu sigma tau : ℝ)
    (hsigma : 0 < sigma) (htau : 0 < tau) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := mu
  scale₁ := sigma
  scale₂ := tau
  scale₁_pos := hsigma
  scale₂_pos := htau

@[simp] theorem d016373
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau).location = mu := rfl

@[simp] theorem d016374
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau).scale₁ = sigma := rfl

@[simp] theorem d016375
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau).scale₂ = tau := rfl



theorem d016376
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hfinite : _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≠ ⊤) :
    Integrable (fun omega ↦ (d omega - theta.location) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  have hmeas : AEMeasurable
      (fun omega ↦ ENNReal.ofReal ((d omega - theta.location) ^ 2))
      (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    _root_.GD.N0230.N0602.d000119
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
      theta.location d
  have hlin :
      (∫⁻ omega, ENNReal.ofReal ((d omega - theta.location) ^ 2)
        ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) ≠ ⊤ := by
    simpa only [_root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000117] using hfinite
  have hint := integrable_toReal_of_lintegral_ne_top hmeas hlin
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint

include hm hn



theorem d016377
    (sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1075.d014487 m n
        (_root_.GD.N0232.N0720.N1078.d016372 0 sigma tau hsigma htau) =
      _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau /
        (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn
          (_root_.GD.N0232.N0720.N1078.d016372 0 sigma tau hsigma htau)).toReal := by
  let theta := _root_.GD.N0232.N0720.N1078.d016372 0 sigma tau hsigma htau
  have hcap := _root_.GD.N0232.N0720.N1071.d014427
    m n hm hn theta
  have hSigma : 0 < _root_.GD.N0107.d009045
      m n sigma tau :=
    _root_.GD.N0107.d009049
      (by omega) (by omega) hsigma htau
  have hp0 : 0 < _root_.GD.N0232.N0720.N1069.d014352 m n theta :=
    _root_.GD.N0232.N0720.N1069.d014353 m n hm hn theta
  have hp1 : _root_.GD.N0232.N0720.N1069.d014352 m n theta < 1 :=
    _root_.GD.N0232.N0720.N1069.d014354 m n hm hn theta
  have htotal : 0 < _root_.GD.N0232.N0720.N1442.d013867
      (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n)
      (_root_.GD.N0232.N0720.N1069.d014352 m n theta) :=
    _root_.GD.N0232.N0720.N1442.d013871 hp0 hp1
  dsimp only [theta] at hcap hp0 hp1 htotal
  unfold _root_.GD.N0232.N0720.N1075.d014487 _root_.GD.N0232.N0720.N1442.d013869
    _root_.GD.N0232.N0720.N1442.d013866 _root_.GD.N0232.N0720.N1502.d016364
  simp only [_root_.GD.N0232.N0720.N1078.d016374, _root_.GD.N0232.N0720.N1078.d016375] at hcap ⊢
  rw [hcap]
  unfold _root_.GD.N0232.N0720.N1069.d014352 _root_.GD.N0232.N0720.N1067.d014408
  simp only [_root_.GD.N0232.N0720.N1078.d016374, _root_.GD.N0232.N0720.N1078.d016375]
  field_simp [hSigma.ne', htotal.ne']



theorem d016378
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn
        (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau)).toReal =
      (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn
        (_root_.GD.N0232.N0720.N1078.d016372 0 sigma tau hsigma htau)).toReal := by
  rw [_root_.GD.N0232.N0720.N1071.d014427
      m n hm hn,
    _root_.GD.N0232.N0720.N1071.d014427
      m n hm hn]
  rfl




theorem d016379
    (sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
    (d : _root_.GD.N0232.N0720.N1025.d014303 m n)
    (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1075.d014487 m n
        (_root_.GD.N0232.N0720.N1078.d016372 0 sigma tau hsigma htau) ≤
      ⨆ mu : ℝ,
        _root_.GD.N0232.N0720.N1066.d014327 m n hm hn
          (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) d := by
  let p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm d
  let pSummary := _root_.GD.N0232.N0720.N1501.d016291 m n p
  obtain ⟨g, hgmem, hg, hgae, hgclass⟩ :=
    _root_.GD.N0232.N0720.N1501.d016307 m n p
  let v := _root_.GD.N0232.N0720.N1502.d016364 m n sigma tau
  let cap : ℝ := (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn
    (_root_.GD.N0232.N0720.N1078.d016372 0 sigma tau hsigma htau)).toReal
  let profile : ℝ → ℝ := fun mu ↦
    _root_.GD.N0232.N0720.N1066.d014327 m n hm hn
      (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) d
  have hv : 0 < v :=
    _root_.GD.N0232.N0720.N1502.d016365 m n hm hn hsigma htau
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hcap : 0 < cap := by
    unfold cap
    exact ENNReal.toReal_pos
      (_root_.GD.N0232.N0720.N1066.d014322 m n hm hn _)
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn _)
  have hpLower : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn := by
    exact (_root_.GD.N0232.N0720.N1025.d014306 m n hm hn d).1 hd
  have hpLeCap : ∀ mu : ℝ,
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) p ≤
        _root_.GD.N0232.N0720.N1066.d014320 m n hm hn
          (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) := by
    intro mu
    exact (hpLower (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau)).trans
      (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn
        (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau)).le
  have hpFinite : ∀ mu : ℝ,
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) p ≠ ⊤ := by
    intro mu
    exact ne_top_of_le_ne_top
      (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn _) (hpLeCap mu)
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
        _ ≤ (_root_.GD.N0232.N0720.N1066.d014320 m n hm hn
            (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau)).toReal :=
          ENNReal.toReal_mono
            (_root_.GD.N0232.N0720.N1066.d014323 m n hm hn _)
            (hpLeCap mu)
        _ = cap := by
          exact _root_.GD.N0232.N0720.N1078.d016378
            m n hm hn mu sigma tau hsigma htau
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
  have hprofileBounded : BddAbove (Set.range profile) := by
    refine ⟨1, ?_⟩
    rintro y ⟨mu, rfl⟩
    exact _root_.GD.N0232.N0720.N1066.d014329 m n hm hn _ d
  have hprofileEq : ∀ mu : ℝ,
      (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) p).toReal =
        cap * profile mu := by
    intro mu
    have hcapEq := _root_.GD.N0232.N0720.N1078.d016378
      m n hm hn mu sigma tau hsigma htau
    simp only [profile, _root_.GD.N0232.N0720.N1066.d014327, hd, dite_true,
      _root_.GD.N0232.N0720.N1066.d014324, _root_.GD.N0232.N0720.N1025.d014305, p, ENNReal.toReal_div]
    rw [hcapEq]
    change (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm d)).toReal =
      cap * ((_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau)
        ((toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm d)).toReal / cap)
    field_simp [hcap.ne']
  have hsummaryUpper :
      (⨆ mu : ℝ,
        _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ g (_root_.GD.N0232.N0720.N1467.d012542 m n omega) - mu)) ≤
        cap * (⨆ mu : ℝ, profile mu) := by
    apply ciSup_le
    intro mu
    calc
      _ ≤ (_root_.GD.N0232.N0720.N1080.d014182 m n
          (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) p).toReal :=
        hsummaryLeRaw mu
      _ = cap * profile mu := hprofileEq mu
      _ ≤ cap * (⨆ lambda : ℝ, profile lambda) :=
        mul_le_mul_of_nonneg_left
          (le_ciSup hprofileBounded mu) hcap.le
  have hvUpper : v ≤ cap * (⨆ mu : ℝ, profile mu) :=
    hsummaryMinimax.trans hsummaryUpper
  rw [_root_.GD.N0232.N0720.N1078.d016377
    m n hm hn sigma tau hsigma htau]
  change v / cap ≤ ⨆ mu : ℝ, profile mu
  exact (div_le_iff₀ hcap).2 (by simpa only [mul_comm] using hvUpper)


def d016380 : Prop :=
  ∀ (sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau)
      (d : _root_.GD.N0232.N0720.N1025.d014303 m n),
    d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn →
    _root_.GD.N0232.N0720.N1075.d014487 m n
        (_root_.GD.N0232.N0720.N1078.d016372 0 sigma tau hsigma htau) ≤
      ⨆ mu : ℝ,
        _root_.GD.N0232.N0720.N1066.d014327 m n hm hn
          (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) d



theorem d016381 :
    _root_.GD.N0232.N0720.N1078.d016380 m n hm hn := by
  intro sigma tau hsigma htau d hd
  exact _root_.GD.N0232.N0720.N1078.d016379
    m n hm hn sigma tau hsigma htau d hd

end

end N1078
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1078.d016379
#print axioms _root_.GD.N0232.N0720.N1078.d016381
