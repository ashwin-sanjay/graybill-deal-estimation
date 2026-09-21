import GD.Module0954
import GD.Module1040
import GD.Module1046
import GD.Module1109
import Mathlib.Tactic


















open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1450

noncomputable section

open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1081
open _root_.GD.N0232.N0720.N1090
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1199
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1478
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0238.N0749

variable {Xi : Type*} [TopologicalSpace Xi] [MeasurableSpace Xi]
variable [OpensMeasurableSpace Xi]









def d017824
    (prior : ℕ → Measure Xi) (rho : ℕ → ℝ) : Prop :=
  ∀ xi U, U ∈ nhds xi →
    ∃ c : ℝ, 0 < c ∧
      ∃ N : ℕ, ∀ k, N ≤ k →
        c * rho k ≤ (prior k U).toReal

omit [OpensMeasurableSpace Xi] in


theorem d017825
    (prior : ℕ → Measure Xi)
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior) :
    _root_.GD.N0232.N0720.N1450.d017824 prior (fun _ ↦ 1) := by
  intro xi U hU
  obtain ⟨c, hc, N, hmass⟩ := hretain xi U hU
  refine ⟨c, hc, N, ?_⟩
  intro k hk
  simpa using hmass k hk



def d017826
    (m n : ℕ) (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (prior : ℕ → Measure Xi) (rho : ℕ → ℝ)
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (lower : ℕ → ℝ) (k : ℕ) : ℝ :=
  (_root_.GD.N0232.N0720.N1111.d016604 m n chart prior k candidate - lower k) / rho k




theorem d017827
    (m n : ℕ)
    (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168) (hchart : Continuous chart)
    (prior : ℕ → Measure Xi)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (rho : ℕ → ℝ)
    (hretain : _root_.GD.N0232.N0720.N1450.d017824 prior rho)
    {candidate e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (he : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e candidate)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) candidate).toReal) (prior k))
    {xi₀ : Xi}
    (hstrict : _root_.GD.N0232.N0720.N1080.d014182 m n (chart xi₀) e <
      _root_.GD.N0232.N0720.N1080.d014182 m n (chart xi₀) candidate) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ N : ℕ, ∀ k, N ≤ k →
        _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k e + epsilon * rho k ≤
          _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k candidate := by
  let candidateRisk : Xi → ℝ :=
    fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) candidate).toReal
  let competitorRisk : Xi → ℝ :=
    fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) e).toReal
  let gap : Xi → ℝ := fun xi ↦ candidateRisk xi - competitorRisk xi
  have heFinite : _root_.GD.N0232.N0720.N1159.d014637 m n e :=
    _root_.GD.N0232.N0720.N1111.d016607
      m n hcandidate he
  have hcandidateContinuous : Continuous candidateRisk :=
    (_root_.GD.N0232.N0720.N1111.d016606
      m n candidate hcandidate).comp hchart
  have heContinuous : Continuous competitorRisk :=
    (_root_.GD.N0232.N0720.N1111.d016606
      m n e heFinite).comp hchart
  have hgapContinuous : Continuous gap :=
    hcandidateContinuous.sub heContinuous
  have hstrictReal : competitorRisk xi₀ < candidateRisk xi₀ := by
    exact
      (ENNReal.toReal_lt_toReal
        (heFinite (chart xi₀)) (hcandidate (chart xi₀))).2 hstrict
  let delta : ℝ := gap xi₀ / 2
  have hdelta : 0 < delta := by
    dsimp [delta, gap]
    linarith
  let U : Set Xi := {xi | delta < gap xi}
  have hUOpen : IsOpen U :=
    isOpen_lt continuous_const hgapContinuous
  have hxi₀U : xi₀ ∈ U := by
    change delta < gap xi₀
    dsimp [delta]
    linarith
  obtain ⟨c, hc, N, hmass⟩ :=
    hretain xi₀ U (hUOpen.mem_nhds hxi₀U)
  refine ⟨delta * c, mul_pos hdelta hc, N, ?_⟩
  intro k hk
  letI : IsFiniteMeasure (prior k) := hpriorFinite k
  have heIntegrable : Integrable competitorRisk (prior k) := by
    simpa only [competitorRisk, candidateRisk] using
      _root_.GD.N0232.N0720.N1111.d016608
        m n chart hchart (prior k) hcandidate he
          (hcandidateIntegrable k)
  have hgapIntegrable : Integrable gap (prior k) :=
    (hcandidateIntegrable k).sub heIntegrable
  have hgapNonneg : ∀ᵐ xi ∂prior k, 0 ≤ gap xi := by
    filter_upwards with xi
    exact sub_nonneg.mpr <|
      (ENNReal.toReal_le_toReal
        (heFinite (chart xi)) (hcandidate (chart xi))).2 (he (chart xi))
  have hmargin : ∀ᵐ xi ∂prior k, xi ∈ U → delta ≤ gap xi := by
    filter_upwards with xi
    intro hxi
    change delta < gap xi at hxi
    exact le_of_lt hxi
  have hpaid :=
    _root_.GD.N0238.N0749.d004829
      (prior k) gap hgapIntegrable U hUOpen.measurableSet delta
      hgapNonneg hmargin
  have hmassk : c * rho k ≤ (prior k U).toReal := hmass k hk
  have hscaled : delta * (c * rho k) ≤ ∫ xi, gap xi ∂prior k :=
    (mul_le_mul_of_nonneg_left hmassk hdelta.le).trans hpaid
  have hgapIntegral :
      (∫ xi, gap xi ∂prior k) =
        _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k candidate -
          _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k e := by
    dsimp [gap, candidateRisk, competitorRisk,
      _root_.GD.N0232.N0720.N1111.d016604]
    rw [integral_sub (hcandidateIntegrable k) heIntegrable]
  rw [hgapIntegral] at hscaled
  nlinarith









theorem d017828
    (m n : ℕ)
    (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (hchartContinuous : Continuous chart)
    (hchartSurjective : Function.Surjective chart)
    (prior : ℕ → Measure Xi)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (rho : ℕ → ℝ) (hrho : ∀ k, 0 < rho k)
    (hretain : _root_.GD.N0232.N0720.N1450.d017824 prior rho)
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) candidate).toReal) (prior k))
    (lower : ℕ → ℝ)
    (hlower : _root_.GD.N0232.N0720.N1111.d016610
      m n chart prior lower)
    (hnotTerminal :
      ¬ _root_.GD.N0232.N0720.N1036.d014669 m n candidate) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ N : ℕ, ∀ k, N ≤ k →
        epsilon ≤ _root_.GD.N0232.N0720.N1450.d017826
          m n chart prior rho candidate lower k := by
  rw [_root_.GD.N0232.N0720.N1036.d014669] at hnotTerminal
  push Not at hnotTerminal
  obtain ⟨e, he, theta, hne⟩ := hnotTerminal
  obtain ⟨xi₀, hxi₀⟩ := hchartSurjective theta
  have hstrict : _root_.GD.N0232.N0720.N1080.d014182 m n (chart xi₀) e <
      _root_.GD.N0232.N0720.N1080.d014182 m n (chart xi₀) candidate := by
    rw [hxi₀]
    exact lt_of_le_of_ne (he theta) hne
  obtain ⟨epsilon, hepsilon, N, hgap⟩ :=
    _root_.GD.N0232.N0720.N1450.d017827
      m n chart hchartContinuous prior hpriorFinite rho hretain
      hcandidate he hcandidateIntegrable hstrict
  refine ⟨epsilon, hepsilon, N, ?_⟩
  intro k hk
  have heFinite : _root_.GD.N0232.N0720.N1159.d014637 m n e :=
    _root_.GD.N0232.N0720.N1111.d016607
      m n hcandidate he
  have heIntegrable : Integrable
      (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) e).toReal) (prior k) :=
    _root_.GD.N0232.N0720.N1111.d016608
      m n chart hchartContinuous (prior k) hcandidate he
        (hcandidateIntegrable k)
  have hminimum := hlower k e heFinite heIntegrable
  have hgapk := hgap k hk
  unfold _root_.GD.N0232.N0720.N1450.d017826
  apply (le_div_iff₀ (hrho k)).2
  linarith





theorem d017829
    (m n : ℕ)
    (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (hchartContinuous : Continuous chart)
    (hchartSurjective : Function.Surjective chart)
    (prior : ℕ → Measure Xi)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (rho : ℕ → ℝ) (hrho : ∀ k, 0 < rho k)
    (hretain : _root_.GD.N0232.N0720.N1450.d017824 prior rho)
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) candidate).toReal) (prior k))
    (lower : ℕ → ℝ)
    (hlower : _root_.GD.N0232.N0720.N1111.d016610
      m n chart prior lower)
    (hratio : Tendsto
      (_root_.GD.N0232.N0720.N1450.d017826
        m n chart prior rho candidate lower) atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1036.d014669 m n candidate := by
  by_contra hnot
  obtain ⟨epsilon, hepsilon, N, hfloor⟩ :=
    _root_.GD.N0232.N0720.N1450.d017828
      m n chart hchartContinuous hchartSurjective prior hpriorFinite
      rho hrho hretain candidate hcandidate hcandidateIntegrable
      lower hlower hnot
  have heventually : ∀ᶠ k in atTop,
      epsilon ≤ _root_.GD.N0232.N0720.N1450.d017826
        m n chart prior rho candidate lower k :=
    Filter.eventually_atTop.2 ⟨N, hfloor⟩
  have hepsilonNonpos : epsilon ≤ 0 :=
    ge_of_tendsto hratio heventually
  exact (not_le_of_gt hepsilon) hepsilonNonpos



variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)


noncomputable def d017830 : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn :=
  (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm
    (_root_.GD.N0232.N0720.N1090.d014984 m n hm hn)


noncomputable def d017831 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  (_root_.GD.N0232.N0720.N1450.d017830 m n hm hn).1

theorem d017832
    (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
        (_root_.GD.N0232.N0720.N1450.d017830 m n hm hn) =
      _root_.GD.N0232.N0720.N1450.d017830 m n hm hn := by
  exact _root_.GD.N0232.N0720.N1025.d014318
    m n hm hn (_root_.GD.N0232.N0720.N1090.d014984 m n hm hn)
      (_root_.GD.N0232.N0720.N1090.d014986 m n hm hn) g



theorem d017833 :
    _root_.GD.N0232.N0720.N1081.d014624 m n hm hn
      (_root_.GD.N0232.N0720.N1450.d017830 m n hm hn) := by
  exact (_root_.GD.N0232.N0720.N1081.d014627
    m n hm hn (_root_.GD.N0232.N0720.N1450.d017830 m n hm hn)).1
      (_root_.GD.N0232.N0720.N1450.d017832 m n hm hn)



noncomputable def d017834 : _root_.GD.N0232.N0720.N1159.d014639 m n where
  value := _root_.GD.N0232.N0720.N1450.d017831 m n hm hn
  finiteRisk := _root_.GD.N0232.N0720.N1199.d016695
    m n hm hn _ (_root_.GD.N0232.N0720.N1450.d017830 m n hm hn).2
  riskCharacter := by
    apply _root_.GD.N0232.N0720.N1159.d014653
      m n
    exact
      _root_.GD.N0232.N0720.N1450.d017833
        m n hm hn

@[simp] theorem d017835 :
    (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn).value =
      _root_.GD.N0232.N0720.N1450.d017831 m n hm hn := rfl



theorem d017836 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn).value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  intro theta
  exact lt_of_le_of_lt
    ((_root_.GD.N0232.N0720.N1450.d017830 m n hm hn).2 theta)
    (_root_.GD.N0232.N0720.N1080.d014186 m n hm hn theta)




theorem d017837
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 m n
      (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn)) :
    _root_.GD.N0232.N0720.N1090.d014987 m n hm hn = 0 := by
  apply (_root_.GD.N0232.N0720.N1090.d014989 m n hm hn).2
  apply (_root_.GD.N0232.N0720.N1025.d014315
    m n (_root_.GD.N0232.N0720.N1090.d014984 m n hm hn).1).2
  simpa [_root_.GD.N0232.N0720.N1450.d017831, _root_.GD.N0232.N0720.N1450.d017830] using
    (_root_.GD.N0232.N0720.N1478.d017820
      m n hterminal)



theorem d017838
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 m n
      (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1036.d014672
    m n hm hn (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn)
      (_root_.GD.N0232.N0720.N1450.d017836 m n hm hn)
  simpa using hterminal



variable {m n}



theorem d017839
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (hchartContinuous : Continuous chart)
    (hchartSurjective : Function.Surjective chart)
    (prior : ℕ → Measure Xi)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (rho : ℕ → ℝ) (hrho : ∀ k, 0 < rho k)
    (hretain : _root_.GD.N0232.N0720.N1450.d017824 prior rho)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun xi ↦
        (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn)).toReal)
      (prior k))
    (lower : ℕ → ℝ)
    (hlower : _root_.GD.N0232.N0720.N1111.d016610
      m n chart prior lower)
    (hratio : Tendsto
      (_root_.GD.N0232.N0720.N1450.d017826 m n chart prior rho
        (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn) lower) atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1036.d014669 m n
      (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn) := by
  apply _root_.GD.N0232.N0720.N1450.d017829
    m n chart hchartContinuous hchartSurjective prior hpriorFinite
      rho hrho hretain (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn)
  · exact (_root_.GD.N0232.N0720.N1450.d017834 m n hm hn).finiteRisk
  · exact hcandidateIntegrable
  · exact hlower
  · exact hratio


theorem d017840
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (hchartContinuous : Continuous chart)
    (hchartSurjective : Function.Surjective chart)
    (prior : ℕ → Measure Xi)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (rho : ℕ → ℝ) (hrho : ∀ k, 0 < rho k)
    (hretain : _root_.GD.N0232.N0720.N1450.d017824 prior rho)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun xi ↦
        (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn)).toReal)
      (prior k))
    (lower : ℕ → ℝ)
    (hlower : _root_.GD.N0232.N0720.N1111.d016610
      m n chart prior lower)
    (hratio : Tendsto
      (_root_.GD.N0232.N0720.N1450.d017826 m n chart prior rho
        (_root_.GD.N0232.N0720.N1450.d017831 m n hm hn) lower) atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1450.d017838
    m n hm hn
  exact _root_.GD.N0232.N0720.N1450.d017839
    hm hn chart hchartContinuous hchartSurjective prior hpriorFinite
      rho hrho hretain hcandidateIntegrable lower hlower hratio

end

end N1450
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1450.d017827
#print axioms _root_.GD.N0232.N0720.N1450.d017828
#print axioms _root_.GD.N0232.N0720.N1450.d017829
#print axioms _root_.GD.N0232.N0720.N1450.d017837
#print axioms _root_.GD.N0232.N0720.N1450.d017840
