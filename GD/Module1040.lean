import GD.Module0076
import GD.Module0933
import GD.Module1039
import GD.Module0325




















































open Filter MeasureTheory Set Topology
open scoped ENNReal Topology

namespace GD
namespace N0232
namespace N0720
namespace N1111

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1133
open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0606
open _root_.GD.N0238.N0749

variable {Xi : Type*} [TopologicalSpace Xi] [MeasurableSpace Xi]
variable [OpensMeasurableSpace Xi]





def d016604
    (m n : ℕ) (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (prior : ℕ → Measure Xi) (k : ℕ)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  ∫ xi, (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) q).toReal ∂prior k






def d016605
    (prior : ℕ → Measure Xi) : Prop :=
  ∀ xi U, U ∈ nhds xi →
    ∃ a : ℝ, 0 < a ∧
      ∃ N : ℕ, ∀ k, N ≤ k →
        a ≤ (prior k U).toReal




theorem d016606
    (m n : ℕ) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q) :
    Continuous (fun theta : _root_.GD.N0232.N0720.N1080.d014168 ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n theta q).toReal) := by
  apply continuous_iff_continuousAt.2
  intro theta
  exact
    (ENNReal.continuousAt_toReal
      (x := _root_.GD.N0232.N0720.N1080.d014182 m n theta q) (hq theta)).tendsto.comp
        (_root_.GD.N0232.N0720.N1133.d016587 m n q hq).continuousAt



theorem d016607
    (m n : ℕ)
    {candidate e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (he : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e candidate) :
    _root_.GD.N0232.N0720.N1159.d014637 m n e := by
  intro theta
  exact ne_top_of_le_ne_top (hcandidate theta) (he theta)






theorem d016608
    (m n : ℕ)
    (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168) (hchart : Continuous chart)
    (mu : Measure Xi)
    {candidate e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (he : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) e candidate)
    (hcandidateIntegrable : Integrable
      (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) candidate).toReal) mu) :
    Integrable (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) e).toReal) mu := by
  have heFinite : _root_.GD.N0232.N0720.N1159.d014637 m n e :=
    _root_.GD.N0232.N0720.N1111.d016607
      m n hcandidate he
  have heContinuous : Continuous
      (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) e).toReal) :=
    (_root_.GD.N0232.N0720.N1111.d016606
      m n e heFinite).comp hchart
  apply Integrable.mono' hcandidateIntegrable
  · exact heContinuous.aestronglyMeasurable
  · filter_upwards with xi
    have hle :
        (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) e).toReal ≤
          (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) candidate).toReal := by
      exact
        (ENNReal.toReal_le_toReal
          (heFinite (chart xi)) (hcandidate (chart xi))).2 (he (chart xi))
    have hcandidateNonneg :
        0 ≤ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) candidate).toReal :=
      ENNReal.toReal_nonneg
    have heNonneg : 0 ≤ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) e).toReal :=
      ENNReal.toReal_nonneg
    simpa only [Real.norm_eq_abs, abs_of_nonneg hcandidateNonneg,
      abs_of_nonneg heNonneg] using hle







theorem d016609
    (m n : ℕ)
    (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168) (hchart : Continuous chart)
    (prior : ℕ → Measure Xi)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
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
        _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k e + epsilon ≤
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
  have hUOpen : IsOpen U := by
    exact isOpen_lt continuous_const hgapContinuous
  have hxi₀U : xi₀ ∈ U := by
    change delta < gap xi₀
    dsimp [delta]
    linarith
  obtain ⟨a, ha, N, hmass⟩ := hretain xi₀ U (hUOpen.mem_nhds hxi₀U)
  refine ⟨delta * a, mul_pos hdelta ha, N, ?_⟩
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
  have hmassk : a ≤ (prior k U).toReal := hmass k hk
  have hfixed : delta * a ≤ ∫ xi, gap xi ∂prior k :=
    (mul_le_mul_of_nonneg_left hmassk hdelta.le).trans hpaid
  have hgapIntegral :
      (∫ xi, gap xi ∂prior k) =
        _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k candidate -
          _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k e := by
    dsimp [gap, candidateRisk, competitorRisk,
      _root_.GD.N0232.N0720.N1111.d016604]
    rw [integral_sub (hcandidateIntegrable k) heIntegrable]
  rw [hgapIntegral] at hfixed
  linarith










def d016610
    (m n : ℕ) (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (prior : ℕ → Measure Xi) (lower : ℕ → ℝ) : Prop :=
  ∀ k q, _root_.GD.N0232.N0720.N1159.d014637 m n q →
    Integrable (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) q).toReal) (prior k) →
      lower k ≤ _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k q











theorem d016611
    (m n : ℕ)
    (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (hchartContinuous : Continuous chart)
    (hchartSurjective : Function.Surjective chart)
    (prior : ℕ → Measure Xi)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) candidate).toReal) (prior k))
    (lower : ℕ → ℝ)
    (hlower : _root_.GD.N0232.N0720.N1111.d016610
      m n chart prior lower)
    (hdeficitZero : _root_.GD.N0230.N0606.d000961 (fun k ↦
      _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k candidate -
        lower k)) :
    _root_.GD.N0232.N0720.N1036.d014669 m n candidate := by
  intro e he theta
  apply le_antisymm (he theta)
  by_contra hnot
  have hstrict : _root_.GD.N0232.N0720.N1080.d014182 m n theta e < _root_.GD.N0232.N0720.N1080.d014182 m n theta candidate :=
    lt_of_not_ge hnot
  obtain ⟨xi₀, hxi₀⟩ := hchartSurjective theta
  have hstrictChart : _root_.GD.N0232.N0720.N1080.d014182 m n (chart xi₀) e <
      _root_.GD.N0232.N0720.N1080.d014182 m n (chart xi₀) candidate := by
    simpa only [hxi₀] using hstrict
  obtain ⟨epsilon, hepsilon, N₁, hgap⟩ :=
    _root_.GD.N0232.N0720.N1111.d016609
      m n chart hchartContinuous prior hpriorFinite hretain
      hcandidate he hcandidateIntegrable hstrictChart
  obtain ⟨N₂, hsmall⟩ := hdeficitZero epsilon hepsilon
  let k := max N₁ N₂
  have hk₁ : N₁ ≤ k := le_max_left N₁ N₂
  have hk₂ : N₂ ≤ k := le_max_right N₁ N₂
  have hfixed := hgap k hk₁
  have heFinite :=
    _root_.GD.N0232.N0720.N1111.d016607 m n hcandidate he
  have heIntegrable :=
    _root_.GD.N0232.N0720.N1111.d016608
      m n chart hchartContinuous (prior k) hcandidate he
        (hcandidateIntegrable k)
  have hmin := hlower k e heFinite heIntegrable
  have hvanish := hsmall k hk₂
  have hupper :
      _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k candidate -
          _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k e ≤
        _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k candidate - lower k := by
    linarith
  have habsUpper :
      _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k candidate -
          lower k < epsilon := by
    exact lt_of_le_of_lt (le_abs_self _) hvanish
  linarith












structure d016612
    (m n : ℕ) (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (prior : ℕ → Measure Xi)
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop where
  finiteRisk : ∀ k, _root_.GD.N0232.N0720.N1159.d014637 m n (bayes k)
  integrable : ∀ k, Integrable
    (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) (bayes k)).toReal) (prior k)
  minimizes : ∀ k q, _root_.GD.N0232.N0720.N1159.d014637 m n q →
    Integrable (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) q).toReal) (prior k) →
      _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k (bayes k) ≤
        _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k q



theorem d016612.d016613
    (m n : ℕ) (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (prior : ℕ → Measure Xi)
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612 m n chart prior bayes) :
    _root_.GD.N0232.N0720.N1111.d016610 m n chart prior
      (fun k ↦ _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k (bayes k)) := by
  intro k q hqFinite hqIntegrable
  exact hbayes.minimizes k q hqFinite hqIntegrable






theorem d016614
    (m n : ℕ)
    (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (hchartContinuous : Continuous chart)
    (hchartSurjective : Function.Surjective chart)
    (prior : ℕ → Measure Xi)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (candidate : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hcandidate : _root_.GD.N0232.N0720.N1159.d014637 m n candidate)
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612 m n chart prior bayes)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) candidate).toReal) (prior k))
    (hdeficitZero : _root_.GD.N0230.N0606.d000961 (fun k ↦
      _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k candidate -
        _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k (bayes k))) :
    _root_.GD.N0232.N0720.N1036.d014669 m n candidate := by
  exact
    _root_.GD.N0232.N0720.N1111.d016611
      m n chart hchartContinuous hchartSurjective prior hpriorFinite hretain
      candidate hcandidate hcandidateIntegrable
      (fun k ↦ _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k (bayes k))
      (_root_.GD.N0232.N0720.N1111.d016612.d016613
        m n chart prior bayes hbayes)
      hdeficitZero




theorem d016615
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (chart : Xi → _root_.GD.N0232.N0720.N1080.d014168)
    (hchartContinuous : Continuous chart)
    (hchartSurjective : Function.Surjective chart)
    (prior : ℕ → Measure Xi)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612 m n chart prior bayes)
    (hsIntegrable : ∀ k, Integrable
      (fun xi ↦ (_root_.GD.N0232.N0720.N1080.d014182 m n (chart xi) s.value).toReal) (prior k))
    (hdeficitZero : _root_.GD.N0230.N0606.d000961 (fun k ↦
      _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k s.value -
        _root_.GD.N0232.N0720.N1111.d016604 m n chart prior k (bayes k))) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1036.d014672
    m n hm hn s hstrict
  exact _root_.GD.N0232.N0720.N1111.d016614
    m n chart hchartContinuous hchartSurjective prior hpriorFinite hretain
    s.value s.finiteRisk bayes hbayes hsIntegrable hdeficitZero

end

end N1111
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1111.d016608
#print axioms _root_.GD.N0232.N0720.N1111.d016611
#print axioms _root_.GD.N0232.N0720.N1111.d016614
#print axioms _root_.GD.N0232.N0720.N1111.d016615
