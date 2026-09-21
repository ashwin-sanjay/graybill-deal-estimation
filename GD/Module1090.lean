import GD.Module1005
import GD.Module1087
import GD.Module1041
import GD.Module1086






























open Filter MeasureTheory Set Topology
open scoped ENNReal Topology

namespace GD
namespace N0232
namespace N0720
namespace N1169

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1112
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1177
open _root_.GD.N0232.N0720.N1171
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608





theorem d017496
    (j₀ j₁ m₀ m₁ : ℝ) (hm₀ : 0 < m₀) (hm₁ : 0 ≤ m₁) :
    (j₀ + j₁) ^ 2 / (m₀ + m₁) ≤ (j₀ + j₁) ^ 2 / m₀ := by
  have hsum : 0 < m₀ + m₁ := add_pos_of_pos_of_nonneg hm₀ hm₁
  rw [div_le_div_iff₀ hsum hm₀]
  nlinarith [sq_nonneg (j₀ + j₁)]




theorem d017497
    (j₀ j₁ m₀ m₁ gamma : ℝ)
    (hm₀ : 0 < m₀) (hm₁ : 0 < m₁)
    (hgamma : 0 ≤ gamma) (hdom : gamma * m₀ ≤ m₁) :
    (j₀ + j₁) ^ 2 / (m₀ + m₁) ≤
      (2 / (1 + gamma)) * (j₀ ^ 2 / m₀) +
        2 * (j₁ ^ 2 / m₁) := by
  have hgammaOne : 0 < 1 + gamma := by linarith
  have hsum : 0 < m₀ + m₁ := add_pos hm₀ hm₁
  have hdom' : (1 + gamma) * m₀ ≤ m₀ + m₁ := by
    nlinarith
  have hcore :
      j₀ ^ 2 / (m₀ + m₁) ≤
        (1 / (1 + gamma)) * (j₀ ^ 2 / m₀) := by
    calc
      j₀ ^ 2 / (m₀ + m₁) ≤
          j₀ ^ 2 / ((1 + gamma) * m₀) :=
        div_le_div_of_nonneg_left (sq_nonneg j₀)
          (mul_pos hgammaOne hm₀) hdom'
      _ = (1 / (1 + gamma)) * (j₀ ^ 2 / m₀) := by
        field_simp [ne_of_gt hgammaOne, ne_of_gt hm₀]
  have hreservoir :
      j₁ ^ 2 / (m₀ + m₁) ≤ j₁ ^ 2 / m₁ := by
    rw [div_le_div_iff₀ hsum hm₁]
    nlinarith [sq_nonneg j₁]
  have hsquare : (j₀ + j₁) ^ 2 ≤ 2 * j₀ ^ 2 + 2 * j₁ ^ 2 := by
    nlinarith [sq_nonneg (j₀ - j₁)]
  have hdivide :
      (j₀ + j₁) ^ 2 / (m₀ + m₁) ≤
        2 * (j₀ ^ 2 / (m₀ + m₁)) +
          2 * (j₁ ^ 2 / (m₀ + m₁)) := by
    rw [div_le_iff₀ hsum]
    field_simp [ne_of_gt hsum]
    nlinarith
  calc
    (j₀ + j₁) ^ 2 / (m₀ + m₁)
        ≤ 2 * (j₀ ^ 2 / (m₀ + m₁)) +
            2 * (j₁ ^ 2 / (m₀ + m₁)) := hdivide
    _ ≤ 2 * ((1 / (1 + gamma)) * (j₀ ^ 2 / m₀)) +
          2 * (j₁ ^ 2 / m₁) := by gcongr
    _ = (2 / (1 + gamma)) * (j₀ ^ 2 / m₀) +
          2 * (j₁ ^ 2 / m₁) := by ring





theorem d017498
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (base reservoir : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hbase : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 base theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hreservoir : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 reservoir theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho)) :
    _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ base theta + reservoir theta) x =
      _root_.GD.N0232.N0720.N1173.d015940 rho base x + _root_.GD.N0232.N0720.N1173.d015940 rho reservoir x := by
  unfold _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0230.N0589.d000088 _root_.GD.N0232.N0720.N1173.d015939 at *
  rw [← integral_add hbase hreservoir]
  apply integral_congr_ae
  filter_upwards [] with theta
  ring



theorem d017499
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (base reservoir : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hbase : Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1173.d015938 theta - _root_.GD.N0232.N0720.N1173.d015944 rho x) *
          _root_.GD.N0232.N0720.N1173.d015939 base theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hreservoir : Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1173.d015938 theta - _root_.GD.N0232.N0720.N1173.d015944 rho x) *
          _root_.GD.N0232.N0720.N1173.d015939 reservoir theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho)) :
    _root_.GD.N0232.N0720.N1173.d015945 rho
        (fun theta ↦ base theta + reservoir theta) x =
      _root_.GD.N0232.N0720.N1173.d015945 rho base x +
        _root_.GD.N0232.N0720.N1173.d015945 rho reservoir x := by
  unfold _root_.GD.N0232.N0720.N1173.d015945 _root_.GD.N0232.N0720.N1173.d015939 at *
  rw [← integral_add hbase hreservoir]
  apply integral_congr_ae
  filter_upwards [] with theta
  ring


theorem d017500
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hweight : ∀ theta, 0 ≤ weight theta) :
    0 ≤ _root_.GD.N0232.N0720.N1173.d015940 rho weight x := by
  unfold _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0230.N0589.d000088 _root_.GD.N0232.N0720.N1173.d015939
  apply integral_nonneg_of_ae
  filter_upwards [] with theta
  exact mul_nonneg
    (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x)
    (hweight theta)





def d017501
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (base reservoir : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) : ℝ :=
  ∫ x,
    (_root_.GD.N0232.N0720.N1173.d015945 rho base x +
        _root_.GD.N0232.N0720.N1173.d015945 rho reservoir x) ^ 2 /
      _root_.GD.N0232.N0720.N1173.d015940 rho base x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2



theorem d017502
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (base reservoir : _root_.GD.N0232.N0720.N1173.d015933 → ℝ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (hbaseEvidence : 0 < _root_.GD.N0232.N0720.N1173.d015940 rho base x)
    (hreservoirEvidence : 0 ≤ _root_.GD.N0232.N0720.N1173.d015940 rho reservoir x)
    (hevidenceAdd :
      _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ base theta + reservoir theta) x =
        _root_.GD.N0232.N0720.N1173.d015940 rho base x + _root_.GD.N0232.N0720.N1173.d015940 rho reservoir x)
    (hcurrentAdd :
      _root_.GD.N0232.N0720.N1173.d015945 rho
          (fun theta ↦ base theta + reservoir theta) x =
        _root_.GD.N0232.N0720.N1173.d015945 rho base x +
          _root_.GD.N0232.N0720.N1173.d015945 rho reservoir x) :
    _root_.GD.N0232.N0720.N1171.d015982 rho
        (fun theta ↦ base theta + reservoir theta) x ≤
      (_root_.GD.N0232.N0720.N1173.d015945 rho base x +
          _root_.GD.N0232.N0720.N1173.d015945 rho reservoir x) ^ 2 /
        _root_.GD.N0232.N0720.N1173.d015940 rho base x := by
  unfold _root_.GD.N0232.N0720.N1171.d015982
  rw [hevidenceAdd, hcurrentAdd]
  exact _root_.GD.N0232.N0720.N1169.d017496 _ _ _ _
    hbaseEvidence hreservoirEvidence


theorem d017503
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (base reservoir : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (htotalIntegrable : Integrable
      (_root_.GD.N0232.N0720.N1171.d015982 rho
        (fun theta ↦ base theta + reservoir theta))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hresidualIntegrable : Integrable
      (fun x ↦
        (_root_.GD.N0232.N0720.N1173.d015945 rho base x +
            _root_.GD.N0232.N0720.N1173.d015945 rho reservoir x) ^ 2 /
          _root_.GD.N0232.N0720.N1173.d015940 rho base x)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hbaseEvidence : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 rho base x)
    (hreservoirEvidence : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 ≤ _root_.GD.N0232.N0720.N1173.d015940 rho reservoir x)
    (hevidenceAdd : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ base theta + reservoir theta) x =
        _root_.GD.N0232.N0720.N1173.d015940 rho base x + _root_.GD.N0232.N0720.N1173.d015940 rho reservoir x)
    (hcurrentAdd : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0232.N0720.N1173.d015945 rho
          (fun theta ↦ base theta + reservoir theta) x =
        _root_.GD.N0232.N0720.N1173.d015945 rho base x +
          _root_.GD.N0232.N0720.N1173.d015945 rho reservoir x) :
    _root_.GD.N0232.N0720.N1171.d015983 rho
        (fun theta ↦ base theta + reservoir theta) ≤
      _root_.GD.N0232.N0720.N1169.d017501 rho base reservoir := by
  unfold _root_.GD.N0232.N0720.N1171.d015983
    _root_.GD.N0232.N0720.N1169.d017501
  apply integral_mono_ae htotalIntegrable hresidualIntegrable
  filter_upwards [hbaseEvidence, hreservoirEvidence,
    hevidenceAdd, hcurrentAdd] with x hb hr he hc
  exact _root_.GD.N0232.N0720.N1169.d017502
    rho base reservoir x hb hr he hc



theorem d017504
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hevidence : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 rho weight x) :
    0 ≤ _root_.GD.N0232.N0720.N1171.d015983 rho weight := by
  unfold _root_.GD.N0232.N0720.N1171.d015983 _root_.GD.N0232.N0720.N1171.d015982
  apply integral_nonneg_of_ae
  filter_upwards [hevidence] with x hx
  exact div_nonneg (sq_nonneg _) hx.le



theorem d017505
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (base reservoir : ℕ → _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hcombinedEvidence : ∀ k, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 rho
        (fun theta ↦ base k theta + reservoir k theta) x)
    (hupper : ∀ k,
      _root_.GD.N0232.N0720.N1171.d015983 rho
          (fun theta ↦ base k theta + reservoir k theta) ≤
        _root_.GD.N0232.N0720.N1169.d017501 rho (base k) (reservoir k))
    (hresidualZero : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1169.d017501 rho (base k) (reservoir k))
      atTop (nhds 0)) :
    Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1171.d015983 rho
        (fun theta ↦ base k theta + reservoir k theta))
      atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hresidualZero
    (Filter.Eventually.of_forall fun k ↦
      _root_.GD.N0232.N0720.N1169.d017504 rho _
        (hcombinedEvidence k))
    (Filter.Eventually.of_forall hupper)





theorem d017506
    {Xi : Type*} [TopologicalSpace Xi] [MeasurableSpace Xi]
    [OpensMeasurableSpace Xi]
    (base prior : ℕ → Measure Xi)
    (hbaseFinite : ∀ k, IsFiniteMeasure (base k))
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hbaseRetains : _root_.GD.N0232.N0720.N1111.d016605 base)
    (hdom : ∀ k, base k ≤ prior k) :
    _root_.GD.N0232.N0720.N1111.d016605 prior := by
  intro xi U hU
  obtain ⟨a, ha, N, hmass⟩ := hbaseRetains xi U hU
  refine ⟨a, ha, N, ?_⟩
  intro k hk
  letI : IsFiniteMeasure (base k) := hbaseFinite k
  letI : IsFiniteMeasure (prior k) := hpriorFinite k
  exact (hmass k hk).trans <|
    (ENNReal.toReal_le_toReal (measure_ne_top (base k) U)
      (measure_ne_top (prior k) U)).2 (hdom k U)









theorem d017507
    (prior : ℕ → Measure _root_.GD.N0232.N0720.N1173.d015933)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612
      2 2 _root_.GD.N0232.N0720.N1173.d015935 prior bayes)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta)
          _root_.GD.N0232.N0720.N1177.d017413).toReal)
      (prior k))
    (weight : ℕ → _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hdeficitEq : ∀ k,
      _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k
          _root_.GD.N0232.N0720.N1177.d017413 -
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k (bayes k) =
          _root_.GD.N0232.N0720.N1171.d015983
            _root_.GD.N0232.N0720.N1493.d016104 (weight k))
    (hactionZero : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1171.d015983
        _root_.GD.N0232.N0720.N1493.d016104 (weight k))
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1036.d014669 2 2 _root_.GD.N0232.N0720.N1177.d017413 := by
  apply _root_.GD.N0232.N0720.N1111.d016614
    2 2 _root_.GD.N0232.N0720.N1173.d015935
  · unfold _root_.GD.N0232.N0720.N1173.d015935
    exact _root_.GD.N0232.N0720.N1486.d015877 2 2 _ _
  · unfold _root_.GD.N0232.N0720.N1173.d015935
    exact _root_.GD.N0232.N0720.N1486.d015893 2 2 _ _
  · exact hpriorFinite
  · exact hretain
  · exact _root_.GD.N0232.N0720.N1177.d017416
  · exact hbayes
  · exact hcandidateIntegrable
  · rw [_root_.GD.N0232.N0720.N1112.d016616]
    have hfunctions :
        (fun k ↦
          _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k
              _root_.GD.N0232.N0720.N1177.d017413 -
            _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k
              (bayes k)) =
          (fun k ↦ _root_.GD.N0232.N0720.N1171.d015983
            _root_.GD.N0232.N0720.N1493.d016104 (weight k)) := by
      funext k
      exact hdeficitEq k
    rw [hfunctions]
    exact hactionZero









theorem d017508
    (prior : ℕ → Measure _root_.GD.N0232.N0720.N1173.d015933)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612
      2 2 _root_.GD.N0232.N0720.N1173.d015935 prior bayes)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta)
          _root_.GD.N0232.N0720.N1177.d017413).toReal)
      (prior k))
    (base reservoir : ℕ → _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hcombinedEvidence : ∀ k, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (fun theta ↦ base k theta + reservoir k theta) x)
    (hupper : ∀ k,
      _root_.GD.N0232.N0720.N1171.d015983 _root_.GD.N0232.N0720.N1493.d016104
          (fun theta ↦ base k theta + reservoir k theta) ≤
        _root_.GD.N0232.N0720.N1169.d017501 _root_.GD.N0232.N0720.N1493.d016104
          (base k) (reservoir k))
    (hresidualZero : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1169.d017501
        _root_.GD.N0232.N0720.N1493.d016104 (base k) (reservoir k))
      atTop (nhds 0))
    (hdeficitEq : ∀ k,
      _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k
          _root_.GD.N0232.N0720.N1177.d017413 -
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k (bayes k) =
          _root_.GD.N0232.N0720.N1171.d015983 _root_.GD.N0232.N0720.N1493.d016104
            (fun theta ↦ base k theta + reservoir k theta)) :
    _root_.GD.N0232.N0720.N1036.d014669 2 2 _root_.GD.N0232.N0720.N1177.d017413 := by
  apply _root_.GD.N0232.N0720.N1169.d017507
    prior hpriorFinite hretain bayes hbayes hcandidateIntegrable
    (fun k theta ↦ base k theta + reservoir k theta) hdeficitEq
  exact _root_.GD.N0232.N0720.N1169.d017505
    _root_.GD.N0232.N0720.N1493.d016104 base reservoir hcombinedEvidence hupper
      hresidualZero




theorem d017509
    (hstrict : _root_.GD.N0232.N0720.N1177.d017420)
    (prior : ℕ → Measure _root_.GD.N0232.N0720.N1173.d015933)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612
      2 2 _root_.GD.N0232.N0720.N1173.d015935 prior bayes)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta)
          _root_.GD.N0232.N0720.N1177.d017413).toReal)
      (prior k))
    (base reservoir : ℕ → _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hcombinedEvidence : ∀ k, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (fun theta ↦ base k theta + reservoir k theta) x)
    (hupper : ∀ k,
      _root_.GD.N0232.N0720.N1171.d015983 _root_.GD.N0232.N0720.N1493.d016104
          (fun theta ↦ base k theta + reservoir k theta) ≤
        _root_.GD.N0232.N0720.N1169.d017501 _root_.GD.N0232.N0720.N1493.d016104
          (base k) (reservoir k))
    (hresidualZero : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1169.d017501
        _root_.GD.N0232.N0720.N1493.d016104 (base k) (reservoir k))
      atTop (nhds 0))
    (hdeficitEq : ∀ k,
      _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k
          _root_.GD.N0232.N0720.N1177.d017413 -
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k (bayes k) =
          _root_.GD.N0232.N0720.N1171.d015983 _root_.GD.N0232.N0720.N1493.d016104
            (fun theta ↦ base k theta + reservoir k theta)) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  apply _root_.GD.N0232.N0720.N1036.d014672
    2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1177.d017418
  · change _root_.GD.N0232.N0720.N1177.d017420
    exact hstrict
  · simpa only [_root_.GD.N0232.N0720.N1177.d017419] using
      _root_.GD.N0232.N0720.N1169.d017508
        prior hpriorFinite hretain bayes hbayes hcandidateIntegrable
        base reservoir hcombinedEvidence hupper hresidualZero hdeficitEq

end

end N1169
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1169.d017496
#print axioms _root_.GD.N0232.N0720.N1169.d017497
#print axioms _root_.GD.N0232.N0720.N1169.d017503
#print axioms _root_.GD.N0232.N0720.N1169.d017505
#print axioms _root_.GD.N0232.N0720.N1169.d017506
#print axioms _root_.GD.N0232.N0720.N1169.d017508
#print axioms _root_.GD.N0232.N0720.N1169.d017509
