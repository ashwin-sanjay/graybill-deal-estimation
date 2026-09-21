import GD.Module0866
import GD.Module0712












open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace GD.N0232.N0719.N0862

open _root_.GD.N0232.N0719.N0900 _root_.GD.N0232.N0719.N0937
open _root_.GD.N0232.N0719.N1006
open _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1414 (d004212)

noncomputable section

variable {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]

def d013361 (mu : Measure Ω) (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131)
    (K : Ω → ℝ) (i : I) : ℝ :=
  (∫ z, (t i z : ℝ) * K z ∂mu) / ∫ z, K z ∂mu

omit [Fintype I] in
theorem d013362 (mu : Measure Ω) (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131)
    (K : Ω → ℝ) (hK : 0 < ∫ z, K z ∂mu) (hpos : ∀ᵐ z ∂mu, 0 ≤ K z) (i : I) :
    0 ≤ _root_.GD.N0232.N0719.N0862.d013361 mu t K i := by
  apply div_nonneg _ hK.le
  exact integral_nonneg_of_ae (hpos.mono fun z hz => mul_nonneg (t i z).2.1 hz)

theorem d013363 (mu : Measure Ω) (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131)
    (K : Ω → ℝ) (hK : 0 < ∫ z, K z ∂mu)
    (hsum : ∀ᵐ z ∂mu, ∑ i, (t i z : ℝ) = 1)
    (hint : ∀ i, Integrable (fun z => (t i z : ℝ) * K z) mu) :
    ∑ i, _root_.GD.N0232.N0719.N0862.d013361 mu t K i = 1 := by
  unfold _root_.GD.N0232.N0719.N0862.d013361
  rw [← Finset.sum_div, ← integral_finsetSum _ (fun i _ => hint i)]
  have heq : (fun z => ∑ i, (t i z : ℝ) * K z) =ᵐ[mu] K := by
    filter_upwards [hsum] with z hz
    rw [← Finset.sum_mul, hz, one_mul]
  rw [integral_congr_ae heq, div_self hK.ne']

omit [Fintype I] in
theorem d013364
    (mu : Measure Ω) (t : I → Ω → _root_.GD.N0232.N0720.N1290.d004131) (K : Ω → ℝ)
    (hK : 0 < ∫ z, K z ∂mu) (hpos : ∀ᵐ z ∂mu, 0 ≤ K z)
    (hKi : Integrable K mu) (i : I)
    (hnum : Integrable (fun z => (t i z : ℝ) * K z) mu)
    {c : ℝ} (hc : ∀ᵐ z ∂mu, (t i z : ℝ) ≤ c) :
    _root_.GD.N0232.N0719.N0862.d013361 mu t K i ≤ c := by
  apply (div_le_iff₀ hK).mpr
  calc
    _ ≤ ∫ z, c * K z ∂mu := integral_mono_ae hnum (hKi.const_mul c) (by
      filter_upwards [hc, hpos] with z hz hp
      exact mul_le_mul_of_nonneg_right hz hp)
    _ = _ := integral_const_mul c K

variable {k : ℕ}



def d013365 (sizes : Fin k → ℕ) (mu : Measure Ω)
    (t : Fin k → Ω → _root_.GD.N0232.N0720.N1290.d004131)
    (K : _root_.GD.N0232.N0719.d009173 k sizes → Ω → ℝ) : Prop :=
  ∀ᵐ x ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
    Integrable (K x) mu ∧ 0 < (∫ z, K x z ∂mu) ∧
      (∀ᵐ z ∂mu, 0 ≤ K x z) ∧
        ∀ i, Integrable (fun z => (t i z : ℝ) * K x z) mu

theorem d013366
    (sizes : Fin k → ℕ) (mu : Measure Ω) (t : Fin k → Ω → _root_.GD.N0232.N0720.N1290.d004131)
    (K : _root_.GD.N0232.N0719.d009173 k sizes → Ω → ℝ)
    (hK : _root_.GD.N0232.N0719.N0862.d013365 sizes mu t K)
    (hsum : ∀ᵐ z ∂mu, ∑ i, (t i z : ℝ) = 1)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hrep : ∀ᵐ x ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
      f x = ∑ i, _root_.GD.N0232.N0719.N0862.d013361 mu t (K x) i * _root_.GD.N0232.N0719.N0900.d009102 k sizes x i)
    (j : Fin k) {c : ℝ} (hc : ∀ᵐ z ∂mu, (t j z : ℝ) ≤ c) :
    _root_.GD.N0232.N0719.N0937.d010576 sizes j f c := by
  filter_upwards [hK, hrep] with x hx hfx
  refine ⟨_root_.GD.N0232.N0719.N0862.d013361 mu t (K x), ?_, ?_, ?_, hfx⟩
  · exact _root_.GD.N0232.N0719.N0862.d013362 mu t (K x) hx.2.1 hx.2.2.1
  · exact _root_.GD.N0232.N0719.N0862.d013363 mu t (K x) hx.2.1 hsum hx.2.2.2
  · exact _root_.GD.N0232.N0719.N0862.d013364 mu t (K x) hx.2.1 hx.2.2.1
      hx.1 j (hx.2.2.2 j) hc


theorem d013367
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (mu : Measure Ω) (t : Fin k → Ω → _root_.GD.N0232.N0720.N1290.d004131) (ht : ∀ i, Measurable (t i))
    (K : _root_.GD.N0232.N0719.d009173 k sizes → Ω → ℝ)
    (hK : _root_.GD.N0232.N0719.N0862.d013365 sizes mu t K)
    (hsum : ∀ᵐ z ∂mu, ∑ i, (t i z : ℝ) = 1)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    (hf : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) → MemLp f 2 (_root_.GD.N0232.N0719.d009176 k sizes 0 s))
    (hcap : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) →
      (∫ x, f x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s) ≤
        ∫ x, _root_.GD.N0232.N0719.N0900.d009111 k sizes x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s)
    (hrep : ∀ᵐ x ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
      f x = ∑ i, _root_.GD.N0232.N0719.N0862.d013361 mu t (K x) i * _root_.GD.N0232.N0719.N0900.d009102 k sizes x i)
    (j : Fin k) (c : ℝ) (hc : c < 1) :
    ¬ (∀ᵐ z : _root_.GD.N0232.N0720.N1290.d004131 ∂_root_.GD.N0232.N0719.N1006.d013356 mu t j, (z : ℝ) ≤ c) := by
  intro hbound
  have hraw : ∀ᵐ z ∂mu, (t j z : ℝ) ≤ c :=
    ae_of_ae_map (ht j).aemeasurable hbound
  exact _root_.GD.N0232.N0719.N0937.d010581 sizes hn j f hfm hf hcap hc
    (_root_.GD.N0232.N0719.N0862.d013366 sizes mu t K hK hsum f hrep j hraw)



theorem d013368
    (hk : 3 ≤ k) (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (q : ℝ) (hq : 3 / 2 ≤ q)
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (t : Fin k → Ω → _root_.GD.N0232.N0720.N1290.d004131) (ht : ∀ i, Measurable (t i))
    (K : _root_.GD.N0232.N0719.d009173 k sizes → Ω → ℝ)
    (hK : _root_.GD.N0232.N0719.N0862.d013365 sizes mu t K)
    (hsum : ∀ᵐ z ∂mu, ∑ i, (t i z : ℝ) = 1)
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hfm : Measurable f)
    (hf : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) → MemLp f 2 (_root_.GD.N0232.N0719.d009176 k sizes 0 s))
    (hcap : ∀ s : Fin k → ℝ, (∀ i, 0 < s i) →
      (∫ x, f x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s) ≤
        ∫ x, _root_.GD.N0232.N0719.N0900.d009111 k sizes x ^ 2 ∂_root_.GD.N0232.N0719.d009176 k sizes 0 s)
    (hrep : ∀ᵐ x ∂_root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => 1),
      f x = ∑ i, _root_.GD.N0232.N0719.N0862.d013361 mu t (K x) i * _root_.GD.N0232.N0719.N0900.d009102 k sizes x i)
    (hF : ∀ i, ∀ᶠ epsilon in 𝓝 (0 : ℝ),
      _root_.GD.N0232.N0720.N1290.d004143 q
        (_root_.GD.N0232.N0720.N1290.d004147 (_root_.GD.N0232.N0720.N1414.d004212 0 1 (_root_.GD.N0232.N0719.N1006.d013356 mu t i)) epsilon)
          (_root_.GD.N0232.N0719.N1006.d013356 mu t i) = 0) : False := by
  exact _root_.GD.N0232.N0719.N1006.d013360 (by simpa using hk) q hq mu t ht hsum hF
    (_root_.GD.N0232.N0719.N0862.d013367 sizes hn mu t ht K hK hsum f hfm hf hcap hrep)

end
end GD.N0232.N0719.N0862

#print axioms _root_.GD.N0232.N0719.N0862.d013364
#print axioms _root_.GD.N0232.N0719.N0862.d013367
#print axioms _root_.GD.N0232.N0719.N0862.d013368
