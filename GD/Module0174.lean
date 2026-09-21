import GD.Module0049
import GD.Module0173

set_option autoImplicit false
set_option warningAsError true























namespace GD.N0230.N0561

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open _root_.GD.N0230.N0556 _root_.GD.N0230.N0622
open _root_.GD.N0230.N0560
open _root_.GD.N0227.N0543

section Packets

variable {H Θ : Type*}



structure d002038 (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ) where
  size : ℕ
  parameter : Fin size → Θ
  weight : Fin size → ℝ
  minimizer : H
  minimizer_mem : minimizer ∈ D
  bayes : _root_.GD.N0230.N0622.d000607 D risk theta0 parameter weight minimizer

def d002039 (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (seed : H) (C : _root_.GD.N0230.N0561.d002038 D risk theta0) : ℝ :=
  _root_.GD.N0230.N0560.d000625 risk theta0 C.parameter C.weight seed C.minimizer

variable {X : Type*} [MeasurableSpace X]




structure d002040 (mu : Measure X)
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ) (seed : H) where
  density : _root_.GD.N0230.N0561.d002038 D risk theta0 → X → ℝ
  error : _root_.GD.N0230.N0561.d002038 D risk theta0 → X → ℝ
  anchor : X → ℝ
  test : X → ℝ
  adjointTest : X → ℝ
  bound : ℝ
  residual : ℝ
  anchorMass : ℝ
  bound_pos : 0 < bound
  residual_lt_one : residual < 1
  anchorMass_pos : 0 < anchorMass
  density_pos : ∀ C, ∀ᵐ x ∂mu, 0 < density C x
  anchor_le : ∀ C, ∀ᵐ x ∂mu, anchor x ≤ density C x
  test_nonneg : ∀ᵐ x ∂mu, 0 ≤ test x
  adjoint_bound : ∀ᵐ x ∂mu, adjointTest x ^ 2 ≤ bound * test x
  error_test_integrable : ∀ C, Integrable (fun x ↦ error C x * adjointTest x) mu
  energy_integrable : ∀ C, Integrable (fun x ↦ error C x ^ 2 / density C x) mu
  density_test_integrable : ∀ C, Integrable (fun x ↦ density C x * test x) mu
  anchor_test_integrable : Integrable (fun x ↦ anchor x * test x) mu
  anchorMass_le : anchorMass ≤ ∫ x, anchor x * test x ∂mu
  tested_residual : ∀ C,
    |(∫ x, density C x * test x ∂mu) - (∫ x, error C x * adjointTest x ∂mu)| ≤
      residual * (∫ x, density C x * test x ∂mu)
  full_objective_deficiency : ∀ C, _root_.GD.N0230.N0561.d002039 D risk theta0 seed C =
    ∫ x, error C x ^ 2 / density C x ∂mu



theorem d002041
    (mu : Measure X) (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ) (seed : H)
    (T : _root_.GD.N0230.N0561.d002040 mu D risk theta0 seed)
    (C : _root_.GD.N0230.N0561.d002038 D risk theta0) :
    (1 - T.residual) ^ 2 * T.anchorMass / T.bound ≤
      _root_.GD.N0230.N0561.d002039 D risk theta0 seed C := by
  rw [T.full_objective_deficiency C]
  exact _root_.GD.N0227.N0543.d002030 T.bound_pos T.residual_lt_one.le
    (T.density_pos C) (T.anchor_le C) T.test_nonneg T.adjoint_bound
    (T.error_test_integrable C) (T.energy_integrable C) (T.density_test_integrable C)
    T.anchor_test_integrable T.anchorMass_le (T.tested_residual C)

theorem d002042
    (mu : Measure X) (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ) (seed : H)
    (T : _root_.GD.N0230.N0561.d002040 mu D risk theta0 seed) :
    0 < (1 - T.residual) ^ 2 * T.anchorMass / T.bound :=
  div_pos (mul_pos (sq_pos_of_pos (sub_pos.mpr T.residual_lt_one)) T.anchorMass_pos)
    T.bound_pos

end Packets

section NullRows

variable {H Θ : Type*}




theorem d002043
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ) (seed : H)
    (c : ℝ) (hc : 0 < c)
    (hfloor : ∀ C : _root_.GD.N0230.N0561.d002038 D risk theta0,
      c ≤ _root_.GD.N0230.N0561.d002039 D risk theta0 seed C) :
    ¬ _root_.GD.N0230.N0560.d000632 D risk theta0 seed := by
  rintro ⟨size, packet, weight, p, hbayes, hzero⟩
  let row (n : ℕ) : _root_.GD.N0230.N0561.d002038 D risk theta0 :=
    ⟨size n, packet n, weight n, p n, (hbayes n).1, (hbayes n).2⟩
  have hbound (n : ℕ) : c ≤ _root_.GD.N0230.N0560.d000625 risk theta0 (packet n) (weight n) seed (p n) :=
    hfloor (row n)
  exact (not_le_of_gt hc) (ge_of_tendsto hzero (Eventually.of_forall hbound))



theorem d002044
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ) (seed : H)
    (T : _root_.GD.N0230.N0561.d002040 mu D risk theta0 seed) :
    ¬ _root_.GD.N0230.N0560.d000632 D risk theta0 seed :=
  _root_.GD.N0230.N0561.d002043 D risk theta0 seed
    ((1 - T.residual) ^ 2 * T.anchorMass / T.bound)
    (_root_.GD.N0230.N0561.d002042 mu D risk theta0 seed T)
    (_root_.GD.N0230.N0561.d002041 mu D risk theta0 seed T)





theorem d002045
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ) (seed : H) (hseed : seed ∈ D)
    (T : _root_.GD.N0230.N0561.d002040 mu D risk theta0 seed)
    (hProducer : _root_.GD.N0230.N0556.d000031 (fun theta (d : D) ↦ risk theta d) ⟨seed, hseed⟩ →
      _root_.GD.N0230.N0560.d000632 D risk theta0 seed) :
    ¬ _root_.GD.N0230.N0556.d000031 (fun theta (d : D) ↦ risk theta d) ⟨seed, hseed⟩ := by
  intro hadmissible
  exact _root_.GD.N0230.N0561.d002044 mu D risk theta0 seed T
    (hProducer hadmissible)

end NullRows

section Admissibility

variable {H Θ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [TopologicalSpace Θ]






theorem d002046
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (D : Set H) (risk : Θ → H → ℝ) (sample : ℕ → Θ)
    (theta0 : Θ) (seed : H) (hseed : seed ∈ D)
    (hDclosed : IsClosed D) (hDconvex : Convex ℝ D)
    (hdecision : ∀ theta, Continuous (risk theta))
    (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (hparameter : ∀ d ∈ D, Continuous (fun theta ↦ risk theta d))
    (hdense : DenseRange sample)
    (scale offset : ℝ) (hscale : 0 < scale)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (T : _root_.GD.N0230.N0561.d002040 mu D risk theta0 seed) :
    ¬ _root_.GD.N0230.N0556.d000031 (fun theta (d : D) ↦ risk theta d) ⟨seed, hseed⟩ := by
  intro hadmissible
  exact _root_.GD.N0230.N0561.d002044 mu D risk theta0 seed T
    ((_root_.GD.N0230.N0560.d000634 D risk sample theta0 seed hseed
      hDclosed hDconvex hdecision hconvex hparameter hdense scale offset hscale hreference).mp
        hadmissible)



theorem d002047
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (D : Set H) (risk : Θ → H → ℝ) (sample : ℕ → Θ)
    (theta0 : Θ) (seed : H) (hseed : seed ∈ D)
    (hDclosed : IsClosed D) (hDconvex : Convex ℝ D)
    (hdecision : ∀ theta, Continuous (risk theta))
    (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (hparameter : ∀ d ∈ D, Continuous (fun theta ↦ risk theta d))
    (hdense : DenseRange sample)
    (scale offset : ℝ) (hscale : 0 < scale)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (T : _root_.GD.N0230.N0561.d002040 mu D risk theta0 seed) :
    ∃ d ∈ D, (∀ theta, risk theta d ≤ risk theta seed) ∧
      ∃ theta, risk theta d < risk theta seed := by
  have h := _root_.GD.N0230.N0561.d002046 mu D risk sample theta0 seed hseed
    hDclosed hDconvex hdecision hconvex hparameter hdense scale offset hscale hreference T
  classical
  rw [_root_.GD.N0230.N0556.d000031, not_not] at h
  obtain ⟨d, hdom, hstrict⟩ := h
  exact ⟨d, d.property, hdom, hstrict⟩

end Admissibility

section ActualDifferentialExpression

open _root_.GD.N0227.N0545
open _root_.GD.N0232.N0720.N1230
open scoped SchwartzMap

variable {H Θ : Type*}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [FiniteDimensional ℝ X]
  (mu : Measure X) [mu.IsAddHaarMeasure]




theorem d002048
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ) (seed : H)
    (a : _root_.GD.N0227.N0545.d002018 X) (chi : 𝓢(X, ℝ)) (k : ℕ) (ha : a.d002019 ≤ k)
    (error : _root_.GD.N0230.N0561.d002038 D risk theta0 → 𝓢(X, ℝ))
    (rho : _root_.GD.N0230.N0561.d002038 D risk theta0 → X → ℝ) (anchor : X → ℝ)
    (hRho : ∀ C, ∀ᵐ x ∂mu, 0 < rho C x)
    (hAnchor : ∀ C, ∀ᵐ x ∂mu, anchor x ≤ rho C x)
    (hEnergy : ∀ C, Integrable (fun x ↦ error C x ^ 2 / rho C x) mu)
    (hAnchorMass : Integrable (fun x ↦ anchor x * _root_.GD.N0227.N0543.d002033 chi k x) mu)
    (hpositive : 0 < ∫ x, anchor x * _root_.GD.N0227.N0543.d002033 chi k x ∂mu)
    (hSource : ∀ C x, x ∈ Function.support (chi : X → ℝ) →
      rho C x = a.d002020 (error C) x)
    (hDeficiency : ∀ C, _root_.GD.N0230.N0561.d002039 D risk theta0 seed C =
      ∫ x, error C x ^ 2 / rho C x ∂mu) :
    Nonempty (_root_.GD.N0230.N0561.d002040 mu D risk theta0 seed) := by
  obtain ⟨K, hK, hbound⟩ := _root_.GD.N0227.N0543.d002035 a chi k ha
  have hMass (C : _root_.GD.N0230.N0561.d002038 D risk theta0) :
      Integrable (fun x ↦ rho C x * _root_.GD.N0227.N0543.d002033 chi k x) mu := by
    have hi := (_root_.GD.N0232.N0720.N1230.d001994 (_root_.GD.N0227.N0543.d002033 chi k) (a.d002020 (error C))).integrable (μ := mu)
    apply hi.congr
    filter_upwards with x
    change _root_.GD.N0227.N0543.d002033 chi k x * a.d002020 (error C) x = rho C x * _root_.GD.N0227.N0543.d002033 chi k x
    by_cases hx : chi x = 0
    · simp [hx]
    · rw [hSource C x hx]
      ring
  refine ⟨{
    density := rho
    error := fun C ↦ error C
    anchor := anchor
    test := _root_.GD.N0227.N0543.d002033 chi k
    adjointTest := a.d002021 (_root_.GD.N0227.N0543.d002033 chi k)
    bound := K
    residual := 0
    anchorMass := ∫ x, anchor x * _root_.GD.N0227.N0543.d002033 chi k x ∂mu
    bound_pos := hK
    residual_lt_one := by norm_num
    anchorMass_pos := hpositive
    density_pos := hRho
    anchor_le := hAnchor
    test_nonneg := Eventually.of_forall (fun x ↦ by rw [_root_.GD.N0227.N0543.d002034]; positivity)
    adjoint_bound := Eventually.of_forall hbound
    error_test_integrable := fun C ↦
      (_root_.GD.N0232.N0720.N1230.d001994 (error C) (a.d002021 (_root_.GD.N0227.N0543.d002033 chi k))).integrable
    energy_integrable := hEnergy
    density_test_integrable := hMass
    anchor_test_integrable := hAnchorMass
    anchorMass_le := le_rfl
    tested_residual := ?_
    full_objective_deficiency := hDeficiency }⟩
  intro C
  rw [_root_.GD.N0227.N0543.d002036 a chi (error C) k (rho C) (hSource C)]
  simp

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [TopologicalSpace Θ]




theorem d002049
    (D : Set H) (risk : Θ → H → ℝ) (sample : ℕ → Θ)
    (theta0 : Θ) (seed : H) (hseed : seed ∈ D)
    (hDclosed : IsClosed D) (hDconvex : Convex ℝ D)
    (hdecision : ∀ theta, Continuous (risk theta))
    (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (hparameter : ∀ d ∈ D, Continuous (fun theta ↦ risk theta d))
    (hdense : DenseRange sample)
    (scale offset : ℝ) (hscale : 0 < scale)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (a : _root_.GD.N0227.N0545.d002018 X) (chi : 𝓢(X, ℝ)) (k : ℕ) (ha : a.d002019 ≤ k)
    (error : _root_.GD.N0230.N0561.d002038 D risk theta0 → 𝓢(X, ℝ))
    (rho : _root_.GD.N0230.N0561.d002038 D risk theta0 → X → ℝ) (anchor : X → ℝ)
    (hRho : ∀ C, ∀ᵐ x ∂mu, 0 < rho C x)
    (hAnchor : ∀ C, ∀ᵐ x ∂mu, anchor x ≤ rho C x)
    (hEnergy : ∀ C, Integrable (fun x ↦ error C x ^ 2 / rho C x) mu)
    (hAnchorMass : Integrable (fun x ↦ anchor x * _root_.GD.N0227.N0543.d002033 chi k x) mu)
    (hpositive : 0 < ∫ x, anchor x * _root_.GD.N0227.N0543.d002033 chi k x ∂mu)
    (hSource : ∀ C x, x ∈ Function.support (chi : X → ℝ) →
      rho C x = a.d002020 (error C) x)
    (hDeficiency : ∀ C, _root_.GD.N0230.N0561.d002039 D risk theta0 seed C =
      ∫ x, error C x ^ 2 / rho C x ∂mu) :
    ¬ _root_.GD.N0230.N0556.d000031 (fun theta (d : D) ↦ risk theta d) ⟨seed, hseed⟩ := by
  obtain ⟨T⟩ := _root_.GD.N0230.N0561.d002048 mu D risk theta0 seed
    a chi k ha error rho anchor hRho hAnchor hEnergy hAnchorMass hpositive hSource hDeficiency
  exact _root_.GD.N0230.N0561.d002046 mu D risk sample theta0 seed hseed
    hDclosed hDconvex hdecision hconvex hparameter hdense scale offset hscale hreference T

end ActualDifferentialExpression

end
end GD.N0230.N0561

#print axioms _root_.GD.N0230.N0561.d002041
#print axioms _root_.GD.N0230.N0561.d002042
#print axioms _root_.GD.N0230.N0561.d002043
#print axioms _root_.GD.N0230.N0561.d002044
#print axioms _root_.GD.N0230.N0561.d002045
#print axioms _root_.GD.N0230.N0561.d002046
#print axioms _root_.GD.N0230.N0561.d002047
#print axioms _root_.GD.N0230.N0561.d002048
#print axioms _root_.GD.N0230.N0561.d002049
