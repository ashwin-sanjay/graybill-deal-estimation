import GD.Module0048
import Mathlib.Analysis.SpecificLimits.Basic











open Filter Set Topology
open scoped BigOperators

namespace GD.N0230.N0560

open _root_.GD.N0230.N0556 _root_.GD.N0230.N0622

noncomputable section

variable {H Θ I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def d000624 [Fintype I] (risk : Θ → H → ℝ) (theta0 : Θ)
    (packet : I → Θ) (weight : I → ℝ) (d : H) : ℝ :=
  risk theta0 d + ∑ i, weight i * risk (packet i) d

def d000625 [Fintype I] (risk : Θ → H → ℝ) (theta0 : Θ)
    (packet : I → Θ) (weight : I → ℝ) (seed p : H) : ℝ :=
  _root_.GD.N0230.N0560.d000624 risk theta0 packet weight seed -
    _root_.GD.N0230.N0560.d000624 risk theta0 packet weight p

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
theorem d000626 [Fintype I]
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (packet : I → Θ) (weight : I → ℝ) (seed p : H)
    (hseed : seed ∈ D)
    (hbayes : _root_.GD.N0230.N0622.d000607 D risk theta0 packet weight p) :
    0 ≤ _root_.GD.N0230.N0560.d000625 risk theta0 packet weight seed p :=
  sub_nonneg.mpr (hbayes.2 seed hseed)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in

theorem d000627 [Fintype I]
    (risk : Θ → H → ℝ) (theta0 : Θ) (packet : I → Θ)
    (weight : I → ℝ) (seed p : H) (epsilon : ℝ)
    (hcomplement : ∑ i, weight i *
      (risk (packet i) p - (risk (packet i) seed + epsilon)) = 0) :
    _root_.GD.N0230.N0560.d000625 risk theta0 packet weight seed p =
      risk theta0 seed - risk theta0 p - epsilon * ∑ i, weight i := by
  have hsplit : (∑ i, weight i *
      (risk (packet i) p - (risk (packet i) seed + epsilon))) =
      (∑ i, weight i * risk (packet i) p) -
        (∑ i, weight i * risk (packet i) seed) - epsilon * ∑ i, weight i := by
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul]
    ring
  rw [hsplit] at hcomplement
  unfold _root_.GD.N0230.N0560.d000625 _root_.GD.N0230.N0560.d000624
  linarith

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in

theorem d000628 [Fintype I]
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (packet : I → Θ) (weight : I → ℝ) (seed p d : H)
    (hd : d ∈ D) (hdom : ∀ theta, risk theta d ≤ risk theta seed)
    (hbayes : _root_.GD.N0230.N0622.d000607 D risk theta0 packet weight p) :
    risk theta0 seed - risk theta0 d ≤
      _root_.GD.N0230.N0560.d000625 risk theta0 packet weight seed p := by
  have hsum : (∑ i, weight i * risk (packet i) d) ≤
      ∑ i, weight i * risk (packet i) seed :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hdom _) (hbayes.1 i)
  have hmin := hbayes.2 d hd
  unfold _root_.GD.N0230.N0560.d000625 _root_.GD.N0230.N0560.d000624
  linarith

omit [InnerProductSpace ℝ H] in


theorem d000629
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (sample : ℕ → Θ) (seed : H) (hseed : seed ∈ D)
    (p : ℕ → H) (weight : ∀ n, Fin n → ℝ) (epsilon : ℕ → ℝ)
    (hp : Tendsto p atTop (𝓝 seed)) (hcontinuous : Continuous (risk theta0))
    (hepsilon : ∀ n, 0 ≤ epsilon n)
    (hbayes : ∀ n, _root_.GD.N0230.N0622.d000607 D risk theta0
      (fun i : Fin n ↦ sample i) (weight n) (p n))
    (hcomplement : ∀ n, ∑ i : Fin n, weight n i *
      (risk (sample i) (p n) - (risk (sample i) seed + epsilon n)) = 0) :
    Tendsto (fun n ↦ _root_.GD.N0230.N0560.d000625 risk theta0 (fun i : Fin n ↦ sample i)
      (weight n) seed (p n)) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ epsilon n * ∑ i : Fin n, weight n i) atTop (𝓝 0) := by
  have hdrop : Tendsto (fun n ↦ risk theta0 seed - risk theta0 (p n))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ risk theta0 seed)
      atTop (𝓝 (risk theta0 seed))).sub ((hcontinuous.tendsto seed).comp hp)
  have hslack (n : ℕ) : 0 ≤ epsilon n * ∑ i : Fin n, weight n i :=
    mul_nonneg (hepsilon n) (Finset.sum_nonneg fun i _ ↦ (hbayes n).1 i)
  have hnonneg (n : ℕ) := _root_.GD.N0230.N0560.d000626 D risk theta0
    (fun i : Fin n ↦ sample i) (weight n) seed (p n) hseed (hbayes n)
  have heq (n : ℕ) := _root_.GD.N0230.N0560.d000627 risk theta0
    (fun i : Fin n ↦ sample i) (weight n) seed (p n) (epsilon n) (hcomplement n)
  constructor
  · exact squeeze_zero hnonneg (fun n ↦ by rw [heq n]; linarith [hslack n]) hdrop
  · exact squeeze_zero hslack (fun n ↦ by linarith [heq n, hnonneg n]) hdrop



theorem d000630
    [CompleteSpace H] [TopologicalSpace Θ]
    (D : Set H) (risk : Θ → H → ℝ) (sample : ℕ → Θ)
    (theta0 : Θ) (seed : H) (hseed : seed ∈ D)
    (hDclosed : IsClosed D) (hDconvex : Convex ℝ D)
    (hdecision : ∀ theta, Continuous (risk theta))
    (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (hparameter : ∀ d ∈ D, Continuous (fun theta ↦ risk theta d))
    (hdense : DenseRange sample)
    (scale offset : ℝ) (hscale : 0 < scale)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (hadmissible : _root_.GD.N0230.N0556.d000031 (fun theta (d : D) ↦ risk theta d) ⟨seed, hseed⟩)
    (epsilon : ℕ → ℝ) (hpositive : ∀ n, 0 < epsilon n)
    (hanti : Antitone epsilon) (hzero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ (p : ℕ → H) (weight : ∀ n, Fin n → ℝ),
      Tendsto p atTop (𝓝 seed) ∧
      (∀ n, p n ∈ D ∧
        _root_.GD.N0230.N0622.d000607 D risk theta0 (fun i : Fin n ↦ sample i)
          (weight n) (p n) ∧
        ∑ i : Fin n, weight n i *
          (risk (sample i) (p n) - (risk (sample i) seed + epsilon n)) = 0) ∧
      Tendsto (fun n ↦ _root_.GD.N0230.N0560.d000625 risk theta0 (fun i : Fin n ↦ sample i)
        (weight n) seed (p n)) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ epsilon n * ∑ i : Fin n, weight n i) atTop (𝓝 0) := by
  obtain ⟨p, weight, hp, hcertificate⟩ :=
    _root_.GD.N0230.N0622.d000622 D risk sample theta0 seed hseed
      hDclosed hDconvex hdecision hconvex hparameter hdense
      (_root_.GD.N0230.N0622.d000620 D (risk theta0) hDconvex
        scale offset hscale hreference) hadmissible epsilon hpositive hanti hzero
  let w : ∀ n, Fin n → ℝ := fun n i ↦ scale * weight n i
  have hbayes (n : ℕ) : _root_.GD.N0230.N0622.d000607 D risk theta0
      (fun i : Fin n ↦ sample i) (w n) (p n) :=
    _root_.GD.N0230.N0622.d000621 D risk theta0 (fun i : Fin n ↦ sample i)
      (weight n) (p n) (hcertificate n).1.1.1 scale offset hscale hreference
      (hcertificate n).2.1
  have hcomplement (n : ℕ) : ∑ i : Fin n, w n i *
      (risk (sample i) (p n) - (risk (sample i) seed + epsilon n)) = 0 := by
    dsimp [w]
    simp only [mul_assoc, ← Finset.mul_sum, (hcertificate n).2.2, mul_zero]
  exact ⟨p, w, hp, (fun n ↦ ⟨(hcertificate n).1.1.1, hbayes n, hcomplement n⟩),
    _root_.GD.N0230.N0560.d000629 D risk theta0 sample seed hseed
      p w epsilon hp (hdecision theta0) (fun n ↦ (hpositive n).le) hbayes hcomplement⟩



theorem d000631
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (seed : H) (hseed : seed ∈ D) (hD : Convex ℝ D)
    (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (hstrict : ∀ x ∈ D, ∀ y ∈ D, x ≠ y →
      risk theta0 ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) <
        (risk theta0 x + risk theta0 y) / 2)
    (size : ℕ → ℕ) (packet : ∀ n, Fin (size n) → Θ)
    (weight : ∀ n, Fin (size n) → ℝ) (p : ℕ → H)
    (hbayes : ∀ n, _root_.GD.N0230.N0622.d000607 D risk theta0 (packet n) (weight n) (p n))
    (hzero : Tendsto (fun n ↦ _root_.GD.N0230.N0560.d000625 risk theta0 (packet n) (weight n) seed (p n))
      atTop (𝓝 0)) :
    _root_.GD.N0230.N0556.d000031 (fun theta (d : D) ↦ risk theta d) ⟨seed, hseed⟩ := by
  rintro ⟨d, hdom, theta, hbetter⟩
  have hne : (d : H) ≠ seed := by
    intro heq
    change risk theta (d : H) < risk theta seed at hbetter
    rw [heq] at hbetter
    exact (lt_irrefl _) hbetter
  let mid : H := (1 / 2 : ℝ) • (d : H) + (1 / 2 : ℝ) • seed
  have hmid : mid ∈ D := hD d.property hseed (by norm_num) (by norm_num) (by norm_num)
  have hmidDom (theta : Θ) : risk theta mid ≤ risk theta seed := by
    have hc := (hconvex theta).2 d.property hseed
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
    change risk theta mid ≤ (1 / 2 : ℝ) * risk theta d + (1 / 2 : ℝ) * risk theta seed at hc
    have hd := hdom theta
    change risk theta (d : H) ≤ risk theta seed at hd
    linarith
  have hpositive : 0 < risk theta0 seed - risk theta0 mid := by
    have hs := hstrict d d.property seed hseed hne
    have hd := hdom theta0
    change risk theta0 (d : H) ≤ risk theta0 seed at hd
    change risk theta0 mid < (risk theta0 d + risk theta0 seed) / 2 at hs
    linarith
  have hfloor (n : ℕ) := _root_.GD.N0230.N0560.d000628 D risk theta0
    (packet n) (weight n) seed (p n) mid hmid hmidDom (hbayes n)
  exact (not_le_of_gt hpositive) (ge_of_tendsto hzero (Eventually.of_forall hfloor))



def d000632
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ) (seed : H) : Prop :=
  ∃ (size : ℕ → ℕ) (packet : ∀ n, Fin (size n) → Θ)
    (weight : ∀ n, Fin (size n) → ℝ) (p : ℕ → H),
    (∀ n, p n ∈ D ∧ _root_.GD.N0230.N0622.d000607 D risk theta0 (packet n) (weight n) (p n)) ∧
    Tendsto (fun n ↦ _root_.GD.N0230.N0560.d000625 risk theta0 (packet n) (weight n) seed (p n)) atTop (𝓝 0)

theorem d000633
    [CompleteSpace H] [TopologicalSpace Θ]
    (D : Set H) (risk : Θ → H → ℝ) (sample : ℕ → Θ)
    (theta0 : Θ) (seed : H) (hseed : seed ∈ D)
    (hDclosed : IsClosed D) (hDconvex : Convex ℝ D)
    (hdecision : ∀ theta, Continuous (risk theta))
    (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (hparameter : ∀ d ∈ D, Continuous (fun theta ↦ risk theta d))
    (hdense : DenseRange sample)
    (scale offset : ℝ) (hscale : 0 < scale)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (epsilon : ℕ → ℝ) (hpositive : ∀ n, 0 < epsilon n)
    (hanti : Antitone epsilon) (hzero : Tendsto epsilon atTop (𝓝 0)) :
    _root_.GD.N0230.N0556.d000031 (fun theta (d : D) ↦ risk theta d) ⟨seed, hseed⟩ ↔
      _root_.GD.N0230.N0560.d000632 D risk theta0 seed := by
  constructor
  · intro hadmissible
    obtain ⟨p, weight, _, hc, hz, _⟩ :=
      _root_.GD.N0230.N0560.d000630 D risk sample theta0 seed hseed
        hDclosed hDconvex hdecision hconvex hparameter hdense scale offset hscale hreference
        hadmissible epsilon hpositive hanti hzero
    exact ⟨id, (fun n i ↦ sample i), weight, p,
      (fun n ↦ ⟨(hc n).1, (hc n).2.1⟩), hz⟩
  · rintro ⟨size, packet, weight, p, hc, hz⟩
    exact _root_.GD.N0230.N0560.d000631 D risk theta0 seed hseed hDconvex hconvex
      (_root_.GD.N0230.N0622.d000620 D (risk theta0) hDconvex
        scale offset hscale hreference) size packet weight p (fun n ↦ (hc n).2) hz



theorem d000634
    [CompleteSpace H] [TopologicalSpace Θ]
    (D : Set H) (risk : Θ → H → ℝ) (sample : ℕ → Θ)
    (theta0 : Θ) (seed : H) (hseed : seed ∈ D)
    (hDclosed : IsClosed D) (hDconvex : Convex ℝ D)
    (hdecision : ∀ theta, Continuous (risk theta))
    (hconvex : ∀ theta, ConvexOn ℝ D (risk theta))
    (hparameter : ∀ d ∈ D, Continuous (fun theta ↦ risk theta d))
    (hdense : DenseRange sample)
    (scale offset : ℝ) (hscale : 0 < scale)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset) :
    _root_.GD.N0230.N0556.d000031 (fun theta (d : D) ↦ risk theta d) ⟨seed, hseed⟩ ↔
      _root_.GD.N0230.N0560.d000632 D risk theta0 seed := by
  apply _root_.GD.N0230.N0560.d000633
    D risk sample theta0 seed hseed hDclosed hDconvex hdecision hconvex hparameter
    hdense scale offset hscale hreference (fun n ↦ 1 / ((n : ℝ) + 1))
  · intro n
    positivity
  · intro n m hnm
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnm 1)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

end
end GD.N0230.N0560

#print axioms _root_.GD.N0230.N0560.d000630
#print axioms _root_.GD.N0230.N0560.d000631
#print axioms _root_.GD.N0230.N0560.d000634
