import GD.Module0004
import GD.Module0017
import GD.Module0046































open Filter Set Topology
open scoped BigOperators

namespace GD
namespace N0230
namespace N0622

open _root_.GD.N0230.N0556 _root_.GD.N0230.N0614
open _root_.GD.N0230.N0685 _root_.GD.N0230.N0649

noncomputable section

variable {H Θ I : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]


def d000605 (D : Set H) (risk : Θ → H → ℝ)
    (packet : I → Θ) (cap : I → ℝ) : Set H :=
  {d | d ∈ D ∧ ∀ i, risk (packet i) d ≤ cap i}



def d000606 [Fintype I]
    (D : Set H) (risk : Θ → H → ℝ) (packet : I → Θ)
    (weight : I → ℝ) (p : H) : Prop :=
  (∀ i, 0 ≤ weight i) ∧ ∀ d ∈ D,
    ‖p‖ ^ 2 + ∑ i, weight i * risk (packet i) p ≤
      ‖d‖ ^ 2 + ∑ i, weight i * risk (packet i) d



def d000607 [Fintype I]
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ) (packet : I → Θ)
    (weight : I → ℝ) (p : H) : Prop :=
  (∀ i, 0 ≤ weight i) ∧ ∀ d ∈ D,
    risk theta0 p + ∑ i, weight i * risk (packet i) p ≤
      risk theta0 d + ∑ i, weight i * risk (packet i) d

theorem d000608
    (D : Set H) (risk : Θ → H → ℝ)
    (packet : I → Θ) (cap : I → ℝ)
    (hD : IsClosed D) (hrisk : ∀ i, Continuous (risk (packet i))) :
    IsClosed (_root_.GD.N0230.N0622.d000605 D risk packet cap) := by
  have heq : _root_.GD.N0230.N0622.d000605 D risk packet cap =
      D ∩ ⋂ i, (risk (packet i)) ⁻¹' Iic (cap i) := by
    ext d
    simp [_root_.GD.N0230.N0622.d000605]
  rw [heq]
  exact hD.inter (isClosed_iInter fun i ↦ isClosed_Iic.preimage (hrisk i))

theorem d000609
    (D : Set H) (risk : Θ → H → ℝ)
    (packet : I → Θ) (cap : I → ℝ)
    (hD : Convex ℝ D) (hrisk : ∀ i, ConvexOn ℝ D (risk (packet i))) :
    Convex ℝ (_root_.GD.N0230.N0622.d000605 D risk packet cap) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hD hx.1 hy.1 ha hb hab, fun i ↦ ?_⟩
  calc
    risk (packet i) (a • x + b • y) ≤
        a * risk (packet i) x + b * risk (packet i) y :=
      (hrisk i).2 hx.1 hy.1 ha hb hab
    _ ≤ a * cap i + b * cap i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx.2 i) ha)
        (mul_le_mul_of_nonneg_left (hy.2 i) hb)
    _ = cap i := by rw [← add_mul, hab, one_mul]


theorem d000610 (D : Set H) (hD : Convex ℝ D) :
    ConvexOn ℝ D (fun d : H ↦ ‖d‖ ^ 2) := by
  have hnorm : ConvexOn ℝ Set.univ (fun d : H ↦ ‖d‖) :=
    convexOn_univ_norm
  exact (hnorm.pow (fun d _ ↦ norm_nonneg d) 2).subset
    (Set.subset_univ D) hD

private theorem d000611
    (D : Set H) (risk : H → ℝ) (cap : ℝ)
    (hrisk : ConvexOn ℝ D risk) :
    ConvexOn ℝ D (fun d ↦ risk d - cap) := by
  refine ⟨hrisk.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hrisk.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h
  have hc : (a + b) * cap = cap := by rw [hab, one_mul]
  change risk (a • x + b • y) - cap ≤
    a * (risk x - cap) + b * (risk y - cap)
  nlinarith

section FiniteMultipliers

variable [Fintype I] [DecidableEq I]




theorem d000612
    (D : Set H) (risk : Θ → H → ℝ)
    (packet : I → Θ) (cap : I → ℝ) (p : H)
    (hD : Convex ℝ D)
    (hrisk : ∀ i, ConvexOn ℝ D (risk (packet i)))
    (hp : _root_.GD.N0230.N0685.d000511 (_root_.GD.N0230.N0622.d000605 D risk packet cap) 0 p)
    (hslater : ∃ s ∈ D, ∀ i, risk (packet i) s < cap i) :
    ∃ weight : I → ℝ,
      _root_.GD.N0230.N0622.d000606 D risk packet weight p ∧
      ∑ i, weight i * (risk (packet i) p - cap i) = 0 := by
  let constraint : I → H → ℝ := fun i d ↦ risk (packet i) d - cap i
  have hlower : ∀ d ∈ D, (∀ i, constraint i d ≤ 0) → ‖p‖ ^ 2 ≤ ‖d‖ ^ 2 := by
    intro d hd hconstraint
    have hdCap : d ∈ _root_.GD.N0230.N0622.d000605 D risk packet cap := by
      refine ⟨hd, fun i ↦ ?_⟩
      exact sub_nonpos.mp (hconstraint i)
    have htax := _root_.GD.N0230.N0685.d000512 hp hdCap
    simp only [sub_zero] at htax
    linarith [sq_nonneg ‖d - p‖]
  obtain ⟨weight, hweight, hcertificate⟩ :=
    _root_.GD.N0230.N0614.d000150
      D (fun d : H ↦ ‖d‖ ^ 2) constraint hD (_root_.GD.N0230.N0622.d000610 D hD)
      (fun i ↦ _root_.GD.N0230.N0622.d000611 D (risk (packet i)) (cap i) (hrisk i))
      (‖p‖ ^ 2) hlower (by
        obtain ⟨s, hs, hstrict⟩ := hslater
        exact ⟨s, hs, fun i ↦ sub_neg.mpr (hstrict i)⟩)
  have hsum_le : (∑ i, weight i * constraint i p) ≤ 0 := by
    exact Finset.sum_nonpos fun i _ ↦
      mul_nonpos_of_nonneg_of_nonpos (hweight i) (sub_nonpos.mpr (hp.1.2 i))
  have hsum_zero : (∑ i, weight i * constraint i p) = 0 := by
    have h := hcertificate p hp.1.1
    linarith
  refine ⟨weight, ⟨hweight, ?_⟩, hsum_zero⟩
  intro d hd
  have h := hcertificate d hd
  have hsplit (q : H) :
      (∑ i, weight i * constraint i q) =
        (∑ i, weight i * risk (packet i) q) - ∑ i, weight i * cap i := by
    simp only [constraint, mul_sub, Finset.sum_sub_distrib]
  rw [hsplit p] at hsum_zero
  rw [hsplit d] at h
  linarith



theorem d000613 [CompleteSpace H]
    (D : Set H) (risk : Θ → H → ℝ)
    (packet : I → Θ) (cap : I → ℝ)
    (hDclosed : IsClosed D) (hDconvex : Convex ℝ D)
    (hcontinuous : ∀ i, Continuous (risk (packet i)))
    (hconvex : ∀ i, ConvexOn ℝ D (risk (packet i)))
    (hslater : ∃ s ∈ D, ∀ i, risk (packet i) s < cap i) :
    ∃ (p : H) (weight : I → ℝ),
      _root_.GD.N0230.N0685.d000511 (_root_.GD.N0230.N0622.d000605 D risk packet cap) 0 p ∧
      _root_.GD.N0230.N0622.d000606 D risk packet weight p ∧
      ∑ i, weight i * (risk (packet i) p - cap i) = 0 := by
  have hnonempty : (_root_.GD.N0230.N0622.d000605 D risk packet cap).Nonempty := by
    obtain ⟨s, hs, hstrict⟩ := hslater
    exact ⟨s, hs, fun i ↦ (hstrict i).le⟩
  obtain ⟨p, hp⟩ := _root_.GD.N0230.N0685.d000521 hnonempty
    (_root_.GD.N0230.N0622.d000608 D risk packet cap hDclosed hcontinuous).isComplete
    (_root_.GD.N0230.N0622.d000609 D risk packet cap hDconvex hconvex) 0
  obtain ⟨weight, hbayes, hcomplement⟩ :=
    _root_.GD.N0230.N0622.d000612 D risk packet cap p
      hDconvex hconvex hp hslater
  exact ⟨p, weight, hp, hbayes, hcomplement⟩

end FiniteMultipliers


def d000614 (D : Set H) (risk : Θ → H → ℝ)
    (sample : ℕ → Θ) (seed : H) (epsilon : ℕ → ℝ) (n : ℕ) : Set H :=
  _root_.GD.N0230.N0622.d000605 D risk (fun i : Fin n ↦ sample i)
    (fun i ↦ risk (sample i) seed + epsilon n)

theorem d000615
    (D : Set H) (risk : Θ → H → ℝ) (sample : ℕ → Θ)
    (seed : H) (epsilon : ℕ → ℝ) (hseed : seed ∈ D)
    (hepsilon : ∀ n, 0 ≤ epsilon n) (n : ℕ) :
    seed ∈ _root_.GD.N0230.N0622.d000614 D risk sample seed epsilon n := by
  exact ⟨hseed, fun i ↦ le_add_of_nonneg_right (hepsilon n)⟩

theorem d000616
    (D : Set H) (risk : Θ → H → ℝ) (sample : ℕ → Θ)
    (seed : H) (epsilon : ℕ → ℝ) (hepsilon : Antitone epsilon) :
    Antitone (_root_.GD.N0230.N0622.d000614 D risk sample seed epsilon) := by
  intro n m hnm d hd
  refine ⟨hd.1, fun i ↦ ?_⟩
  apply (hd.2 ⟨i, lt_of_lt_of_le i.isLt hnm⟩).trans
  change risk (sample (i : ℕ)) seed + epsilon m ≤
    risk (sample (i : ℕ)) seed + epsilon n
  exact add_le_add le_rfl (hepsilon hnm)


theorem d000617
    (D : Set H) (risk : Θ → H → ℝ) (sample : ℕ → Θ)
    (seed : H) (epsilon : ℕ → ℝ)
    (hepsilon : ∀ n, 0 ≤ epsilon n)
    (hzero : Tendsto epsilon atTop (𝓝 0)) (d : H) :
    d ∈ ⋂ n, _root_.GD.N0230.N0622.d000614 D risk sample seed epsilon n ↔
      d ∈ D ∧ ∀ i, risk (sample i) d ≤ risk (sample i) seed := by
  constructor
  · intro hd
    refine ⟨(Set.mem_iInter.mp hd 0).1, fun i ↦ ?_⟩
    have hlimit : Tendsto (fun n ↦ risk (sample i) seed + epsilon n)
        atTop (𝓝 (risk (sample i) seed)) := by
      simpa only [add_zero] using tendsto_const_nhds.add hzero
    apply ge_of_tendsto hlimit
    filter_upwards [eventually_ge_atTop (i + 1)] with n hn
    exact (Set.mem_iInter.mp hd n).2 ⟨i, by omega⟩
  · rintro ⟨hd, hcap⟩
    exact Set.mem_iInter.mpr fun n ↦
      ⟨hd, fun i ↦ (hcap i).trans (le_add_of_nonneg_right (hepsilon n))⟩


theorem d000618 [TopologicalSpace Θ]
    (D : Set H) (risk : Θ → H → ℝ) (sample : ℕ → Θ)
    (hdense : DenseRange sample) (seed d : H)
    (hseed : seed ∈ D) (hd : d ∈ D)
    (hcontinuous : ∀ q ∈ D, Continuous (fun θ ↦ risk θ q))
    (hsample : ∀ i, risk (sample i) d ≤ risk (sample i) seed) :
    ∀ θ, risk θ d ≤ risk θ seed := by
  intro θ
  by_contra hθ
  have hopen : IsOpen {η | risk η seed < risk η d} :=
    isOpen_lt (hcontinuous seed hseed) (hcontinuous d hd)
  obtain ⟨i, hi⟩ := hdense.exists_mem_open hopen ⟨θ, lt_of_not_ge hθ⟩
  exact (not_lt_of_ge (hsample i)) hi



theorem d000619
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ)
    (seed : H) (hseed : seed ∈ D) (hD : Convex ℝ D)
    (hconvex : ∀ θ, ConvexOn ℝ D (risk θ))
    (hstrict : ∀ x ∈ D, ∀ y ∈ D, x ≠ y →
      risk theta0 ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) <
        (risk theta0 x + risk theta0 y) / 2)
    (hadmissible : _root_.GD.N0230.N0556.d000031 (fun θ (d : D) ↦ risk θ d) ⟨seed, hseed⟩)
    (d : H) (hd : d ∈ D) (hdom : ∀ θ, risk θ d ≤ risk θ seed) :
    d = seed := by
  by_contra hne
  let m : H := (1 / 2 : ℝ) • d + (1 / 2 : ℝ) • seed
  have hm : m ∈ D := hD hd hseed (by norm_num) (by norm_num) (by norm_num)
  apply hadmissible
  refine ⟨⟨m, hm⟩, ?_, theta0, ?_⟩
  · intro θ
    have h := (hconvex θ).2 hd hseed
      (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)
    change risk θ m ≤ risk θ seed
    change risk θ m ≤ (1 / 2 : ℝ) * risk θ d + (1 / 2 : ℝ) * risk θ seed at h
    linarith [hdom θ]
  · have h := hstrict d hd seed hseed hne
    change risk theta0 m < risk theta0 seed
    change risk theta0 m < (risk theta0 d + risk theta0 seed) / 2 at h
    linarith [hdom theta0]



theorem d000620
    (D : Set H) (risk : H → ℝ) (hD : Convex ℝ D)
    (scale offset : ℝ) (hscale : 0 < scale)
    (hreference : ∀ d ∈ D, risk d = scale * ‖d‖ ^ 2 + offset)
    (x : H) (hx : x ∈ D) (y : H) (hy : y ∈ D) (hne : x ≠ y) :
    risk ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) < (risk x + risk y) / 2 := by
  have hmD : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ D :=
    hD hx hy (by norm_num) (by norm_num) (by norm_num)
  have hmnorm : ‖(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y‖ ^ 2 =
      (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 - ‖x - y‖ ^ 2 / 4 := by
    rw [← smul_add, norm_smul, Real.norm_eq_abs]
    norm_num
    nlinarith [parallelogram_law_with_norm ℝ x y]
  have hgap : 0 < scale * ‖x - y‖ ^ 2 :=
    mul_pos hscale (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
  rw [hreference _ hmD, hreference x hx, hreference y hy, hmnorm]
  nlinarith



theorem d000621 [Fintype I]
    (D : Set H) (risk : Θ → H → ℝ) (theta0 : Θ) (packet : I → Θ)
    (weight : I → ℝ) (p : H) (hp : p ∈ D)
    (scale offset : ℝ) (hscale : 0 < scale)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (hbayes : _root_.GD.N0230.N0622.d000606 D risk packet weight p) :
    _root_.GD.N0230.N0622.d000607 D risk theta0 packet
      (fun i ↦ scale * weight i) p := by
  refine ⟨fun i ↦ mul_nonneg hscale.le (hbayes.1 i), ?_⟩
  intro d hd
  have hsum (q : H) :
      (∑ i, (scale * weight i) * risk (packet i) q) =
        scale * ∑ i, weight i * risk (packet i) q := by
    simp only [mul_assoc, Finset.mul_sum]
  rw [hreference p hp, hreference d hd, hsum p, hsum d]
  have h := mul_le_mul_of_nonneg_left (hbayes.2 d hd) hscale.le
  nlinarith








theorem d000622
    [CompleteSpace H] [TopologicalSpace Θ]
    (D : Set H) (risk : Θ → H → ℝ) (sample : ℕ → Θ)
    (theta0 : Θ) (seed : H) (hseed : seed ∈ D)
    (hDclosed : IsClosed D) (hDconvex : Convex ℝ D)
    (hdecision : ∀ θ, Continuous (risk θ))
    (hconvex : ∀ θ, ConvexOn ℝ D (risk θ))
    (hparameter : ∀ d ∈ D, Continuous (fun θ ↦ risk θ d))
    (hdense : DenseRange sample)
    (hstrict : ∀ x ∈ D, ∀ y ∈ D, x ≠ y →
      risk theta0 ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) <
        (risk theta0 x + risk theta0 y) / 2)
    (hadmissible : _root_.GD.N0230.N0556.d000031 (fun θ (d : D) ↦ risk θ d) ⟨seed, hseed⟩)
    (epsilon : ℕ → ℝ) (hpositive : ∀ n, 0 < epsilon n)
    (hanti : Antitone epsilon) (hzero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ (p : ℕ → H) (weight : ∀ n, Fin n → ℝ),
      Tendsto p atTop (𝓝 seed) ∧ ∀ n,
        _root_.GD.N0230.N0685.d000511 (_root_.GD.N0230.N0622.d000614 D risk sample seed epsilon n) 0 (p n) ∧
        _root_.GD.N0230.N0622.d000606 D risk (fun i : Fin n ↦ sample i)
          (weight n) (p n) ∧
        ∑ i : Fin n, weight n i *
          (risk (sample i) (p n) - (risk (sample i) seed + epsilon n)) = 0 := by
  classical
  have hexists (n : ℕ) := _root_.GD.N0230.N0622.d000613
    D risk (fun i : Fin n ↦ sample i)
    (fun i ↦ risk (sample i) seed + epsilon n)
    hDclosed hDconvex (fun i ↦ hdecision (sample i))
    (fun i ↦ hconvex (sample i))
    ⟨seed, hseed, fun i ↦ lt_add_of_pos_right _ (hpositive n)⟩
  choose p weight hp hbayes hcomplement using hexists
  have hclosed (n : ℕ) : IsClosed (_root_.GD.N0230.N0622.d000614 D risk sample seed epsilon n) :=
    _root_.GD.N0230.N0622.d000608 D risk (fun i : Fin n ↦ sample i)
      (fun i ↦ risk (sample i) seed + epsilon n)
      hDclosed (fun i ↦ hdecision (sample i))
  have hinter : (⋂ n, _root_.GD.N0230.N0622.d000614 D risk sample seed epsilon n) = {seed} := by
    ext d
    rw [_root_.GD.N0230.N0622.d000617 D risk sample seed epsilon
      (fun n ↦ (hpositive n).le) hzero d, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hd, hsample⟩
      exact _root_.GD.N0230.N0622.d000619 D risk theta0 seed hseed
        hDconvex hconvex hstrict hadmissible d hd
        (_root_.GD.N0230.N0622.d000618 D risk sample hdense seed d hseed hd hparameter hsample)
    · rintro rfl
      exact ⟨hseed, fun _ ↦ le_rfl⟩
  have hseedProjection :
      _root_.GD.N0230.N0685.d000511 (⋂ n, _root_.GD.N0230.N0622.d000614 D risk sample seed epsilon n) 0 seed := by
    rw [hinter]
    refine ⟨by simp, ?_⟩
    intro d hd
    have hdseed : d = seed := Set.mem_singleton_iff.mp hd
    subst d
    simp
  refine ⟨p, weight, ?_, fun n ↦ ⟨hp n, hbayes n, hcomplement n⟩⟩
  exact _root_.GD.N0230.N0649.d000583 (_root_.GD.N0230.N0622.d000614 D risk sample seed epsilon)
    p seed (_root_.GD.N0230.N0622.d000616 D risk sample seed epsilon hanti)
    hclosed hp hseedProjection





theorem d000623
    [CompleteSpace H] [TopologicalSpace Θ]
    (D : Set H) (risk : Θ → H → ℝ) (sample : ℕ → Θ)
    (theta0 : Θ) (seed : H) (hseed : seed ∈ D)
    (hDclosed : IsClosed D) (hDconvex : Convex ℝ D)
    (hdecision : ∀ θ, Continuous (risk θ))
    (hconvex : ∀ θ, ConvexOn ℝ D (risk θ))
    (hparameter : ∀ d ∈ D, Continuous (fun θ ↦ risk θ d))
    (hdense : DenseRange sample)
    (scale offset : ℝ) (hscale : 0 < scale)
    (hreference : ∀ d ∈ D, risk theta0 d = scale * ‖d‖ ^ 2 + offset)
    (hadmissible : _root_.GD.N0230.N0556.d000031 (fun θ (d : D) ↦ risk θ d) ⟨seed, hseed⟩)
    (epsilon : ℕ → ℝ) (hpositive : ∀ n, 0 < epsilon n)
    (hanti : Antitone epsilon) (hzero : Tendsto epsilon atTop (𝓝 0)) :
    ∃ (p : ℕ → H) (weight : ∀ n, Fin n → ℝ),
      Tendsto p atTop (𝓝 seed) ∧ ∀ n,
        _root_.GD.N0230.N0685.d000511 (_root_.GD.N0230.N0622.d000614 D risk sample seed epsilon n) 0 (p n) ∧
        _root_.GD.N0230.N0622.d000607 D risk theta0 (fun i : Fin n ↦ sample i)
          (weight n) (p n) := by
  obtain ⟨p, weight, hlimit, hcertificate⟩ :=
    _root_.GD.N0230.N0622.d000622 D risk sample theta0 seed hseed
      hDclosed hDconvex hdecision hconvex hparameter hdense
      (_root_.GD.N0230.N0622.d000620 D (risk theta0) hDconvex
        scale offset hscale hreference)
      hadmissible epsilon hpositive hanti hzero
  refine ⟨p, (fun n i ↦ scale * weight n i), hlimit, fun n ↦ ?_⟩
  refine ⟨(hcertificate n).1, ?_⟩
  exact _root_.GD.N0230.N0622.d000621 D risk theta0 (fun i : Fin n ↦ sample i)
    (weight n) (p n) (hcertificate n).1.1.1 scale offset hscale hreference
    (hcertificate n).2.1

end

end N0622
end N0230
end GD

#print axioms _root_.GD.N0230.N0622.d000612
#print axioms _root_.GD.N0230.N0622.d000613
#print axioms _root_.GD.N0230.N0622.d000619
#print axioms _root_.GD.N0230.N0622.d000622
#print axioms _root_.GD.N0230.N0622.d000623
