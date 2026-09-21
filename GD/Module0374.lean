import GD.Module0373
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic










































set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Set Filter Topology Polynomial Matrix
open scoped ENNReal BigOperators

namespace GD.N0106.N0428.N0765.N1555
open _root_.GD.N0106.N0428.N0765.N1534 _root_.GD.N0106.N0428.N0765.N1547 _root_.GD.N0106.N0428.N0765.N1614 _root_.GD.N0106.N0428.N0765.N1556
noncomputable section




def d005682 (η s : ℝ) : ℝ := 10 * (1 + η) * (η + s) / (η * (1 + s))

theorem d005683 {η s : ℝ} (hη : 0 < η) (hs : 0 < s) : 0 < _root_.GD.N0106.N0428.N0765.N1555.d005682 η s := by
  unfold _root_.GD.N0106.N0428.N0765.N1555.d005682
  have h1 : 0 < 1 + η := by linarith
  have h2 : 0 < η + s := by linarith
  have h3 : 0 < 1 + s := by linarith
  positivity


theorem d005684 {η u s : ℝ} (hη : 0 < η) (hs : 0 < s) :
    _root_.GD.N0106.N0428.N0765.N1556.d005641 η u s + η * _root_.GD.N0106.N0428.N0765.N1556.d005642 η u s = (1 - u) * η * (1 + s) / (η + s) := by
  unfold _root_.GD.N0106.N0428.N0765.N1556.d005641 _root_.GD.N0106.N0428.N0765.N1556.d005642
  have h2 : η + s ≠ 0 := (by linarith : (0 : ℝ) < η + s).ne'
  field_simp


theorem d005685 {η u s : ℝ} (hη : 0 < η) (hu : u < 1) (hs : 0 < s) :
    _root_.GD.N0106.N0428.N0765.N1556.d005644 η u s = _root_.GD.N0106.N0428.N0765.N1555.d005682 η s * (u / (1 - u)) := by
  rw [_root_.GD.N0106.N0428.N0765.N1556.d005644, _root_.GD.N0106.N0428.N0765.N1555.d005684 hη hs, _root_.GD.N0106.N0428.N0765.N1555.d005682]
  have h1 : (1 - u) ≠ 0 := (sub_pos.mpr hu).ne'
  have h2 : η + s ≠ 0 := (by linarith : (0 : ℝ) < η + s).ne'
  have h3 : η ≠ 0 := hη.ne'
  have h4 : 1 + s ≠ 0 := (by linarith : (0 : ℝ) < 1 + s).ne'
  field_simp


theorem d005686 {η u s : ℝ} (hη : 0 < η) (hu : u < 1) (hs : 0 < s) :
    HasDerivAt (fun u => _root_.GD.N0106.N0428.N0765.N1556.d005644 η u s) (_root_.GD.N0106.N0428.N0765.N1555.d005682 η s / (1 - u) ^ 2) u := by
  have h1 : (1 - u) ≠ 0 := (sub_pos.mpr hu).ne'
  have hd : HasDerivAt (fun u : ℝ => u / (1 - u)) (1 / (1 - u) ^ 2) u := by
    have := (hasDerivAt_id u).div ((hasDerivAt_id u).const_sub 1) h1
    refine this.congr_deriv ?_
    simp only [id]
    field_simp <;> ring
  have hmul := hd.const_mul (_root_.GD.N0106.N0428.N0765.N1555.d005682 η s)
  refine HasDerivAt.congr_of_eventuallyEq (f := fun y => _root_.GD.N0106.N0428.N0765.N1555.d005682 η s * (y / (1 - y))) ?_ ?_
  · exact hmul.congr_deriv (by ring)
  · filter_upwards [eventually_lt_nhds hu] with u' hu'
    exact _root_.GD.N0106.N0428.N0765.N1555.d005685 hη hu' hs


theorem d005687 {η u s : ℝ} (hη : 0 < η) (hu : u < 1) (hs : 0 < s) :
    0 < deriv (fun u => _root_.GD.N0106.N0428.N0765.N1556.d005644 η u s) u := by
  rw [(_root_.GD.N0106.N0428.N0765.N1555.d005686 hη hu hs).deriv]
  exact div_pos (_root_.GD.N0106.N0428.N0765.N1555.d005683 hη hs) (pow_pos (sub_pos.mpr hu) 2)


theorem d005688 {η s : ℝ} (hη : 0 < η) (hs : 0 < s) :
    0 < deriv (fun u => _root_.GD.N0106.N0428.N0765.N1556.d005644 η u s) 0 :=
  _root_.GD.N0106.N0428.N0765.N1555.d005687 hη (by norm_num) hs




def d005689 (η : ℝ) (g : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (g.1 / (g.1 + g.2.1 + g.2.2), η * g.2.2 / g.2.1)


def d005690 : Set (ℝ × (ℝ × ℝ)) := Ioi 0 ×ˢ (Ioi 0 ×ˢ Ioi 0)

theorem d005691 {g : ℝ × (ℝ × ℝ)} : g ∈ _root_.GD.N0106.N0428.N0765.N1555.d005690 ↔ 0 < g.1 ∧ 0 < g.2.1 ∧ 0 < g.2.2 := by
  simp [_root_.GD.N0106.N0428.N0765.N1555.d005690, Set.mem_prod]

theorem d005692 : IsOpen _root_.GD.N0106.N0428.N0765.N1555.d005690 :=
  isOpen_Ioi.prod (isOpen_Ioi.prod isOpen_Ioi)

theorem d005693 (η : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1555.d005689 η) := by
  unfold _root_.GD.N0106.N0428.N0765.N1555.d005689
  fun_prop

theorem d005694 (η : ℝ) : ContinuousOn (_root_.GD.N0106.N0428.N0765.N1555.d005689 η) _root_.GD.N0106.N0428.N0765.N1555.d005690 := by
  have h1 : ContinuousOn (fun g : ℝ × (ℝ × ℝ) => g.1 / (g.1 + g.2.1 + g.2.2)) _root_.GD.N0106.N0428.N0765.N1555.d005690 := by
    refine ContinuousOn.div continuousOn_fst
      ((continuousOn_fst.add (continuous_fst.comp continuous_snd).continuousOn).add
        (continuous_snd.comp continuous_snd).continuousOn) ?_
    intro g hg
    obtain ⟨h1, h2, h3⟩ := _root_.GD.N0106.N0428.N0765.N1555.d005691.mp hg
    exact (by linarith : (0 : ℝ) < g.1 + g.2.1 + g.2.2).ne'
  have h2 : ContinuousOn (fun g : ℝ × (ℝ × ℝ) => η * g.2.2 / g.2.1) _root_.GD.N0106.N0428.N0765.N1555.d005690 := by
    refine ContinuousOn.div
      (continuousOn_const.mul (continuous_snd.comp continuous_snd).continuousOn)
      (continuous_fst.comp continuous_snd).continuousOn ?_
    intro g hg
    exact (_root_.GD.N0106.N0428.N0765.N1555.d005691.mp hg).2.1.ne'
  exact h1.prodMk h2


def d005695 (η : ℝ) (p : ℝ × ℝ) : ℝ × (ℝ × ℝ) := (p.1, (_root_.GD.N0106.N0428.N0765.N1556.d005641 η p.1 p.2, _root_.GD.N0106.N0428.N0765.N1556.d005642 η p.1 p.2))

theorem d005696 {η : ℝ} (hη : 0 < η) {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1556.d005646) :
    _root_.GD.N0106.N0428.N0765.N1555.d005695 η p ∈ _root_.GD.N0106.N0428.N0765.N1555.d005690 := by
  obtain ⟨h1, h2, h3⟩ := hp
  exact _root_.GD.N0106.N0428.N0765.N1555.d005691.mpr ⟨h1, _root_.GD.N0106.N0428.N0765.N1556.d005665 hη h2 h3, _root_.GD.N0106.N0428.N0765.N1556.d005666 hη h2 h3⟩

theorem d005697 {η : ℝ} (hη : 0 < η) {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1556.d005646) :
    _root_.GD.N0106.N0428.N0765.N1555.d005689 η (_root_.GD.N0106.N0428.N0765.N1555.d005695 η p) = p := by
  obtain ⟨h1, h2, h3⟩ := hp
  unfold _root_.GD.N0106.N0428.N0765.N1555.d005689 _root_.GD.N0106.N0428.N0765.N1555.d005695
  simp only
  rw [_root_.GD.N0106.N0428.N0765.N1556.d005667 hη p.1 h3, div_one, _root_.GD.N0106.N0428.N0765.N1556.d005668 hη h2 h3]


def d005698 (a b c r : ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  (gammaMeasure a r).prod ((gammaMeasure b r).prod (gammaMeasure c r))

theorem d005699 (a r : ℝ) : Measurable (gammaPDF a r) := by
  unfold gammaPDF
  exact (measurable_gammaPDFReal a r).ennreal_ofReal


theorem d005700 {a r x y : ℝ} (ha : 0 < a) (hr : 0 < r) (hxy : x < y)
    (hsub : Ioo x y ⊆ Ioi 0) : 0 < gammaMeasure a r (Ioo x y) := by
  unfold gammaMeasure
  rw [withDensity_apply _ measurableSet_Ioo, setLIntegral_pos_iff (_root_.GD.N0106.N0428.N0765.N1555.d005699 a r)]
  have hsupp : Ioo x y ⊆ Function.support (gammaPDF a r) ∩ Ioo x y := by
    intro z hz
    have hz0 : 0 < z := hsub hz
    refine ⟨?_, hz⟩
    rw [Function.mem_support, gammaPDF_of_nonneg hz0.le, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := gammaPDFReal_pos ha hr hz0
    simpa [gammaPDFReal, if_pos hz0.le] using this
  refine lt_of_lt_of_le ?_ (measure_mono hsupp)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)


theorem d005701 {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : 0 < r) {W : Set (ℝ × (ℝ × ℝ))} (hW : IsOpen W) (hsub : W ⊆ _root_.GD.N0106.N0428.N0765.N1555.d005690)
    (hne : W.Nonempty) : 0 < _root_.GD.N0106.N0428.N0765.N1555.d005698 a b c r W := by
  obtain ⟨g, hg⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW g hg
  set box : Set (ℝ × (ℝ × ℝ)) :=
    Ioo (g.1 - ε) (g.1 + ε) ×ˢ (Ioo (g.2.1 - ε) (g.2.1 + ε) ×ˢ Ioo (g.2.2 - ε) (g.2.2 + ε))
    with hbox
  have hball' : box ⊆ Metric.ball g ε := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq,
      max_lt_iff, max_lt_iff, abs_sub_lt_iff, abs_sub_lt_iff, abs_sub_lt_iff]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  have hoct : ∀ z ∈ box, 0 < z.1 ∧ 0 < z.2.1 ∧ 0 < z.2.2 :=
    fun z hz => _root_.GD.N0106.N0428.N0765.N1555.d005691.mp (hsub (hball (hball' hz)))
  have hb1 : Ioo (g.1 - ε) (g.1 + ε) ⊆ Ioi 0 := fun x hx =>
    (hoct (x, g.2) ⟨hx, ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩⟩).1
  have hb2 : Ioo (g.2.1 - ε) (g.2.1 + ε) ⊆ Ioi 0 := fun x hx =>
    (hoct (g.1, (x, g.2.2)) ⟨⟨by linarith, by linarith⟩, ⟨hx, ⟨by linarith, by linarith⟩⟩⟩).2.1
  have hb3 : Ioo (g.2.2 - ε) (g.2.2 + ε) ⊆ Ioi 0 := fun x hx =>
    (hoct (g.1, (g.2.1, x)) ⟨⟨by linarith, by linarith⟩, ⟨⟨by linarith, by linarith⟩, hx⟩⟩).2.2
  haveI := isProbabilityMeasure_gammaMeasure ha hr
  haveI := isProbabilityMeasure_gammaMeasure hb hr
  haveI := isProbabilityMeasure_gammaMeasure hc hr
  calc (0 : ℝ≥0∞) < _root_.GD.N0106.N0428.N0765.N1555.d005698 a b c r box := by
        rw [hbox]
        unfold _root_.GD.N0106.N0428.N0765.N1555.d005698
        rw [Measure.prod_prod, Measure.prod_prod]
        exact ENNReal.mul_pos (_root_.GD.N0106.N0428.N0765.N1555.d005700 ha hr (by linarith) hb1).ne'
          (ENNReal.mul_pos (_root_.GD.N0106.N0428.N0765.N1555.d005700 hb hr (by linarith) hb2).ne'
            (_root_.GD.N0106.N0428.N0765.N1555.d005700 hc hr (by linarith) hb3).ne').ne'
    _ ≤ _root_.GD.N0106.N0428.N0765.N1555.d005698 a b c r W := measure_mono (hball'.trans hball)


def d005702 (η a b c r : ℝ) : Measure (ℝ × ℝ) := (_root_.GD.N0106.N0428.N0765.N1555.d005698 a b c r).map (_root_.GD.N0106.N0428.N0765.N1555.d005689 η)


theorem d005703 {η a b c r : ℝ} (hη : 0 < η) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : 0 < r) :
    ∀ V : Set (ℝ × ℝ), IsOpen V → (V ∩ _root_.GD.N0106.N0428.N0765.N1556.d005646).Nonempty → 0 < _root_.GD.N0106.N0428.N0765.N1555.d005702 η a b c r V := by
  intro V hV hne
  unfold _root_.GD.N0106.N0428.N0765.N1555.d005702
  rw [Measure.map_apply (_root_.GD.N0106.N0428.N0765.N1555.d005693 η) hV.measurableSet]
  have hW : IsOpen (_root_.GD.N0106.N0428.N0765.N1555.d005690 ∩ _root_.GD.N0106.N0428.N0765.N1555.d005689 η ⁻¹' V) :=
    (_root_.GD.N0106.N0428.N0765.N1555.d005694 η).isOpen_inter_preimage _root_.GD.N0106.N0428.N0765.N1555.d005692 hV
  obtain ⟨p, hpV, hpI⟩ := hne
  have hne' : (_root_.GD.N0106.N0428.N0765.N1555.d005690 ∩ _root_.GD.N0106.N0428.N0765.N1555.d005689 η ⁻¹' V).Nonempty :=
    ⟨_root_.GD.N0106.N0428.N0765.N1555.d005695 η p, _root_.GD.N0106.N0428.N0765.N1555.d005696 hη hpI, by simp only [mem_preimage, _root_.GD.N0106.N0428.N0765.N1555.d005697 hη hpI]; exact hpV⟩
  exact lt_of_lt_of_le (_root_.GD.N0106.N0428.N0765.N1555.d005701 ha hb hc hr hW inter_subset_left hne')
    (measure_mono inter_subset_right)



def d005704 (η : ℝ) : Measure (ℝ × ℝ) := _root_.GD.N0106.N0428.N0765.N1555.d005702 η (3 / 2) 5 5 (1 / 2)

theorem d005705 {η : ℝ} (hη : 0 < η) :
    ∀ V : Set (ℝ × ℝ), IsOpen V → (V ∩ _root_.GD.N0106.N0428.N0765.N1556.d005646).Nonempty → 0 < _root_.GD.N0106.N0428.N0765.N1555.d005704 η V :=
  _root_.GD.N0106.N0428.N0765.N1555.d005703 hη (by norm_num) (by norm_num) (by norm_num) (by norm_num)



theorem d005706 {η a b c r : ℝ} (hη : 0 < η) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hr : 0 < r) {A B : ℝ[X]}
    (h : ∀ᵐ p ∂_root_.GD.N0106.N0428.N0765.N1555.d005702 η a b c r,
      A.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2) * _root_.GD.N0106.N0428.N0765.N1556.d005644 η p.1 p.2 - B.eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2) = 0) :
    A = 0 ∧ B = 0 :=
  _root_.GD.N0106.N0428.N0765.N1556.d005681 hη (_root_.GD.N0106.N0428.N0765.N1555.d005703 hη ha hb hc hr)
    (h.mono fun _ hp _ => hp)





def d005707 (k : ℕ) (h : ℝ) : ℝ := h ^ (k + 1) * (1 - h)


def d005708 (a : Fin 5 → ℝ) : ℝ[X] :=
  ∑ k : Fin 5, Polynomial.C (a k) * (X ^ ((k : ℕ) + 1) * (1 - X : ℝ[X]))

theorem d005709 (a : Fin 5 → ℝ) (h : ℝ) :
    (_root_.GD.N0106.N0428.N0765.N1555.d005708 a).eval h = ∑ k : Fin 5, a k * _root_.GD.N0106.N0428.N0765.N1555.d005707 k h := by
  simp [_root_.GD.N0106.N0428.N0765.N1555.d005708, _root_.GD.N0106.N0428.N0765.N1555.d005707, eval_finset_sum]


theorem d005710 {a : Fin 5 → ℝ} (h0 : _root_.GD.N0106.N0428.N0765.N1555.d005708 a = 0) : a = 0 := by
  have hfac : _root_.GD.N0106.N0428.N0765.N1555.d005708 a = (X * (1 - X : ℝ[X])) * ∑ k : Fin 5, Polynomial.C (a k) * X ^ (k : ℕ) := by
    unfold _root_.GD.N0106.N0428.N0765.N1555.d005708
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hX : (X * (1 - X) : ℝ[X]) ≠ 0 := by
    intro h
    have := congrArg (eval (1 / 2 : ℝ)) h
    norm_num at this
  rw [hfac, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 hX
  · funext k
    have := congrArg (fun q : ℝ[X] => q.coeff (k : ℕ)) h0
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single k] at this
    · simpa using this
    · intro j _ hj
      rw [if_neg]
      exact fun h => hj (Fin.ext h).symm
    · intro h
      exact absurd (Finset.mem_univ k) h




abbrev d005711 := Fin 5 ⊕ Fin 5


def d005712 (η : ℝ) : _root_.GD.N0106.N0428.N0765.N1555.d005711 → ℝ × ℝ → ℝ
  | Sum.inl k => fun p => _root_.GD.N0106.N0428.N0765.N1555.d005707 k (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2) * _root_.GD.N0106.N0428.N0765.N1556.d005644 η p.1 p.2
  | Sum.inr k => fun p => _root_.GD.N0106.N0428.N0765.N1555.d005707 k (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2)


def d005713 (η : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1555.d005711 → ℝ) (p : ℝ × ℝ) : ℝ := ∑ i, x i * _root_.GD.N0106.N0428.N0765.N1555.d005712 η i p


theorem d005714 (η : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1555.d005711 → ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0765.N1555.d005713 η x p =
      (_root_.GD.N0106.N0428.N0765.N1555.d005708 fun k => x (Sum.inl k)).eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2) * _root_.GD.N0106.N0428.N0765.N1556.d005644 η p.1 p.2 -
        (_root_.GD.N0106.N0428.N0765.N1555.d005708 fun k => -x (Sum.inr k)).eval (_root_.GD.N0106.N0428.N0765.N1556.d005643 η p.1 p.2) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1555.d005713, _root_.GD.N0106.N0428.N0765.N1555.d005709, Fintype.sum_sum_type, _root_.GD.N0106.N0428.N0765.N1555.d005712, Finset.sum_mul, neg_mul,
    Finset.sum_neg_distrib, sub_neg_eq_add]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring


def d005715 (η : ℝ) (μ : Measure (ℝ × ℝ)) : Matrix _root_.GD.N0106.N0428.N0765.N1555.d005711 _root_.GD.N0106.N0428.N0765.N1555.d005711 ℝ :=
  fun i j => ∫ p, _root_.GD.N0106.N0428.N0765.N1555.d005712 η i p * _root_.GD.N0106.N0428.N0765.N1555.d005712 η j p ∂μ

theorem d005716 (η : ℝ) (μ : Measure (ℝ × ℝ)) : (_root_.GD.N0106.N0428.N0765.N1555.d005715 η μ).IsHermitian :=
  Matrix.IsHermitian.ext fun i j => by simp only [_root_.GD.N0106.N0428.N0765.N1555.d005715, star_trivial, mul_comm]

theorem d005717 (η : ℝ) (x : _root_.GD.N0106.N0428.N0765.N1555.d005711 → ℝ) (p : ℝ × ℝ) :
    (_root_.GD.N0106.N0428.N0765.N1555.d005713 η x p) ^ 2 = ∑ i, ∑ j, x i * x j * (_root_.GD.N0106.N0428.N0765.N1555.d005712 η i p * _root_.GD.N0106.N0428.N0765.N1555.d005712 η j p) := by
  simp only [_root_.GD.N0106.N0428.N0765.N1555.d005713, sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem d005718 {η : ℝ} {μ : Measure (ℝ × ℝ)}
    (hint : ∀ i j, Integrable (fun p => _root_.GD.N0106.N0428.N0765.N1555.d005712 η i p * _root_.GD.N0106.N0428.N0765.N1555.d005712 η j p) μ) (x : _root_.GD.N0106.N0428.N0765.N1555.d005711 → ℝ) :
    Integrable (fun p => (_root_.GD.N0106.N0428.N0765.N1555.d005713 η x p) ^ 2) μ := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1555.d005717]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hint i j).const_mul _


theorem d005719 {η : ℝ} {μ : Measure (ℝ × ℝ)}
    (hint : ∀ i j, Integrable (fun p => _root_.GD.N0106.N0428.N0765.N1555.d005712 η i p * _root_.GD.N0106.N0428.N0765.N1555.d005712 η j p) μ) (x : _root_.GD.N0106.N0428.N0765.N1555.d005711 → ℝ) :
    x ⬝ᵥ (_root_.GD.N0106.N0428.N0765.N1555.d005715 η μ *ᵥ x) = ∫ p, (_root_.GD.N0106.N0428.N0765.N1555.d005713 η x p) ^ 2 ∂μ := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1555.d005717]
  rw [integral_finset_sum _ fun i _ =>
    integrable_finset_sum _ fun j _ => (hint i j).const_mul _]
  simp only [dotProduct, mulVec, _root_.GD.N0106.N0428.N0765.N1555.d005715]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => (hint i j).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  ring



theorem d005720 {η : ℝ} (hη : 0 < η) {μ : Measure (ℝ × ℝ)}
    (hμ : ∀ V : Set (ℝ × ℝ), IsOpen V → (V ∩ _root_.GD.N0106.N0428.N0765.N1556.d005646).Nonempty → 0 < μ V)
    (hint : ∀ i j, Integrable (fun p => _root_.GD.N0106.N0428.N0765.N1555.d005712 η i p * _root_.GD.N0106.N0428.N0765.N1555.d005712 η j p) μ) :
    (_root_.GD.N0106.N0428.N0765.N1555.d005715 η μ).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨_root_.GD.N0106.N0428.N0765.N1555.d005716 η μ, fun x hx => ?_⟩
  rw [star_trivial, _root_.GD.N0106.N0428.N0765.N1555.d005719 hint x]
  have hnn : 0 ≤ ∫ p, (_root_.GD.N0106.N0428.N0765.N1555.d005713 η x p) ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg _
  refine lt_of_le_of_ne hnn fun h0 => hx ?_
  have hae : (fun p => (_root_.GD.N0106.N0428.N0765.N1555.d005713 η x p) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg _) (_root_.GD.N0106.N0428.N0765.N1555.d005718 hint x)).mp
      h0.symm
  have hAB := _root_.GD.N0106.N0428.N0765.N1556.d005681 hη hμ
    (A := _root_.GD.N0106.N0428.N0765.N1555.d005708 fun k => x (Sum.inl k)) (B := _root_.GD.N0106.N0428.N0765.N1555.d005708 fun k => -x (Sum.inr k)) ?_
  · funext i
    rcases i with k | k
    · have := congrFun (_root_.GD.N0106.N0428.N0765.N1555.d005710 hAB.1) k
      simpa using this
    · have := congrFun (_root_.GD.N0106.N0428.N0765.N1555.d005710 hAB.2) k
      simpa using this
  · filter_upwards [hae] with p hp _
    rw [← _root_.GD.N0106.N0428.N0765.N1555.d005714]
    have h2 : (_root_.GD.N0106.N0428.N0765.N1555.d005713 η x p) ^ 2 = 0 := by simpa using hp
    exact (pow_eq_zero_iff two_ne_zero).mp h2



theorem d005721 {η : ℝ} (hη : 0 < η)
    (hint : ∀ i j, Integrable (fun p => _root_.GD.N0106.N0428.N0765.N1555.d005712 η i p * _root_.GD.N0106.N0428.N0765.N1555.d005712 η j p) (_root_.GD.N0106.N0428.N0765.N1555.d005704 η)) :
    (_root_.GD.N0106.N0428.N0765.N1555.d005715 η (_root_.GD.N0106.N0428.N0765.N1555.d005704 η)).PosDef :=
  _root_.GD.N0106.N0428.N0765.N1555.d005720 hη (_root_.GD.N0106.N0428.N0765.N1555.d005705 hη) hint

end

end GD.N0106.N0428.N0765.N1555
