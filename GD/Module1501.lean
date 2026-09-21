import GD.Module1460
import GD.Module1498
import GD.Module0149

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0225.N0538
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0675
open _root_.GD.N0230.N0718

variable (k : ℕ) (sizes : Fin k → ℕ)

theorem d023457
    {f g : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (hg : g ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ g ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f)
    (hstrict : ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ g < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f) :
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (fun z => (f z + g z) / 2) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := by
  classical
  obtain ⟨θ₀, hstrict₀⟩ := hstrict
  let p := _root_.GD.N0232.N0719.N0970.d012312 k sizes f hf
  let q := _root_.GD.N0232.N0719.N0970.d012312 k sizes g hg
  have hp (θ) : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f :=
    _root_.GD.N0232.N0719.N0970.d012313 k sizes f hf θ
  have hq (θ) : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ q = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ g :=
    _root_.GD.N0232.N0719.N0970.d012313 k sizes g hg θ
  have hpAE : (p : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] f :=
    (_root_.GD.N0232.N0719.N0896.d011095 k sizes f hf.1
      (hf.2 (_root_.GD.N0232.N0719.N0859.d010810 k))).coeFn_toLp
  have hqAE : (q : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] g :=
    (_root_.GD.N0232.N0719.N0896.d011095 k sizes g hg.1
      (hg.2 (_root_.GD.N0232.N0719.N0859.d010810 k))).coeFn_toLp
  have hpq : p ≠ q := by
    intro heq
    have heqRisk : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ₀ g = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ₀ f := by
      rw [← hq, ← hp, heq]
    exact hstrict₀.ne heqRisk
  have hfiniteP (θ) : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p ≠ ⊤ := by rw [hp]; exact hf.2 θ
  have hfiniteQ (θ) : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ q ≠ ⊤ := by rw [hq]; exact hg.2 θ
  have hweakPQ (θ) : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ q ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p := by
    rw [hp, hq]
    exact hweak θ
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0719.N0896.d011096 k sizes p := by
    apply _root_.GD.N0232.N0719.N0896.d011098 k sizes p (fun _ => le_rfl) hweakPQ
    all_goals norm_num
  have hfiniteMid (θ) : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0230.N0718.d001528 p q) ≠ ⊤ :=
    ne_top_of_le_ne_top (hfiniteP θ) (hmid θ)
  have hstrict := _root_.GD.N0230.N0675.d001657
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes) (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes)
    (fun θ => (_root_.GD.N0232.N0719.d009183
      k sizes θ.location θ.scale θ.scale_pos).2)
    hfiniteP hfiniteQ
    (fun θ => ENNReal.toReal_mono (hfiniteP θ) (hweakPQ θ)) hpq
  have hmidAE : ((_root_.GD.N0230.N0718.d001528 p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
      _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] (fun z => (f z + g z) / 2) := by
    filter_upwards [Lp.coeFn_add ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q),
      Lp.coeFn_smul (1 / 2 : ℝ) p, Lp.coeFn_smul (1 / 2 : ℝ) q,
      hpAE, hqAE] with z hadd hps hqs hpf hqg
    simp only [_root_.GD.N0230.N0718.d001528, hadd, hps, hqs, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, hpf, hqg]
    ring
  intro θ
  have hrmid : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0230.N0718.d001528 p q) =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (fun z => (f z + g z) / 2) :=
    _root_.GD.N0232.N0719.N0896.d011094 k sizes θ
      ((_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hmidAE)
  rw [← hrmid, ← hp]
  exact (ENNReal.toReal_lt_toReal (hfiniteMid θ) (hfiniteP θ)).mp (hstrict θ)


open _root_.GD.N0072

variable {k}

def d023458 (p w : (Fin k → ℝ) → Fin k → ℝ) :
    (Fin k → ℝ) → Fin k → ℝ := fun t i => (p t i + w t i) / 2

@[fun_prop] theorem d023459
    (p w : (Fin k → ℝ) → Fin k → ℝ) (hp : Measurable p) (hw : Measurable w) :
    Measurable (_root_.GD.N0225.N0538.d023458 p w) := by unfold _root_.GD.N0225.N0538.d023458; fun_prop

theorem d023460 (p w : (Fin k → ℝ) → Fin k → ℝ)
    (hp : ∀ t, ∑ i, p t i = 1) (hw : ∀ t, ∑ i, w t i = 1) :
    ∀ t, ∑ i, _root_.GD.N0225.N0538.d023458 p w t i = 1 := by
  intro t
  simp only [_root_.GD.N0225.N0538.d023458, ← Finset.sum_div, Finset.sum_add_distrib, hp, hw]
  norm_num

theorem d023461 (p w : (Fin k → ℝ) → Fin k → ℝ)
    (hp : ∀ t i, 0 ≤ p t i) (hw : ∀ t i, 0 ≤ w t i) :
    ∀ t i, 0 ≤ _root_.GD.N0225.N0538.d023458 p w t i := by
  intro t i
  exact div_nonneg (add_nonneg (hp t i) (hw t i)) (by norm_num)

theorem d023462 (p w : (Fin k → ℝ) → Fin k → ℝ) :
    _root_.GD.N0072.d023291 sizes (_root_.GD.N0225.N0538.d023458 p w) =
      fun z => (_root_.GD.N0072.d023291 sizes p z + _root_.GD.N0072.d023291 sizes w z) / 2 := by
  funext z
  simp only [_root_.GD.N0072.d023291, _root_.GD.N0232.N0719.N0885.d009311, _root_.GD.N0225.N0538.d023458]
  simp_rw [add_div, add_mul, div_mul_eq_mul_div]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]

theorem d023463 (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) (hnonneg : ∀ t i, 0 ≤ w t i) :
    _root_.GD.N0072.d023291 sizes w ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := by
  have heq : _root_.GD.N0072.d007614 ∘ w = w := by
    funext t i
    simp only [Function.comp_apply, _root_.GD.N0072.d007614, _root_.GD.N0072.d007613,
      max_eq_left (hnonneg t _), hunit, div_one]
  rw [← heq]
  exact _root_.GD.N0072.d023443 sizes hn w hw hunit

theorem d023464
    (p w : (Fin k → ℝ) → Fin k → ℝ)
    (hp : _root_.GD.N0072.d023291 sizes p ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hw : _root_.GD.N0072.d023291 sizes w ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p))
    (hstrict : ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p)) :
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes (_root_.GD.N0225.N0538.d023458 p w)) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p) := by
  rw [_root_.GD.N0225.N0538.d023462]
  exact _root_.GD.N0225.N0538.d023457 k sizes hp hw hweak hstrict

theorem d023465 (hn : ∀ i, 2 ≤ sizes i)
    (p w : (Fin k → ℝ) → Fin k → ℝ)
    (hp : Measurable p) (hw : Measurable w)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hwunit : ∀ t, ∑ i, w t i = 1)
    (hpnn : ∀ t i, 0 ≤ p t i) (hwnn : ∀ t i, 0 ≤ w t i)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p))
    (hstrict : ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p)) :
    Measurable (_root_.GD.N0225.N0538.d023458 p w) ∧
    (∀ t, ∑ i, _root_.GD.N0225.N0538.d023458 p w t i = 1) ∧
    (∀ t i, 0 ≤ _root_.GD.N0225.N0538.d023458 p w t i) ∧
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes (_root_.GD.N0225.N0538.d023458 p w)) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p) :=
  ⟨_root_.GD.N0225.N0538.d023459 p w hp hw, _root_.GD.N0225.N0538.d023460 p w hpunit hwunit,
    _root_.GD.N0225.N0538.d023461 p w hpnn hwnn,
    _root_.GD.N0225.N0538.d023464 sizes p w
      (_root_.GD.N0225.N0538.d023463 sizes hn p hp hpunit hpnn)
      (_root_.GD.N0225.N0538.d023463 sizes hn w hw hwunit hwnn) hweak hstrict⟩

end
end GD.N0225.N0538

#print axioms _root_.GD.N0225.N0538.d023457

#print axioms _root_.GD.N0225.N0538.d023460

#print axioms _root_.GD.N0225.N0538.d023461

#print axioms _root_.GD.N0225.N0538.d023462

#print axioms _root_.GD.N0225.N0538.d023463

#print axioms _root_.GD.N0225.N0538.d023464

#print axioms _root_.GD.N0225.N0538.d023465
