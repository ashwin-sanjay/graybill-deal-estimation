import GD.Module1749
import GD.Module0148

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0019
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0092
open _root_.GD.N0213.N0502
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0718
open _root_.GD.N0230.N0670
open _root_.GD.N0230.N0671
open _root_.GD.N0230.N0611

variable {k : ℕ} (sizes : Fin k → ℕ)


theorem d029018
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hpq : p ≠ q) (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (hp : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p ≠ ⊤) (hq : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ q ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0230.N0718.d001528 p q) < _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p := by
  have heq := _root_.GD.N0230.N0670.d001647
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ) θ.location p q
  have htax := _root_.GD.N0230.N0671.d001651
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ)
    (_root_.GD.N0232.N0719.d009183
      k sizes θ.location θ.scale θ.scale_pos).2 hpq
  have htotal : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0230.N0718.d001528 p q) +
      _root_.GD.N0230.N0602.d000117 (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) 0 (_root_.GD.N0230.N0670.d001646 p q) ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p := by
    calc
      _ = ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p +
          ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0719.N0859.d010821 k sizes θ q := heq
      _ ≤ ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p +
          ENNReal.ofReal (1 / 2 : ℝ) * _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p :=
        add_le_add le_rfl (mul_le_mul_right hq _)
      _ = _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p := by
        rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
  have hmid : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0230.N0718.d001528 p q) ≠ ⊤ :=
    ne_top_of_le_ne_top hp ((le_add_right le_rfl).trans htotal)
  exact (ENNReal.lt_add_right hmid (ne_of_gt htax)).trans_le htotal

private theorem d029019
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) :
    (fun ω => _root_.GD.N0232.N0719.N0970.d012312 k sizes d hd ω) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] d :=
  (_root_.GD.N0232.N0719.N0896.d011095 k sizes d hd.1
    (hd.2 (_root_.GD.N0232.N0719.N0859.d010810 k))).coeFn_toLp



theorem d029020
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    {d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (ha : d ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes) (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes d) :
    ∃ e ∈ _root_.GD.N0092.d023968 k sizes,
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ e < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d) ∧
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e ≤ _root_.GD.N0232.N0719.N0962.d012187 k sizes d ∧
      ¬ _root_.GD.N0019.d028999 sizes e := by
  have hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes :=
    _root_.GD.N0213.N0502.d022053 k sizes hk hn ⟨ha.1, fun θ => (hs θ).le⟩
  let t := _root_.GD.N0232.N0719.N0970.d012314 k sizes d hd
  have htmem : t ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := _root_.GD.N0232.N0719.N0970.d012316 k sizes d hd
  have ht : t ∈ _root_.GD.N0092.d023968 k sizes :=
    ⟨htmem, _root_.GD.N0232.N0719.N0970.d012321 k sizes d hd hs,
      _root_.GD.N0232.N0719.N0970.d012317 k sizes d hd⟩
  let p := _root_.GD.N0232.N0719.N0970.d012312 k sizes d hd
  let q := _root_.GD.N0232.N0719.N0970.d012312 k sizes t htmem
  have hpq : p ≠ q := by
    intro hpq
    apply _root_.GD.N0019.d029003 sizes hk hn ht
    refine ⟨d, ha, ?_⟩
    have hdp : (fun ω => p ω) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] d :=
      _root_.GD.N0019.d029019 sizes d hd
    have htq : (fun ω => q ω) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] t :=
      _root_.GD.N0019.d029019 sizes t htmem
    rw [← hpq] at htq
    exact htq.symm.trans hdp
  let m := _root_.GD.N0232.N0719.N0896.d011088 k sizes (_root_.GD.N0230.N0718.d001528 p q)
  have hm (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ m < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d := by
    change _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0896.d011088 k sizes _) < _
    rw [_root_.GD.N0232.N0719.N0896.d011093, ← _root_.GD.N0232.N0719.N0970.d012313 k sizes d hd]
    apply _root_.GD.N0019.d029018 sizes p q hpq θ
    · simpa only [p, _root_.GD.N0232.N0719.N0970.d012313] using hd.2 θ
    · simpa only [p, q, _root_.GD.N0232.N0719.N0970.d012313] using _root_.GD.N0232.N0719.N0970.d012315 k sizes d hd θ
  have hmfinite : m ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes :=
    ⟨_root_.GD.N0232.N0719.N0896.d011089 k sizes _, fun θ => ne_top_of_lt (hm θ)⟩
  let e := _root_.GD.N0232.N0719.N0970.d012314 k sizes m hmfinite
  have hed (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ e < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d :=
    (_root_.GD.N0232.N0719.N0970.d012315 k sizes m hmfinite θ).trans_lt (hm θ)
  have he : e ∈ _root_.GD.N0092.d023968 k sizes :=
    ⟨_root_.GD.N0232.N0719.N0970.d012316 k sizes m hmfinite, fun θ => (hed θ).trans (hs θ),
      _root_.GD.N0232.N0719.N0970.d012317 k sizes m hmfinite⟩
  exact ⟨e, he, hed, _root_.GD.N0232.N0719.N0970.d012318 k sizes (fun θ => (hed θ).le),
    _root_.GD.N0019.d029003 sizes hk hn he⟩



theorem d029021
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    {d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (ha : d ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes) (hs : _root_.GD.N0232.N0719.N0970.d012310 k sizes d)
    (hv : _root_.GD.N0232.N0719.N0962.d012187 k sizes d = _root_.GD.N0213.N0502.d022051 k sizes) :
    ∃ e ∈ _root_.GD.N0092.d023968 k sizes,
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ e < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d) ∧
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e = _root_.GD.N0213.N0502.d022051 k sizes ∧
      ¬ _root_.GD.N0019.d028999 sizes e := by
  obtain ⟨e, he, hed, hew, hena⟩ :=
    _root_.GD.N0019.d029020 sizes hk hn ha hs
  refine ⟨e, he, hed, le_antisymm (hew.trans_eq hv) ?_, hena⟩
  exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
    (_root_.GD.N0092.d023969 k sizes he)

end
end GD.N0019

#print axioms _root_.GD.N0019.d029018
#print axioms _root_.GD.N0019.d029020
#print axioms _root_.GD.N0019.d029021
