import GD.Module1270
import GD.Module1228

set_option autoImplicit false
set_option warningAsError true











open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0719.N0998

open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1314
  (d019720 d019721 d019722)
open _root_.GD.N0232.N0720.N1330
  (d020032 d020033 d020036 d020026)
open _root_.GD.N0238.N0753
open _root_.GD.N0230.N0556
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0719.N0990 _root_.GD.N0232.N0719.N0991
open _root_.GD.N0232.N0719.N0996 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0983
open _root_.GD.N0107

noncomputable section

variable {k d : ℕ} (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
variable (hn : ∀ i, 0 < sizes i)

def d020547 {I : Type*} (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) : Option I → _root_.GD.N0232.N0719.N0988.d019777 k
  | none => _root_.GD.N0232.N0719.N0988.d019778 k
  | some i => q i

theorem d020548 {I : Type*} (q : I → _root_.GD.N0232.N0719.N0988.d019777 k) :
    _root_.GD.N0232.N0719.N0988.d019787 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q =
      fun i => _root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (_root_.GD.N0232.N0719.N0998.d020547 q i) := by
  funext i
  cases i <;> rfl



theorem d020549 (q : _root_.GD.N0232.N0719.N0988.d019777 k)
    {P : _root_.GD.N0232.N0720.N1341.d004414 d → Prop}
    (hP : ∀ᵐ omega ∂_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q),
      P (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega)) : ∀ᵐ x ∂volume, P x := by
  have hmap : ∀ᵐ x ∂(_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q)).map
      (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim), P x :=
    (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).measurableEmbedding.ae_map_iff.mpr hP
  rw [_root_.GD.N0232.N0719.N0997.d019814] at hmap
  have hm : Measurable (fun x : _root_.GD.N0232.N0720.N1341.d004414 d => ENNReal.ofReal
      (_root_.GD.N0232.N0720.N1316.d004445 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x)) := by
    unfold _root_.GD.N0232.N0720.N1316.d004445
    fun_prop
  have hv := (ae_withDensity_iff hm).mp hmap
  filter_upwards [hv] with x hx
  apply hx
  apply (ENNReal.ofReal_pos.mpr ?_).ne'
  exact mul_pos (_root_.GD.N0232.N0720.N1316.d004446 _) (Real.exp_pos _)

include hn


theorem d020550 (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (ha : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0719.N0988.d019782 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim)) h) :
    ∃ (ell : ℕ → ℕ)
      (p : ∀ j, Option (Fin (ell j)) → _root_.GD.N0232.N0719.N0990.d020496 k)
      (a : ∀ j, Option (Fin (ell j)) → ℝ)
      (ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k)),
      (∀ j i, 0 ≤ a j i) ∧ (∀ j, ∑ i, a j i = 1) ∧
      (∀ j, (ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) =
        ∑ i, ENNReal.ofReal (a j i) • Measure.dirac (p j i)) ∧
      (∀ j i l, 0 < (_root_.GD.N0232.N0719.N0983.d009710 l (p j i).2 : ℝ)) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
        Tendsto (fun j => _root_.GD.N0232.N0719.N0991.d020538 sizes hdim (ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x)
          atTop (𝓝 (_root_.GD.N0232.N0720.N1341.d004418 h x))) := by
  obtain ⟨w, ns, hw, _hns, hlim⟩ :=
    _root_.GD.N0232.N0719.N0988.d019793 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) h ha
  let q : ∀ j, Option (Fin (ns j)) → _root_.GD.N0232.N0719.N0988.d019777 k :=
    fun j => _root_.GD.N0232.N0719.N0998.d020547 (fun i : Fin (ns j) => _root_.GD.N0232.N0719.N0988.d019790 k i)
  let v : ∀ j, Option (Fin (ns j)) → ℝ := fun j => _root_.GD.N0232.N0720.N1314.d019720 (w (ns j))
  have hv : ∀ j i, 0 ≤ v j i := fun j => _root_.GD.N0232.N0720.N1314.d019721 _ (hw (ns j))
  have hp : ∀ j, ∃ i, 0 < v j i := fun j => _root_.GD.N0232.N0720.N1314.d019722 _
  let ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k) :=
    fun j => _root_.GD.N0232.N0719.N0991.d020535 sizes hdim hn (q j) (v j) (hv j) (hp j)
  have hlim' : ∀ᵐ u : _root_.GD.N0232.N0720.N1341.d004415 d ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      Tendsto (fun j => _root_.GD.N0232.N0720.N1330.d020032
        (fun i => _root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q j i)) (v j) u)
        atTop (𝓝 (h u)) := by
    simpa only [q, v, _root_.GD.N0232.N0720.N1330.d020033, _root_.GD.N0232.N0719.N0998.d020548] using hlim
  have hraw := _root_.GD.N0232.N0720.N1330.d020026
    (fun j => _root_.GD.N0232.N0720.N1330.d020032 (fun i => _root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) (q j i)) (v j))
    (fun j => _root_.GD.N0232.N0720.N1330.d020036 _ (v j)) h hlim'
  refine ⟨ns, (fun j i => _root_.GD.N0232.N0719.N0990.d020507 sizes hdim hn (q j i)),
    (fun j => _root_.GD.N0232.N0719.N0991.d020532 sizes hdim (q j) (v j)), ν,
    (fun j i => _root_.GD.N0232.N0719.N0991.d020533 sizes hdim hn (q j) (v j) (hv j) (hp j) i),
    (fun j => _root_.GD.N0232.N0719.N0991.d020534 sizes hdim hn (q j) (v j) (hv j) (hp j)),
    (fun _ => rfl), ?_, ?_⟩
  · intro j i l
    exact div_pos (_root_.GD.N0232.N0719.N0990.d020503 sizes hn (q j i) l)
      (_root_.GD.N0232.N0719.N0990.d020504 sizes hdim hn (q j i))
  · filter_upwards [hraw] with x hx
    simpa only [ν, _root_.GD.N0232.N0719.N0991.d020539] using hx



theorem d020551
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∃ (ell : ℕ → ℕ)
      (p : ∀ j, Option (Fin (ell j)) → _root_.GD.N0232.N0719.N0990.d020496 k)
      (a : ∀ j, Option (Fin (ell j)) → ℝ)
      (ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k)),
      (∀ j i, 0 ≤ a j i) ∧ (∀ j, ∑ i, a j i = 1) ∧
      (∀ j, (ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) =
        ∑ i, ENNReal.ofReal (a j i) • Measure.dirac (p j i)) ∧
      (∀ j i l, 0 < (_root_.GD.N0232.N0719.N0983.d009710 l (p j i).2 : ℝ)) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
        Tendsto (fun j => _root_.GD.N0232.N0719.N0991.d020538 sizes hdim (ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x)
          atTop (𝓝 (s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)))) := by
  obtain ⟨h, ha, heq⟩ := _root_.GD.N0232.N0719.N0996.d019946 sizes hdim hs
  obtain ⟨ell, p, a, ν, han, has, hν, hpi, hlim⟩ :=
    _root_.GD.N0232.N0719.N0998.d020550 sizes hdim hn h ha
  have heqv : _root_.GD.N0232.N0720.N1341.d004418 h =ᵐ[volume] s ∘ (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm := by
    apply _root_.GD.N0232.N0719.N0998.d020549 sizes hdim (_root_.GD.N0232.N0719.N0988.d019778 k)
    simpa only [Filter.EventuallyEq, _root_.GD.N0232.N0719.N0996.d019931,
      Function.comp_def, MeasurableEquiv.symm_apply_apply,
      _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0996.d019935] using
      heq (_root_.GD.N0232.N0719.N0996.d019935 (_root_.GD.N0232.N0719.N0988.d019778 k))
  refine ⟨ell, p, a, ν, han, has, hν, hpi, ?_⟩
  filter_upwards [hlim, heqv] with x hx he
  simpa only [he, Function.comp_apply] using hx

end
end GD.N0232.N0719.N0998

#print axioms _root_.GD.N0232.N0719.N0998.d020551
