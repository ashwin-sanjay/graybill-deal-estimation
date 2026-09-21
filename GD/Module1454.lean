import GD.Module1280
import GD.Module1228
import GD.Module1262

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace GD.N0212.N0470
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0996 _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0719.N0896 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0156.N0444 _root_.GD.N0232.N0719.N0981
open _root_.GD.N0232.N0719.N0962

abbrev d023014 (d : ℕ) := _root_.GD.N0232.N0720.N1341.d004414 d
variable {k d : ℕ}

def d023015 (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (x : _root_.GD.N0212.N0470.d023014 d) : _root_.GD.N0232.N0719.N0873.d011295 (Fin k) :=
  _root_.GD.N0232.N0719.N0986.d020362 sizes ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)



theorem d023016 (sizes : Fin k → ℕ)
    (hdim : (∑ i, sizes i) = d + 1) (q : _root_.GD.N0232.N0719.N0988.d019777 k)
    {P : _root_.GD.N0212.N0470.d023014 d → Prop}
    (hP : ∀ᵐ omega ∂_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q),
      P (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim omega)) : ∀ᵐ x ∂volume, P x := by
  have hmap : ∀ᵐ x ∂(_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q)).map
      (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim), P x :=
    (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).measurableEmbedding.ae_map_iff.mpr hP
  rw [_root_.GD.N0232.N0719.N0997.d019814] at hmap
  have hm : Measurable (fun x : _root_.GD.N0212.N0470.d023014 d => ENNReal.ofReal
      (_root_.GD.N0232.N0720.N1316.d004445
        (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x)) := by
    unfold _root_.GD.N0232.N0720.N1316.d004445
    fun_prop
  have hv := (ae_withDensity_iff hm).mp hmap
  filter_upwards [hv] with x hx
  apply hx
  apply (ENNReal.ofReal_pos.mpr ?_).ne'
  exact mul_pos (_root_.GD.N0232.N0720.N1316.d004446 _)
    (Real.exp_pos _)

variable [NeZero k]



theorem d023017 (sizes : Fin k → ℕ)
    (hdim : (∑ i, sizes i) = d + 1) (hn : ∀ i, 0 < sizes i)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    (∀ᵐ x ∂(volume : Measure (_root_.GD.N0212.N0470.d023014 d)),
      ∀ c : ℝ, (∀ i, (_root_.GD.N0212.N0470.d023015 sizes hdim x).1 i ≤ c) →
        s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x) ≤ c) ∧
    (∀ᵐ x ∂(volume : Measure (_root_.GD.N0212.N0470.d023014 d)),
      ∀ c : ℝ, (∀ i, c ≤ (_root_.GD.N0212.N0470.d023015 sizes hdim x).1 i) →
        c ≤ s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)) := by
  have hfinite : s ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes :=
    ⟨hs.1, fun θ => ne_top_of_lt (hs.2.2.1 θ)⟩
  have htrans : ∀ c : ℝ, ∀ z, s (fun i j => c + z i j) = c + s z := by
    intro c z
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨c, 0⟩
    have h := hs.2.1 g z
    change s (fun i j => c + Real.exp 0 * z i j) = c + Real.exp 0 * s z at h
    simpa only [Real.exp_zero, one_mul] using h
  have hraw := _root_.GD.N0156.N0444.d020673 sizes hn s hfinite htrans hs.2.2.2
    (_root_.GD.N0232.N0719.N0996.d019935 (_root_.GD.N0232.N0719.N0988.d019778 k))
  have hvolume : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0212.N0470.d023014 d)),
      _root_.GD.N0156.N0444.d020667 sizes s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x) := by
    apply _root_.GD.N0212.N0470.d023016 sizes hdim (_root_.GD.N0232.N0719.N0988.d019778 k)
    simpa only [MeasurableEquiv.symm_apply_apply, _root_.GD.N0232.N0719.N0859.d010812,
      _root_.GD.N0232.N0719.N0996.d019935] using hraw
  constructor
  · filter_upwards [hvolume] with x hx
    intro c hc
    apply hx.2.trans
    apply Finset.sup'_le
    intro i _
    exact hc i
  · filter_upwards [hvolume] with x hx
    intro c hc
    apply le_trans _ hx.1
    apply Finset.le_inf'
    intro i _
    exact hc i

end
end GD.N0212.N0470

#print axioms _root_.GD.N0212.N0470.d023017
