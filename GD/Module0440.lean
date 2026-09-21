import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true

open Filter Set
open scoped Topology

namespace GD.N0154
noncomputable section


def d006782 (t : ℝ) : ℝ := t / (1 - t)

theorem d006783 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < _root_.GD.N0154.d006782 t :=
  div_pos ht.1 (sub_pos.mpr ht.2)


theorem d006784 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0154.d006782 t / (1 + _root_.GD.N0154.d006782 t) = t := by
  have hd : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
  have ho : 1 + _root_.GD.N0154.d006782 t ≠ 0 := (by linarith [_root_.GD.N0154.d006783 ht] : 0 < 1 + _root_.GD.N0154.d006782 t).ne'
  apply (div_eq_iff ho).mpr
  unfold _root_.GD.N0154.d006782
  field_simp
  ring



theorem d006785 {α : Type*} {l : Filter α} {t : α → ℝ}
    (ht : ∀ᶠ i in l, t i ∈ Ioo (0 : ℝ) 1)
    (hzero : Tendsto t l (𝓝 0)) :
    Tendsto (fun i => _root_.GD.N0154.d006782 (t i)) l (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa [_root_.GD.N0154.d006782, Pi.div_def] using
      hzero.div (tendsto_const_nhds.sub hzero) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  · exact ht.mono fun _ hi => _root_.GD.N0154.d006783 hi



theorem d006786 {α : Type*} {l : Filter α}
    {t : α → ℝ} {R : ℝ → ℝ} {L : α → ℝ}
    (ht : ∀ᶠ i in l, t i ∈ Ioo (0 : ℝ) 1)
    (hzero : Tendsto t l (𝓝 0))
    (hrisk : Tendsto (fun w => R w / (w / (1 + w))) (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hidentity : ∀ᶠ i in l, 1 + L i = R (_root_.GD.N0154.d006782 (t i)) / t i) :
    Tendsto L l (𝓝 0) := by
  have hratio := hrisk.comp (_root_.GD.N0154.d006785 ht hzero)
  have hid : (fun i => R (_root_.GD.N0154.d006782 (t i)) / (_root_.GD.N0154.d006782 (t i) / (1 + _root_.GD.N0154.d006782 (t i))) - 1)
      =ᶠ[l] L := by
    filter_upwards [ht, hidentity] with i hi heq
    rw [_root_.GD.N0154.d006784 hi, ← heq]
    ring
  have hsub : Tendsto (fun i =>
      R (_root_.GD.N0154.d006782 (t i)) / (_root_.GD.N0154.d006782 (t i) / (1 + _root_.GD.N0154.d006782 (t i))) - 1) l (𝓝 (0 : ℝ)) := by
    simpa only [Pi.sub_def, Function.comp_apply, sub_self] using
      hratio.sub (tendsto_const_nhds (x := (1 : ℝ)))
  exact hsub.congr' hid

end
end GD.N0154

#print axioms _root_.GD.N0154.d006783
#print axioms _root_.GD.N0154.d006784
#print axioms _root_.GD.N0154.d006785
#print axioms _root_.GD.N0154.d006786
