import GD.Module0724
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Isometry



















open Function Set

namespace GD
namespace N0232
namespace N0719
namespace N0859


def d011196 (k : ℕ) :
    _root_.GD.N0232.N0719.N0859.d010809 k → ℝ × (Fin k → ℝ) :=
  fun θ ↦ (θ.location, θ.scale)

theorem d011197 (k : ℕ) :
    Function.Injective (_root_.GD.N0232.N0719.N0859.d011196 k) := by
  intro θ η h
  cases θ with
  | mk θlocation θscale θpositive =>
    cases η with
    | mk ηlocation ηscale ηpositive =>
      simp only [_root_.GD.N0232.N0719.N0859.d011196, Prod.mk.injEq] at h
      cases h.1
      cases h.2
      rfl



noncomputable instance d011198 (k : ℕ) :
    MetricSpace (_root_.GD.N0232.N0719.N0859.d010809 k) :=
  MetricSpace.induced
    (_root_.GD.N0232.N0719.N0859.d011196 k) (_root_.GD.N0232.N0719.N0859.d011197 k) inferInstance


theorem d011199 (k : ℕ) :
    Isometry (_root_.GD.N0232.N0719.N0859.d011196 k) :=
  MetricSpace.isometry_induced
    (_root_.GD.N0232.N0719.N0859.d011196 k) (_root_.GD.N0232.N0719.N0859.d011197 k)


theorem d011200 (k : ℕ) :
    Continuous (_root_.GD.N0232.N0719.N0859.d011196 k) :=
  (_root_.GD.N0232.N0719.N0859.d011199 k).continuous

@[fun_prop]
theorem d011201 (k : ℕ) :
    Continuous (_root_.GD.N0232.N0719.N0859.d010809.location : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) := by
  change Continuous (fun θ : _root_.GD.N0232.N0719.N0859.d010809 k ↦ (_root_.GD.N0232.N0719.N0859.d011196 k θ).1)
  exact continuous_fst.comp (_root_.GD.N0232.N0719.N0859.d011200 k)

@[fun_prop]
theorem d011202 (k : ℕ) :
    Continuous (_root_.GD.N0232.N0719.N0859.d010809.scale : _root_.GD.N0232.N0719.N0859.d010809 k → Fin k → ℝ) := by
  change Continuous (fun θ : _root_.GD.N0232.N0719.N0859.d010809 k ↦ (_root_.GD.N0232.N0719.N0859.d011196 k θ).2)
  exact continuous_snd.comp (_root_.GD.N0232.N0719.N0859.d011200 k)

@[fun_prop]
theorem d011203 (k : ℕ) (i : Fin k) :
    Continuous (fun θ : _root_.GD.N0232.N0719.N0859.d010809 k ↦ θ.scale i) :=
  (continuous_apply i).comp (_root_.GD.N0232.N0719.N0859.d011202 k)


def d011204 (k : ℕ) : Set (ℝ × (Fin k → ℝ)) :=
  {x | ∀ i, 0 < x.2 i}

theorem d011205 (k : ℕ) :
    range (_root_.GD.N0232.N0719.N0859.d011196 k) = _root_.GD.N0232.N0719.N0859.d011204 k := by
  ext x
  constructor
  · rintro ⟨θ, rfl⟩
    exact θ.scale_pos
  · intro hx
    exact ⟨
      { location := x.1
        scale := x.2
        scale_pos := hx }, rfl⟩


theorem d011206 (k : ℕ) : IsOpen (_root_.GD.N0232.N0719.N0859.d011204 k) := by
  have hopen : IsOpen (⋂ i : Fin k, {x : ℝ × (Fin k → ℝ) | 0 < x.2 i}) := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const ((continuous_apply i).comp continuous_snd)
  convert hopen using 1
  ext x
  simp [_root_.GD.N0232.N0719.N0859.d011204]



def d011207 (k : ℕ) : _root_.GD.N0232.N0719.N0859.d010809 k ≃ _root_.GD.N0232.N0719.N0859.d011204 k where
  toFun θ := ⟨_root_.GD.N0232.N0719.N0859.d011196 k θ, θ.scale_pos⟩
  invFun x :=
    { location := x.1.1
      scale := x.1.2
      scale_pos := x.2 }
  left_inv θ := by
    cases θ
    rfl
  right_inv x := by
    cases x
    rfl


noncomputable def d011208 (k : ℕ) :
    _root_.GD.N0232.N0719.N0859.d010809 k ≃ₜ _root_.GD.N0232.N0719.N0859.d011204 k where
  toEquiv := _root_.GD.N0232.N0719.N0859.d011207 k
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact _root_.GD.N0232.N0719.N0859.d011200 k
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val



noncomputable instance d011209 (k : ℕ) :
    SecondCountableTopology (_root_.GD.N0232.N0719.N0859.d010809 k) :=
  (_root_.GD.N0232.N0719.N0859.d011199 k).isEmbedding.secondCountableTopology


instance d011210 (k : ℕ) : Nonempty (_root_.GD.N0232.N0719.N0859.d010809 k) :=
  ⟨_root_.GD.N0232.N0719.N0859.d010810 k⟩



noncomputable def d011211 (k : ℕ) : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k :=
  TopologicalSpace.denseSeq (_root_.GD.N0232.N0719.N0859.d010809 k)




theorem d011212 (k : ℕ) :
    DenseRange (_root_.GD.N0232.N0719.N0859.d011211 k) :=
  by
    change DenseRange (TopologicalSpace.denseSeq (_root_.GD.N0232.N0719.N0859.d010809 k))
    exact TopologicalSpace.denseRange_denseSeq (_root_.GD.N0232.N0719.N0859.d010809 k)



theorem d011213 (k : ℕ) :
    ∃ sample : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k, DenseRange sample :=
  TopologicalSpace.exists_dense_seq (_root_.GD.N0232.N0719.N0859.d010809 k)

end N0859
end N0719
end N0232
end GD
