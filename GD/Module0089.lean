import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Analysis.LocallyConvex.WeakSpace























open Filter Topology

namespace GD
namespace N0230
namespace N0708

variable {𝕜 ι H E F Z : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]



def d001170 (𝕜 : Type*) [RCLike 𝕜]
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (u : ι → E) (l : Filter ι) (x : E) : Prop :=
  Tendsto (fun i => toWeakSpace 𝕜 E (u i)) l
    (𝓝 (toWeakSpace 𝕜 E x))


theorem d001171 (l : Filter ι) (x : E) :
    _root_.GD.N0230.N0708.d001170 𝕜 (fun _ : ι => x) l x := by
  exact tendsto_const_nhds


theorem d001170.d001172
    {u : ι → E} {l : Filter ι} {x : E}
    (hu : _root_.GD.N0230.N0708.d001170 𝕜 u l x) (T : E →L[𝕜] F) :
    _root_.GD.N0230.N0708.d001170 𝕜 (fun i => T (u i)) l (T x) := by
  exact (WeakSpace.map T).continuous.continuousAt.tendsto.comp hu




theorem d001170.d001173
    {u : ι → E} {v : ι → F} {l : Filter ι} {x : E} {y : F}
    (hu : _root_.GD.N0230.N0708.d001170 𝕜 u l x) (hv : _root_.GD.N0230.N0708.d001170 𝕜 v l y) :
    _root_.GD.N0230.N0708.d001170 𝕜 (fun i => (u i, v i)) l (x, y) := by
  have hu' := hu.d001172 (ContinuousLinearMap.inl 𝕜 E F)
  have hv' := hv.d001172 (ContinuousLinearMap.inr 𝕜 E F)
  simpa only [_root_.GD.N0230.N0708.d001170, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk, add_zero,
    zero_add] using hu'.add hv'


theorem d001174
    {u : ι → E} {l : Filter ι} [NeBot l] {x y : E}
    (hx : _root_.GD.N0230.N0708.d001170 𝕜 u l x) (hy : _root_.GD.N0230.N0708.d001170 𝕜 u l y) :
    x = y := by
  apply (toWeakSpace 𝕜 E).injective
  exact tendsto_nhds_unique hx hy





theorem d001175
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Set V} (hKconv : Convex ℝ K) (hKclosed : IsClosed K) :
    IsClosed (toWeakSpace ℝ V '' K) := by
  apply closure_eq_iff_isClosed.mp
  rw [← hKconv.toWeakSpace_closure ℝ, hKclosed.closure_eq]



theorem d001176
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u : ι → V} {l : Filter ι} [NeBot l] {x : V} {K : Set V}
    (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hu : _root_.GD.N0230.N0708.d001170 ℝ u l x) (hmem : ∀ᶠ i in l, u i ∈ K) :
    x ∈ K := by
  have himage : ∀ᶠ i in l, toWeakSpace ℝ V (u i) ∈ toWeakSpace ℝ V '' K :=
    hmem.mono fun i hi => ⟨u i, hi, rfl⟩
  have hximage : toWeakSpace ℝ V x ∈ toWeakSpace ℝ V '' K :=
    (_root_.GD.N0230.N0708.d001175 hKconv hKclosed).mem_of_tendsto hu himage
  obtain ⟨y, hy, hxy⟩ := hximage
  exact (toWeakSpace ℝ V).injective hxy ▸ hy



def d001177 (left : H →L[𝕜] E) (right : H →L[𝕜] F)
    (x : E) (y : F) : Prop :=
  ∃ h : H, left h = x ∧ right h = y






theorem d001178
    {H₀ E₀ F₀ ι₀ : Type*}
    [NormedAddCommGroup H₀] [NormedSpace ℝ H₀]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
    (left : H₀ →L[ℝ] E₀) (right : H₀ →L[ℝ] F₀)
    (hclosed : IsClosed (Set.range (left.prod right)))
    {u : ι₀ → H₀} {l : Filter ι₀} [NeBot l] {x : E₀} {y : F₀}
    (hlim : _root_.GD.N0230.N0708.d001170 ℝ
      (fun i => (left (u i), right (u i))) l (x, y)) :
    _root_.GD.N0230.N0708.d001177 left right x y := by
  have hconv : Convex ℝ (Set.range (left.prod right)) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ c d hc hd hcd
    refine ⟨c • a + d • b, ?_⟩
    rw [map_add, map_smul, map_smul]
  have hevent : ∀ᶠ i in l, (left (u i), right (u i)) ∈ Set.range (left.prod right) :=
    Filter.Eventually.of_forall fun i => ⟨u i, by simp⟩
  have hxy : (x, y) ∈ Set.range (left.prod right) :=
    _root_.GD.N0230.N0708.d001176 hconv hclosed hlim hevent
  obtain ⟨h, hh⟩ := hxy
  refine ⟨h, ?_, ?_⟩
  · exact congr_arg Prod.fst hh
  · exact congr_arg Prod.snd hh


theorem d001179
    {H₀ E₀ F₀ ι₀ : Type*}
    [NormedAddCommGroup H₀] [NormedSpace ℝ H₀]
    [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
    (left : H₀ →L[ℝ] E₀) (right : H₀ →L[ℝ] F₀)
    (hclosed : IsClosed (Set.range (left.prod right)))
    {u : ι₀ → H₀} {l : Filter ι₀} [NeBot l] {x : E₀} {y : F₀}
    (hx : _root_.GD.N0230.N0708.d001170 ℝ (fun i => left (u i)) l x)
    (hy : _root_.GD.N0230.N0708.d001170 ℝ (fun i => right (u i)) l y) :
    _root_.GD.N0230.N0708.d001177 left right x y := by
  exact _root_.GD.N0230.N0708.d001178 left right hclosed (hx.d001173 hy)






theorem d001180
    {u : ι → H} {l : Filter ι} [NeBot l] {h : H} {x : E} {y : F}
    (left : H →L[𝕜] E) (right : H →L[𝕜] F)
    (hh : _root_.GD.N0230.N0708.d001170 𝕜 u l h)
    (hx : _root_.GD.N0230.N0708.d001170 𝕜 (fun i => left (u i)) l x)
    (hy : _root_.GD.N0230.N0708.d001170 𝕜 (fun i => right (u i)) l y) :
    _root_.GD.N0230.N0708.d001177 left right x y := by
  refine ⟨h, ?_, ?_⟩
  · exact _root_.GD.N0230.N0708.d001174 (hh.d001172 left) hx
  · exact _root_.GD.N0230.N0708.d001174 (hh.d001172 right) hy




theorem d001181
    {u : ι → H} {l l' : Filter ι} {h : H} {x : E} {y : F}
    (left : H →L[𝕜] E) (right : H →L[𝕜] F)
    (hl' : l' ≤ l) (hl'ne : l' ≠ ⊥)
    (hh : _root_.GD.N0230.N0708.d001170 𝕜 u l' h)
    (hx : _root_.GD.N0230.N0708.d001170 𝕜 (fun i => left (u i)) l x)
    (hy : _root_.GD.N0230.N0708.d001170 𝕜 (fun i => right (u i)) l y) :
    _root_.GD.N0230.N0708.d001177 left right x y := by
  letI : NeBot l' := ⟨hl'ne⟩
  exact _root_.GD.N0230.N0708.d001180 left right hh
    (hx.mono_left hl') (hy.mono_left hl')



theorem d001182
    {u : ι → H} {l : Filter ι} {x : E} {y : F}
    (left : H →L[𝕜] E) (right : H →L[𝕜] F)
    (hx : _root_.GD.N0230.N0708.d001170 𝕜 (fun i => left (u i)) l x)
    (hy : _root_.GD.N0230.N0708.d001170 𝕜 (fun i => right (u i)) l y)
    (hxy : ¬ _root_.GD.N0230.N0708.d001177 left right x y) :
    ¬ ∃ (l' : Filter ι) (h : H),
        l' ≤ l ∧ l' ≠ ⊥ ∧ _root_.GD.N0230.N0708.d001170 𝕜 u l' h := by
  rintro ⟨l', h, hl', hl'ne, hh⟩
  exact hxy (_root_.GD.N0230.N0708.d001181 left right hl' hl'ne hh hx hy)



theorem d001183
    (left : H →L[𝕜] E) (right : H →L[𝕜] F)
    (observeLeft : E →L[𝕜] Z) (observeRight : F →L[𝕜] Z)
    (hcomm : observeLeft.comp left = observeRight.comp right)
    {x : E} {y : F} (hxy : _root_.GD.N0230.N0708.d001177 left right x y) :
    observeLeft x = observeRight y := by
  obtain ⟨h, rfl, rfl⟩ := hxy
  exact DFunLike.congr_fun hcomm h


theorem d001184
    {u : ι → H} {l : Filter ι} [NeBot l] {h : H} {x : E} {y : F}
    (left : H →L[𝕜] E) (right : H →L[𝕜] F)
    (observeLeft : E →L[𝕜] Z) (observeRight : F →L[𝕜] Z)
    (hcomm : observeLeft.comp left = observeRight.comp right)
    (hh : _root_.GD.N0230.N0708.d001170 𝕜 u l h)
    (hx : _root_.GD.N0230.N0708.d001170 𝕜 (fun i => left (u i)) l x)
    (hy : _root_.GD.N0230.N0708.d001170 𝕜 (fun i => right (u i)) l y) :
    observeLeft x = observeRight y := by
  exact _root_.GD.N0230.N0708.d001183 left right observeLeft observeRight hcomm
    (_root_.GD.N0230.N0708.d001180 left right hh hx hy)




theorem d001185
    (left : H →L[𝕜] E) (hleft : Function.Injective left)
    {u : ι → H} {l : Filter ι} {h₁ h₂ : H} {x : E}
    [NeBot l]
    (hh₁ : _root_.GD.N0230.N0708.d001170 𝕜 u l h₁) (hh₂ : _root_.GD.N0230.N0708.d001170 𝕜 u l h₂)
    (hx : _root_.GD.N0230.N0708.d001170 𝕜 (fun i => left (u i)) l x) :
    h₁ = h₂ := by
  apply hleft
  have h₁x : left h₁ = x := _root_.GD.N0230.N0708.d001174 (hh₁.d001172 left) hx
  have h₂x : left h₂ = x := _root_.GD.N0230.N0708.d001174 (hh₂.d001172 left) hx
  exact h₁x.trans h₂x.symm

end N0708
end N0230
end GD
