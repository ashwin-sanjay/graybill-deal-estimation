import GD.Module0089










open Topology

namespace GD
namespace N0230
namespace N0715

open _root_.GD.N0230.N0708

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


noncomputable def d001270 :
    WeakSpace ℝ (E × F) ≃ₜ (WeakSpace ℝ E × WeakSpace ℝ F) where
  toFun z := (z.1, z.2)
  invFun z := (z.1, z.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    change Continuous (fun z : WeakSpace ℝ (E × F) =>
      (WeakSpace.map (ContinuousLinearMap.fst ℝ E F) z,
        WeakSpace.map (ContinuousLinearMap.snd ℝ E F) z))
    exact Continuous.prodMk
      (WeakSpace.map (ContinuousLinearMap.fst ℝ E F)).continuous
      (WeakSpace.map (ContinuousLinearMap.snd ℝ E F)).continuous
  continuous_invFun := by
    have hcont : Continuous (fun z : WeakSpace ℝ E × WeakSpace ℝ F =>
        WeakSpace.map (ContinuousLinearMap.inl ℝ E F) z.1 +
          WeakSpace.map (ContinuousLinearMap.inr ℝ E F) z.2) :=
      ((WeakSpace.map (ContinuousLinearMap.inl ℝ E F)).continuous.comp
          continuous_fst).add
        ((WeakSpace.map (ContinuousLinearMap.inr ℝ E F)).continuous.comp
          continuous_snd)
    convert hcont using 1
    funext z
    apply (toWeakSpace ℝ (E × F)).injective
    change (z.1, z.2) = (z.1, 0) + (0, z.2)
    simp

@[simp] theorem d001271
    (z : WeakSpace ℝ (E × F)) :
    _root_.GD.N0230.N0715.d001270 z =
      (WeakSpace.map (ContinuousLinearMap.fst ℝ E F) z,
        WeakSpace.map (ContinuousLinearMap.snd ℝ E F) z) := rfl



def d001272
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (left : H →L[ℝ] E) (right : H →L[ℝ] F) :
    Set (WeakSpace ℝ E × WeakSpace ℝ F) :=
  {p | _root_.GD.N0230.N0708.d001177 left right
    ((toWeakSpace ℝ E).symm p.1)
    ((toWeakSpace ℝ F).symm p.2)}



theorem d001273
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (left : H →L[ℝ] E) (right : H →L[ℝ] F) :
    _root_.GD.N0230.N0715.d001272 left right =
      _root_.GD.N0230.N0715.d001270 ''
        (toWeakSpace ℝ (E × F) '' Set.range (left.prod right)) := by
  ext p
  constructor
  · rintro ⟨h, hhleft, hhright⟩
    refine ⟨toWeakSpace ℝ (E × F) ((left.prod right) h), ?_, ?_⟩
    · exact ⟨(left.prod right) h, ⟨h, rfl⟩, rfl⟩
    · apply Prod.ext
      · change toWeakSpace ℝ E (left h) = p.1
        exact congrArg (toWeakSpace ℝ E) hhleft
      · change toWeakSpace ℝ F (right h) = p.2
        exact congrArg (toWeakSpace ℝ F) hhright
  · rintro ⟨z, ⟨q, ⟨h, rfl⟩, rfl⟩, rfl⟩
    refine ⟨h, ?_, ?_⟩
    · change left h = left h
      rfl
    · change right h = right h
      rfl



theorem d001274
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (left : H →L[ℝ] E) (right : H →L[ℝ] F)
    (hclosed : IsClosed (Set.range (left.prod right))) :
    IsClosed (_root_.GD.N0230.N0715.d001272 left right) := by
  rw [_root_.GD.N0230.N0715.d001273]
  apply (_root_.GD.N0230.N0715.d001270.isClosed_image).2
  apply _root_.GD.N0230.N0708.d001175
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ c d hc hd hcd
    refine ⟨c • a + d • b, ?_⟩
    rw [map_add, map_smul, map_smul]
  · exact hclosed

end N0715
end N0230
end GD

#print axioms _root_.GD.N0230.N0715.d001270
