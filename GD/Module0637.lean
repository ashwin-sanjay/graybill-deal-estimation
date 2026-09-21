import GD.Module0636




















open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace GD.N0232.N0719.N0933

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N1009


def d009286 (n : ℕ) (location scale z : ℝ) : ℝ :=
  location + (scale / Real.sqrt n) * z



def d009287 (n : ℕ) (scale q : ℝ) : ℝ :=
  (scale ^ 2 / n) * q



noncomputable def d009288
    (n : ℕ) (location scale : ℝ) : Measure ℝ :=
  (gaussianReal 0 1).map (_root_.GD.N0232.N0719.N0933.d009286 n location scale)


noncomputable def d009289
    (n : ℕ) (scale : ℝ) : Measure ℝ :=
  (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
      (((n - 1 : ℕ) : ℝ) / 2)).map
    (_root_.GD.N0232.N0719.N0933.d009287 n scale)

noncomputable instance d009290
    (a r : ℝ) :
    SigmaFinite (gammaMeasure a r) := by
  unfold gammaMeasure gammaPDF
  infer_instance

noncomputable instance d009291
    (n : ℕ) (location scale : ℝ) :
    SFinite (_root_.GD.N0232.N0719.N0933.d009288 n location scale) := by
  unfold _root_.GD.N0232.N0719.N0933.d009288
  infer_instance

noncomputable instance d009292
    (n : ℕ) (scale : ℝ) :
    SFinite (_root_.GD.N0232.N0719.N0933.d009289 n scale) := by
  unfold _root_.GD.N0232.N0719.N0933.d009289 gammaMeasure
  infer_instance

@[fun_prop]
theorem d009293
    (n : ℕ) (location scale : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0933.d009286 n location scale) := by
  unfold _root_.GD.N0232.N0719.N0933.d009286
  fun_prop

@[fun_prop]
theorem d009294
    (n : ℕ) (scale : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0933.d009287 n scale) := by
  unfold _root_.GD.N0232.N0719.N0933.d009287
  fun_prop

noncomputable instance d009295
    (n : ℕ) (location scale : ℝ) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009288 n location scale) := by
  unfold _root_.GD.N0232.N0719.N0933.d009288
  exact Measure.isProbabilityMeasure_map
    (_root_.GD.N0232.N0719.N0933.d009293 n location scale).aemeasurable

theorem d009296
    (n : ℕ) (location scale : ℝ) :
    _root_.GD.N0232.N0719.N1009.d009274 n location scale =
      Prod.map (_root_.GD.N0232.N0719.N0933.d009286 n location scale)
        (_root_.GD.N0232.N0719.N0933.d009287 n scale) := by
  funext z
  rfl










theorem d009297
    {n : ℕ} (hn : 0 < n)
    (location scale : ℝ) :
    _root_.GD.N0232.N0719.N0933.d009288 n location scale =
      gaussianReal location
        (.mk (scale ^ 2 / (n : ℝ))
          (div_nonneg (sq_nonneg scale) (Nat.cast_nonneg n))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 hnR
  unfold _root_.GD.N0232.N0719.N0933.d009288 _root_.GD.N0232.N0719.N0933.d009286
  calc
    (gaussianReal 0 1).map
        (fun z : ℝ => location + scale / Real.sqrt (n : ℝ) * z) =
        ((gaussianReal 0 1).map
          (fun z : ℝ => (scale / Real.sqrt (n : ℝ)) * z)).map
            (fun z : ℝ => location + z) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
    _ =
        (gaussianReal 0
          (.mk ((scale / Real.sqrt (n : ℝ)) ^ 2)
            (sq_nonneg _))).map
              (fun z : ℝ => location + z) := by
      rw [gaussianReal_map_const_mul]
      simp
    _ =
        gaussianReal location
          (.mk ((scale / Real.sqrt (n : ℝ)) ^ 2)
            (sq_nonneg _)) := by
      rw [gaussianReal_map_const_add]
      simp
    _ =
        gaussianReal location
          (.mk (scale ^ 2 / (n : ℝ))
            (div_nonneg (sq_nonneg scale) (Nat.cast_nonneg n))) := by
      congr 2
      rw [div_pow, Real.sq_sqrt hnR.le]



theorem d009298
    (n : ℕ) (location scale : ℝ) :
    _root_.GD.N0232.N0719.N1009.d009276 n location scale =
      (_root_.GD.N0232.N0719.N0933.d009288 n location scale).prod
        (_root_.GD.N0232.N0719.N0933.d009289 n scale) := by
  unfold _root_.GD.N0232.N0719.N1009.d009276 _root_.GD.N0232.N0719.N1009.d009275
    _root_.GD.N0232.N0719.N0933.d009288 _root_.GD.N0232.N0719.N0933.d009289
  rw [_root_.GD.N0232.N0719.N0933.d009296]
  exact
    (Measure.map_prod_map
      (gaussianReal 0 1)
      (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2))
      (_root_.GD.N0232.N0719.N0933.d009293 n location scale)
      (_root_.GD.N0232.N0719.N0933.d009294 n scale)).symm



def d009299 (k : ℕ) :
    (Fin k → ℝ × ℝ) ≃ᵐ ((Fin k → ℝ) × (Fin k → ℝ)) :=
  MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin k)


noncomputable def d009300
    (k : ℕ) (sizes : Fin k → ℕ)
    (location : ℝ) (scales : Fin k → ℝ) :
    Measure (Fin k → ℝ) :=
  Measure.pi (fun i =>
    _root_.GD.N0232.N0719.N0933.d009288 (sizes i) location (scales i))


noncomputable def d009301
    (k : ℕ) (sizes : Fin k → ℕ)
    (scales : Fin k → ℝ) :
    Measure (Fin k → ℝ) :=
  Measure.pi (fun i =>
    _root_.GD.N0232.N0719.N0933.d009289 (sizes i) (scales i))










theorem d009302
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0933.d009300 k sizes location scales =
      Measure.pi (fun i =>
        gaussianReal location
          (.mk (scales i ^ 2 / (sizes i : ℝ))
            (div_nonneg (sq_nonneg (scales i))
              (Nat.cast_nonneg (sizes i))))) := by
  unfold _root_.GD.N0232.N0719.N0933.d009300
  congr 1
  funext i
  exact _root_.GD.N0232.N0719.N0933.d009297
    (lt_of_lt_of_le (by decide : 0 < 2) (hsizes i))
    location (scales i)



theorem d009303
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    (_root_.GD.N0232.N0719.N1009.d009283 k sizes location scales).map
        (_root_.GD.N0232.N0719.N0933.d009299 k) =
      (_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales).prod
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) := by
  letI (i : Fin k) :
      IsProbabilityMeasure
        (_root_.GD.N0232.N0719.N0933.d009289 (sizes i) (scales i)) := by
    have hshapeNat : 0 < sizes i - 1 := by
      have := hsizes i
      omega
    have hshapeReal :
        0 < (((sizes i - 1 : ℕ) : ℝ) / 2) := by
      have : 0 < ((sizes i - 1 : ℕ) : ℝ) := by
        exact_mod_cast hshapeNat
      positivity
    unfold _root_.GD.N0232.N0719.N0933.d009289
    letI :
        IsProbabilityMeasure
          (gammaMeasure (((sizes i - 1 : ℕ) : ℝ) / 2)
            (((sizes i - 1 : ℕ) : ℝ) / 2)) :=
      isProbabilityMeasure_gammaMeasure hshapeReal hshapeReal
    exact Measure.isProbabilityMeasure_map
      (_root_.GD.N0232.N0719.N0933.d009294 (sizes i) (scales i)).aemeasurable
  unfold _root_.GD.N0232.N0719.N1009.d009283 _root_.GD.N0232.N0719.N0933.d009300 _root_.GD.N0232.N0719.N0933.d009301
  simp_rw [_root_.GD.N0232.N0719.N0933.d009298]
  exact
    (measurePreserving_arrowProdEquivProdArrow
      ℝ ℝ (Fin k)
      (fun i => _root_.GD.N0232.N0719.N0933.d009288 (sizes i) location (scales i))
      (fun i => _root_.GD.N0232.N0719.N0933.d009289 (sizes i) (scales i))).map_eq


def d009304
    (k : ℕ) (sizes : Fin k → ℕ) :
    _root_.GD.N0232.N0719.d009173 k sizes → ((Fin k → ℝ) × (Fin k → ℝ)) :=
  fun x => _root_.GD.N0232.N0719.N0933.d009299 k (_root_.GD.N0232.N0719.N1009.d009282 k sizes x)



def d009305 (k : ℕ) :
    ((Fin k → ℝ) × (Fin k → ℝ)) → _root_.GD.N0232.N0719.N0900.d009096 k :=
  fun z => ⟨z.1, z.2⟩

@[fun_prop]
theorem d009306 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0719.N0933.d009305 k) := by
  rw [measurable_comap_iff]
  change Measurable
    (fun z : (Fin k → ℝ) × (Fin k → ℝ) => z)
  exact measurable_id



theorem d009307
    (k : ℕ) (sizes : Fin k → ℕ)
    (x : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0933.d009305 k (_root_.GD.N0232.N0719.N0933.d009304 k sizes x) =
      _root_.GD.N0232.N0719.N0900.d009104 k sizes x := by
  rfl

@[fun_prop]
theorem d009308
    (k : ℕ) (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0232.N0719.N0933.d009304 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0933.d009304
  fun_prop



theorem d009309
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    (_root_.GD.N0232.N0719.d009176 k sizes location scales).map
        (_root_.GD.N0232.N0719.N0933.d009304 k sizes) =
      (_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales).prod
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) := by
  calc
    (_root_.GD.N0232.N0719.d009176 k sizes location scales).map
        (_root_.GD.N0232.N0719.N0933.d009304 k sizes) =
      ((_root_.GD.N0232.N0719.d009176 k sizes location scales).map
        (_root_.GD.N0232.N0719.N1009.d009282 k sizes)).map (_root_.GD.N0232.N0719.N0933.d009299 k) := by
          rw [Measure.map_map
            (_root_.GD.N0232.N0719.N0933.d009299 k).measurable
            (_root_.GD.N0232.N0719.N1009.d009284 k sizes)]
          rfl
    _ =
      (_root_.GD.N0232.N0719.N1009.d009283 k sizes location scales).map
        (_root_.GD.N0232.N0719.N0933.d009299 k) := by
          rw [_root_.GD.N0232.N0719.N1009.d009285
            k sizes hsizes location scales]
    _ =
      (_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales).prod
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) :=
          _root_.GD.N0232.N0719.N0933.d009303
            k sizes hsizes location scales










theorem d009310
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ)
    (F : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ)
    (hF : Measurable F) :
    (∫ x, F (_root_.GD.N0232.N0719.N0900.d009104 k sizes x)
        ∂_root_.GD.N0232.N0719.d009176 k sizes location scales) =
      ∫ z, F (_root_.GD.N0232.N0719.N0933.d009305 k z)
        ∂((_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales).prod
          (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales)) := by
  have hsplit :=
    _root_.GD.N0232.N0719.N0933.d009309
      k sizes hsizes location scales
  calc
    (∫ x, F (_root_.GD.N0232.N0719.N0900.d009104 k sizes x)
        ∂_root_.GD.N0232.N0719.d009176 k sizes location scales) =
        ∫ x,
          (F ∘ _root_.GD.N0232.N0719.N0933.d009305 k)
            (_root_.GD.N0232.N0719.N0933.d009304 k sizes x)
          ∂_root_.GD.N0232.N0719.d009176 k sizes location scales := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Function.comp_apply,
        _root_.GD.N0232.N0719.N0933.d009307]
    _ =
        ∫ z, (F ∘ _root_.GD.N0232.N0719.N0933.d009305 k) z
          ∂((_root_.GD.N0232.N0719.d009176 k sizes location scales).map
            (_root_.GD.N0232.N0719.N0933.d009304 k sizes)) := by
      rw [integral_map_of_stronglyMeasurable
        (_root_.GD.N0232.N0719.N0933.d009308 k sizes)
        ((hF.comp (_root_.GD.N0232.N0719.N0933.d009306 k)).stronglyMeasurable)]
    _ =
        ∫ z, F (_root_.GD.N0232.N0719.N0933.d009305 k z)
          ∂((_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales).prod
            (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales)) := by
      rw [hsplit]
      rfl

end

end GD.N0232.N0719.N0933
