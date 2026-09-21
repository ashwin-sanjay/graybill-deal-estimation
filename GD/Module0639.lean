import GD.Module0637




















open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0232.N0719.N0897

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N1009 _root_.GD.N0232.N0719.N0933 _root_.GD.N0232.N0719.N0900



def d009332
    (k : ℕ) (sizes : Fin k → ℕ)
    (locations scales : Fin k → ℝ) :
    Measure (_root_.GD.N0232.N0719.d009173 k sizes) :=
  Measure.pi (fun i ↦ _root_.GD.N0232.N0719.d009175 (sizes i) (locations i) (scales i))

noncomputable instance d009333
    (k : ℕ) (sizes : Fin k → ℕ)
    (locations scales : Fin k → ℝ) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0897.d009332 k sizes locations scales) := by
  unfold _root_.GD.N0232.N0719.N0897.d009332
  infer_instance



def d009334
    (k : ℕ) (sizes : Fin k → ℕ)
    (locations scales : Fin k → ℝ) :
    Measure (Fin k → ℝ × ℝ) :=
  Measure.pi
    (fun i ↦ _root_.GD.N0232.N0719.N1009.d009276 (sizes i) (locations i) (scales i))



theorem d009335
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (locations scales : Fin k → ℝ) :
    (_root_.GD.N0232.N0719.N0897.d009332 k sizes locations scales).map
        (_root_.GD.N0232.N0719.N1009.d009282 k sizes) =
      _root_.GD.N0232.N0719.N0897.d009334 k sizes locations scales := by
  unfold _root_.GD.N0232.N0719.N0897.d009332 _root_.GD.N0232.N0719.N0897.d009334
    _root_.GD.N0232.N0719.N1009.d009282
  rw [Measure.pi_map_pi]
  · congr 1
    funext i
    exact _root_.GD.N0232.N0719.N1009.d009281
      (hsizes i) (locations i) (scales i)
  · intro i
    exact (_root_.GD.N0232.N0719.N1009.d009277 (sizes i)).aemeasurable


def d009336
    (k : ℕ) (sizes : Fin k → ℕ)
    (locations scales : Fin k → ℝ) :
    Measure (Fin k → ℝ) :=
  Measure.pi (fun i ↦
    _root_.GD.N0232.N0719.N0933.d009288 (sizes i) (locations i) (scales i))



theorem d009337
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (locations scales : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0897.d009336 k sizes locations scales =
      Measure.pi (fun i ↦
        gaussianReal (locations i)
          (.mk (scales i ^ 2 / (sizes i : ℝ))
            (div_nonneg (sq_nonneg (scales i))
              (Nat.cast_nonneg (sizes i))))) := by
  unfold _root_.GD.N0232.N0719.N0897.d009336
  congr 1
  funext i
  exact _root_.GD.N0232.N0719.N0933.d009297
    (lt_of_lt_of_le (by decide : 0 < 2) (hsizes i))
    (locations i) (scales i)



theorem d009338
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (locations scales : Fin k → ℝ) :
    (_root_.GD.N0232.N0719.N0897.d009334 k sizes locations scales).map
        (_root_.GD.N0232.N0719.N0933.d009299 k) =
      (_root_.GD.N0232.N0719.N0897.d009336 k sizes locations scales).prod
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
  unfold _root_.GD.N0232.N0719.N0897.d009334 _root_.GD.N0232.N0719.N0897.d009336
    _root_.GD.N0232.N0719.N0933.d009301
  simp_rw [_root_.GD.N0232.N0719.N0933.d009298]
  exact
    (measurePreserving_arrowProdEquivProdArrow
      ℝ ℝ (Fin k)
      (fun i ↦ _root_.GD.N0232.N0719.N0933.d009288 (sizes i) (locations i) (scales i))
      (fun i ↦ _root_.GD.N0232.N0719.N0933.d009289 (sizes i) (scales i))).map_eq



theorem d009339
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (locations scales : Fin k → ℝ) :
    (_root_.GD.N0232.N0719.N0897.d009332 k sizes locations scales).map
        (_root_.GD.N0232.N0719.N0933.d009304 k sizes) =
      (_root_.GD.N0232.N0719.N0897.d009336 k sizes locations scales).prod
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) := by
  calc
    (_root_.GD.N0232.N0719.N0897.d009332 k sizes locations scales).map
        (_root_.GD.N0232.N0719.N0933.d009304 k sizes) =
      ((_root_.GD.N0232.N0719.N0897.d009332 k sizes locations scales).map
        (_root_.GD.N0232.N0719.N1009.d009282 k sizes)).map
          (_root_.GD.N0232.N0719.N0933.d009299 k) := by
            rw [Measure.map_map
              (_root_.GD.N0232.N0719.N0933.d009299 k).measurable
              (_root_.GD.N0232.N0719.N1009.d009284 k sizes)]
            rfl
    _ = (_root_.GD.N0232.N0719.N0897.d009334 k sizes locations scales).map
          (_root_.GD.N0232.N0719.N0933.d009299 k) := by
            rw [_root_.GD.N0232.N0719.N0897.d009335
              k sizes hsizes locations scales]
    _ = (_root_.GD.N0232.N0719.N0897.d009336 k sizes locations scales).prod
          (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) :=
            _root_.GD.N0232.N0719.N0897.d009338
              k sizes hsizes locations scales


def d009340
    (k : ℕ) (sizes : Fin k → ℕ)
    (locations scales : Fin k → ℝ) :
    Measure (_root_.GD.N0232.N0719.N0900.d009096 k) :=
  ((_root_.GD.N0232.N0719.N0897.d009336 k sizes locations scales).prod
      (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales)).map
    (_root_.GD.N0232.N0719.N0933.d009305 k)


theorem d009341
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (locations scales : Fin k → ℝ) :
    (_root_.GD.N0232.N0719.N0897.d009332 k sizes locations scales).map
        (_root_.GD.N0232.N0719.N0900.d009104 k sizes) =
      _root_.GD.N0232.N0719.N0897.d009340 k sizes locations scales := by
  have hsplit := _root_.GD.N0232.N0719.N0897.d009339
    k sizes hsizes locations scales
  calc
    (_root_.GD.N0232.N0719.N0897.d009332 k sizes locations scales).map
        (_root_.GD.N0232.N0719.N0900.d009104 k sizes) =
      (_root_.GD.N0232.N0719.N0897.d009332 k sizes locations scales).map
        (_root_.GD.N0232.N0719.N0933.d009305 k ∘ _root_.GD.N0232.N0719.N0933.d009304 k sizes) := by
          rfl
    _ = ((_root_.GD.N0232.N0719.N0897.d009332 k sizes locations scales).map
          (_root_.GD.N0232.N0719.N0933.d009304 k sizes)).map
            (_root_.GD.N0232.N0719.N0933.d009305 k) := by
          rw [Measure.map_map
            (_root_.GD.N0232.N0719.N0933.d009306 k)
            (_root_.GD.N0232.N0719.N0933.d009308 k sizes)]
    _ = _root_.GD.N0232.N0719.N0897.d009340 k sizes locations scales := by
          rw [hsplit]
          rfl

end

end GD.N0232.N0719.N0897

#print axioms _root_.GD.N0232.N0719.N0897.d009335
#print axioms _root_.GD.N0232.N0719.N0897.d009337
#print axioms _root_.GD.N0232.N0719.N0897.d009338
#print axioms _root_.GD.N0232.N0719.N0897.d009339
#print axioms _root_.GD.N0232.N0719.N0897.d009341
