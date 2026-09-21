import GD.Module0414



















namespace GD.N0124


def d006405 (p : _root_.GD.N0124.d006387) : Fin 3 → ℝ :=
  ![p.1, p.2.1, p.2.2]


def d006406 (x : Fin 3 → ℝ) : _root_.GD.N0124.d006387 :=
  (x 0, (x 1, x 2))



noncomputable def d006407 : _root_.GD.N0124.d006387 ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun := _root_.GD.N0124.d006405
  invFun := _root_.GD.N0124.d006406
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' c x := by
    funext i
    fin_cases i <;> rfl


noncomputable def d006408 (e : ℝ) (p : _root_.GD.N0124.d006387) :
    _root_.GD.N0124.d006387 →ₗ[ℝ] _root_.GD.N0124.d006387 where
  toFun v :=
    (-p.2.2 / (1 - e) * v.1 + (1 - p.1) / (1 - e) * v.2.2,
      (p.2.2 / e * v.1 + p.1 / e * v.2.2,
        p.2.2 * v.2.1 + p.2.1 * v.2.2))
  map_add' x y := by
    apply Prod.ext
    · dsimp
      ring
    · apply Prod.ext
      · dsimp
        ring
      · dsimp
        ring
  map_smul' c x := by
    apply Prod.ext
    · dsimp
      ring
    · apply Prod.ext
      · dsimp
        ring
      · dsimp
        ring




noncomputable def d006409 (e : ℝ) (p : _root_.GD.N0124.d006387) :
    _root_.GD.N0124.d006387 →L[ℝ] _root_.GD.N0124.d006387 :=
  LinearMap.toContinuousLinearMap (_root_.GD.N0124.d006408 e p)

@[simp]
theorem d006410 (e : ℝ) (p v : _root_.GD.N0124.d006387) :
    _root_.GD.N0124.d006409 e p v =
      (-p.2.2 / (1 - e) * v.1 + (1 - p.1) / (1 - e) * v.2.2,
        (p.2.2 / e * v.1 + p.1 / e * v.2.2,
          p.2.2 * v.2.1 + p.2.1 * v.2.2)) := by
  rfl




theorem d006411 (e : ℝ) (p : _root_.GD.N0124.d006387) :
    HasFDerivAt (_root_.GD.N0124.d006392 e) (_root_.GD.N0124.d006409 e p) p := by
  let dL : _root_.GD.N0124.d006387 →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
  let dF : _root_.GD.N0124.d006387 →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  let dH : _root_.GD.N0124.d006387 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have hL :
      HasFDerivAt (fun q : _root_.GD.N0124.d006387 => q.1)
        dL p :=
    hasFDerivAt_fst
  have hF :
      HasFDerivAt (fun q : _root_.GD.N0124.d006387 => q.2.1)
        dF p :=
    (hasFDerivAt_snd : HasFDerivAt (fun q : _root_.GD.N0124.d006387 => q.2)
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) p).fst
  have hH :
      HasFDerivAt (fun q : _root_.GD.N0124.d006387 => q.2.2)
        dH p :=
    (hasFDerivAt_snd : HasFDerivAt (fun q : _root_.GD.N0124.d006387 => q.2)
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) p).snd
  have hRx :=
    (((hasFDerivAt_const (1 : ℝ) p).sub hL).mul hH).mul_const ((1 - e)⁻¹)
  have hRy := (hL.mul hH).mul_const e⁻¹
  have hW := hF.mul hH
  let D : _root_.GD.N0124.d006387 →L[ℝ] _root_.GD.N0124.d006387 :=
    ((1 - e)⁻¹ • ((1 - p.1) • dH + p.2.2 • (0 - dL))).prod
      ((e⁻¹ • (p.1 • dH + p.2.2 • dL)).prod
        (p.2.1 • dH + p.2.2 • dF))
  have h :
      HasFDerivAt
        (fun q : _root_.GD.N0124.d006387 =>
          (((1 - q.1) * q.2.2) * (1 - e)⁻¹,
            ((q.1 * q.2.2) * e⁻¹, q.2.1 * q.2.2)))
        D p := by
    simpa [D] using hRx.prodMk (hRy.prodMk hW)
  have hD : D = _root_.GD.N0124.d006409 e p := by
    apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext
    · simp [D, dL, dF, dH, _root_.GD.N0124.d006409, _root_.GD.N0124.d006408]
      ring
    · apply Prod.ext
      · simp [D, dL, dF, dH, _root_.GD.N0124.d006409, _root_.GD.N0124.d006408]
        ring
      · simp [D, dL, dF, dH, _root_.GD.N0124.d006409, _root_.GD.N0124.d006408]
        ring
  apply (h.congr_fderiv hD).congr_of_eventuallyEq
  filter_upwards with q
  simp only [_root_.GD.N0124.d006392, div_eq_mul_inv]


theorem d006412 (e : ℝ) :
    Differentiable ℝ (_root_.GD.N0124.d006392 e) :=
  fun p => (_root_.GD.N0124.d006411 e p).differentiableAt


theorem d006413 (e : ℝ) (p : _root_.GD.N0124.d006387) :
    fderiv ℝ (_root_.GD.N0124.d006392 e) p = _root_.GD.N0124.d006409 e p :=
  (_root_.GD.N0124.d006411 e p).fderiv


noncomputable def d006414 (e : ℝ) (p : _root_.GD.N0124.d006387) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  _root_.GD.N0124.d006407.toLinearMap.comp
    ((_root_.GD.N0124.d006408 e p).comp
      _root_.GD.N0124.d006407.symm.toLinearMap)



theorem d006415 (e : ℝ) (p : _root_.GD.N0124.d006387) :
    _root_.GD.N0124.d006414 e p = Matrix.toLin' (_root_.GD.N0124.d006401 e p) := by
  ext x i
  fin_cases x <;> fin_cases i <;>
    simp [_root_.GD.N0124.d006414, _root_.GD.N0124.d006407, _root_.GD.N0124.d006405, _root_.GD.N0124.d006406,
      _root_.GD.N0124.d006408, _root_.GD.N0124.d006401, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, Pi.single_apply]




theorem d006416 (e : ℝ) (p : _root_.GD.N0124.d006387) :
    LinearMap.toMatrix' (_root_.GD.N0124.d006414 e p) =
      _root_.GD.N0124.d006401 e p := by
  rw [_root_.GD.N0124.d006415,
    LinearMap.toMatrix'_toLin']



theorem d006417 {e : ℝ} (p : _root_.GD.N0124.d006387)
    (he : e ≠ 0) (h1e : 1 - e ≠ 0) :
    (LinearMap.toMatrix' (_root_.GD.N0124.d006414 e p)).det =
      p.2.2 ^ 2 / (e * (1 - e)) := by
  rw [_root_.GD.N0124.d006416]
  exact _root_.GD.N0124.d006402 p he h1e



theorem d006418 {e : ℝ} {p : _root_.GD.N0124.d006387}
    (he0 : 0 < e) (he1 : e < 1) (hp : p ∈ _root_.GD.N0124.d006389) :
    0 < (LinearMap.toMatrix' (_root_.GD.N0124.d006414 e p)).det := by
  rw [_root_.GD.N0124.d006416]
  exact _root_.GD.N0124.d006404 he0 he1 hp

end GD.N0124
