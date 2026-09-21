import GD.Module0232




















namespace GD.N0238.N0753

noncomputable section

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

local instance : DecidableEq V := Classical.decEq V


def d004397 (f : V → W) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ x : V, f (a • x) = a • f x



abbrev d004398 (V : Type*) [NormedAddCommGroup V] :=
  {x : V // ‖x‖ = 1}


def d004399 (x : V) (hx : x ≠ 0) : _root_.GD.N0238.N0753.d004398 V :=
  ⟨(‖x‖⁻¹ : ℝ) • x, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_pos_iff.mpr hx).ne'⟩


theorem d004400
    (a : ℝ) (ha : 0 < a) (x : V) (hx : x ≠ 0) :
    _root_.GD.N0238.N0753.d004399 (a • x) (smul_ne_zero ha.ne' hx) =
      _root_.GD.N0238.N0753.d004399 x hx := by
  apply Subtype.ext
  change (‖a • x‖⁻¹ : ℝ) • (a • x) = (‖x‖⁻¹ : ℝ) • x
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, smul_smul]
  have hnorm : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx).ne'
  have hcoeff : (a * ‖x‖)⁻¹ * a = ‖x‖⁻¹ := by
    field_simp [ha.ne', hnorm]
  rw [hcoeff]


theorem d004401
    (x : V) (hx : x ≠ 0) (hnorm : ‖x‖ = 1) :
    _root_.GD.N0238.N0753.d004399 x hx = ⟨x, hnorm⟩ := by
  apply Subtype.ext
  simp [_root_.GD.N0238.N0753.d004399, hnorm]



def d004402 (φ : _root_.GD.N0238.N0753.d004398 V → W) : V → W :=
  fun x ↦ if hx : x = 0 then 0 else ‖x‖ • φ (_root_.GD.N0238.N0753.d004399 x hx)


theorem d004403
    (φ : _root_.GD.N0238.N0753.d004398 V → W) :
    _root_.GD.N0238.N0753.d004397 (_root_.GD.N0238.N0753.d004402 φ) := by
  intro a ha x
  by_cases hx : x = 0
  · subst x
    simp [_root_.GD.N0238.N0753.d004402]
  · have hax : a • x ≠ 0 := smul_ne_zero ha.ne' hx
    simp only [_root_.GD.N0238.N0753.d004402, dif_neg hax, dif_neg hx]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    rw [_root_.GD.N0238.N0753.d004400 a ha x hx]
    rw [smul_smul]


theorem d004404
    (φ : _root_.GD.N0238.N0753.d004398 V → W) (u : _root_.GD.N0238.N0753.d004398 V) :
    _root_.GD.N0238.N0753.d004402 φ u = φ u := by
  have hu : (u : V) ≠ 0 := by
    intro hzero
    have := u.property
    simp [hzero] at this
  simp only [_root_.GD.N0238.N0753.d004402, dif_neg hu]
  rw [u.property, one_smul]
  rw [_root_.GD.N0238.N0753.d004401 (u : V) hu u.property]


def d004405 (f : V → W) : _root_.GD.N0238.N0753.d004398 V → W :=
  fun u ↦ f u

theorem d004406
    (φ : _root_.GD.N0238.N0753.d004398 V → W) :
    _root_.GD.N0238.N0753.d004405 (_root_.GD.N0238.N0753.d004402 φ) = φ := by
  funext u
  exact _root_.GD.N0238.N0753.d004404 φ u


theorem d004407
    (f : V → W) (hf : _root_.GD.N0238.N0753.d004397 f) :
    f 0 = 0 := by
  have htwo := hf 2 (by norm_num) 0
  have hsub := congrArg (fun y : W ↦ y - f 0) htwo
  simpa [two_smul] using hsub.symm


theorem d004408
    (x : V) (hx : x ≠ 0) :
    ‖x‖ • (_root_.GD.N0238.N0753.d004399 x hx : V) = x := by
  change ‖x‖ • ((‖x‖⁻¹ : ℝ) • x) = x
  rw [smul_smul]
  simp [(norm_pos_iff.mpr hx).ne']


theorem d004409
    (f : V → W) (hf : _root_.GD.N0238.N0753.d004397 f) :
    _root_.GD.N0238.N0753.d004402 (_root_.GD.N0238.N0753.d004405 f) = f := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [_root_.GD.N0238.N0753.d004402, _root_.GD.N0238.N0753.d004407 f hf]
  · simp only [_root_.GD.N0238.N0753.d004402, dif_neg hx, _root_.GD.N0238.N0753.d004405]
    have hscale := hf ‖x‖ (norm_pos_iff.mpr hx) (_root_.GD.N0238.N0753.d004399 x hx : V)
    rw [_root_.GD.N0238.N0753.d004408 x hx] at hscale
    exact hscale.symm



theorem d004410
    (f g : V → W)
    (hf : _root_.GD.N0238.N0753.d004397 f)
    (hg : _root_.GD.N0238.N0753.d004397 g)
    (hsphere : ∀ u : _root_.GD.N0238.N0753.d004398 V, f u = g u) :
    f = g := by
  calc
    f = _root_.GD.N0238.N0753.d004402 (_root_.GD.N0238.N0753.d004405 f) :=
      (_root_.GD.N0238.N0753.d004409 f hf).symm
    _ = _root_.GD.N0238.N0753.d004402 (_root_.GD.N0238.N0753.d004405 g) := by
      apply congrArg _root_.GD.N0238.N0753.d004402
      funext u
      exact hsphere u
    _ = g := _root_.GD.N0238.N0753.d004409 g hg


def d004411 (V W : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] :=
  {f : V → W // _root_.GD.N0238.N0753.d004397 f}



def d004412 :
    _root_.GD.N0238.N0753.d004411 V W ≃ (_root_.GD.N0238.N0753.d004398 V → W) where
  toFun f := _root_.GD.N0238.N0753.d004405 f.1
  invFun φ := ⟨_root_.GD.N0238.N0753.d004402 φ,
    _root_.GD.N0238.N0753.d004403 φ⟩
  left_inv f := by
    apply Subtype.ext
    exact _root_.GD.N0238.N0753.d004409 f.1 f.2
  right_inv φ := _root_.GD.N0238.N0753.d004406 φ




theorem d004413
    (f g : ℝ → W)
    (hf : _root_.GD.N0238.N0753.d004397 f)
    (hg : _root_.GD.N0238.N0753.d004397 g)
    (hone : f 1 = g 1)
    (hneg : f (-1) = g (-1)) :
    f = g := by
  funext x
  by_cases hxzero : x = 0
  · subst x
    rw [_root_.GD.N0238.N0753.d004407 f hf,
      _root_.GD.N0238.N0753.d004407 g hg]
  · by_cases hxpos : 0 < x
    · have hfx := hf x hxpos 1
      have hgx := hg x hxpos 1
      calc
        f x = x • f 1 := by simpa using hfx
        _ = x • g 1 := congrArg (fun y : W ↦ x • y) hone
        _ = g x := by simpa using hgx.symm
    · have hxneg : 0 < -x := neg_pos.mpr (lt_of_le_of_ne
        (le_of_not_gt hxpos) hxzero)
      have hfx := hf (-x) hxneg (-1)
      have hgx := hg (-x) hxneg (-1)
      have hmul : (-x : ℝ) • (-1 : ℝ) = x := by
        simp
      rw [hmul] at hfx hgx
      calc
        f x = (-x) • f (-1) := hfx
        _ = (-x) • g (-1) :=
          congrArg (fun y : W ↦ (-x) • y) hneg
        _ = g x := hgx.symm

end

end GD.N0238.N0753

#print axioms _root_.GD.N0238.N0753.d004403
#print axioms _root_.GD.N0238.N0753.d004410
#print axioms _root_.GD.N0238.N0753.d004412
#print axioms _root_.GD.N0238.N0753.d004413
