import GD.Module0629



























open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0232.N0719.N1009

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0107
open _root_.GD.N0232.N0719



def d009272
    (n : ℕ) (x : _root_.GD.N0137.d008894 n) : ℝ × ℝ :=
  (_root_.GD.N0107.d009084 x, _root_.GD.N0107.d009085 x / (n : ℝ))



def d009273
    (n : ℕ) (x : _root_.GD.N0137.d008894 n) : ℝ × ℝ :=
  (_root_.GD.N0137.d008896 n x, _root_.GD.N0137.d008897 n x)



def d009274
    (n : ℕ) (location scale : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (location + (scale / Real.sqrt n) * z.1,
    (scale ^ 2 / n) * z.2)


noncomputable def d009275 (n : ℕ) :
    Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod
    (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
      (((n - 1 : ℕ) : ℝ) / 2))



noncomputable def d009276
    (n : ℕ) (location scale : ℝ) : Measure (ℝ × ℝ) :=
  (_root_.GD.N0232.N0719.N1009.d009275 n).map
    (_root_.GD.N0232.N0719.N1009.d009274 n location scale)

@[fun_prop]
theorem d009277 (n : ℕ) :
    Measurable (_root_.GD.N0232.N0719.N1009.d009272 n) := by
  unfold _root_.GD.N0232.N0719.N1009.d009272 _root_.GD.N0107.d009084 _root_.GD.N0107.d009085
    _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
    _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
  fun_prop

@[fun_prop]
theorem d009278 (n : ℕ) :
    Measurable (_root_.GD.N0232.N0719.N1009.d009273 n) := by
  unfold _root_.GD.N0232.N0719.N1009.d009273
  fun_prop

@[fun_prop]
theorem d009279
    (n : ℕ) (location scale : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N1009.d009274 n location scale) := by
  unfold _root_.GD.N0232.N0719.N1009.d009274
  fun_prop



theorem d009280
    {n : ℕ} (hn : 2 ≤ n)
    (location scale : ℝ) (x : _root_.GD.N0137.d008894 n) :
    _root_.GD.N0232.N0719.N1009.d009272 n (_root_.GD.N0107.d009018 n location scale x) =
      _root_.GD.N0232.N0719.N1009.d009274 n location scale
        (_root_.GD.N0232.N0719.N1009.d009273 n x) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnR)
  apply Prod.ext
  · unfold _root_.GD.N0232.N0719.N1009.d009272 _root_.GD.N0232.N0719.N1009.d009274
      _root_.GD.N0232.N0719.N1009.d009273 _root_.GD.N0107.d009084 _root_.GD.N0137.d008896
    rw [_root_.GD.N0107.d009086 hn0 location scale x]
    field_simp [hsqrt]
  · unfold _root_.GD.N0232.N0719.N1009.d009272 _root_.GD.N0232.N0719.N1009.d009274
      _root_.GD.N0232.N0719.N1009.d009273 _root_.GD.N0137.d008897
      _root_.GD.N0107.d009085
    rw [_root_.GD.N0107.d009088 hn0 location scale x]
    ring


theorem d009281
    {n : ℕ} (hn : 2 ≤ n)
    (location scale : ℝ) :
    (_root_.GD.N0232.N0719.d009175 n location scale).map (_root_.GD.N0232.N0719.N1009.d009272 n) =
      _root_.GD.N0232.N0719.N1009.d009276 n location scale := by
  change
    ((_root_.GD.N0137.d008895 n).map (_root_.GD.N0107.d009018 n location scale)).map
        (_root_.GD.N0232.N0719.N1009.d009272 n) =
      _root_.GD.N0232.N0719.N1009.d009276 n location scale
  rw [Measure.map_map
    (_root_.GD.N0232.N0719.N1009.d009277 n)
    (_root_.GD.N0107.d009020 n location scale)]
  rw [show
      _root_.GD.N0232.N0719.N1009.d009272 n ∘ _root_.GD.N0107.d009018 n location scale =
        _root_.GD.N0232.N0719.N1009.d009274 n location scale ∘
          _root_.GD.N0232.N0719.N1009.d009273 n by
      funext x
      exact _root_.GD.N0232.N0719.N1009.d009280 hn location scale x]
  rw [← Measure.map_map
    (_root_.GD.N0232.N0719.N1009.d009279 n location scale)
    (_root_.GD.N0232.N0719.N1009.d009278 n)]
  rw [show
      (_root_.GD.N0137.d008895 n).map
          (_root_.GD.N0232.N0719.N1009.d009273 n) =
        _root_.GD.N0232.N0719.N1009.d009275 n by
      exact _root_.GD.N0137.d008909 n hn]
  rfl


def d009282
    (k : ℕ) (sizes : Fin k → ℕ)
    (x : _root_.GD.N0232.N0719.d009173 k sizes) : ∀ i : Fin k, ℝ × ℝ :=
  fun i => _root_.GD.N0232.N0719.N1009.d009272 (sizes i) (x i)


noncomputable def d009283
    (k : ℕ) (sizes : Fin k → ℕ)
    (location : ℝ) (scales : Fin k → ℝ) :
    Measure (∀ i : Fin k, ℝ × ℝ) :=
  Measure.pi
    (fun i => _root_.GD.N0232.N0719.N1009.d009276 (sizes i) location (scales i))

@[fun_prop]
theorem d009284
    (k : ℕ) (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0232.N0719.N1009.d009282 k sizes) := by
  unfold _root_.GD.N0232.N0719.N1009.d009282
  fun_prop






theorem d009285
    (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    (_root_.GD.N0232.N0719.d009176 k sizes location scales).map
        (_root_.GD.N0232.N0719.N1009.d009282 k sizes) =
      _root_.GD.N0232.N0719.N1009.d009283 k sizes location scales := by
  unfold _root_.GD.N0232.N0719.d009176 _root_.GD.N0232.N0719.N1009.d009282 _root_.GD.N0232.N0719.N1009.d009283
  rw [Measure.pi_map_pi]
  · congr 1
    funext i
    exact _root_.GD.N0232.N0719.N1009.d009281
      (hsizes i) location (scales i)
  · intro i
    exact (_root_.GD.N0232.N0719.N1009.d009277 (sizes i)).aemeasurable

end

end GD.N0232.N0719.N1009
