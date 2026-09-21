import GD.Module0624














open MeasureTheory

namespace GD.N0228.N0548

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0107



def d009148 {k : ℕ} (sizes : Fin k → ℕ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) : _root_.GD.N0232.N0719.N0900.d009096 k where
  mean := s.mean
  meanVariance i := (sizes i : ℝ) * s.meanVariance i



def d009149 {k : ℕ} (sizes : Fin k → ℕ)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) : _root_.GD.N0232.N0719.N0900.d009096 k where
  mean := s.mean
  meanVariance i := s.meanVariance i / (sizes i : ℝ)

@[fun_prop]
theorem d009150 {k : ℕ} (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0228.N0548.d009148 sizes) := by
  rw [measurable_comap_iff]
  change Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 k ↦
    (s.mean, fun i ↦ (sizes i : ℝ) * s.meanVariance i))
  fun_prop

@[fun_prop]
theorem d009151 {k : ℕ} (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0228.N0548.d009149 sizes) := by
  rw [measurable_comap_iff]
  change Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 k ↦
    (s.mean, fun i ↦ s.meanVariance i / (sizes i : ℝ)))
  fun_prop

@[simp]
theorem d009152 {k : ℕ}
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 0 < sizes i) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0228.N0548.d009149 sizes (_root_.GD.N0228.N0548.d009148 sizes s) = s := by
  have hsize : ∀ i, (sizes i : ℝ) ≠ 0 :=
    fun i ↦ Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hsizes i))
  ext i <;> simp [_root_.GD.N0228.N0548.d009148, _root_.GD.N0228.N0548.d009149, hsize i]

@[simp]
theorem d009153 {k : ℕ}
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 0 < sizes i) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0228.N0548.d009148 sizes (_root_.GD.N0228.N0548.d009149 sizes s) = s := by
  have hsize : ∀ i, (sizes i : ℝ) ≠ 0 :=
    fun i ↦ Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hsizes i))
  ext i
  · rfl
  · change (sizes i : ℝ) * (s.meanVariance i / (sizes i : ℝ)) = s.meanVariance i
    exact mul_div_cancel₀ _ (hsize i)



def d009154 {k : ℕ}
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 0 < sizes i) :
    _root_.GD.N0232.N0719.N0900.d009096 k ≃ᵐ _root_.GD.N0232.N0719.N0900.d009096 k where
  toFun := _root_.GD.N0228.N0548.d009148 sizes
  invFun := _root_.GD.N0228.N0548.d009149 sizes
  left_inv := _root_.GD.N0228.N0548.d009152 sizes hsizes
  right_inv := _root_.GD.N0228.N0548.d009153 sizes hsizes
  measurable_toFun := _root_.GD.N0228.N0548.d009150 sizes
  measurable_invFun := _root_.GD.N0228.N0548.d009151 sizes



def d009155 (k : ℕ) (sizes : Fin k → ℕ)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) : _root_.GD.N0232.N0719.N0900.d009096 k where
  mean i := _root_.GD.N0107.d009084 (ω i)
  meanVariance i := _root_.GD.N0107.d009085 (ω i)



theorem d009156 (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0228.N0548.d009148 sizes (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) =
      _root_.GD.N0228.N0548.d009155 k sizes ω := by
  have hsize : ∀ i, (sizes i : ℝ) ≠ 0 :=
    fun i ↦ Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hsizes i))
  ext i
  · rfl
  · change (sizes i : ℝ) *
        (_root_.GD.N0107.d009085 (ω i) / (sizes i : ℝ)) =
      _root_.GD.N0107.d009085 (ω i)
    exact mul_div_cancel₀ _ (hsize i)



theorem d009157 (k : ℕ)
    (sizes : Fin k → ℕ) (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0228.N0548.d009149 sizes (_root_.GD.N0228.N0548.d009155 k sizes ω) =
      _root_.GD.N0232.N0719.N0900.d009104 k sizes ω := by
  rfl

@[fun_prop]
theorem d009158 (k : ℕ) (sizes : Fin k → ℕ) :
    Measurable (_root_.GD.N0228.N0548.d009155 k sizes) := by
  rw [measurable_comap_iff]
  change Measurable (fun ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes ↦
    ((fun i ↦ _root_.GD.N0107.d009084 (ω i)),
      (fun i ↦ _root_.GD.N0107.d009085 (ω i))))
  unfold _root_.GD.N0107.d009084 _root_.GD.N0107.d009085
    _root_.GD.N0126.d006422 _root_.GD.N0126.d006421
    _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
  fun_prop




theorem d009159 (k : ℕ) (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) (ν : Measure (_root_.GD.N0232.N0719.N0900.d009094 k sizes)) :
    ν.map (_root_.GD.N0228.N0548.d009155 k sizes) =
      (ν.map (_root_.GD.N0232.N0719.N0900.d009104 k sizes)).map (_root_.GD.N0228.N0548.d009148 sizes) := by
  rw [Measure.map_map (_root_.GD.N0228.N0548.d009150 sizes)
    (_root_.GD.N0232.N0719.N0900.d009115 k sizes)]
  congr 1
  funext ω
  exact (_root_.GD.N0228.N0548.d009156 k sizes hsizes ω).symm

#print axioms _root_.GD.N0228.N0548.d009150
#print axioms _root_.GD.N0228.N0548.d009151
#print axioms _root_.GD.N0228.N0548.d009152
#print axioms _root_.GD.N0228.N0548.d009153
#print axioms _root_.GD.N0228.N0548.d009154
#print axioms _root_.GD.N0228.N0548.d009156
#print axioms _root_.GD.N0228.N0548.d009157
#print axioms _root_.GD.N0228.N0548.d009158
#print axioms _root_.GD.N0228.N0548.d009159

end

end GD.N0228.N0548
