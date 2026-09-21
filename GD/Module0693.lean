import GD.Module0692



















open MeasureTheory
open scoped BigOperators

namespace GD.N0232.N0719.N0852

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1018



def d010153 {k : ℕ} (σ : Equiv.Perm (Fin k))
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) : _root_.GD.N0232.N0719.N0900.d009096 k where
  mean i := s.mean (σ i)
  meanVariance i := s.meanVariance (σ i)

@[simp]
theorem d010154 {k : ℕ} (σ : Equiv.Perm (Fin k))
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i : Fin k) :
    (_root_.GD.N0232.N0719.N0852.d010153 σ s).mean i = s.mean (σ i) :=
  rfl

@[simp]
theorem d010155 {k : ℕ} (σ : Equiv.Perm (Fin k))
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i : Fin k) :
    (_root_.GD.N0232.N0719.N0852.d010153 σ s).meanVariance i = s.meanVariance (σ i) :=
  rfl

@[fun_prop]
theorem d010156 {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    Measurable (_root_.GD.N0232.N0719.N0852.d010153 σ : _root_.GD.N0232.N0719.N0900.d009096 k → _root_.GD.N0232.N0719.N0900.d009096 k) := by
  rw [measurable_comap_iff]
  change Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 k =>
    ((fun i => s.mean (σ i)), fun i => s.meanVariance (σ i)))
  fun_prop

@[simp]
theorem d010157 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0852.d010153 (Equiv.refl (Fin k)) s = s := by
  ext i <;> rfl

theorem d010158 {k : ℕ}
    (σ τ : Equiv.Perm (Fin k)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0852.d010153 σ (_root_.GD.N0232.N0719.N0852.d010153 τ s) =
      _root_.GD.N0232.N0719.N0852.d010153 (σ.trans τ) s := by
  ext i <;> rfl


def d010159 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (triangle : Fin 3 ↪ Fin k) : Fin 3 ↪ Fin k :=
  triangle.trans σ.toEmbedding

@[simp]
theorem d010160 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (triangle : Fin 3 ↪ Fin k) (j : Fin 3) :
    _root_.GD.N0232.N0719.N0852.d010159 σ triangle j = σ (triangle j) :=
  rfl



def d010161 {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (Fin 3 ↪ Fin k) ≃ (Fin 3 ↪ Fin k) where
  toFun := _root_.GD.N0232.N0719.N0852.d010159 σ
  invFun := _root_.GD.N0232.N0719.N0852.d010159 σ.symm
  left_inv triangle := by
    ext j
    simp [_root_.GD.N0232.N0719.N0852.d010159]
  right_inv triangle := by
    ext j
    simp [_root_.GD.N0232.N0719.N0852.d010159]

@[simp]
theorem d010162 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009106 (_root_.GD.N0232.N0719.N0852.d010153 σ s) i = _root_.GD.N0232.N0719.N0900.d009106 s (σ i) :=
  rfl

theorem d010163 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0900.d009107 (_root_.GD.N0232.N0719.N0852.d010153 σ s) = _root_.GD.N0232.N0719.N0900.d009107 s := by
  unfold _root_.GD.N0232.N0719.N0900.d009107
  simpa using (Equiv.sum_comp σ (fun i : Fin k => _root_.GD.N0232.N0719.N0900.d009106 s i))

@[simp]
theorem d010164 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0852.d010153 σ s) i = _root_.GD.N0232.N0719.N0900.d009108 s (σ i) := by
  unfold _root_.GD.N0232.N0719.N0900.d009108
  rw [_root_.GD.N0232.N0719.N0852.d010163]
  rfl

theorem d010165 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0852.d010153 σ s) = _root_.GD.N0232.N0719.N0900.d009110 s := by
  unfold _root_.GD.N0232.N0719.N0900.d009110
  simpa using
    (Equiv.sum_comp σ (fun i : Fin k => _root_.GD.N0232.N0719.N0900.d009108 s i * s.mean i))

theorem d010166 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010019 (_root_.GD.N0232.N0719.N0852.d010153 σ s) ↔ _root_.GD.N0232.N0719.N1018.d010019 s := by
  constructor
  · intro h i
    simpa using h (σ.symm i)
  · intro h i
    simpa using h (σ i)

theorem d010167 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010020 (_root_.GD.N0232.N0719.N0852.d010153 σ s) = _root_.GD.N0232.N0719.N1018.d010020 s := by
  unfold _root_.GD.N0232.N0719.N1018.d010020
  rw [_root_.GD.N0232.N0719.N0852.d010166]

theorem d010168 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (triangle : Fin 3 ↪ Fin k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010012 triangle (_root_.GD.N0232.N0719.N0852.d010153 σ s) =
      _root_.GD.N0232.N0719.N1018.d010012 (_root_.GD.N0232.N0719.N0852.d010159 σ triangle) s := by
  unfold _root_.GD.N0232.N0719.N1018.d010012
  simp_rw [_root_.GD.N0232.N0719.N0852.d010164]
  rfl

theorem d010169 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (triangle : Fin 3 ↪ Fin k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (j : Fin 3) :
    _root_.GD.N0232.N0719.N1018.d010013 triangle (_root_.GD.N0232.N0719.N0852.d010153 σ s) j =
      _root_.GD.N0232.N0719.N1018.d010013 (_root_.GD.N0232.N0719.N0852.d010159 σ triangle) s j := by
  unfold _root_.GD.N0232.N0719.N1018.d010013
  rw [_root_.GD.N0232.N0719.N0852.d010168, _root_.GD.N0232.N0719.N0852.d010164]
  rfl

theorem d010170 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (triangle : Fin 3 ↪ Fin k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (j : Fin 3) :
    _root_.GD.N0232.N0719.N1018.d010014 triangle (_root_.GD.N0232.N0719.N0852.d010153 σ s) j =
      _root_.GD.N0232.N0719.N1018.d010014 (_root_.GD.N0232.N0719.N0852.d010159 σ triangle) s j :=
  rfl

theorem d010171 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (triangle : Fin 3 ↪ Fin k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010015 triangle (_root_.GD.N0232.N0719.N0852.d010153 σ s) =
      _root_.GD.N0232.N0719.N1018.d010015 (_root_.GD.N0232.N0719.N0852.d010159 σ triangle) s := by
  rfl

theorem d010172 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (triangle : Fin 3 ↪ Fin k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010016 triangle (_root_.GD.N0232.N0719.N0852.d010153 σ s) =
      _root_.GD.N0232.N0719.N1018.d010016 (_root_.GD.N0232.N0719.N0852.d010159 σ triangle) s := by
  unfold _root_.GD.N0232.N0719.N1018.d010016
  simp_rw [_root_.GD.N0232.N0719.N0852.d010169, _root_.GD.N0232.N0719.N0852.d010170]

theorem d010173 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (triangle : Fin 3 ↪ Fin k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010017 triangle (_root_.GD.N0232.N0719.N0852.d010153 σ s) =
      _root_.GD.N0232.N0719.N1018.d010017 (_root_.GD.N0232.N0719.N0852.d010159 σ triangle) s := by
  unfold _root_.GD.N0232.N0719.N1018.d010017
  simp_rw [_root_.GD.N0232.N0719.N0852.d010169, _root_.GD.N0232.N0719.N0852.d010170,
    _root_.GD.N0232.N0719.N0852.d010172]

theorem d010174 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (triangle : Fin 3 ↪ Fin k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010018 triangle (_root_.GD.N0232.N0719.N0852.d010153 σ s) =
      _root_.GD.N0232.N0719.N1018.d010018 (_root_.GD.N0232.N0719.N0852.d010159 σ triangle) s := by
  unfold _root_.GD.N0232.N0719.N1018.d010018
  rw [_root_.GD.N0232.N0719.N0852.d010169, _root_.GD.N0232.N0719.N0852.d010169,
    _root_.GD.N0232.N0719.N0852.d010169, _root_.GD.N0232.N0719.N0852.d010170,
    _root_.GD.N0232.N0719.N0852.d010170, _root_.GD.N0232.N0719.N0852.d010170]



theorem d010175 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (triangle : Fin 3 ↪ Fin k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0852.d010153 σ s) =
      _root_.GD.N0232.N0719.N1018.d010021 (_root_.GD.N0232.N0719.N0852.d010159 σ triangle) s := by
  unfold _root_.GD.N0232.N0719.N1018.d010021
  rw [_root_.GD.N0232.N0719.N0852.d010167, _root_.GD.N0232.N0719.N0852.d010168,
    _root_.GD.N0232.N0719.N0852.d010174, _root_.GD.N0232.N0719.N0852.d010171,
    _root_.GD.N0232.N0719.N0852.d010173]



def d010176 (k : ℕ) : ℝ :=
  ((Fintype.card (Fin 3 ↪ Fin k) : ℕ) : ℝ)⁻¹



def d010177 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  _root_.GD.N0232.N0719.N0852.d010176 k *
    ∑ triangle : Fin 3 ↪ Fin k, _root_.GD.N0232.N0719.N1018.d010021 triangle s


def d010178 {k : ℕ} (ε : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  _root_.GD.N0232.N0719.N0900.d009110 s + ε * _root_.GD.N0232.N0719.N0852.d010177 s


def d010179
    (k : ℕ) (sizes : Fin k → ℕ) (ε : ℝ)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0852.d010178 ε (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)

theorem d010180 {k : ℕ} (hk : 3 ≤ k) :
    0 < _root_.GD.N0232.N0719.N0852.d010176 k := by
  haveI : Nonempty (Fin 3 ↪ Fin k) := ⟨Fin.castLEEmb hk⟩
  unfold _root_.GD.N0232.N0719.N0852.d010176
  positivity

theorem d010181 {k : ℕ} (hk : 3 ≤ k) :
    ∑ _triangle : Fin 3 ↪ Fin k, _root_.GD.N0232.N0719.N0852.d010176 k = 1 := by
  have hcard : (Fintype.card (Fin 3 ↪ Fin k) : ℝ) ≠ 0 := by
    haveI : Nonempty (Fin 3 ↪ Fin k) := ⟨Fin.castLEEmb hk⟩
    exact_mod_cast Fintype.card_ne_zero
  calc
    (∑ _triangle : Fin 3 ↪ Fin k, _root_.GD.N0232.N0719.N0852.d010176 k) =
        (Fintype.card (Fin 3 ↪ Fin k) : ℝ) *
          _root_.GD.N0232.N0719.N0852.d010176 k := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 1 := by
      unfold _root_.GD.N0232.N0719.N0852.d010176
      exact mul_inv_cancel₀ hcard

@[fun_prop]
theorem d010182 {k : ℕ} :
    Measurable (_root_.GD.N0232.N0719.N0852.d010177 : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N0852.d010177
  fun_prop

@[fun_prop]
theorem d010183 {k : ℕ} (ε : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0852.d010178 ε : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N0852.d010178
  fun_prop

@[fun_prop]
theorem d010184
    (k : ℕ) (sizes : Fin k → ℕ) (ε : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0852.d010179 k sizes ε) := by
  unfold _root_.GD.N0232.N0719.N0852.d010179
  fun_prop



theorem d010185 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0852.d010177 (_root_.GD.N0232.N0719.N0852.d010153 σ s) =
      _root_.GD.N0232.N0719.N0852.d010177 s := by
  unfold _root_.GD.N0232.N0719.N0852.d010177
  simp_rw [_root_.GD.N0232.N0719.N0852.d010175]
  congr 1
  simpa [_root_.GD.N0232.N0719.N0852.d010161] using
    (Equiv.sum_comp (_root_.GD.N0232.N0719.N0852.d010161 σ)
      (fun triangle : Fin 3 ↪ Fin k => _root_.GD.N0232.N0719.N1018.d010021 triangle s))



theorem d010186 {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (ε : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0852.d010178 ε (_root_.GD.N0232.N0719.N0852.d010153 σ s) =
      _root_.GD.N0232.N0719.N0852.d010178 ε s := by
  unfold _root_.GD.N0232.N0719.N0852.d010178
  rw [_root_.GD.N0232.N0719.N0852.d010165, _root_.GD.N0232.N0719.N0852.d010185]



theorem d010187 {k : ℕ}
    (hk : 0 < k) (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0852.d010177 (_root_.GD.N0232.N0719.N0900.d009101 location scale s) =
      scale * _root_.GD.N0232.N0719.N0852.d010177 s := by
  unfold _root_.GD.N0232.N0719.N0852.d010177
  simp_rw [_root_.GD.N0232.N0719.N1018.d010057 hk _ location hscale s]
  rw [← Finset.mul_sum]
  ring



theorem d010188 {k : ℕ}
    (hk : 0 < k) (ε location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0852.d010178 ε (_root_.GD.N0232.N0719.N0900.d009101 location scale s) =
      location + scale * _root_.GD.N0232.N0719.N0852.d010178 ε s := by
  unfold _root_.GD.N0232.N0719.N0852.d010178
  rw [_root_.GD.N0232.N0719.N0900.d009145 hk location hscale,
    _root_.GD.N0232.N0719.N0852.d010187 hk location hscale]
  ring


theorem d010189
    {k : ℕ} (hk : 0 < k)
    {sizes : Fin k → ℕ} (hsizes : ∀ i, 0 < sizes i)
    (ε location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0232.N0719.N0852.d010179 k sizes ε
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) =
      location + scale * _root_.GD.N0232.N0719.N0852.d010179 k sizes ε ω := by
  unfold _root_.GD.N0232.N0719.N0852.d010179
  rw [_root_.GD.N0232.N0719.N0900.d009139 hsizes location scale]
  exact _root_.GD.N0232.N0719.N0852.d010188 hk ε location hscale _

end

end GD.N0232.N0719.N0852
