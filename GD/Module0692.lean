import GD.Module0687




















open scoped BigOperators

namespace GD.N0232.N0719.N1017

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1016
open _root_.GD.N0232.N0719.N1018


def d010128 (p z : Fin 3 → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1016.d003608 (p 0) (p 1) (p 2) (z 0) (z 1) (z 2)


def d010129 (p z : Fin 3 → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1016.d003609 (p 0) (p 1) (p 2) (z 0) (z 1) (z 2)


def d010130 (f : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, f i j



theorem d010131
    (σ : Equiv.Perm (Fin 3)) (f : Fin 3 → Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N1017.d010130 (fun i j => f (σ i) (σ j)) = _root_.GD.N0232.N0719.N1017.d010130 f := by
  unfold _root_.GD.N0232.N0719.N1017.d010130
  calc
    (∑ i : Fin 3, ∑ j : Fin 3, f (σ i) (σ j)) =
        ∑ i : Fin 3, ∑ j : Fin 3, f (σ i) j := by
      apply Fintype.sum_congr
      intro i
      exact Equiv.sum_comp σ (fun j => f (σ i) j)
    _ = ∑ i : Fin 3, ∑ j : Fin 3, f i j :=
      Equiv.sum_comp σ (fun i => ∑ j : Fin 3, f i j)


def d010132 (pᵢ pⱼ zᵢ zⱼ : ℝ) : ℝ :=
  (zᵢ - zⱼ) ^ 2 / (pᵢ + pⱼ)


def d010133 (p z : Fin 3 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * _root_.GD.N0232.N0719.N1017.d010130 (fun i j =>
    if i = j then 0 else _root_.GD.N0232.N0719.N1017.d010132 (p i) (p j) (z i) (z j))


def d010134 (pᵢ pⱼ zᵢ zⱼ : ℝ) : ℝ :=
  (-pᵢ * zᵢ ^ 3 - pⱼ * zⱼ ^ 3 +
      3 * pᵢ * zᵢ ^ 2 * zⱼ + 3 * pⱼ * zᵢ * zⱼ ^ 2) /
    (3 * (pᵢ + pⱼ))





def d010135 (p z : Fin 3 → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N1017.d010134 (p 0) (p 1) (z 0) (z 1) +
  _root_.GD.N0232.N0719.N1017.d010134 (p 0) (p 2) (z 0) (z 2) +
  _root_.GD.N0232.N0719.N1017.d010134 (p 1) (p 2) (z 1) (z 2) -
  2 * z 0 * z 1 * z 2


def d010136 (p z : Fin 3 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * _root_.GD.N0232.N0719.N1017.d010130 (fun i j =>
    if i = j then 0 else _root_.GD.N0232.N0719.N1017.d010134 (p i) (p j) (z i) (z j)) -
  2 * ∏ i : Fin 3, z i




theorem d010137
    (σ : Equiv.Perm (Fin 3)) (p z : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N1017.d010128 (p ∘ σ) (z ∘ σ) = _root_.GD.N0232.N0719.N1017.d010128 p z := by
  have hsymmetric (q w : Fin 3 → ℝ) :
      _root_.GD.N0232.N0719.N1017.d010128 q w = _root_.GD.N0232.N0719.N1017.d010133 q w := by
    simp [_root_.GD.N0232.N0719.N1017.d010128, _root_.GD.N0232.N0719.N1017.d010133, _root_.GD.N0232.N0719.N1017.d010130, _root_.GD.N0232.N0719.N1017.d010132, _root_.GD.N0232.N0719.N1016.d003608,
      Fin.sum_univ_succ]
    ring
  have hreindex : _root_.GD.N0232.N0719.N1017.d010133 (p ∘ σ) (z ∘ σ) =
      _root_.GD.N0232.N0719.N1017.d010133 p z := by
    unfold _root_.GD.N0232.N0719.N1017.d010133
    simp only [Function.comp_apply]
    have h := _root_.GD.N0232.N0719.N1017.d010131 σ (fun i j : Fin 3 =>
      if i = j then 0 else _root_.GD.N0232.N0719.N1017.d010132 (p i) (p j) (z i) (z j))
    simpa using h
  calc
    _root_.GD.N0232.N0719.N1017.d010128 (p ∘ σ) (z ∘ σ) =
        _root_.GD.N0232.N0719.N1017.d010133 (p ∘ σ) (z ∘ σ) := hsymmetric _ _
    _ = _root_.GD.N0232.N0719.N1017.d010133 p z := hreindex
    _ = _root_.GD.N0232.N0719.N1017.d010128 p z := (hsymmetric _ _).symm



theorem d010138
    (σ : Equiv.Perm (Fin 3)) (p z : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N1017.d010135 (p ∘ σ) (z ∘ σ) = _root_.GD.N0232.N0719.N1017.d010135 p z := by
  have hexplicit (q w : Fin 3 → ℝ) :
      _root_.GD.N0232.N0719.N1017.d010135 q w = _root_.GD.N0232.N0719.N1017.d010136 q w := by
    simp [_root_.GD.N0232.N0719.N1017.d010135, _root_.GD.N0232.N0719.N1017.d010136, _root_.GD.N0232.N0719.N1017.d010130, _root_.GD.N0232.N0719.N1017.d010134,
      Fin.sum_univ_succ, Fin.prod_univ_succ]
    ring
  have hreindex : _root_.GD.N0232.N0719.N1017.d010136 (p ∘ σ) (z ∘ σ) =
      _root_.GD.N0232.N0719.N1017.d010136 p z := by
    unfold _root_.GD.N0232.N0719.N1017.d010136
    simp only [Function.comp_apply]
    rw [Equiv.prod_comp σ z]
    have h := _root_.GD.N0232.N0719.N1017.d010131 σ (fun i j : Fin 3 =>
      if i = j then 0 else _root_.GD.N0232.N0719.N1017.d010134 (p i) (p j) (z i) (z j))
    simpa using h
  calc
    _root_.GD.N0232.N0719.N1017.d010135 (p ∘ σ) (z ∘ σ) =
        _root_.GD.N0232.N0719.N1017.d010136 (p ∘ σ) (z ∘ σ) := hexplicit _ _
    _ = _root_.GD.N0232.N0719.N1017.d010136 p z := hreindex
    _ = _root_.GD.N0232.N0719.N1017.d010135 p z := (hexplicit _ _).symm







theorem d010139
    (p z : Fin 3 → ℝ) (hp : ∀ i, 0 < p i) :
    _root_.GD.N0232.N0719.N1017.d010129 p z = _root_.GD.N0232.N0719.N1017.d010135 p z := by
  simp only [_root_.GD.N0232.N0719.N1017.d010129, _root_.GD.N0232.N0719.N1017.d010135, _root_.GD.N0232.N0719.N1017.d010134, _root_.GD.N0232.N0719.N1016.d003609]
  field_simp [ne_of_gt (add_pos (hp 0) (hp 1)),
    ne_of_gt (add_pos (hp 0) (hp 2)),
    ne_of_gt (add_pos (hp 1) (hp 2))]
  ring








theorem d010140
    (σ : Equiv.Perm (Fin 3)) (p z : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) :
    _root_.GD.N0232.N0719.N1017.d010129 (p ∘ σ) (z ∘ σ) = _root_.GD.N0232.N0719.N1017.d010129 p z := by
  calc
    _root_.GD.N0232.N0719.N1017.d010129 (p ∘ σ) (z ∘ σ) =
        _root_.GD.N0232.N0719.N1017.d010135 (p ∘ σ) (z ∘ σ) :=
      _root_.GD.N0232.N0719.N1017.d010139 (p ∘ σ) (z ∘ σ) (fun i => hp (σ i))
    _ = _root_.GD.N0232.N0719.N1017.d010135 p z := _root_.GD.N0232.N0719.N1017.d010138 σ p z
    _ = _root_.GD.N0232.N0719.N1017.d010129 p z := (_root_.GD.N0232.N0719.N1017.d010139 p z hp).symm



def d010141 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (σ : Equiv.Perm (Fin 3)) : Fin 3 ↪ Fin k :=
  σ.toEmbedding.trans triangle

@[simp]
theorem d010142 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (σ : Equiv.Perm (Fin 3)) (j : Fin 3) :
    _root_.GD.N0232.N0719.N1017.d010141 triangle σ j = triangle (σ j) :=
  rfl



theorem d010143 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (σ : Equiv.Perm (Fin 3)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010012 (_root_.GD.N0232.N0719.N1017.d010141 triangle σ) s = _root_.GD.N0232.N0719.N1018.d010012 triangle s := by
  classical
  unfold _root_.GD.N0232.N0719.N1018.d010012
  simpa using (Equiv.sum_comp σ (fun j : Fin 3 => _root_.GD.N0232.N0719.N0900.d009108 s (triangle j)))


theorem d010144 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (σ : Equiv.Perm (Fin 3))
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (j : Fin 3) :
    _root_.GD.N0232.N0719.N1018.d010013 (_root_.GD.N0232.N0719.N1017.d010141 triangle σ) s j =
      _root_.GD.N0232.N0719.N1018.d010013 triangle s (σ j) := by
  simp [_root_.GD.N0232.N0719.N1018.d010013, _root_.GD.N0232.N0719.N1017.d010143]


theorem d010145 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (σ : Equiv.Perm (Fin 3))
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (j : Fin 3) :
    _root_.GD.N0232.N0719.N1018.d010014 (_root_.GD.N0232.N0719.N1017.d010141 triangle σ) s j =
      _root_.GD.N0232.N0719.N1018.d010014 triangle s (σ j) :=
  rfl


theorem d010146 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (σ : Equiv.Perm (Fin 3)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010015 (_root_.GD.N0232.N0719.N1017.d010141 triangle σ) s = _root_.GD.N0232.N0719.N1018.d010015 triangle s := by
  classical
  unfold _root_.GD.N0232.N0719.N1018.d010015
  simp only [_root_.GD.N0232.N0719.N1017.d010142]
  rw [Equiv.sum_comp σ (fun j : Fin 3 => _root_.GD.N0232.N0719.N0900.d009106 s (triangle j))]


theorem d010147 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (σ : Equiv.Perm (Fin 3)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010016 (_root_.GD.N0232.N0719.N1017.d010141 triangle σ) s =
      _root_.GD.N0232.N0719.N1018.d010016 triangle s := by
  classical
  unfold _root_.GD.N0232.N0719.N1018.d010016
  simp_rw [_root_.GD.N0232.N0719.N1017.d010144, _root_.GD.N0232.N0719.N1017.d010145]
  simpa using (Equiv.sum_comp σ (fun j : Fin 3 =>
    _root_.GD.N0232.N0719.N1018.d010013 triangle s j * _root_.GD.N0232.N0719.N1018.d010014 triangle s j))


theorem d010148 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (σ : Equiv.Perm (Fin 3)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010017 (_root_.GD.N0232.N0719.N1017.d010141 triangle σ) s =
      _root_.GD.N0232.N0719.N1018.d010017 triangle s := by
  classical
  unfold _root_.GD.N0232.N0719.N1018.d010017
  simp_rw [_root_.GD.N0232.N0719.N1017.d010144, _root_.GD.N0232.N0719.N1017.d010145,
    _root_.GD.N0232.N0719.N1017.d010147]
  simpa using (Equiv.sum_comp σ (fun j : Fin 3 =>
    _root_.GD.N0232.N0719.N1018.d010013 triangle s j *
      (_root_.GD.N0232.N0719.N1018.d010014 triangle s j - _root_.GD.N0232.N0719.N1018.d010016 triangle s) ^ 2))



theorem d010149 {k : ℕ}
    (hk : 0 < k) (triangle : Fin 3 ↪ Fin k)
    (σ : Equiv.Perm (Fin 3)) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hcell : _root_.GD.N0232.N0719.N1018.d010019 s) :
    _root_.GD.N0232.N0719.N1018.d010018 (_root_.GD.N0232.N0719.N1017.d010141 triangle σ) s = _root_.GD.N0232.N0719.N1018.d010018 triangle s := by
  let p : Fin 3 → ℝ := fun j => _root_.GD.N0232.N0719.N1018.d010013 triangle s j
  let z : Fin 3 → ℝ := fun j => _root_.GD.N0232.N0719.N1018.d010014 triangle s j
  have hp : ∀ j, 0 < p j := fun j =>
    _root_.GD.N0232.N0719.N1018.d010027 hk triangle s hcell j
  have hperm := _root_.GD.N0232.N0719.N1017.d010140 σ p z hp
  simpa [_root_.GD.N0232.N0719.N1018.d010018, _root_.GD.N0232.N0719.N1017.d010129, p, z, Function.comp_def,
    _root_.GD.N0232.N0719.N1017.d010144, _root_.GD.N0232.N0719.N1017.d010145] using hperm






theorem d010150 {k : ℕ}
    (hk : 0 < k) (triangle : Fin 3 ↪ Fin k)
    (σ : Equiv.Perm (Fin 3)) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010021 (_root_.GD.N0232.N0719.N1017.d010141 triangle σ) s = _root_.GD.N0232.N0719.N1018.d010021 triangle s := by
  by_cases hcell : _root_.GD.N0232.N0719.N1018.d010019 s
  · unfold _root_.GD.N0232.N0719.N1018.d010021
    rw [_root_.GD.N0232.N0719.N1017.d010143,
      _root_.GD.N0232.N0719.N1017.d010149 hk triangle σ s hcell,
      _root_.GD.N0232.N0719.N1017.d010146, _root_.GD.N0232.N0719.N1017.d010148]
  · simp [_root_.GD.N0232.N0719.N1018.d010021, _root_.GD.N0232.N0719.N1018.d010020, hcell]



theorem d010151 {k : ℕ}
    (hk : 0 < k) (triangle : Fin 3 ↪ Fin k)
    (σ : Equiv.Perm (Fin 3)) (ε : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010022 (_root_.GD.N0232.N0719.N1017.d010141 triangle σ) ε s = _root_.GD.N0232.N0719.N1018.d010022 triangle ε s := by
  simp [_root_.GD.N0232.N0719.N1018.d010022, _root_.GD.N0232.N0719.N1017.d010150 hk triangle σ s]



theorem d010152 {k : ℕ}
    (hk : 0 < k) (sizes : Fin k → ℕ)
    (triangle : Fin 3 ↪ Fin k) (σ : Equiv.Perm (Fin 3))
    (ε : ℝ) (x : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0232.N0719.N1018.d010023 k sizes (_root_.GD.N0232.N0719.N1017.d010141 triangle σ) ε x =
      _root_.GD.N0232.N0719.N1018.d010023 k sizes triangle ε x := by
  exact _root_.GD.N0232.N0719.N1017.d010151 hk triangle σ ε (_root_.GD.N0232.N0719.N0900.d009104 k sizes x)

end

end GD.N0232.N0719.N1017
