import GD.Module0624
import GD.Module0252






































open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N1018

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1016


def d010012 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  ∑ j, _root_.GD.N0232.N0719.N0900.d009108 s (triangle j)


def d010013 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) (j : Fin 3) : ℝ :=
  _root_.GD.N0232.N0719.N0900.d009108 s (triangle j) / _root_.GD.N0232.N0719.N1018.d010012 triangle s


def d010014 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) (j : Fin 3) : ℝ :=
  s.mean (triangle j)


def d010015 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  (∑ j, _root_.GD.N0232.N0719.N0900.d009106 s (triangle j))⁻¹


def d010016 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  ∑ j, _root_.GD.N0232.N0719.N1018.d010013 triangle s j * _root_.GD.N0232.N0719.N1018.d010014 triangle s j


def d010017 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  ∑ j, _root_.GD.N0232.N0719.N1018.d010013 triangle s j *
    (_root_.GD.N0232.N0719.N1018.d010014 triangle s j - _root_.GD.N0232.N0719.N1018.d010016 triangle s) ^ 2



def d010018 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  _root_.GD.N0232.N0719.N1016.d003609
    (_root_.GD.N0232.N0719.N1018.d010013 triangle s 0)
    (_root_.GD.N0232.N0719.N1018.d010013 triangle s 1)
    (_root_.GD.N0232.N0719.N1018.d010013 triangle s 2)
    (_root_.GD.N0232.N0719.N1018.d010014 triangle s 0)
    (_root_.GD.N0232.N0719.N1018.d010014 triangle s 1)
    (_root_.GD.N0232.N0719.N1018.d010014 triangle s 2)




def d010019 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) : Prop :=
  ∀ i,
    (3 : ℝ) / (4 * k) ≤ _root_.GD.N0232.N0719.N0900.d009108 s i ∧
      _root_.GD.N0232.N0719.N0900.d009108 s i ≤ (5 : ℝ) / (4 * k)


def d010020 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  @ite ℝ (_root_.GD.N0232.N0719.N1018.d010019 s) (Classical.propDecidable _) 1 0


def d010021 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  _root_.GD.N0232.N0719.N1018.d010020 s * _root_.GD.N0232.N0719.N1018.d010012 triangle s *
    _root_.GD.N0232.N0719.N1018.d010018 triangle s /
      (_root_.GD.N0232.N0719.N1018.d010015 triangle s + _root_.GD.N0232.N0719.N1018.d010017 triangle s)


def d010022 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (ε : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  _root_.GD.N0232.N0719.N0900.d009110 s + ε * _root_.GD.N0232.N0719.N1018.d010021 triangle s


def d010023
    (k : ℕ) (sizes : Fin k → ℕ)
    (triangle : Fin 3 ↪ Fin k) (ε : ℝ)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N1018.d010022 triangle ε (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)

theorem d010024
    {k : ℕ} (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hmass : _root_.GD.N0232.N0719.N1018.d010012 triangle s ≠ 0) :
    ∑ j, _root_.GD.N0232.N0719.N1018.d010013 triangle s j = 1 := by
  unfold _root_.GD.N0232.N0719.N1018.d010013 _root_.GD.N0232.N0719.N1018.d010012
  rw [← Finset.sum_div]
  exact div_self hmass



theorem d010025
    {k : ℕ} (hk : 0 < k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hcell : _root_.GD.N0232.N0719.N1018.d010019 s) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0900.d009108 s i := by
  have hlower : 0 < (3 : ℝ) / (4 * k) := by
    positivity
  exact lt_of_lt_of_le hlower (hcell i).1



theorem d010026
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hcell : _root_.GD.N0232.N0719.N1018.d010019 s) :
    0 < _root_.GD.N0232.N0719.N1018.d010012 triangle s := by
  unfold _root_.GD.N0232.N0719.N1018.d010012
  exact Finset.sum_pos
    (fun j _ => _root_.GD.N0232.N0719.N1018.d010025 hk s hcell (triangle j))
    Finset.univ_nonempty



theorem d010027
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hcell : _root_.GD.N0232.N0719.N1018.d010019 s) (j : Fin 3) :
    0 < _root_.GD.N0232.N0719.N1018.d010013 triangle s j := by
  exact div_pos
    (_root_.GD.N0232.N0719.N1018.d010025 hk s hcell (triangle j))
    (_root_.GD.N0232.N0719.N1018.d010026 hk triangle s hcell)



theorem d010028
    {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hvar : ∀ i, 0 < s.meanVariance i) :
    0 < _root_.GD.N0232.N0719.N1018.d010015 triangle s := by
  unfold _root_.GD.N0232.N0719.N1018.d010015 _root_.GD.N0232.N0719.N0900.d009106
  apply inv_pos.mpr
  exact Finset.sum_pos
    (fun j _ => by
      rw [_root_.GD.N0232.N0719.N0900.d009127 (hvar (triangle j))]
      exact inv_pos.mpr (hvar (triangle j)))
    Finset.univ_nonempty

theorem d010029
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hmass : 0 ≤ _root_.GD.N0232.N0719.N1018.d010012 triangle s) :
    0 ≤ _root_.GD.N0232.N0719.N1018.d010017 triangle s := by
  unfold _root_.GD.N0232.N0719.N1018.d010017 _root_.GD.N0232.N0719.N1018.d010013
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg
    (div_nonneg (_root_.GD.N0232.N0719.N0900.d009132 hk s (triangle j)) hmass)
    (sq_nonneg _)



theorem d010030
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k)
    (hvar : ∀ i, 0 < s.meanVariance i) :
    0 <
      _root_.GD.N0232.N0719.N1018.d010015 triangle s + _root_.GD.N0232.N0719.N1018.d010017 triangle s := by
  have hmassNonneg : 0 ≤ _root_.GD.N0232.N0719.N1018.d010012 triangle s := by
    unfold _root_.GD.N0232.N0719.N1018.d010012
    exact Finset.sum_nonneg fun j _ => _root_.GD.N0232.N0719.N0900.d009132 hk s (triangle j)
  exact add_pos_of_pos_of_nonneg
    (_root_.GD.N0232.N0719.N1018.d010028 triangle s hvar)
    (_root_.GD.N0232.N0719.N1018.d010029 hk triangle s hmassNonneg)

theorem d010031 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010020 s = 0 ∨ _root_.GD.N0232.N0719.N1018.d010020 s = 1 := by
  by_cases h : _root_.GD.N0232.N0719.N1018.d010019 s
  · exact Or.inr (by simp [_root_.GD.N0232.N0719.N1018.d010020, h])
  · exact Or.inl (by simp [_root_.GD.N0232.N0719.N1018.d010020, h])

theorem d010032 {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    0 ≤ _root_.GD.N0232.N0719.N1018.d010020 s := by
  rcases _root_.GD.N0232.N0719.N1018.d010031 s with h | h <;> simp [h]

theorem d010033
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (ε : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010022 triangle ε s - _root_.GD.N0232.N0719.N0900.d009110 s =
      ε * _root_.GD.N0232.N0719.N1018.d010021 triangle s := by
  simp [_root_.GD.N0232.N0719.N1018.d010022]



theorem d010034
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (ε target : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    (_root_.GD.N0232.N0719.N1018.d010022 triangle ε s - target) ^ 2 -
        (_root_.GD.N0232.N0719.N0900.d009110 s - target) ^ 2 =
      2 * ε * (_root_.GD.N0232.N0719.N0900.d009110 s - target) * _root_.GD.N0232.N0719.N1018.d010021 triangle s +
        ε ^ 2 * _root_.GD.N0232.N0719.N1018.d010021 triangle s ^ 2 := by
  unfold _root_.GD.N0232.N0719.N1018.d010022
  ring

@[fun_prop]
theorem d010035 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    Measurable (_root_.GD.N0232.N0719.N1018.d010012 triangle : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N1018.d010012
  fun_prop

@[fun_prop]
theorem d010036 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (j : Fin 3) :
    Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 k => _root_.GD.N0232.N0719.N1018.d010013 triangle s j) := by
  unfold _root_.GD.N0232.N0719.N1018.d010013
  fun_prop

@[fun_prop]
theorem d010037 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (j : Fin 3) :
    Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 k => _root_.GD.N0232.N0719.N1018.d010014 triangle s j) := by
  unfold _root_.GD.N0232.N0719.N1018.d010014
  fun_prop

@[fun_prop]
theorem d010038 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    Measurable (_root_.GD.N0232.N0719.N1018.d010015 triangle : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N1018.d010015
  fun_prop

@[fun_prop]
theorem d010039 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    Measurable (_root_.GD.N0232.N0719.N1018.d010016 triangle : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N1018.d010016
  fun_prop

@[fun_prop]
theorem d010040 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    Measurable (_root_.GD.N0232.N0719.N1018.d010017 triangle : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N1018.d010017
  fun_prop

@[fun_prop]
theorem d010041 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    Measurable (_root_.GD.N0232.N0719.N1018.d010018 triangle : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N1018.d010018 _root_.GD.N0232.N0719.N1016.d003609
  fun_prop

theorem d010042 {k : ℕ} :
    MeasurableSet {s : _root_.GD.N0232.N0719.N0900.d009096 k | _root_.GD.N0232.N0719.N1018.d010019 s} := by
  simp only [_root_.GD.N0232.N0719.N1018.d010019, setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have hLowerConst :
      Measurable
        (fun _ : _root_.GD.N0232.N0719.N0900.d009096 k => (3 : ℝ) / (4 * (k : ℝ))) :=
    measurable_const
  have hUpperConst :
      Measurable
        (fun _ : _root_.GD.N0232.N0719.N0900.d009096 k => (5 : ℝ) / (4 * (k : ℝ))) :=
    measurable_const
  exact
    (measurableSet_le hLowerConst (_root_.GD.N0232.N0719.N0900.d009119 i)).inter
      (measurableSet_le (_root_.GD.N0232.N0719.N0900.d009119 i) hUpperConst)

@[fun_prop]
theorem d010043 {k : ℕ} :
    Measurable (_root_.GD.N0232.N0719.N1018.d010020 : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N1018.d010020
  exact Measurable.ite
    _root_.GD.N0232.N0719.N1018.d010042 measurable_const measurable_const

@[fun_prop]
theorem d010044 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) :
    Measurable (_root_.GD.N0232.N0719.N1018.d010021 triangle : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N1018.d010021
  fun_prop

@[fun_prop]
theorem d010045 {k : ℕ}
    (triangle : Fin 3 ↪ Fin k) (ε : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N1018.d010022 triangle ε : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N1018.d010022
  fun_prop

@[fun_prop]
theorem d010046
    (k : ℕ) (sizes : Fin k → ℕ)
    (triangle : Fin 3 ↪ Fin k) (ε : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N1018.d010023 k sizes triangle ε) := by
  unfold _root_.GD.N0232.N0719.N1018.d010023
  fun_prop

theorem d010047
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010012 triangle (_root_.GD.N0232.N0719.N0900.d009101 location scale s) =
      _root_.GD.N0232.N0719.N1018.d010012 triangle s := by
  unfold _root_.GD.N0232.N0719.N1018.d010012
  simp_rw [_root_.GD.N0232.N0719.N0900.d009143 location hscale s]

theorem d010048
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (j : Fin 3) :
    _root_.GD.N0232.N0719.N1018.d010013 triangle (_root_.GD.N0232.N0719.N0900.d009101 location scale s) j =
      _root_.GD.N0232.N0719.N1018.d010013 triangle s j := by
  unfold _root_.GD.N0232.N0719.N1018.d010013
  rw [_root_.GD.N0232.N0719.N0900.d009143 location hscale s,
    _root_.GD.N0232.N0719.N1018.d010047 triangle location hscale s]

theorem d010049
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (location scale : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) (j : Fin 3) :
    _root_.GD.N0232.N0719.N1018.d010014 triangle (_root_.GD.N0232.N0719.N0900.d009101 location scale s) j =
      location + scale * _root_.GD.N0232.N0719.N1018.d010014 triangle s j :=
  rfl

theorem d010050
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010015 triangle (_root_.GD.N0232.N0719.N0900.d009101 location scale s) =
      scale ^ 2 * _root_.GD.N0232.N0719.N1018.d010015 triangle s := by
  unfold _root_.GD.N0232.N0719.N1018.d010015
  simp_rw [_root_.GD.N0232.N0719.N0900.d009141 location hscale s]
  rw [← Finset.mul_sum]
  rw [mul_inv_rev]
  simp [hscale]
  ring

theorem d010051
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hmass : _root_.GD.N0232.N0719.N1018.d010012 triangle s ≠ 0) :
    _root_.GD.N0232.N0719.N1018.d010016 triangle (_root_.GD.N0232.N0719.N0900.d009101 location scale s) =
      location + scale * _root_.GD.N0232.N0719.N1018.d010016 triangle s := by
  unfold _root_.GD.N0232.N0719.N1018.d010016
  simp_rw [_root_.GD.N0232.N0719.N1018.d010048 triangle location hscale s,
    _root_.GD.N0232.N0719.N1018.d010049]
  calc
    (∑ j,
        _root_.GD.N0232.N0719.N1018.d010013 triangle s j *
          (location + scale * _root_.GD.N0232.N0719.N1018.d010014 triangle s j)) =
        location * (∑ j, _root_.GD.N0232.N0719.N1018.d010013 triangle s j) +
          scale *
            (∑ j,
              _root_.GD.N0232.N0719.N1018.d010013 triangle s j *
                _root_.GD.N0232.N0719.N1018.d010014 triangle s j) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = location + scale *
          (∑ j,
            _root_.GD.N0232.N0719.N1018.d010013 triangle s j *
              _root_.GD.N0232.N0719.N1018.d010014 triangle s j) := by
          rw [_root_.GD.N0232.N0719.N1018.d010024 triangle s hmass]
          ring

theorem d010052
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hmass : _root_.GD.N0232.N0719.N1018.d010012 triangle s ≠ 0) :
    _root_.GD.N0232.N0719.N1018.d010017 triangle (_root_.GD.N0232.N0719.N0900.d009101 location scale s) =
      scale ^ 2 * _root_.GD.N0232.N0719.N1018.d010017 triangle s := by
  unfold _root_.GD.N0232.N0719.N1018.d010017
  simp_rw [_root_.GD.N0232.N0719.N1018.d010048 triangle location hscale s,
    _root_.GD.N0232.N0719.N1018.d010049,
    _root_.GD.N0232.N0719.N1018.d010051 triangle location hscale s hmass]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem d010053
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010018 triangle (_root_.GD.N0232.N0719.N0900.d009101 location scale s) =
      scale ^ 3 * _root_.GD.N0232.N0719.N1018.d010018 triangle s := by
  unfold _root_.GD.N0232.N0719.N1018.d010018 _root_.GD.N0232.N0719.N1016.d003609
  simp_rw [_root_.GD.N0232.N0719.N1018.d010048 triangle location hscale s,
    _root_.GD.N0232.N0719.N1018.d010049]
  ring

theorem d010054
    {k : ℕ} (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010019 (_root_.GD.N0232.N0719.N0900.d009101 location scale s) ↔ _root_.GD.N0232.N0719.N1018.d010019 s := by
  simp only [_root_.GD.N0232.N0719.N1018.d010019, _root_.GD.N0232.N0719.N0900.d009143 location hscale s]

theorem d010055
    {k : ℕ} (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010020 (_root_.GD.N0232.N0719.N0900.d009101 location scale s) = _root_.GD.N0232.N0719.N1018.d010020 s := by
  unfold _root_.GD.N0232.N0719.N1018.d010020
  by_cases hcell : _root_.GD.N0232.N0719.N1018.d010019 s
  · have hcell' :
        _root_.GD.N0232.N0719.N1018.d010019 (_root_.GD.N0232.N0719.N0900.d009101 location scale s) :=
      (_root_.GD.N0232.N0719.N1018.d010054 location hscale s).2 hcell
    simp [hcell, hcell']
  · have hcell' :
        ¬_root_.GD.N0232.N0719.N1018.d010019 (_root_.GD.N0232.N0719.N0900.d009101 location scale s) := by
      rwa [_root_.GD.N0232.N0719.N1018.d010054 location hscale s]
    simp [hcell, hcell']




theorem d010056
    {k : ℕ} (triangle : Fin 3 ↪ Fin k)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (hmass : _root_.GD.N0232.N0719.N1018.d010012 triangle s ≠ 0) :
    _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0900.d009101 location scale s) =
      scale * _root_.GD.N0232.N0719.N1018.d010021 triangle s := by
  unfold _root_.GD.N0232.N0719.N1018.d010021
  rw [_root_.GD.N0232.N0719.N1018.d010055 location hscale,
    _root_.GD.N0232.N0719.N1018.d010047 triangle location hscale,
    _root_.GD.N0232.N0719.N1018.d010053 triangle location hscale,
    _root_.GD.N0232.N0719.N1018.d010050 triangle location hscale,
    _root_.GD.N0232.N0719.N1018.d010052 triangle location hscale s hmass]
  field_simp [hscale]







theorem d010057
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010021 triangle (_root_.GD.N0232.N0719.N0900.d009101 location scale s) =
      scale * _root_.GD.N0232.N0719.N1018.d010021 triangle s := by
  by_cases hcell : _root_.GD.N0232.N0719.N1018.d010019 s
  · exact _root_.GD.N0232.N0719.N1018.d010056
      triangle location hscale s
      (ne_of_gt
        (_root_.GD.N0232.N0719.N1018.d010026
          hk triangle s hcell))
  · have hcell' :
        ¬_root_.GD.N0232.N0719.N1018.d010019 (_root_.GD.N0232.N0719.N0900.d009101 location scale s) := by
      rwa [_root_.GD.N0232.N0719.N1018.d010054 location hscale s]
    simp [_root_.GD.N0232.N0719.N1018.d010021, _root_.GD.N0232.N0719.N1018.d010020, hcell, hcell']

theorem d010058
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (ε location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N1018.d010022 triangle ε (_root_.GD.N0232.N0719.N0900.d009101 location scale s) =
      location + scale * _root_.GD.N0232.N0719.N1018.d010022 triangle ε s := by
  unfold _root_.GD.N0232.N0719.N1018.d010022
  rw [_root_.GD.N0232.N0719.N0900.d009145 hk location hscale,
    _root_.GD.N0232.N0719.N1018.d010057 hk triangle location hscale s]
  ring


theorem d010059
    {k : ℕ} (hk : 0 < k)
    {sizes : Fin k → ℕ} (hsizes : ∀ i, 0 < sizes i)
    (triangle : Fin 3 ↪ Fin k)
    (ε location : ℝ) {scale : ℝ} (hscale : scale ≠ 0)
    (ω : _root_.GD.N0232.N0719.N0900.d009094 k sizes) :
    _root_.GD.N0232.N0719.N1018.d010023 k sizes triangle ε
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes location scale ω) =
      location + scale * _root_.GD.N0232.N0719.N1018.d010023 k sizes triangle ε ω := by
  unfold _root_.GD.N0232.N0719.N1018.d010023
  rw [_root_.GD.N0232.N0719.N0900.d009139 hsizes location scale ω]
  exact _root_.GD.N0232.N0719.N1018.d010058
    hk triangle ε location hscale _

end

end GD.N0232.N0719.N1018
