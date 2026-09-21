import GD.Module0658

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0960

noncomputable section




def d009692 {k : ℕ}
    (shape variance : Fin k → ℝ) (i : Fin k) : ℝ :=
  shape i / variance i





theorem d009693
    {k : ℕ} (hk : 0 < k)
    {shape variance p : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hvariance : ∀ i, 0 < variance i)
    (hp : _root_.GD.N0232.N0719.N0951.d003580 p)
    (i : Fin k) {V : ℝ} (hvi : variance i ≤ V) :
    (4 * (k : ℝ) / 5) * (shape i / V) ≤
      _root_.GD.N0232.N0719.N0951.d003587 (_root_.GD.N0232.N0719.N0960.d009692 shape variance) p := by
  have hV : 0 < V := lt_of_lt_of_le (hvariance i) hvi
  have hterm_nonneg :
      ∀ j : Fin k, 0 ≤ _root_.GD.N0232.N0719.N0960.d009692 shape variance j / p j := by
    intro j
    exact div_nonneg
      (div_nonneg (hshape j).le (hvariance j).le)
      (_root_.GD.N0232.N0719.N0951.d003590 hk hp j).le
  have hterm :
      _root_.GD.N0232.N0719.N0960.d009692 shape variance i / p i ≤
        _root_.GD.N0232.N0719.N0951.d003587 (_root_.GD.N0232.N0719.N0960.d009692 shape variance) p := by
    unfold _root_.GD.N0232.N0719.N0951.d003587
    exact Finset.single_le_sum
      (fun j _ => hterm_nonneg j) (Finset.mem_univ i)
  have hrate :
      (4 * (k : ℝ) / 5) * (shape i / V) ≤
        _root_.GD.N0232.N0719.N0960.d009692 shape variance i / p i := by
    have hrecip := _root_.GD.N0232.N0719.N0951.d003598 hk hp i
    have hvdiv :
        shape i / V ≤ shape i / variance i :=
      div_le_div_of_nonneg_left (hshape i).le
        (hvariance i) hvi
    unfold _root_.GD.N0232.N0719.N0960.d009692
    calc
      (4 * (k : ℝ) / 5) * (shape i / V) ≤
          (1 / p i) * (shape i / V) :=
        mul_le_mul_of_nonneg_right hrecip
          (div_nonneg (hshape i).le hV.le)
      _ ≤ (1 / p i) * (shape i / variance i) :=
        mul_le_mul_of_nonneg_left hvdiv
          (one_div_nonneg.mpr
            (_root_.GD.N0232.N0719.N0951.d003590 hk hp i).le)
      _ = (shape i / variance i) / p i := by ring
  exact hrate.trans hterm





theorem d009694
    {k : ℕ} (hk : 0 < k)
    {shape variance p : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hvariance : ∀ i, 0 < variance i)
    (hp : _root_.GD.N0232.N0719.N0951.d003580 p)
    (i : Fin k) {V : ℝ} (hvi : variance i ≤ V) :
    _root_.GD.N0232.N0719.N0954.d009503 shape /
          _root_.GD.N0232.N0719.N0951.d003587 (_root_.GD.N0232.N0719.N0960.d009692 shape variance) p ≤
      (5 * _root_.GD.N0232.N0719.N0954.d009503 shape /
          (4 * (k : ℝ) * shape i)) * V := by
  have hV : 0 < V := lt_of_lt_of_le (hvariance i) hvi
  have hA : 0 < _root_.GD.N0232.N0719.N0954.d009503 shape :=
    _root_.GD.N0232.N0719.N0954.d009504 hk hshape
  have hR :
      0 < _root_.GD.N0232.N0719.N0951.d003587 (_root_.GD.N0232.N0719.N0960.d009692 shape variance) p := by
    unfold _root_.GD.N0232.N0719.N0951.d003587
    exact Finset.sum_pos
      (fun j _ => by
        unfold _root_.GD.N0232.N0719.N0960.d009692
        exact div_pos (div_pos (hshape j) (hvariance j))
          (_root_.GD.N0232.N0719.N0951.d003590 hk hp j))
      ⟨i, Finset.mem_univ _⟩
  have hRlower :=
    _root_.GD.N0232.N0719.N0960.d009693
      hk hshape hvariance hp i hvi
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hden :
      0 < (4 * (k : ℝ) / 5) * (shape i / V) := by
    exact mul_pos
      (div_pos (mul_pos (by norm_num) hkR) (by norm_num))
      (div_pos (hshape i) hV)
  have hinv :
      1 / _root_.GD.N0232.N0719.N0951.d003587 (_root_.GD.N0232.N0719.N0960.d009692 shape variance) p ≤
        1 / ((4 * (k : ℝ) / 5) * (shape i / V)) :=
    one_div_le_one_div_of_le hden hRlower
  have hscaled :=
    mul_le_mul_of_nonneg_left hinv hA.le
  calc
    _root_.GD.N0232.N0719.N0954.d009503 shape /
          _root_.GD.N0232.N0719.N0951.d003587 (_root_.GD.N0232.N0719.N0960.d009692 shape variance) p =
        _root_.GD.N0232.N0719.N0954.d009503 shape *
          (1 / _root_.GD.N0232.N0719.N0951.d003587
            (_root_.GD.N0232.N0719.N0960.d009692 shape variance) p) := by ring
    _ ≤ _root_.GD.N0232.N0719.N0954.d009503 shape *
          (1 / ((4 * (k : ℝ) / 5) * (shape i / V))) :=
      hscaled
    _ =
        (5 * _root_.GD.N0232.N0719.N0954.d009503 shape /
          (4 * (k : ℝ) * shape i)) * V := by
      field_simp [hkR.ne', (hshape i).ne', hV.ne']








theorem d009695
    {k : ℕ} (hk : 0 < k)
    {shape variance p : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hvariance : ∀ i, 0 < variance i)
    (hp : _root_.GD.N0232.N0719.N0951.d003580 p)
    (i : Fin k) {V : ℝ} (hvi : variance i ≤ V) :
    (1 /
        (1 + 5 * _root_.GD.N0232.N0719.N0954.d009503 shape /
          (4 * (k : ℝ) * shape i))) / V ≤
      ∫ ω,
        1 / (ω + V)
          ∂gammaMeasure
            (_root_.GD.N0232.N0719.N0954.d009503 shape)
            (_root_.GD.N0232.N0719.N0951.d003587
              (_root_.GD.N0232.N0719.N0960.d009692 shape variance) p) := by
  have hV : 0 < V := lt_of_lt_of_le (hvariance i) hvi
  have hA : 0 < _root_.GD.N0232.N0719.N0954.d009503 shape :=
    _root_.GD.N0232.N0719.N0954.d009504 hk hshape
  have hR :
      0 < _root_.GD.N0232.N0719.N0951.d003587 (_root_.GD.N0232.N0719.N0960.d009692 shape variance) p := by
    unfold _root_.GD.N0232.N0719.N0951.d003587
    exact Finset.sum_pos
      (fun j _ => by
        unfold _root_.GD.N0232.N0719.N0960.d009692
        exact div_pos (div_pos (hshape j) (hvariance j))
          (_root_.GD.N0232.N0719.N0951.d003590 hk hp j))
      ⟨i, Finset.mem_univ _⟩
  have hgamma :=
    _root_.GD.N0232.N0719.N0960.d009685 hA hR hV
  have hmean :=
    _root_.GD.N0232.N0719.N0960.d009694
      hk hshape hvariance hp i hvi
  have hC :
      0 ≤ 5 * _root_.GD.N0232.N0719.N0954.d009503 shape /
        (4 * (k : ℝ) * shape i) := by
    exact div_nonneg
      (mul_nonneg (by norm_num) hA.le)
      (mul_nonneg
        (mul_nonneg (by norm_num) (by exact_mod_cast hk.le))
        (hshape i).le)
  have hden :
      0 <
        (5 * _root_.GD.N0232.N0719.N0954.d009503 shape /
          (4 * (k : ℝ) * shape i)) * V + V := by
    positivity
  have hrecip :
      1 /
          ((5 * _root_.GD.N0232.N0719.N0954.d009503 shape /
            (4 * (k : ℝ) * shape i)) * V + V) ≤
        1 /
          (_root_.GD.N0232.N0719.N0954.d009503 shape /
            _root_.GD.N0232.N0719.N0951.d003587
              (_root_.GD.N0232.N0719.N0960.d009692 shape variance) p + V) :=
    one_div_le_one_div_of_le
      (add_pos_of_pos_of_nonneg (div_pos hA hR) hV.le)
      (by simpa [add_comm] using add_le_add_right hmean V)
  calc
    (1 /
        (1 + 5 * _root_.GD.N0232.N0719.N0954.d009503 shape /
          (4 * (k : ℝ) * shape i))) / V =
      1 /
        ((5 * _root_.GD.N0232.N0719.N0954.d009503 shape /
          (4 * (k : ℝ) * shape i)) * V + V) := by
            field_simp [hV.ne']
            ring
    _ ≤ 1 /
        (_root_.GD.N0232.N0719.N0954.d009503 shape /
          _root_.GD.N0232.N0719.N0951.d003587
            (_root_.GD.N0232.N0719.N0960.d009692 shape variance) p + V) :=
      hrecip
    _ ≤ ∫ ω,
        1 / (ω + V)
          ∂gammaMeasure
            (_root_.GD.N0232.N0719.N0954.d009503 shape)
            (_root_.GD.N0232.N0719.N0951.d003587
              (_root_.GD.N0232.N0719.N0960.d009692 shape variance) p) :=
      hgamma

end

end GD.N0232.N0719.N0960
