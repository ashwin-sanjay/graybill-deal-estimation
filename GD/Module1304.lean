import GD.Module0377
import GD.Module0358
import GD.Module1303









namespace GD.N0106.N0428.N0765.N1566

set_option autoImplicit false
set_option warningAsError true

open Set Polynomial _root_.GD.N0106.N0428.N0765.N1624 _root_.GD.N0106.N0428.N0765.N1524 _root_.GD.N0106.N0428.N0765.N1523

open scoped ContDiff

noncomputable section


def d021320 (location x : ℝ) : ℝ :=
  11 * _root_.GD.N0106.N0428.N0765.N1627.d021120 location (Real.exp x) / (1 + Real.exp x)

theorem d021321 : ContDiff ℝ ∞ _root_.GD.N0106.N0428.N0765.N1523.d021314 := by
  apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
  intro n _
  rw [_root_.GD.N0106.N0428.N0765.N1523.d021316]
  intro x
  have h := (_root_.GD.N0106.N0428.N0765.N1523.d021315 n
    (_root_.GD.N0106.N0428.N0765.N1535.d021138 x)).differentiableAt.hasDerivAt
  exact h.real_of_complex.differentiableAt

theorem d021322 (location : ℝ) : ContDiff ℝ ∞ (_root_.GD.N0106.N0428.N0765.N1566.d021320 location) := by
  change ContDiff ℝ ∞ (fun x : ℝ =>
    11 * _root_.GD.N0106.N0428.N0765.N1627.d021120 location (Real.exp x) / (1 + Real.exp x))
  rw [_root_.GD.N0106.N0428.N0765.N1523.d021317]
  exact _root_.GD.N0106.N0428.N0765.N1566.d021321

theorem d021323 (location : ℝ) (n : ℕ) (x : ℝ) :
    |iteratedDeriv n (_root_.GD.N0106.N0428.N0765.N1566.d021320 location) x| ≤ 11 * (n.factorial : ℝ) * 7 ^ n :=
  _root_.GD.N0106.N0428.N0765.N1523.d021318 location n x


def d021324 (location c : ℝ) : ℝ[X] :=
  Lagrange.interpolate (_root_.GD.N0106.N0428.N0765.N1524.d005288 c) id (_root_.GD.N0106.N0428.N0765.N1566.d021320 location)

theorem d021325 (location c : ℝ) :
    (_root_.GD.N0106.N0428.N0765.N1566.d021324 location c).degree ≤ (13 : WithBot ℕ) := by
  have h := Lagrange.degree_interpolate_le (s := _root_.GD.N0106.N0428.N0765.N1524.d005288 c) (v := id)
    (_root_.GD.N0106.N0428.N0765.N1566.d021320 location) Function.injective_id.injOn
  have hdeg : (_root_.GD.N0106.N0428.N0765.N1566.d021324 location c).degree ≤ ((13 : ℕ) : WithBot ℕ) := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1566.d021324, _root_.GD.N0106.N0428.N0765.N1524.d005290, Nat.reduceSub] using h
  exact hdeg.trans (by norm_num)

theorem d021326 (location c : ℝ) {x : ℝ} (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1524.d005288 c) :
    (_root_.GD.N0106.N0428.N0765.N1566.d021324 location c).eval x = _root_.GD.N0106.N0428.N0765.N1566.d021320 location x :=
  Lagrange.eval_interpolate_at_node (_root_.GD.N0106.N0428.N0765.N1566.d021320 location) Function.injective_id.injOn hx


theorem d021327 (location c : ℝ) {x : ℝ}
    (hx : x ∈ Icc (c - 1 / 14) (c + 1 / 14)) :
    |_root_.GD.N0106.N0428.N0765.N1566.d021320 location x - (_root_.GD.N0106.N0428.N0765.N1566.d021324 location c).eval x| ≤ (11 : ℝ) / 134217728 := by
  obtain ⟨ξ, _, he⟩ := _root_.GD.N0106.N0428.N0765.N1624.d005784 (_root_.GD.N0106.N0428.N0765.N1566.d021322 location)
    (_root_.GD.N0106.N0428.N0765.N1524.d005288 c) (_root_.GD.N0106.N0428.N0765.N1524.d005290 c) (fun _ ht => _root_.GD.N0106.N0428.N0765.N1524.d005292 c ht) hx
  change |_root_.GD.N0106.N0428.N0765.N1566.d021320 location x - (Lagrange.interpolate (_root_.GD.N0106.N0428.N0765.N1524.d005288 c) id
    (_root_.GD.N0106.N0428.N0765.N1566.d021320 location)).eval x| ≤ _
  rw [he, abs_mul, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < ((14 : ℕ).factorial : ℝ))]
  have hd : |iteratedDeriv 14 (_root_.GD.N0106.N0428.N0765.N1566.d021320 location) ξ| / ((14 : ℕ).factorial : ℝ) ≤
      11 * (7 : ℝ) ^ 14 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((14 : ℕ).factorial : ℝ))).mpr
    calc
      |iteratedDeriv 14 (_root_.GD.N0106.N0428.N0765.N1566.d021320 location) ξ| ≤
          11 * ((14 : ℕ).factorial : ℝ) * 7 ^ 14 := _root_.GD.N0106.N0428.N0765.N1566.d021323 location 14 ξ
      _ = (11 * (7 : ℝ) ^ 14) * ((14 : ℕ).factorial : ℝ) := by ring
  calc
    (|iteratedDeriv 14 (_root_.GD.N0106.N0428.N0765.N1566.d021320 location) ξ| / ((14 : ℕ).factorial : ℝ)) *
        |∏ t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005288 c, (x - t)| ≤
        (11 * (7 : ℝ) ^ 14) * (((1 : ℝ) / 14) ^ 14 / 8192) :=
      mul_le_mul hd (_root_.GD.N0106.N0428.N0765.N1524.d005294 c hx) (abs_nonneg _) (by positivity)
    _ = (11 : ℝ) / 134217728 := by norm_num


def d021328 (j : Fin 28) : ℝ := (2 * (j.val : ℝ) + 1) / 14

theorem d021329 (j : Fin 28) :
    Icc (_root_.GD.N0106.N0428.N0765.N1566.d021328 j - 1 / 14) (_root_.GD.N0106.N0428.N0765.N1566.d021328 j + 1 / 14) =
      Icc ((j.val : ℝ) / 7) (((j.val : ℝ) + 1) / 7) := by
  congr 1 <;> dsimp [_root_.GD.N0106.N0428.N0765.N1566.d021328] <;> ring

theorem d021330 (location : ℝ) (j : Fin 28) {x : ℝ}
    (hx : x ∈ Icc ((j.val : ℝ) / 7) (((j.val : ℝ) + 1) / 7)) :
    |_root_.GD.N0106.N0428.N0765.N1566.d021320 location x - (_root_.GD.N0106.N0428.N0765.N1566.d021324 location (_root_.GD.N0106.N0428.N0765.N1566.d021328 j)).eval x| ≤
      (11 : ℝ) / 134217728 := by
  apply _root_.GD.N0106.N0428.N0765.N1566.d021327 location (_root_.GD.N0106.N0428.N0765.N1566.d021328 j)
  rwa [_root_.GD.N0106.N0428.N0765.N1566.d021329]



theorem d021331 (location : ℝ) (j : Fin 28) :
    (_root_.GD.N0106.N0428.N0765.N1524.d005288 (_root_.GD.N0106.N0428.N0765.N1566.d021328 j)).card = 14 ∧
    (_root_.GD.N0106.N0428.N0765.N1566.d021324 location (_root_.GD.N0106.N0428.N0765.N1566.d021328 j)).degree ≤ (13 : WithBot ℕ) ∧
    (∀ t ∈ _root_.GD.N0106.N0428.N0765.N1524.d005288 (_root_.GD.N0106.N0428.N0765.N1566.d021328 j),
      (_root_.GD.N0106.N0428.N0765.N1566.d021324 location (_root_.GD.N0106.N0428.N0765.N1566.d021328 j)).eval t =
        11 * _root_.GD.N0106.N0428.N0765.N1627.d021120 location (Real.exp t) / (1 + Real.exp t)) ∧
    ∀ x ∈ Icc ((j.val : ℝ) / 7) (((j.val : ℝ) + 1) / 7),
      |11 * _root_.GD.N0106.N0428.N0765.N1627.d021120 location (Real.exp x) / (1 + Real.exp x) -
        (_root_.GD.N0106.N0428.N0765.N1566.d021324 location (_root_.GD.N0106.N0428.N0765.N1566.d021328 j)).eval x| ≤ (11 : ℝ) / 134217728 :=
  ⟨_root_.GD.N0106.N0428.N0765.N1524.d005290 _, _root_.GD.N0106.N0428.N0765.N1566.d021325 _ _,
    fun _ ht => _root_.GD.N0106.N0428.N0765.N1566.d021326 _ _ ht, fun _ hx => _root_.GD.N0106.N0428.N0765.N1566.d021330 _ _ hx⟩

end
end GD.N0106.N0428.N0765.N1566

#print axioms _root_.GD.N0106.N0428.N0765.N1566.d021321
#print axioms _root_.GD.N0106.N0428.N0765.N1566.d021322
#print axioms _root_.GD.N0106.N0428.N0765.N1566.d021323
#print axioms _root_.GD.N0106.N0428.N0765.N1566.d021325
#print axioms _root_.GD.N0106.N0428.N0765.N1566.d021326
#print axioms _root_.GD.N0106.N0428.N0765.N1566.d021327
#print axioms _root_.GD.N0106.N0428.N0765.N1566.d021330
#print axioms _root_.GD.N0106.N0428.N0765.N1566.d021331
