import GD.Module1466
import GD.Module0575

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace GD.N0101.N0348
noncomputable section

open _root_.GD.N0101.N0402
open _root_.GD.N0213.N0495
open _root_.GD.N0213.N0506
open _root_.GD.N0230.N0665



theorem d023094 {k : ℕ}
    (s r v : Fin k → ℝ) (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) (L : ℝ) :
    (∫ z, (∑ i, (z i)⁻¹ * v i ^ 2) * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r) =
      ∑ i, (∫ z, (z i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r) * v i ^ 2 := by
  calc
    _ = ∫ z, ∑ i, ((z i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2) * v i ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r := by
      apply integral_congr_ae
      filter_upwards with z
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun i _ =>
        (_root_.GD.N0101.N0402.d023088 s r hs hr L i).mul_const (v i ^ 2))]
      simp only [integral_mul_const]





theorem d023095 {n : ℕ}
    (a t w : Fin (n + 1) → ℝ) (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i)
    {ρ L : ℝ} (hρ : ρ < 1) (hL : 0 < L)
    (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1) (hunit : ∑ i, w i = 1) :
    let s := fun i => a i * (1 - ρ)
    let r := fun i => a i * t i
    let P := _root_.GD.N0101.N0402.d023083 s r
    let M := fun i => ∫ z, (z i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂P
    let D := ∫ z, _root_.GD.N0213.N0495.d007175 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂P
    (∑ i, M i * _root_.GD.N0230.N0665.d000407 t i ^ 2) - (∑ i, M i * w i ^ 2) ≤
      ∑ i, ∑ j, if i = j then 0 else
        4 * (D / s i ^ 2 + D / s j ^ 2) / ((1 - ρ)⁻¹ * (t i + t j)) := by
  let s : Fin (n + 1) → ℝ := fun i => a i * (1 - ρ)
  let r : Fin (n + 1) → ℝ := fun i => a i * t i
  let c : ℝ := (1 - ρ)⁻¹
  let m : ℝ := ∫ z, _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r
  let e : ℝ := ∫ z, _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) * _root_.GD.N0213.N0495.d007175 L (_root_.GD.N0101.N0402.d023084 z) ∂_root_.GD.N0101.N0402.d023083 s r
  let D : ℝ := ∫ z, _root_.GD.N0213.N0495.d007175 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r
  have hs : ∀ i, 0 < s i := fun i => mul_pos (ha i) (sub_pos.mpr hρ)
  have hr : ∀ i, 0 < r i := fun i => mul_pos (ha i) (ht i)
  have hc : 0 < c := inv_pos.mpr (sub_pos.mpr hρ)
  have hm : 0 < m := _root_.GD.N0101.N0402.d023091 s r hs hr L
  have hCS : e ^ 2 ≤ m * D := _root_.GD.N0101.N0402.d023092 s r hs hr hL
  have hratio (i : Fin (n + 1)) : r i / s i = c * t i := by
    dsimp only [r, s, c]
    field_simp [(ha i).ne', (sub_pos.mpr hρ).ne']
  have hM (i : Fin (n + 1)) :
      (∫ z, (z i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r) =
        c * m * t i - 2 * e / s i := by
    have h := _root_.GD.N0101.N0402.d023093 s r hs hr hL i
    rw [hratio i] at h
    change _ = (c * t i) * m - (2 / s i) * e at h
    rw [h]
    ring
  change (∑ i, (∫ z, (z i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r) *
      _root_.GD.N0230.N0665.d000407 t i ^ 2) -
    (∑ i, (∫ z, (z i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂_root_.GD.N0101.N0402.d023083 s r) * w i ^ 2) ≤
      ∑ i, ∑ j, if i = j then 0 else
        4 * (D / s i ^ 2 + D / s j ^ 2) / (c * (t i + t j))
  simp_rw [hM]
  exact _root_.GD.N0213.N0506.d008441 t s (fun _ => e) (fun _ => D) w c m
    ht hs hc hm hw hunit (fun _ => hCS)




theorem d023096 {n : ℕ}
    (a t w : Fin (n + 1) → ℝ) (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i)
    {ρ L : ℝ} (hρ : ρ < 1) (hL : 0 < L)
    (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1) (hunit : ∑ i, w i = 1) :
    let s := fun i => a i * (1 - ρ)
    let r := fun i => a i * t i
    let P := _root_.GD.N0101.N0402.d023083 s r
    let D := ∫ z, _root_.GD.N0213.N0495.d007175 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂P
    (∫ z, (∑ i, (z i)⁻¹ * _root_.GD.N0230.N0665.d000407 t i ^ 2) * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂P) -
      (∫ z, (∑ i, (z i)⁻¹ * w i ^ 2) * _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0402.d023084 z) ^ 2 ∂P) ≤
        ∑ i, ∑ j, if i = j then 0 else
          4 * (D / s i ^ 2 + D / s j ^ 2) / ((1 - ρ)⁻¹ * (t i + t j)) := by
  dsimp only
  rw [_root_.GD.N0101.N0348.d023094 _ _ (_root_.GD.N0230.N0665.d000407 t)
      (fun i => mul_pos (ha i) (sub_pos.mpr hρ)) (fun i => mul_pos (ha i) (ht i)),
    _root_.GD.N0101.N0348.d023094 _ _ w
      (fun i => mul_pos (ha i) (sub_pos.mpr hρ)) (fun i => mul_pos (ha i) (ht i))]
  exact _root_.GD.N0101.N0348.d023095 a t w ha ht hρ hL hw hunit

end
end GD.N0101.N0348

#print axioms _root_.GD.N0101.N0348.d023094
#print axioms _root_.GD.N0101.N0348.d023095
#print axioms _root_.GD.N0101.N0348.d023096
