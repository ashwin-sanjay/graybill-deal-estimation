import GD.Module1380
import GD.Module0475












set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set Filter
open scoped BigOperators Topology

namespace GD.N0159
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0178 _root_.GD.N0163
open _root_.GD.N0193 _root_.GD.N0181

def d022224 (t : ℝ) : ℝ := t * Real.sqrt t

theorem d022225 {t : ℝ} (ht : 0 ≤ t) : 0 ≤ _root_.GD.N0159.d022224 t :=
  mul_nonneg ht (Real.sqrt_nonneg _)

theorem d022226 {t v : ℝ} (ht : 0 ≤ t) (htv : t ≤ v) :
    _root_.GD.N0159.d022224 t ≤ _root_.GD.N0159.d022224 v :=
  mul_le_mul htv (Real.sqrt_le_sqrt htv) (Real.sqrt_nonneg _) (ht.trans htv)

theorem d022227 {t : ℝ} (ht : 0 < t) :
    _root_.GD.N0159.d022224 t = t ^ (3 / 2 : ℝ) := by
  calc
    _root_.GD.N0159.d022224 t = t ^ ((1 : ℝ) + 1 / 2) := by
      rw [Real.rpow_add ht, Real.rpow_one, ← Real.sqrt_eq_rpow]
      rfl
    _ = t ^ (3 / 2 : ℝ) := by norm_num


theorem d022228 {K : Set _root_.GD.N0232.N0720.N1436.d013217} (hK : IsCompact K)
    (hOmega : K ⊆ _root_.GD.N0232.N0720.N1436.d013218) :
    ∃ a > 0, ∃ S > 0, ∀ x ∈ K,
      a ≤ x.1 ∧ x.1 ≤ 1 - a ∧ 0 < x.2 ∧ x.2 ≤ S := by
  obtain ⟨a₀, ha₀, h₀⟩ := hK.exists_forall_le'
    (f := fun x : _root_.GD.N0232.N0720.N1436.d013217 => x.1) continuous_fst.continuousOn
    (fun x hx => (hOmega hx).1.1)
  obtain ⟨a₁, ha₁, h₁⟩ := hK.exists_forall_le'
    (f := fun x : _root_.GD.N0232.N0720.N1436.d013217 => 1 - x.1)
    (continuous_const.sub continuous_fst).continuousOn
    (fun x hx => sub_pos.mpr (hOmega hx).1.2)
  obtain ⟨S, hS⟩ := (hK.image continuous_snd).bddAbove
  refine ⟨min a₀ a₁, lt_min ha₀ ha₁, max 1 S,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _), ?_⟩
  intro x hx
  refine ⟨(min_le_left _ _).trans (h₀ x hx), ?_, (hOmega hx).2, ?_⟩
  · have hmin := min_le_right a₀ a₁
    have hx₁ := h₁ x hx
    linarith
  · exact (hS (mem_image_of_mem Prod.snd hx)).trans (le_max_right _ _)

def d022229 (a S : ℝ) : ℝ := 60 * Real.sqrt S / _root_.GD.N0178.d007130 a

theorem d022230 {a S : ℝ} (ha : 0 < a) (hS : 0 < S) :
    0 < _root_.GD.N0159.d022229 a S := by
  exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hS)) (_root_.GD.N0178.d007134 ha)


theorem d022231 {a S t u s : ℝ} (ha : 0 < a) (hS : 0 < S)
    (ht : 0 < t) (htHalf : t ≤ 1 / 2) (hau : a ≤ u) (hu : u ≤ 1)
    (hs : 0 < s) (hsS : s ≤ S) :
    _root_.GD.N0178.d007131 t u s ≤ _root_.GD.N0159.d022229 a S * _root_.GD.N0159.d022224 t := by
  have ht1 : t < 1 := by linarith
  have hu0 : 0 ≤ u := ha.le.trans hau
  have hD := _root_.GD.N0178.d007138 ht ht1 hu0 hu hs
  have hrest : 0 ≤ t * (s + 2 * (1 - u) / (1 - t)) := by positivity
  have hidentity : t * _root_.GD.N0178.d007129 t u s =
      t * (s + 2 * (1 - u) / (1 - t)) + 2 * u := by
    unfold _root_.GD.N0178.d007129
    field_simp [ht.ne', (sub_pos.mpr ht1).ne'] <;> ring
  have hscaled : a ≤ t * _root_.GD.N0178.d007129 t u s := by
    rw [hidentity]
    linarith
  have hpower := _root_.GD.N0178.d007136 ha.le hscaled
  rw [_root_.GD.N0178.d007135 ht.le] at hpower
  have hquarter : (1 / 4 : ℝ) ≤ (1 - t) ^ 2 := by
    nlinarith [sq_nonneg (t - 1 / 2)]
  have hproduct := mul_le_mul hquarter hpower (_root_.GD.N0178.d007133 ha.le) (sq_nonneg (1 - t))
  let Q := t ^ 2 * (1 - t) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0178.d007129 t u s)
  have hQ : 0 < Q := by
    exact mul_pos (mul_pos (sq_pos_of_pos ht) (sq_pos_of_pos (sub_pos.mpr ht1)))
      (_root_.GD.N0178.d007134 hD)
  have hbound : _root_.GD.N0178.d007130 a / 4 ≤ _root_.GD.N0159.d022224 t * Q := by
    calc
      _root_.GD.N0178.d007130 a / 4 = (1 / 4 : ℝ) * _root_.GD.N0178.d007130 a := by ring
      _ ≤ (1 - t) ^ 2 * (_root_.GD.N0178.d007130 t * _root_.GD.N0178.d007130 (_root_.GD.N0178.d007129 t u s)) := hproduct
      _ = _root_.GD.N0159.d022224 t * Q := by unfold Q _root_.GD.N0159.d022224 _root_.GD.N0178.d007130; ring
  change 15 * Real.sqrt s / Q ≤ _
  apply (div_le_iff₀ hQ).2
  calc
    15 * Real.sqrt s ≤ 15 * Real.sqrt S :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsS) (by norm_num)
    _ = _root_.GD.N0159.d022229 a S * (_root_.GD.N0178.d007130 a / 4) := by
      unfold _root_.GD.N0159.d022229
      field_simp [(_root_.GD.N0178.d007134 ha).ne'] <;> ring
    _ ≤ _root_.GD.N0159.d022229 a S * (_root_.GD.N0159.d022224 t * Q) :=
      mul_le_mul_of_nonneg_left hbound (_root_.GD.N0159.d022230 ha hS).le
    _ = _root_.GD.N0159.d022229 a S * _root_.GD.N0159.d022224 t * Q := by ring


theorem d022232 {K : Set _root_.GD.N0232.N0720.N1436.d013217} (hK : IsCompact K)
    (hOmega : K ⊆ _root_.GD.N0232.N0720.N1436.d013218) :
    ∃ C > 0, ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ x ∈ K,
      _root_.GD.N0178.d007131 t x.1 x.2 ≤ C * _root_.GD.N0159.d022224 t ∧
      _root_.GD.N0178.d007131 (1 - t) x.1 x.2 ≤ C * _root_.GD.N0159.d022224 t := by
  obtain ⟨_root_.GD.N0181.d007271, ha, S, hS, hbox⟩ := _root_.GD.N0159.d022228 hK hOmega
  refine ⟨_root_.GD.N0159.d022229 _root_.GD.N0181.d007271 S, _root_.GD.N0159.d022230 ha hS, ?_⟩
  intro t ht htHalf x hx
  obtain ⟨hau, hua, hs, hsS⟩ := hbox x hx
  have hu0 : 0 ≤ x.1 := ha.le.trans hau
  have hu1 : x.1 ≤ 1 := by linarith
  refine ⟨_root_.GD.N0159.d022231 ha hS ht htHalf hau hu1 hs hsS, ?_⟩
  rw [_root_.GD.N0182.d022217]
  exact _root_.GD.N0159.d022231 ha hS ht htHalf (by linarith) (by linarith) hs hsS


theorem d022233 {K : Set _root_.GD.N0232.N0720.N1436.d013217} (hK : IsCompact K)
    (hOmega : K ⊆ _root_.GD.N0232.N0720.N1436.d013218) :
    ∃ C > 0, ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ x ∈ K,
      |_root_.GD.N0178.d007131 t x.1 x.2| ≤ C * t ^ (3 / 2 : ℝ) ∧
      |_root_.GD.N0178.d007131 (1 - t) x.1 x.2| ≤ C * t ^ (3 / 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := _root_.GD.N0159.d022232 hK hOmega
  refine ⟨C, hC, ?_⟩
  intro t ht htHalf x hx
  have ht1 : t < 1 := by linarith
  have hxO := hOmega hx
  have hleft := _root_.GD.N0178.d007141 ht ht1 hxO.1.1.le hxO.1.2.le hxO.2
  have hright := _root_.GD.N0178.d007141 (sub_pos.mpr ht1) (by linarith : 1 - t < 1)
    hxO.1.1.le hxO.1.2.le hxO.2
  rw [abs_of_nonneg hleft, abs_of_nonneg hright, ← _root_.GD.N0159.d022227 ht]
  exact hbound t ht htHalf x hx


def d022234 (N : ℕ) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  ∑ i : _root_.GD.N0193.d007344 N, _root_.GD.N0193.d007348 N * _root_.GD.N0178.d007131 (_root_.GD.N0193.d007347 N i) x.1 x.2


theorem d022235 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0159.d022234 N = _root_.GD.N0163.d022178 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N)
      (fun i => (⟨_root_.GD.N0193.d007347 N i, _root_.GD.N0193.d007363 hN i⟩ : _root_.GD.N0232.N0720.N1441.d013676)) := rfl


theorem d022236 {N : ℕ} (t : _root_.GD.N0193.d007344 N → _root_.GD.N0232.N0720.N1441.d013676)
    (ht : ∀ i, (t i : ℝ) = _root_.GD.N0193.d007347 N i) :
    _root_.GD.N0159.d022234 N = _root_.GD.N0163.d022178 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) t := by
  funext x
  unfold _root_.GD.N0159.d022234 _root_.GD.N0163.d022178 _root_.GD.N0163.d022177
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i]


theorem d022237 {K : Set _root_.GD.N0232.N0720.N1436.d013217} (hK : IsCompact K)
    (hOmega : K ⊆ _root_.GD.N0232.N0720.N1436.d013218) :
    ∃ C > 0, ∀ N : ℕ, 2 ≤ N → ∀ x ∈ K,
      0 ≤ _root_.GD.N0159.d022234 N x ∧ _root_.GD.N0159.d022234 N x ≤ C * _root_.GD.N0159.d022224 (_root_.GD.N0181.d007269 N) := by
  obtain ⟨C, hC, hbound⟩ := _root_.GD.N0159.d022232 hK hOmega
  refine ⟨C, hC, ?_⟩
  intro N hN x hx
  have hxO := hOmega hx
  have hweight := (_root_.GD.N0193.d007367 hN).le
  have hsingle (i : _root_.GD.N0193.d007344 N) : _root_.GD.N0178.d007131 (_root_.GD.N0193.d007347 N i) x.1 x.2 ≤ C * _root_.GD.N0159.d022224 (_root_.GD.N0181.d007269 N) := by
    have ht0 := _root_.GD.N0193.d007358 hN i.1
    have hhalf := (_root_.GD.N0193.d007361 hN i.1).le
    have hb := hbound (_root_.GD.N0193.d007346 N i.1) ht0 hhalf x hx
    have hsmall := mul_le_mul_of_nonneg_left
      (_root_.GD.N0159.d022226 ht0.le (_root_.GD.N0193.d007360 hN i.1)) hC.le
    unfold _root_.GD.N0193.d007347
    split_ifs
    · exact hb.1.trans hsmall
    · exact hb.2.trans hsmall
  constructor
  · apply Finset.sum_nonneg
    intro i _
    have ht := _root_.GD.N0193.d007363 hN i
    exact mul_nonneg hweight (_root_.GD.N0178.d007141 ht.1 ht.2 hxO.1.1.le hxO.1.2.le hxO.2)
  · calc
      _root_.GD.N0159.d022234 N x ≤ ∑ i : _root_.GD.N0193.d007344 N, _root_.GD.N0193.d007348 N * (C * _root_.GD.N0159.d022224 (_root_.GD.N0181.d007269 N)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hsingle i) hweight)
      _ = C * _root_.GD.N0159.d022224 (_root_.GD.N0181.d007269 N) := by rw [← Finset.sum_mul, _root_.GD.N0193.d007374 hN, one_mul]


theorem d022238 : Tendsto _root_.GD.N0181.d007269 atTop (𝓝 0) := by
  apply squeeze_zero'
    (by filter_upwards [eventually_ge_atTop 2] with N hN using (_root_.GD.N0181.d007278 hN).le)
    (g := fun N : ℕ => (1 / 2 : ℝ) ^ N)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    simpa only [div_pow, one_pow] using (_root_.GD.N0181.d007281 hN).le
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem d022239 :
    Tendsto (fun N : ℕ => _root_.GD.N0159.d022224 (_root_.GD.N0181.d007269 N)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N : ℕ => Real.sqrt (_root_.GD.N0181.d007269 N)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp _root_.GD.N0159.d022238
  simpa [_root_.GD.N0159.d022224] using _root_.GD.N0159.d022238.mul hs


theorem d022240 {K : Set _root_.GD.N0232.N0720.N1436.d013217} (hK : IsCompact K)
    (hOmega : K ⊆ _root_.GD.N0232.N0720.N1436.d013218) :
    TendstoUniformlyOn _root_.GD.N0159.d022234 (fun _ => 0) atTop K := by
  obtain ⟨C, _hC, hbound⟩ := _root_.GD.N0159.d022237 hK hOmega
  have hlimit : Tendsto (fun N : ℕ => C * _root_.GD.N0159.d022224 (_root_.GD.N0181.d007269 N)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul _root_.GD.N0159.d022239
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall : ∀ᶠ N : ℕ in atTop, C * _root_.GD.N0159.d022224 (_root_.GD.N0181.d007269 N) < ε :=
    (tendsto_order.1 hlimit).2 ε hε
  filter_upwards [hsmall, eventually_ge_atTop 2] with N hsmallN hN
  intro x hx
  have hb := hbound N hN x hx
  simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hb.1] using hb.2.trans_lt hsmallN

end
end GD.N0159

#print axioms _root_.GD.N0159.d022225
#print axioms _root_.GD.N0159.d022226
#print axioms _root_.GD.N0159.d022227
#print axioms _root_.GD.N0159.d022228
#print axioms _root_.GD.N0159.d022230
#print axioms _root_.GD.N0159.d022231
#print axioms _root_.GD.N0159.d022232
#print axioms _root_.GD.N0159.d022233
#print axioms _root_.GD.N0159.d022235
#print axioms _root_.GD.N0159.d022236
#print axioms _root_.GD.N0159.d022237
#print axioms _root_.GD.N0159.d022238
#print axioms _root_.GD.N0159.d022239
#print axioms _root_.GD.N0159.d022240
