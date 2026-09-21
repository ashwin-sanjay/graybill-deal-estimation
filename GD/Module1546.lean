import GD.Module1545
import GD.Module1533
import GD.Module1357
import GD.Module0822

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace GD.N0064
noncomputable section
open _root_.GD.N0051 _root_.GD.N0069 _root_.GD.N0088
open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1467 _root_.GD.N0232.N0720.N1497
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1437
open _root_.GD.N0232.N0719.N0933

def d023942 (n : ℕ) : ℝ := ((n - 1 : ℕ) : ℝ) / 2

theorem d023943 {n : ℕ} (hn : 2 ≤ n) : 0 < _root_.GD.N0064.d023942 n := by
  unfold _root_.GD.N0064.d023942
  exact div_pos (Nat.cast_pos.mpr (by omega)) (by norm_num)

def d023944 (m n : ℕ) (ω : _root_.GD.N0232.N0720.N1080.d014170 m n) : _root_.GD.N0051.d023832 :=
  ((_root_.GD.N0107.d009084 ω.1, _root_.GD.N0107.d009084 ω.2),
    (_root_.GD.N0232.N0720.N1084.d014252 m n ω,
      _root_.GD.N0232.N0720.N1084.d014253 m n ω))

theorem d023945 (m n : ℕ) : Measurable (_root_.GD.N0064.d023944 m n) := by
  unfold _root_.GD.N0064.d023944 _root_.GD.N0232.N0720.N1084.d014252
    _root_.GD.N0232.N0720.N1084.d014253
  fun_prop

theorem d023946 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1080.d014171 m n θ).map (_root_.GD.N0064.d023944 m n) =
      (_root_.GD.N0051.d023833 (_root_.GD.N0064.d023942 m) (_root_.GD.N0064.d023942 n)).map
        (_root_.GD.N0051.d023834 θ.location (θ.scale₁ ^ 2 / m) (θ.scale₂ ^ 2 / n)) := by
  have hsizes : ∀ i, 2 ≤ _root_.GD.N0232.N0720.N1467.d012537 m n i := by intro i; fin_cases i <;> assumption
  have hh := (_root_.GD.N0069.d022761 (_root_.GD.N0232.N0720.N1467.d012537 m n) hsizes
    0 1 (by decide) θ.location ![θ.scale₁, θ.scale₂]).comp
    (_root_.GD.N0232.N0720.N1497.d012552 m n θ.location θ.scale₁ θ.scale₂)
  have heq : _root_.GD.N0069.d022759 (_root_.GD.N0232.N0720.N1467.d012537 m n) 0 1 ∘ _root_.GD.N0232.N0720.N1467.d012541 m n =
      _root_.GD.N0064.d023944 m n := by funext ω; rfl
  rw [heq] at hh
  change (_root_.GD.N0107.d009030 m n θ.location θ.scale₁ θ.scale₂).map _ = _
  rw [hh.map_eq]
  simp only [_root_.GD.N0232.N0720.N1467.d012538, _root_.GD.N0232.N0720.N1467.d012539, Matrix.cons_val_zero, Matrix.cons_val_one,
    _root_.GD.N0232.N0719.N0933.d009288, _root_.GD.N0232.N0719.N0933.d009289]
  rw [Measure.map_prod_map _ _ (_root_.GD.N0232.N0719.N0933.d009293 _ _ _) (_root_.GD.N0232.N0719.N0933.d009293 _ _ _),
    Measure.map_prod_map _ _ (_root_.GD.N0232.N0719.N0933.d009294 _ _) (_root_.GD.N0232.N0719.N0933.d009294 _ _),
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  congr 1
  funext u
  rcases u with ⟨⟨x, y⟩, ⟨s, t⟩⟩
  dsimp only [Prod.map, _root_.GD.N0051.d023834, _root_.GD.N0232.N0719.N0933.d009286, _root_.GD.N0232.N0719.N0933.d009287]
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq θ.scale₁_pos.le,
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq θ.scale₂_pos.le]

def d023947 (p q : ℝ) (z : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  if ((1 - z.1) / (1 - z.1 + z.2)) ^ p ≤ (z.1 / (z.1 + z.2)) ^ q then 1 else 0

theorem d023948 (p q : ℝ) : Measurable (_root_.GD.N0064.d023947 p q) := by
  unfold _root_.GD.N0064.d023947
  exact Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const measurable_const

theorem d023949 (p q : ℝ) (z : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0064.d023947 p q z ∈ Icc (0 : ℝ) 1 := by
  unfold _root_.GD.N0064.d023947
  split_ifs <;> norm_num

theorem d023950 {p q x y s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    _root_.GD.N0232.N0720.N1437.d002998 (fun r u => _root_.GD.N0064.d023947 p q (r, u)) x y s t =
      _root_.GD.N0051.d022763 p q x y s t := by
  have hst : s + t ≠ 0 := (add_pos hs ht).ne'
  have hf : 1 - t / (s + t) = s / (s + t) := by field_simp; ring
  have hx : (1 - t / (s + t)) / (1 - t / (s + t) + (x - y) ^ 2 / (s + t)) =
      _root_.GD.N0051.d022762 s (y - x) := by
    unfold _root_.GD.N0051.d022762
    rw [hf, ← add_div, div_div_div_cancel_right₀ hst, sub_sq_comm]
  have hy : (t / (s + t)) / (t / (s + t) + (x - y) ^ 2 / (s + t)) =
      _root_.GD.N0051.d022762 t (y - x) := by
    unfold _root_.GD.N0051.d022762
    rw [← add_div, div_div_div_cancel_right₀ hst, sub_sq_comm]
  unfold _root_.GD.N0232.N0720.N1437.d002998 _root_.GD.N0232.N0720.N1437.d002996 _root_.GD.N0232.N0720.N1437.d002997 _root_.GD.N0064.d023947 _root_.GD.N0051.d022763
  dsimp only
  rw [hx, hy]
  split_ifs <;> ring

theorem d023951 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (p q : ℝ) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0064.d023947 p q)) =
      ∫⁻ u, ENNReal.ofReal
        ((_root_.GD.N0051.d023841 p q (_root_.GD.N0051.d023834 θ.location
          (θ.scale₁ ^ 2 / m) (θ.scale₂ ^ 2 / n) u) - θ.location) ^ 2)
        ∂_root_.GD.N0051.d023833 (_root_.GD.N0064.d023942 m) (_root_.GD.N0064.d023942 n) := by
  let F : _root_.GD.N0051.d023832 → ℝ := fun z =>
    _root_.GD.N0232.N0720.N1437.d002998 (fun r s => _root_.GD.N0064.d023947 p q (r, s)) z.1.1 z.1.2 z.2.1 z.2.2
  have hF : Measurable F := by
    unfold F _root_.GD.N0232.N0720.N1437.d002998 _root_.GD.N0232.N0720.N1437.d002996 _root_.GD.N0232.N0720.N1437.d002997
    have hc := _root_.GD.N0064.d023948 p q
    fun_prop
  have hl : Measurable (fun z : _root_.GD.N0051.d023832 => ENNReal.ofReal ((F z - θ.location) ^ 2)) := by
    fun_prop
  have hv : 0 < θ.scale₁ ^ 2 / m := div_pos (sq_pos_of_pos θ.scale₁_pos)
    (Nat.cast_pos.mpr (by omega))
  have hw : 0 < θ.scale₂ ^ 2 / n := div_pos (sq_pos_of_pos θ.scale₂_pos)
    (Nat.cast_pos.mpr (by omega))
  change (∫⁻ ω, ENNReal.ofReal ((F (_root_.GD.N0064.d023944 m n ω) - θ.location) ^ 2) ∂_root_.GD.N0232.N0720.N1080.d014171 m n θ) = _
  rw [← lintegral_map hl (_root_.GD.N0064.d023945 m n),
    _root_.GD.N0064.d023946 m n hm hn θ, lintegral_map hl (by unfold _root_.GD.N0051.d023834; fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0088.d023937 (_root_.GD.N0064.d023943 hm) (_root_.GD.N0064.d023943 hn)] with u hu
  dsimp only [F, _root_.GD.N0051.d023834, _root_.GD.N0051.d023841]
  rw [_root_.GD.N0064.d023950 (mul_pos hv hu.1) (mul_pos hw hu.2.1)]

theorem d023952 {v w : ℝ} (hv : 0 < v) (hw : 0 < w) :
    min v w ≤ 2 * (v⁻¹ + w⁻¹)⁻¹ := by
  have heq : (v⁻¹ + w⁻¹)⁻¹ = v * w / (v + w) := by
    field_simp
    ring
  rw [heq, ← mul_div_assoc]
  apply (le_div_iff₀ (add_pos hv hw)).mpr
  rcases le_total v w with h | h
  · rw [min_eq_left h]
    nlinarith [mul_nonneg hv.le (sub_nonneg.mpr h)]
  · rw [min_eq_right h]
    nlinarith [mul_nonneg hw.le (sub_nonneg.mpr h)]

theorem d023953 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hqa : p / q < _root_.GD.N0064.d023942 m) (hpb : q / p < _root_.GD.N0064.d023942 n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0064.d023947 p q)) ≤
      ENNReal.ofReal ((2 * _root_.GD.N0051.d023842 (_root_.GD.N0064.d023942 m) (_root_.GD.N0064.d023942 n) p q) *
        _root_.GD.N0232.N0720.N1257.d015508 m n θ) := by
  have hv : 0 < θ.scale₁ ^ 2 / m := div_pos (sq_pos_of_pos θ.scale₁_pos)
    (Nat.cast_pos.mpr (by omega))
  have hw : 0 < θ.scale₂ ^ 2 / n := div_pos (sq_pos_of_pos θ.scale₂_pos)
    (Nat.cast_pos.mpr (by omega))
  have hcap := _root_.GD.N0051.d023844 (m := θ.location)
    (_root_.GD.N0064.d023943 hm) (_root_.GD.N0064.d023943 hn) hp hq hqa hpb hv hw
  rw [_root_.GD.N0064.d023951 m n hm hn p q θ,
    ← ofReal_integral_eq_lintegral_ofReal hcap.1 (ae_of_all _ fun _ => sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  apply hcap.2.trans
  have ho := _root_.GD.N0064.d023952 hv hw
  have hc := _root_.GD.N0051.d023843 (_root_.GD.N0064.d023943 hm) (_root_.GD.N0064.d023943 hn) hqa hpb
  have hh := mul_le_mul_of_nonneg_left ho hc.le
  simpa only [_root_.GD.N0232.N0720.N1257.d015508, inv_div, mul_assoc, mul_comm,
    mul_left_comm] using hh

theorem d023954 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hqa : p / q < _root_.GD.N0064.d023942 m) (hpb : q / p < _root_.GD.N0064.d023942 n) :
    ∀ t, _root_.GD.N0024.N0277.d007882
      (_root_.GD.N0023.N0261.d021897 m n hm hn) (_root_.GD.N0064.d023947 p q) t ≤
        2 * _root_.GD.N0051.d023842 (_root_.GD.N0064.d023942 m) (_root_.GD.N0064.d023942 n) p q - 1 := by
  exact _root_.GD.N0023.N0262.d021914 m n hm hn
    (_root_.GD.N0064.d023947 p q) (_root_.GD.N0064.d023948 p q) (_root_.GD.N0064.d023949 p q) _
    (mul_nonneg (by norm_num)
      (_root_.GD.N0051.d023843 (_root_.GD.N0064.d023943 hm) (_root_.GD.N0064.d023943 hn) hqa hpb).le)
    (_root_.GD.N0064.d023953 m n hm hn hp hq hqa hpb)

open _root_.GD.N0024.N0277
open _root_.GD.N0023 _root_.GD.N0023.N0262

def d023955 (w : ℝ) (hw : 0 < w) : _root_.GD.N0024.N0277.d007878 :=
  ⟨w / (1 + w), div_pos hw (by linarith),
    (div_lt_one (by linarith)).mpr (by linarith)⟩

def d023956 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (w : ℝ) (hw : 0 < w) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := 0
  scale₁ := Real.sqrt m
  scale₂ := Real.sqrt ((n : ℝ) * w)
  scale₁_pos := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  scale₂_pos := Real.sqrt_pos.mpr (mul_pos (Nat.cast_pos.mpr (by omega)) hw)

theorem d023957 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (w : ℝ) (hw : 0 < w) :
    (_root_.GD.N0064.d023956 m n hm hn w hw).scale₁ ^ 2 / m = 1 ∧
      (_root_.GD.N0064.d023956 m n hm hn w hw).scale₂ ^ 2 / n = w := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [_root_.GD.N0064.d023956, Real.sq_sqrt (Nat.cast_nonneg m),
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) hw.le), div_self hm0,
    mul_div_cancel_left₀ w hn0, and_self]

theorem d023958 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (w : ℝ) (hw : 0 < w) :
    _root_.GD.N0023.N0262.d021905 m n hm hn (_root_.GD.N0064.d023956 m n hm hn w hw) = _root_.GD.N0064.d023955 w hw := by
  apply Subtype.ext
  change _ / (_ + _) = w / (1 + w)
  unfold _root_.GD.N0107.d009043 _root_.GD.N0107.d009044
  rw [(_root_.GD.N0064.d023957 m n hm hn w hw).1,
    (_root_.GD.N0064.d023957 m n hm hn w hw).2]

theorem d023959 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (w : ℝ) (hw : 0 < w) :
    _root_.GD.N0232.N0720.N1257.d015508 m n (_root_.GD.N0064.d023956 m n hm hn w hw) = w / (1 + w) := by
  have hv := _root_.GD.N0064.d023957 m n hm hn w hw
  have he : _root_.GD.N0232.N0720.N1257.d015508 m n (_root_.GD.N0064.d023956 m n hm hn w hw) =
      (((_root_.GD.N0064.d023956 m n hm hn w hw).scale₁ ^ 2 / m)⁻¹ +
        ((_root_.GD.N0064.d023956 m n hm hn w hw).scale₂ ^ 2 / n)⁻¹)⁻¹ := by
    simp only [_root_.GD.N0232.N0720.N1257.d015508, inv_div]
  rw [he, hv.1, hv.2, inv_one]
  field_simp
  ring

theorem d023960 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hqa : p / q < _root_.GD.N0064.d023942 m) (hpb : q / p < _root_.GD.N0064.d023942 n)
    (w : ℝ) (hw : 0 < w) :
    1 + _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) (_root_.GD.N0064.d023947 p q) (_root_.GD.N0064.d023955 w hw) =
      (∫ u, _root_.GD.N0051.d023841 p q (_root_.GD.N0051.d023834 0 1 w u) ^ 2
        ∂_root_.GD.N0051.d023833 (_root_.GD.N0064.d023942 m) (_root_.GD.N0064.d023942 n)) / (w / (1 + w)) := by
  let θ := _root_.GD.N0064.d023956 m n hm hn w hw
  have hv := _root_.GD.N0064.d023957 m n hm hn w hw
  have hi := (_root_.GD.N0051.d023844 (m := 0) (_root_.GD.N0064.d023943 hm) (_root_.GD.N0064.d023943 hn)
    hp hq hqa hpb (by norm_num : (0 : ℝ) < 1) hw).1
  simp only [sub_zero] at hi
  have he := _root_.GD.N0023.N0262.d021911 m n hm hn (_root_.GD.N0064.d023947 p q)
    (_root_.GD.N0064.d023948 p q) (_root_.GD.N0064.d023949 p q) θ
  unfold _root_.GD.N0232.N0720.N1256.d015547 at he
  rw [_root_.GD.N0064.d023951 m n hm hn p q θ,
    show θ.location = 0 from rfl, hv.1, hv.2] at he
  simp only [sub_zero] at he
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _),
    _root_.GD.N0064.d023959, _root_.GD.N0064.d023958,
    ← ENNReal.ofReal_div_of_pos (div_pos hw (by linarith : 0 < 1 + w))] at he
  have hl : 0 ≤ 1 + _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn)
      (_root_.GD.N0064.d023947 p q) (_root_.GD.N0064.d023955 w hw) := by
    unfold _root_.GD.N0024.N0277.d007882 _root_.GD.N0024.N0277.d007881
    exact add_nonneg (by norm_num) (div_nonneg (integral_nonneg fun _ => sq_nonneg _)
      (_root_.GD.N0024.N0277.d007880 _).le)
  have hr : 0 ≤ (∫ u, _root_.GD.N0051.d023841 p q (_root_.GD.N0051.d023834 0 1 w u) ^ 2
      ∂_root_.GD.N0051.d023833 (_root_.GD.N0064.d023942 m) (_root_.GD.N0064.d023942 n)) / (w / (1 + w)) := by
    exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) (by positivity)
  exact le_antisymm ((ENNReal.ofReal_le_ofReal_iff hr).mp he.ge)
    ((ENNReal.ofReal_le_ofReal_iff hl).mp he.le)

theorem d023961 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hqa : p / q < _root_.GD.N0064.d023942 m) (hpb : q / p < _root_.GD.N0064.d023942 n)
    (t : ℕ → _root_.GD.N0024.N0277.d007878) (ht : Tendsto (fun j => (t j).val) atTop (𝓝 0)) :
    Tendsto (fun j => _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) (_root_.GD.N0064.d023947 p q) (t j))
      atTop (𝓝 0) := by
  let w : ℕ → ℝ := fun j => (t j).val / (1 - (t j).val)
  have hw (j : ℕ) : 0 < w j := div_pos (t j).property.1 (sub_pos.mpr (t j).property.2)
  have hwt : Tendsto w atTop (𝓝 0) := by
    simpa only [w, sub_zero, zero_div, Pi.div_def] using
      ht.div (tendsto_const_nhds.sub ht) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have hwgt : Tendsto w atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_inf.mpr ⟨hwt, tendsto_principal.mpr (Eventually.of_forall hw)⟩
  have hfrac (j : ℕ) : _root_.GD.N0064.d023955 (w j) (hw j) = t j := by
    apply Subtype.ext
    dsimp only [_root_.GD.N0064.d023955, w]
    have ht1 : 1 - (t j).val ≠ 0 := (sub_pos.mpr (t j).property.2).ne'
    field_simp
    ring
  have heq (j : ℕ) : _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) (_root_.GD.N0064.d023947 p q) (t j) =
      (∫ u, _root_.GD.N0051.d023841 p q (_root_.GD.N0051.d023834 0 1 (w j) u) ^ 2
        ∂_root_.GD.N0051.d023833 (_root_.GD.N0064.d023942 m) (_root_.GD.N0064.d023942 n)) / (w j / (1 + w j)) - 1 := by
    have hh := _root_.GD.N0064.d023960 m n hm hn hp hq hqa hpb (w j) (hw j)
    rw [hfrac] at hh
    linarith
  have hlim := ((_root_.GD.N0088.d023941 (_root_.GD.N0064.d023943 hm)
    (_root_.GD.N0064.d023943 hn) hp hq hqa).comp hwgt).sub_const 1
  simpa only [heq, sub_self, Function.comp_apply] using hlim

theorem d023962 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hab : 1 < _root_.GD.N0064.d023942 m * _root_.GD.N0064.d023942 n) :
    ∃ f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ, Measurable f ∧ (∀ z, f z ∈ Icc (0 : ℝ) 1) ∧
      ∃ C : ℝ, (∀ t, _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) f t ≤ C) ∧
        ∀ t : ℕ → _root_.GD.N0024.N0277.d007878, Tendsto (fun j => (t j).val) atTop (𝓝 0) →
          Tendsto (fun j => _root_.GD.N0024.N0277.d007882 (_root_.GD.N0023.N0261.d021897 m n hm hn) f (t j)) atTop (𝓝 0) := by
  obtain ⟨r, hr, hrn, hra⟩ := (_root_.GD.N0051.d022772 (_root_.GD.N0064.d023943 hm)).mpr hab
  refine ⟨_root_.GD.N0064.d023947 1 r, _root_.GD.N0064.d023948 1 r, _root_.GD.N0064.d023949 1 r,
    2 * _root_.GD.N0051.d023842 (_root_.GD.N0064.d023942 m) (_root_.GD.N0064.d023942 n) 1 r - 1,
    _root_.GD.N0064.d023954 m n hm hn (by norm_num) hr hra (by simpa using hrn), ?_⟩
  exact _root_.GD.N0064.d023961 m n hm hn (by norm_num) hr hra (by simpa using hrn)

#print axioms _root_.GD.N0064.d023943
#print axioms _root_.GD.N0064.d023945
#print axioms _root_.GD.N0064.d023946
#print axioms _root_.GD.N0064.d023948
#print axioms _root_.GD.N0064.d023949
#print axioms _root_.GD.N0064.d023950
#print axioms _root_.GD.N0064.d023951
#print axioms _root_.GD.N0064.d023952
#print axioms _root_.GD.N0064.d023953
#print axioms _root_.GD.N0064.d023954
#print axioms _root_.GD.N0064.d023957
#print axioms _root_.GD.N0064.d023958
#print axioms _root_.GD.N0064.d023959
#print axioms _root_.GD.N0064.d023960
#print axioms _root_.GD.N0064.d023961
#print axioms _root_.GD.N0064.d023962
end
end GD.N0064
