import GD.Module1485
import GD.Module1503
import GD.Module1669
import GD.Module1472
import GD.Module0035

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace GD.N0225.N0536
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0933
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0963
open _root_.GD.N0072 _root_.GD.N0021
open _root_.GD.N0225.N0538 _root_.GD.N0225.N0540
open _root_.GD.N0225.N0539
open _root_.GD.N0232.N0719.N0954

local instance : MeasurableSpace (_root_.GD.N0232.N0719.N0859.d010809 2) := borel (_root_.GD.N0232.N0719.N0859.d010809 2)
local instance : BorelSpace (_root_.GD.N0232.N0719.N0859.d010809 2) := ⟨rfl⟩

def d028342 : Fin 2 → ℕ := fun _ => 3

theorem d028343 : ∀ i, 2 ≤ _root_.GD.N0225.N0536.d028342 i := by intro i; norm_num [_root_.GD.N0225.N0536.d028342]

def d028344 (β : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  if 0 < β i then β i else 1

theorem d028345 (β : Fin 2 → ℝ) (i : Fin 2) :
    0 < _root_.GD.N0225.N0536.d028344 β i := by
  unfold _root_.GD.N0225.N0536.d028344
  split_ifs with h
  · exact h
  · exact zero_lt_one

@[fun_prop] theorem d028346 : Measurable _root_.GD.N0225.N0536.d028344 := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply i))
    (measurable_pi_apply i) measurable_const

theorem d028347 (β : Fin 2 → ℝ) (hβ : ∀ i, 0 < β i) :
    _root_.GD.N0225.N0536.d028344 β = β := by
  funext i
  exact if_pos (hβ i)

def d028348 (β : Fin 2 → ℝ) : _root_.GD.N0232.N0719.N0859.d010809 2 :=
  _root_.GD.N0002.d023306 _root_.GD.N0225.N0536.d028342 _root_.GD.N0225.N0536.d028343
    (_root_.GD.N0225.N0536.d028344 β) (_root_.GD.N0225.N0536.d028345 β)

@[fun_prop] theorem d028349 : Measurable _root_.GD.N0225.N0536.d028348 := by
  let F : (Fin 2 → ℝ) → _root_.GD.N0232.N0719.N0859.d011204 2 := fun β =>
    ⟨(0, fun i => Real.sqrt ((_root_.GD.N0225.N0536.d028342 i : ℝ) / _root_.GD.N0225.N0536.d028344 β i)),
      fun i => Real.sqrt_pos.mpr (div_pos (by norm_num [_root_.GD.N0225.N0536.d028342]) (_root_.GD.N0225.N0536.d028345 β i))⟩
  have hF : Measurable F := by
    apply Measurable.subtype_mk
    exact measurable_const.prodMk (by fun_prop)
  exact (_root_.GD.N0232.N0719.N0859.d011208 2).symm.continuous.measurable.comp hF

theorem d028350 (β : Fin 2 → ℝ) (hβ : ∀ i, 0 < β i) (i : Fin 2) :
    (_root_.GD.N0225.N0536.d028348 β).scale i ^ 2 / (_root_.GD.N0225.N0536.d028342 i : ℝ) = (β i)⁻¹ := by
  have h := _root_.GD.N0002.d023307 _root_.GD.N0225.N0536.d028342 _root_.GD.N0225.N0536.d028343
    (_root_.GD.N0225.N0536.d028344 β) (_root_.GD.N0225.N0536.d028345 β) i
  change (_root_.GD.N0225.N0536.d028348 β).scale i ^ 2 / (_root_.GD.N0225.N0536.d028342 i : ℝ) = _ at h
  simpa only [_root_.GD.N0225.N0536.d028347 β hβ] using h

theorem d028351 (β : Fin 2 → ℝ) (hβ : ∀ i, 0 < β i) :
    _root_.GD.N0232.N0719.N0933.d009301 2 _root_.GD.N0225.N0536.d028342 (_root_.GD.N0225.N0536.d028348 β).scale =
      _root_.GD.N0101.N0357.d023160 (fun _ => 1) β := by
  rw [_root_.GD.N0232.N0719.N0954.d009362 _root_.GD.N0225.N0536.d028342 _root_.GD.N0225.N0536.d028343 _
    (_root_.GD.N0225.N0536.d028348 β).scale_pos]
  unfold _root_.GD.N0101.N0357.d023160 _root_.GD.N0232.N0719.N0954.d009342
  apply congrArg Measure.pi
  funext i
  have hs : _root_.GD.N0232.N0719.N0954.d009355 _root_.GD.N0225.N0536.d028342 i = 1 := by norm_num [_root_.GD.N0232.N0719.N0954.d009355, _root_.GD.N0225.N0536.d028342]
  have hv : _root_.GD.N0232.N0719.N0954.d009356 _root_.GD.N0225.N0536.d028342 (_root_.GD.N0225.N0536.d028348 β).scale i = (β i)⁻¹ :=
    _root_.GD.N0225.N0536.d028350 β hβ i
  rw [hs]
  congr 1
  rw [_root_.GD.N0232.N0719.N0954.d009357, hs, hv]
  simp

theorem d028352 (β : Fin 2 → ℝ) (hβ : ∀ i, 0 < β i)
    (w : (Fin 2 → ℝ) → Fin 2 → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) :
    _root_.GD.N0232.N0719.N0859.d010840 2 _root_.GD.N0225.N0536.d028342 (_root_.GD.N0225.N0536.d028348 β) (_root_.GD.N0072.d023291 _root_.GD.N0225.N0536.d028342 w) =
      ∫⁻ t, ENNReal.ofReal (∑ i, (β i)⁻¹ * w t i ^ 2)
        ∂_root_.GD.N0101.N0357.d023160 (fun _ => 1) β := by
  rw [_root_.GD.N0072.d023297 _root_.GD.N0225.N0536.d028342 _root_.GD.N0225.N0536.d028343 w hw hunit,
    _root_.GD.N0225.N0536.d028351 β hβ]
  apply lintegral_congr
  intro t
  congr 1
  unfold _root_.GD.N0072.d007621
  apply Finset.sum_congr rfl
  intro i _
  change w t i ^ 2 * ((_root_.GD.N0225.N0536.d028348 β).scale i ^ 2 / (_root_.GD.N0225.N0536.d028342 i : ℝ)) = _
  rw [_root_.GD.N0225.N0536.d028350 β hβ i, mul_comm]

theorem d028353 : Measurable (_root_.GD.N0021.d023313 (k := 2)) := _root_.GD.N0021.d023314

theorem d028354 : ∀ t : Fin 2 → ℝ, ∑ i, _root_.GD.N0021.d023313 t i = 1 :=
  fun t => _root_.GD.N0232.N0719.N0900.d009131 (by decide) (_root_.GD.N0232.N0719.N0933.d009305 2 ((fun _ => 0), t))

theorem d028355 : ∀ (t : Fin 2 → ℝ) i, 0 ≤ _root_.GD.N0021.d023313 t i :=
  fun t i => _root_.GD.N0232.N0719.N0900.d009132 (by decide)
    (_root_.GD.N0232.N0719.N0933.d009305 2 ((fun _ => 0), t)) i

theorem d028356 (t : Fin 2 → ℝ) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0021.d023313 t = _root_.GD.N0230.N0665.d000407 t := by
  let s := _root_.GD.N0232.N0719.N0933.d009305 2 ((fun _ => 0), t)
  have hp (i : Fin 2) : _root_.GD.N0232.N0719.N0900.d009106 s i = (t i)⁻¹ :=
    _root_.GD.N0232.N0719.N0900.d009127 (ht i)
  have hsum : _root_.GD.N0232.N0719.N0900.d009107 s =
      _root_.GD.N0230.N0665.d000406 t :=
    Finset.sum_congr rfl (fun i _ => hp i)
  have hpos := _root_.GD.N0230.N0665.d000408 ht
  funext i
  change (if _root_.GD.N0232.N0719.N0900.d009107 s = 0 then _ else
    _root_.GD.N0232.N0719.N0900.d009106 s i / _root_.GD.N0232.N0719.N0900.d009107 s) = _
  rw [hsum, if_neg hpos.ne', hp]
  rfl

theorem d028357 :
    _root_.GD.N0232.N0719.N0859.d010815 2 _root_.GD.N0225.N0536.d028342 = _root_.GD.N0072.d023291 _root_.GD.N0225.N0536.d028342 _root_.GD.N0021.d023313 :=
  _root_.GD.N0021.d023315 _root_.GD.N0225.N0536.d028342

theorem d028358 :
    _root_.GD.N0072.d023291 _root_.GD.N0225.N0536.d028342 _root_.GD.N0021.d023313 ∈ _root_.GD.N0232.N0719.N0962.d012190 2 _root_.GD.N0225.N0536.d028342 :=
  _root_.GD.N0225.N0538.d023463 _root_.GD.N0225.N0536.d028342 _root_.GD.N0225.N0536.d028343 _root_.GD.N0021.d023313 _root_.GD.N0225.N0536.d028353
    _root_.GD.N0225.N0536.d028354 _root_.GD.N0225.N0536.d028355

theorem d028359 (β : Fin 2 → ℝ) (hβ : ∀ i, 0 < β i) :
    _root_.GD.N0232.N0719.N0963.d012141 2 _root_.GD.N0225.N0536.d028342 (_root_.GD.N0225.N0536.d028348 β) = (∑ i, β i)⁻¹ := by
  unfold _root_.GD.N0232.N0719.N0963.d012141 _root_.GD.N0232.N0719.N0838.d012097
    _root_.GD.N0232.N0719.N0838.d012096
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  calc
    (_root_.GD.N0225.N0536.d028342 i : ℝ) / (_root_.GD.N0225.N0536.d028348 β).scale i ^ 2 =
        ((_root_.GD.N0225.N0536.d028348 β).scale i ^ 2 / (_root_.GD.N0225.N0536.d028342 i : ℝ))⁻¹ := (inv_div _ _).symm
    _ = β i := by rw [_root_.GD.N0225.N0536.d028350 β hβ i, inv_inv]

theorem d028360 (β : Fin 2 → ℝ) (hβ : ∀ i, 0 < β i) :
    (_root_.GD.N0232.N0719.N0859.d010840 2 _root_.GD.N0225.N0536.d028342 (_root_.GD.N0225.N0536.d028348 β)
      (_root_.GD.N0072.d023291 _root_.GD.N0225.N0536.d028342 _root_.GD.N0021.d023313)).toReal ≤ 2 / (∑ i, β i) := by
  have hsup : _root_.GD.N0232.N0719.N0962.d012187 2 _root_.GD.N0225.N0536.d028342 (_root_.GD.N0232.N0719.N0859.d010815 2 _root_.GD.N0225.N0536.d028342) ≤ ENNReal.ofReal (2 : ℝ) := by
    change _root_.GD.N0232.N0719.N0962.d012187 2 (fun _ => 3)
      (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 3)) ≤ ENNReal.ofReal (2 : ℝ)
    exact _root_.GD.N0071.d028309 (by decide)
  have hθ : _root_.GD.N0232.N0719.N0962.d012186 2 _root_.GD.N0225.N0536.d028342 (_root_.GD.N0225.N0536.d028348 β) (_root_.GD.N0232.N0719.N0859.d010815 2 _root_.GD.N0225.N0536.d028342) ≤
      ENNReal.ofReal (2 : ℝ) :=
    (le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 2 _root_.GD.N0225.N0536.d028342 θ (_root_.GD.N0232.N0719.N0859.d010815 2 _root_.GD.N0225.N0536.d028342)) (_root_.GD.N0225.N0536.d028348 β)).trans hsup
  have hcap := (_root_.GD.N0232.N0719.N0962.d012192 2 _root_.GD.N0225.N0536.d028342 (by decide)
    (by intro i; norm_num [_root_.GD.N0225.N0536.d028342]) 2 (by norm_num) (_root_.GD.N0225.N0536.d028348 β) (_root_.GD.N0232.N0719.N0859.d010815 2 _root_.GD.N0225.N0536.d028342)).mp hθ
  rw [_root_.GD.N0225.N0536.d028357, _root_.GD.N0225.N0536.d028359 β hβ] at hcap
  have hR : 0 < ∑ i, β i := Finset.sum_pos (fun i _ => hβ i) Finset.univ_nonempty
  simpa only [div_eq_mul_inv] using
    ENNReal.toReal_le_of_le_ofReal (by positivity : 0 ≤ 2 * (∑ i, β i)⁻¹) hcap

theorem d028361 (α : Fin 2 → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) {L : ℝ} (hL : 0 < L) :
    Integrable (fun β => (_root_.GD.N0232.N0719.N0859.d010840 2 _root_.GD.N0225.N0536.d028342 (_root_.GD.N0225.N0536.d028348 β)
      (_root_.GD.N0072.d023291 _root_.GD.N0225.N0536.d028342 _root_.GD.N0021.d023313)).toReal) (_root_.GD.N0225.N0539.d008058 α L) :=
  _root_.GD.N0225.N0540.d023482 _root_.GD.N0225.N0536.d028342 α hα hsum hL _root_.GD.N0225.N0536.d028348
    _root_.GD.N0225.N0536.d028349 _ _root_.GD.N0225.N0536.d028358 2 (fun β hβ => _root_.GD.N0225.N0536.d028360 β hβ)


theorem d028362 (α : Fin 2 → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) {L : ℝ} (hL : 0 < L) :
    (∫⁻ β, ∫⁻ t, ENNReal.ofReal (∑ i, (β i)⁻¹ * _root_.GD.N0021.d023313 t i ^ 2)
      ∂_root_.GD.N0101.N0357.d023160 (fun _ => 1) β
      ∂_root_.GD.N0225.N0539.d008058 α L) ≠ ⊤ := by
  have heq : (∫⁻ β, ∫⁻ t, ENNReal.ofReal (∑ i, (β i)⁻¹ * _root_.GD.N0021.d023313 t i ^ 2)
      ∂_root_.GD.N0101.N0357.d023160 (fun _ => 1) β
      ∂_root_.GD.N0225.N0539.d008058 α L) =
      ∫⁻ β, _root_.GD.N0232.N0719.N0859.d010840 2 _root_.GD.N0225.N0536.d028342 (_root_.GD.N0225.N0536.d028348 β)
        (_root_.GD.N0072.d023291 _root_.GD.N0225.N0536.d028342 _root_.GD.N0021.d023313) ∂_root_.GD.N0225.N0539.d008058 α L := by
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0225.N0541.d008081 α L] with β hβ
    exact (_root_.GD.N0225.N0536.d028352 β hβ _root_.GD.N0021.d023313 _root_.GD.N0225.N0536.d028353 _root_.GD.N0225.N0536.d028354).symm
  rw [heq]
  have heqReal : (∫⁻ β, _root_.GD.N0232.N0719.N0859.d010840 2 _root_.GD.N0225.N0536.d028342 (_root_.GD.N0225.N0536.d028348 β)
      (_root_.GD.N0072.d023291 _root_.GD.N0225.N0536.d028342 _root_.GD.N0021.d023313) ∂_root_.GD.N0225.N0539.d008058 α L) =
      ENNReal.ofReal (∫ β, (_root_.GD.N0232.N0719.N0859.d010840 2 _root_.GD.N0225.N0536.d028342 (_root_.GD.N0225.N0536.d028348 β)
        (_root_.GD.N0072.d023291 _root_.GD.N0225.N0536.d028342 _root_.GD.N0021.d023313)).toReal ∂_root_.GD.N0225.N0539.d008058 α L) := by
    calc
      _ = ∫⁻ β, ENNReal.ofReal ((_root_.GD.N0232.N0719.N0859.d010840 2 _root_.GD.N0225.N0536.d028342 (_root_.GD.N0225.N0536.d028348 β)
          (_root_.GD.N0072.d023291 _root_.GD.N0225.N0536.d028342 _root_.GD.N0021.d023313)).toReal) ∂_root_.GD.N0225.N0539.d008058 α L := by
        apply lintegral_congr
        intro β
        exact (ENNReal.ofReal_toReal (_root_.GD.N0225.N0536.d028358.2 (_root_.GD.N0225.N0536.d028348 β))).symm
      _ = _ := (ofReal_integral_eq_lintegral_ofReal (_root_.GD.N0225.N0536.d028361 α hα hsum hL)
        (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))).symm
  rw [heqReal]
  exact ENNReal.ofReal_ne_top

end
end GD.N0225.N0536

#print axioms _root_.GD.N0225.N0536.d028349
#print axioms _root_.GD.N0225.N0536.d028350
#print axioms _root_.GD.N0225.N0536.d028351
#print axioms _root_.GD.N0225.N0536.d028352
#print axioms _root_.GD.N0225.N0536.d028353
#print axioms _root_.GD.N0225.N0536.d028354
#print axioms _root_.GD.N0225.N0536.d028355
#print axioms _root_.GD.N0225.N0536.d028356
#print axioms _root_.GD.N0225.N0536.d028357
#print axioms _root_.GD.N0225.N0536.d028358
#print axioms _root_.GD.N0225.N0536.d028359
#print axioms _root_.GD.N0225.N0536.d028360
#print axioms _root_.GD.N0225.N0536.d028361

#print axioms _root_.GD.N0225.N0536.d028362
