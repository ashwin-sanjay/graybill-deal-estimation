import GD.Module0532
import GD.Module1684

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0365
noncomputable section

open _root_.GD.N0101.N0362 _root_.GD.N0101.N0403 _root_.GD.N0101.N0404
open _root_.GD.N0213.N0508
open _root_.GD.N0101.N0357 _root_.GD.N0101.N0398
open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0230.N0665

def d028458 (a : Fin 2 → ℝ) (N : ℝ) : Measure (Fin 2 → ℝ) :=
  _root_.GD.N0101.N0403.d028436 a (_root_.GD.N0101.N0362.d007947 N)

def d028459 : Set (Fin 2 → ℝ) := _root_.GD.N0101.N0403.d028435 1 (Real.exp 1)

theorem d028460 : _root_.GD.N0101.N0365.d028459 ⊆ _root_.GD.N0101.N0362.d007960 := by
  intro β hβ
  have hpos : β ∈ _root_.GD.N0101.N0362.d007944 := fun i => lt_of_lt_of_le zero_lt_one (hβ.1 i)
  have hlogs : ∀ i, 0 ≤ Real.log (β i) ∧ Real.log (β i) ≤ 1 := by
    intro i
    refine ⟨Real.log_nonneg (hβ.1 i), ?_⟩
    calc
      Real.log (β i) ≤ Real.log (Real.exp 1) := Real.log_le_log (hpos i) (hβ.2 i)
      _ = 1 := Real.log_exp 1
  refine ⟨hpos, ?_, ?_⟩
  · rw [_root_.GD.N0101.N0362.d007945, abs_le]
    constructor <;> linarith [(hlogs 0).1, (hlogs 0).2, (hlogs 1).1, (hlogs 1).2]
  · rw [_root_.GD.N0101.N0362.d007946, abs_le]
    constructor <;> linarith [(hlogs 0).1, (hlogs 0).2, (hlogs 1).1, (hlogs 1).2]

theorem d028461 : 0 < volume _root_.GD.N0101.N0365.d028459 := by
  have hexp : 1 < Real.exp (1 : ℝ) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (zero_lt_one : (0 : ℝ) < 1)
  simp only [_root_.GD.N0101.N0365.d028459, _root_.GD.N0101.N0403.d028435, Real.volume_Icc_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  positivity

theorem d028462 (a : Fin 2 → ℝ) {N : ℝ} (hN : 0 < N) :
    _root_.GD.N0101.N0365.d028458 a N univ ≠ ⊤ :=
  _root_.GD.N0101.N0403.d028440 a (_root_.GD.N0101.N0362.d007947 N) (_root_.GD.N0101.N0362.d007950 N)
    (_root_.GD.N0101.N0362.d007957 hN)

theorem d028463 (a : Fin 2 → ℝ) {N : ℝ} (hN : 1 ≤ N) :
    0 < _root_.GD.N0101.N0365.d028458 a N univ := by
  apply _root_.GD.N0101.N0404.d028457 a (_root_.GD.N0101.N0362.d007947 N) (S := _root_.GD.N0101.N0365.d028459) measurableSet_Icc
    (fun _ hβ => _root_.GD.N0101.N0362.d007961 hN (_root_.GD.N0101.N0365.d028460 hβ))
    (fun _ hβ => (_root_.GD.N0101.N0365.d028460 hβ).1) _root_.GD.N0101.N0365.d028461

def d028464 (a : Fin 2 → ℝ) : Measure (Fin 2 → ℝ) :=
  (_root_.GD.N0213.N0508.d028429 a).restrict _root_.GD.N0101.N0365.d028459

theorem d028465 (a : Fin 2 → ℝ) : 0 < _root_.GD.N0101.N0365.d028464 a univ := by
  rw [_root_.GD.N0101.N0365.d028464, Measure.restrict_apply_univ]
  exact _root_.GD.N0101.N0404.d028452 a (fun _ hβ => (_root_.GD.N0101.N0365.d028460 hβ).1)
    _root_.GD.N0101.N0365.d028461

theorem d028466 (a : Fin 2 → ℝ) : _root_.GD.N0101.N0365.d028464 a univ ≠ ⊤ := by
  rw [_root_.GD.N0101.N0365.d028464, Measure.restrict_apply_univ]
  apply ne_top_of_le_ne_top (b := volume _root_.GD.N0101.N0365.d028459)
  · simp only [_root_.GD.N0101.N0365.d028459, _root_.GD.N0101.N0403.d028435, Real.volume_Icc_pi,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    finiteness
  · exact _root_.GD.N0101.N0403.d028437 a _root_.GD.N0101.N0365.d028459



theorem d028467 (a : Fin 2 → ℝ) {N : ℝ} (hN : 1 ≤ N) :
    _root_.GD.N0101.N0365.d028464 a ≤ _root_.GD.N0101.N0365.d028458 a N :=
  _root_.GD.N0101.N0404.d028455 a (_root_.GD.N0101.N0362.d007947 N) measurableSet_Icc
    (fun _ hβ => _root_.GD.N0101.N0362.d007961 hN (_root_.GD.N0101.N0365.d028460 hβ))

theorem d028468 (a : Fin 2 → ℝ) {N M : ℝ}
    (hN : 0 < N) (hNM : N ≤ M) : _root_.GD.N0101.N0365.d028458 a N ≤ _root_.GD.N0101.N0365.d028458 a M := by
  apply withDensity_mono
  filter_upwards with β
  apply ENNReal.ofReal_le_ofReal
  exact (sq_le_sq₀ (_root_.GD.N0101.N0362.d007950 N β).1 (_root_.GD.N0101.N0362.d007950 M β).1).mpr
    (_root_.GD.N0101.N0362.d007955 hN hNM β)



theorem d028469 (sizes : Fin 2 → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) {N : ℝ} (hN : 0 < N)
    (p : (Fin 2 → ℝ) → Fin 2 → ℝ) (hp : Measurable p)
    (hpunit : ∀ t, ∑ i, p t i = 1)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t) :
    Integrable (fun β => (_root_.GD.N0101.N0398.d023335 sizes hn p β).toReal)
      (_root_.GD.N0101.N0365.d028458 (_root_.GD.N0232.N0719.N0954.d009355 sizes) N) :=
  _root_.GD.N0101.N0403.d028449 sizes hn (_root_.GD.N0101.N0362.d007947 N) (Real.exp_pos (-4 * N))
    (_root_.GD.N0101.N0362.d007950 N) (_root_.GD.N0101.N0362.d007957 hN) p hp hpunit hporacle

theorem d028470 (sizes : Fin 2 → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) {N : ℝ} (hN : 0 < N)
    (p : (Fin 2 → ℝ) → Fin 2 → ℝ) (hp : Measurable p)
    (hpunit : ∀ t, ∑ i, p t i = 1)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t) :
    (∫⁻ β, _root_.GD.N0101.N0398.d023335 sizes hn p β ∂_root_.GD.N0101.N0365.d028458 (_root_.GD.N0232.N0719.N0954.d009355 sizes) N) ≠ ⊤ :=
  _root_.GD.N0101.N0403.d028450 sizes hn (_root_.GD.N0101.N0362.d007947 N) (Real.exp_pos (-4 * N))
    (_root_.GD.N0101.N0362.d007950 N) (_root_.GD.N0101.N0362.d007957 hN) p hp hpunit hporacle

end
end GD.N0101.N0365

#print axioms _root_.GD.N0101.N0365.d028462
#print axioms _root_.GD.N0101.N0365.d028463
#print axioms _root_.GD.N0101.N0365.d028465
#print axioms _root_.GD.N0101.N0365.d028466
#print axioms _root_.GD.N0101.N0365.d028467
#print axioms _root_.GD.N0101.N0365.d028468
#print axioms _root_.GD.N0101.N0365.d028469
#print axioms _root_.GD.N0101.N0365.d028470
