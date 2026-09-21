import GD.Module1334
import GD.Module1871
import GD.Module1339





set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0381
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0101.N0380 _root_.GD.N0101.N0379
open _root_.GD.N0101.N0382 _root_.GD.N0101.N0387

def d030647 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (a ε : ℝ)
    (z : _root_.GD.N0232.N0720.N1436.d013217) : ℝ≥0∞ :=
  ∫⁻ t in Ioo a ε,
    ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) *
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t z) *
      ENNReal.ofReal ((g z - t) ^ 2)

def d030648 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (a ε : ℝ)
    (z : _root_.GD.N0232.N0720.N1436.d013217) : ℝ≥0∞ :=
  ∫⁻ t in Ioo a ε,
    ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) *
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (_root_.GD.N0101.N0380.d021698 z)) *
      ENNReal.ofReal ((g z - (1 - t)) ^ 2)

def d030649 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (a ε : ℝ)
    (z : _root_.GD.N0232.N0720.N1436.d013217) : ℝ≥0∞ :=
  _root_.GD.N0101.N0381.d030647 g a ε z + _root_.GD.N0101.N0381.d030648 g a ε z

theorem d030650
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g) (a ε : ℝ) :
    Measurable (_root_.GD.N0101.N0381.d030647 g a ε) := by
  have hpdf : Measurable (fun p : _root_.GD.N0232.N0720.N1436.d013217 × ℝ =>
      _root_.GD.N0232.N0720.N1436.d013273 2 2 p.2 p.1) :=
    _root_.GD.N0101.N0380.d021700.comp measurable_swap
  exact (show Measurable (fun p : _root_.GD.N0232.N0720.N1436.d013217 × ℝ =>
    ENNReal.ofReal (p.2 ^ (-(3 / 2 : ℝ))) *
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 p.2 p.1) *
      ENNReal.ofReal ((g p.1 - p.2) ^ 2)) by fun_prop).lintegral_prod_right

theorem d030651
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g) (a ε : ℝ) :
    Measurable (_root_.GD.N0101.N0381.d030648 g a ε) := by
  have hr : Measurable _root_.GD.N0101.N0380.d021698 := by unfold _root_.GD.N0101.N0380.d021698; fun_prop
  have hpdf : Measurable (fun p : _root_.GD.N0232.N0720.N1436.d013217 × ℝ =>
      _root_.GD.N0232.N0720.N1436.d013273 2 2 p.2 (_root_.GD.N0101.N0380.d021698 p.1)) :=
    _root_.GD.N0101.N0380.d021700.comp
      (measurable_snd.prodMk (hr.comp measurable_fst))
  exact (show Measurable (fun p : _root_.GD.N0232.N0720.N1436.d013217 × ℝ =>
    ENNReal.ofReal (p.2 ^ (-(3 / 2 : ℝ))) *
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 p.2 (_root_.GD.N0101.N0380.d021698 p.1)) *
      ENNReal.ofReal ((g p.1 - (1 - p.2)) ^ 2)) by fun_prop).lintegral_prod_right

theorem d030652
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g) (a ε : ℝ) :
    Measurable (_root_.GD.N0101.N0381.d030649 g a ε) :=
  (_root_.GD.N0101.N0381.d030650 g hg a ε).add
    (_root_.GD.N0101.N0381.d030651 g hg a ε)

theorem d030653
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g) :
    Measurable (fun t => ∫⁻ z, ENNReal.ofReal ((g z - t) ^ 2)
      ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) := by
  letI : SFinite _root_.GD.N0232.N0720.N1436.d013288 := by
    unfold _root_.GD.N0232.N0720.N1436.d013288
    infer_instance
  have heq : (fun t => ∫⁻ z, ENNReal.ofReal ((g z - t) ^ 2)
      ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) = fun t => ∫⁻ z,
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t z) *
        ENNReal.ofReal ((g z - t) ^ 2) ∂_root_.GD.N0232.N0720.N1436.d013288 := by
    funext t
    exact lintegral_withDensity_eq_lintegral_mul _
      (_root_.GD.N0232.N0720.N1436.d013279 2 2 t).ennreal_ofReal (by fun_prop)
  rw [heq]
  exact (show Measurable (fun p : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
    ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 p.1 p.2) *
      ENNReal.ofReal ((g p.2 - p.1) ^ 2)) by fun_prop).lintegral_prod_right



theorem d030654
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g) (a ε : ℝ) :
    _root_.GD.N0101.N0379.d030644 (fun t => ∫⁻ z, ENNReal.ofReal ((g z - t) ^ 2)
      ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) a ε =
      ∫⁻ z, _root_.GD.N0101.N0381.d030649 g a ε z ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  have hm := _root_.GD.N0101.N0381.d030653 g hg
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ (-(3 / 2 : ℝ)))) := by
    fun_prop
  unfold _root_.GD.N0101.N0379.d030644
  simp_rw [mul_add]
  rw [lintegral_add_left (hw.mul hm), _root_.GD.N0101.N0380.d021702 g hg a ε,
    _root_.GD.N0101.N0380.d021703 g hg a ε]
  exact (lintegral_add_left (_root_.GD.N0101.N0381.d030650 g hg a ε)
    (_root_.GD.N0101.N0381.d030648 g a ε)).symm

theorem d030655
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (a ε : ℝ) (z : _root_.GD.N0232.N0720.N1436.d013217)
    (hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218) (ha0 : 0 ≤ a) (he1 : ε < 1) :
    _root_.GD.N0101.N0381.d030647 g a ε z =
      ENNReal.ofReal (_root_.GD.N0101.N0382.d021727 (g z) z.1 z.2 a ε) := by
  have hi := (_root_.GD.N0101.N0382.d021728 (g z) hz.1 hz.2 he1).mono_set
    (show Ioo a ε ⊆ Ioo (0 : ℝ) ε from fun _ ht => ⟨ha0.trans_lt ht.1, ht.2⟩)
  have hnon : 0 ≤ᵐ[volume.restrict (Ioo a ε)]
      (fun t => (g z - t) ^ 2 * _root_.GD.N0101.N0387.d021710 z.1 z.2 t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg (sq_nonneg _) (mul_nonneg
      (_root_.GD.N0232.N0720.N1436.d013286 (m := 2) (n := 2) (by norm_num) (by norm_num)
        (ha0.trans_lt ht.1) (ht.2.trans he1) hz).le
      (Real.rpow_nonneg (ha0.trans_lt ht.1).le _))
  rw [_root_.GD.N0101.N0382.d021727, ofReal_integral_eq_lintegral_ofReal hi hnon]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 := ha0.trans_lt ht.1
  have hpdf := (_root_.GD.N0232.N0720.N1436.d013286 (m := 2) (n := 2)
    (by norm_num) (by norm_num) ht0 (ht.2.trans he1) hz).le
  rw [_root_.GD.N0101.N0387.d021710, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul hpdf]
  ring



theorem d030656
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (a ε : ℝ) (z : _root_.GD.N0232.N0720.N1436.d013217)
    (hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218) (ha0 : 0 ≤ a) (he1 : ε < 1) :
    _root_.GD.N0101.N0381.d030649 g a ε z = ENNReal.ofReal
      (_root_.GD.N0101.N0382.d021727 (g z) z.1 z.2 a ε +
        _root_.GD.N0101.N0382.d021727 (1 - g z) (1 - z.1) z.2 a ε) := by
  have hrz : _root_.GD.N0101.N0380.d021698 z ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
    ⟨⟨by dsimp [_root_.GD.N0101.N0380.d021698]; linarith [hz.1.2],
       by dsimp [_root_.GD.N0101.N0380.d021698]; linarith [hz.1.1]⟩, hz.2⟩
  have hr : _root_.GD.N0101.N0381.d030648 g a ε z =
      _root_.GD.N0101.N0381.d030647 (fun _ => 1 - g z) a ε (_root_.GD.N0101.N0380.d021698 z) := by
    apply lintegral_congr
    intro t
    rw [show (g z - (1 - t)) ^ 2 = (1 - g z - t) ^ 2 by ring]
  have hleft := _root_.GD.N0101.N0381.d030655 g a ε z hz ha0 he1
  have hright := _root_.GD.N0101.N0381.d030655 (fun _ => 1 - g z)
    a ε (_root_.GD.N0101.N0380.d021698 z) hrz ha0 he1
  have hn (w : ℝ) (v : _root_.GD.N0232.N0720.N1436.d013217) (hv : v ∈ _root_.GD.N0232.N0720.N1436.d013218) :
      0 ≤ _root_.GD.N0101.N0382.d021727 w v.1 v.2 a ε := by
    apply setIntegral_nonneg measurableSet_Ioo
    intro t ht
    exact mul_nonneg (sq_nonneg _) (mul_nonneg
      (_root_.GD.N0232.N0720.N1436.d013286 (m := 2) (n := 2) (by norm_num) (by norm_num)
        (ha0.trans_lt ht.1) (ht.2.trans he1) hv).le
      (Real.rpow_nonneg (ha0.trans_lt ht.1).le _))
  unfold _root_.GD.N0101.N0381.d030649
  rw [hleft, hr, hright, ← ENNReal.ofReal_add (hn (g z) z hz)
    (hn (1 - g z) (_root_.GD.N0101.N0380.d021698 z) hrz)]
  rfl

end
end GD.N0101.N0381

#print axioms _root_.GD.N0101.N0381.d030652
#print axioms _root_.GD.N0101.N0381.d030653
#print axioms _root_.GD.N0101.N0381.d030654
#print axioms _root_.GD.N0101.N0381.d030655
#print axioms _root_.GD.N0101.N0381.d030656
