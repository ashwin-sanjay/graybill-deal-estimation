import GD.Module1034




























open Filter MeasureTheory Topology
open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1037

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}

set_option linter.unusedSectionVars false





def d016512 (m n : ℕ) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun omega ↦ _root_.GD.N0232.N0720.N1499.d015001 m n
    (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) omega

theorem d016513 (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1037.d016512 m n g omega :=
  _root_.GD.N0232.N0720.N1499.d015003 m n _ omega

theorem d016514 (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 < _root_.GD.N0232.N0720.N1037.d016512 m n g omega :=
  _root_.GD.N0232.N0720.N1499.d015005 m n _ omega

@[fun_prop]
theorem d016515 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    Measurable (_root_.GD.N0232.N0720.N1037.d016512 m n g) :=
  _root_.GD.N0232.N0720.N1499.d015002 m n _

theorem d016516 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    Integrable (_root_.GD.N0232.N0720.N1037.d016512 m n g) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1484.d015103 m n _


theorem d016517 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    (∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 1 :=
  _root_.GD.N0232.N0720.N1484.d015104 m n _






theorem d016518 (g : _root_.GD.N0232.N0719.N0946.d009229) (F : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hF : AEStronglyMeasurable F
      (_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169))) :
    (∫ omega, F (g • omega) ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g omega * F omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  have hG : Measurable
      (_root_.GD.N0107.d009024 m n
        g.shift g.d009239 g.d009239) :=
    _root_.GD.N0107.d009026 m n _ _ _
  have hmap : (_root_.GD.N0232.N0720.N1080.d014172 m n).map
        (_root_.GD.N0107.d009024 m n
          g.shift g.d009239 g.d009239) =
      _root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) :=
    _root_.GD.N0232.N0720.N1215.d014282 m n g _root_.GD.N0232.N0720.N1080.d014169
  have h1 : (∫ omega, F omega ∂_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)) =
      ∫ omega, F (g • omega) ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    rw [← hmap, integral_map hG.aemeasurable (by rwa [hmap])]
    rfl
  have h2 : (∫ omega, F omega ∂_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169)) =
      ∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g omega * F omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    rw [_root_.GD.N0232.N0720.N1499.d015006 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169),
      integral_withDensity_eq_integral_toReal_smul
        (by fun_prop)
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards with omega
    rw [smul_eq_mul,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1499.d015003 m n _ omega)]
    rfl
  rw [← h1, h2]




theorem d016519 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (F : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hF : AEStronglyMeasurable (fun omega ↦ F (g • omega))
      (_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169))) :
    (∫ omega, F omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega * F (g • omega)
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  have h := _root_.GD.N0232.N0720.N1037.d016518 g⁻¹ (fun omega ↦ F (g • omega)) hF
  have hcancel : ∀ omega : _root_.GD.N0232.N0720.N1080.d014170 m n, g • g⁻¹ • omega = omega := by
    intro omega
    rw [smul_smul, mul_inv_cancel]
    exact one_smul _ _
  simp only [hcancel] at h
  exact h






theorem d016520 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    (∀ omega : _root_.GD.N0232.N0720.N1080.d014170 m n, 0 ≤ _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega) ∧
      Integrable (_root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹) (_root_.GD.N0232.N0720.N1080.d014172 m n) ∧
      (∫ omega, _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 1 :=
  ⟨fun omega ↦ _root_.GD.N0232.N0720.N1037.d016513 g⁻¹ omega,
    _root_.GD.N0232.N0720.N1037.d016516 g⁻¹,
    _root_.GD.N0232.N0720.N1037.d016517 g⁻¹⟩

end

end N1037
end N0720
end N0232
end GD
