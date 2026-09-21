import GD.Module1069
import GD.Module1123
import GD.Module1028
import GD.Module0093









































open Filter MeasureTheory Topology
open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1108

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0691
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1037
open _root_.GD.N0232.N0720.N1031
open _root_.GD.N0232.N0720.N1039
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1113
open _root_.GD.N0232.N0720.N1148
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false




theorem d018075 (A : ℕ → ℝ) (c : ℝ) (hc : 0 < c) (hA1 : ∀ j, 1 ≤ A j)
    (hA : Tendsto A atTop atTop) :
    Tendsto (fun j ↦ A j / _root_.GD.N0232.N0720.N1039.d016521 (A j) c) atTop (𝓝 (1 / c)) := by
  have hinv : Tendsto (fun j ↦ (A j)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hA
  have hden : Tendsto (fun j ↦ (A j)⁻¹ + c * (1 - (A j)⁻¹)) atTop (𝓝 (0 + c * (1 - 0))) :=
    hinv.add ((tendsto_const_nhds.sub hinv).const_mul c)
  have hden' : Tendsto (fun j ↦ (A j)⁻¹ + c * (1 - (A j)⁻¹)) atTop (𝓝 c) := by
    simpa using hden
  have hlim := hden'.inv₀ hc.ne'
  have hfun : ∀ j, A j / _root_.GD.N0232.N0720.N1039.d016521 (A j) c = ((A j)⁻¹ + c * (1 - (A j)⁻¹))⁻¹ := by
    intro j
    have hA0 : A j ≠ 0 := by linarith [hA1 j]
    have hT : _root_.GD.N0232.N0720.N1039.d016521 (A j) c ≠ 0 := (_root_.GD.N0232.N0720.N1039.d016524 (hA1 j) hc).ne'
    unfold _root_.GD.N0232.N0720.N1039.d016521 at hT ⊢
    field_simp
  simp_rw [hfun]
  simpa [one_div] using hlim



theorem d018076 (μs A : ℕ → ℝ) (c μ : ℝ) (hc : 0 < c)
    (hA1 : ∀ j, 1 ≤ A j) (hA : Tendsto A atTop atTop) (hμ : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun j ↦ (μs j * A j) ^ 2 * (c - 1) / (A j * _root_.GD.N0232.N0720.N1039.d016521 (A j) c)) atTop
      (𝓝 (μ ^ 2 * (c - 1) / c)) := by
  have hratio := _root_.GD.N0232.N0720.N1108.d018075 A c hc hA1 hA
  have hprod := ((hμ.pow 2).mul_const (c - 1)).mul hratio
  have hfun : ∀ j, (μs j * A j) ^ 2 * (c - 1) / (A j * _root_.GD.N0232.N0720.N1039.d016521 (A j) c) =
      μs j ^ 2 * (c - 1) * (A j / _root_.GD.N0232.N0720.N1039.d016521 (A j) c) := by
    intro j
    have hA0 : A j ≠ 0 := by linarith [hA1 j]
    have hT : _root_.GD.N0232.N0720.N1039.d016521 (A j) c ≠ 0 := (_root_.GD.N0232.N0720.N1039.d016524 (hA1 j) hc).ne'
    field_simp
  simp_rw [hfun]
  convert hprod using 2
  ring





def d018077 (m n : ℕ) (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)

theorem d018078 (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 < _root_.GD.N0232.N0720.N1108.d018077 m n g omega :=
  _root_.GD.N0232.N0720.N1499.d015005 m n _ _


def d018079 (g : _root_.GD.N0232.N0719.N0946.d009229) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  (_root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega) ^ 2 *
    (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) - 1) /
    (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
      _root_.GD.N0232.N0720.N1039.d016521 (_root_.GD.N0232.N0720.N1126.d016415 packet weight omega)
        (_root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega)))

theorem d018080 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    _root_.GD.N0232.N0720.N1031.d017143 m n g packet weight =
      ∫ omega, _root_.GD.N0232.N0720.N1108.d018079 g packet weight omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n := rfl


theorem d018081 (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0230.N0617.d000164 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet) omega =
      _root_.GD.N0232.N0720.N1126.d016416 packet weight omega *
        _root_.GD.N0232.N0720.N1126.d016415 packet weight omega := by
  unfold _root_.GD.N0232.N0720.N1126.d016416 _root_.GD.N0230.N0617.d000166 _root_.GD.N0232.N0720.N1126.d016415
  have hA : _root_.GD.N0230.N0617.d000163 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) omega ≠ 0 := by
    have := _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet) hweight
      (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
    linarith
  field_simp


def d018082 (g : _root_.GD.N0232.N0719.N0946.d009229) (P : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  P omega ^ 2 * (_root_.GD.N0232.N0720.N1108.d018077 m n g omega - 1) / _root_.GD.N0232.N0720.N1108.d018077 m n g omega



theorem d018083 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074) (P : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hesc : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
      atTop atTop)
    (hcompl : Tendsto (fun j ↦
      _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
      atTop (𝓝 (P omega))) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega) atTop
      (𝓝 (_root_.GD.N0232.N0720.N1108.d018082 g P omega)) := by
  have hc : 0 < _root_.GD.N0232.N0720.N1108.d018077 m n g omega := _root_.GD.N0232.N0720.N1108.d018078 g omega
  have hA1 : ∀ j, 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega :=
    fun j ↦ _root_.GD.N0230.N0617.d000168 _ _ (candidate j).weight_nonneg
      (_root_.GD.N0232.N0720.N1126.d016419 _) omega
  have h := _root_.GD.N0232.N0720.N1108.d018076
    (fun j ↦ _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
    (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
    (_root_.GD.N0232.N0720.N1108.d018077 m n g omega) (P omega) hc hA1 hesc hcompl
  refine h.congr ?_
  intro j
  unfold _root_.GD.N0232.N0720.N1108.d018079 _root_.GD.N0232.N0720.N1108.d018077
  rw [_root_.GD.N0232.N0720.N1108.d018081 _ _ (candidate j).weight_nonneg]







theorem d018084 (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074) (P : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hesc : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
        atTop atTop)
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (P omega)))
    (G : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG : Integrable G (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega| ≤ G omega) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1031.d017143 m n g (candidate j).packet (candidate j).weight) atTop
      (𝓝 (∫ omega, _root_.GD.N0232.N0720.N1108.d018082 g P omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n)) := by
  have hmeas : ∀ j, AEStronglyMeasurable
      (fun omega ↦ _root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    fun j ↦ (_root_.GD.N0232.N0720.N1031.d017147 (m := m) (n := n) g hg (candidate j).packet
      (candidate j).weight (candidate j).weight_nonneg).aestronglyMeasurable
  have hbound : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      ‖_root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega‖ ≤ G omega := by
    intro j
    filter_upwards [hdom j] with omega h
    simpa [Real.norm_eq_abs] using h
  have hlim : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1108.d018082 g P omega)) := by
    filter_upwards [hesc, hcompl] with omega h1 h2
    exact _root_.GD.N0232.N0720.N1108.d018083 g candidate P omega h1 h2
  exact tendsto_integral_of_dominated_convergence G hmeas hG hbound hlim





theorem d018085 (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0) :
    (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169).location = 0 := by
  simp [_root_.GD.N0232.N0720.N1215.d014273, _root_.GD.N0232.N0720.N1080.d014169, _root_.GD.N0232.N0719.N0946.d009229.d009237, hg]



theorem d018086 (theta : _root_.GD.N0232.N0720.N1080.d014168) (hloc : theta.location = 0)
    (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hfin : _root_.GD.N0232.N0720.N1080.d014182 m n theta P ≠ ⊤) :
    Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1499.d015001 m n theta omega * (P omega) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have h1 := _root_.GD.N0232.N0720.N1078.d016376 m n theta P hfin
  rw [hloc] at h1
  simp only [sub_zero] at h1
  rw [_root_.GD.N0232.N0720.N1499.d015006 m n theta,
    integrable_withDensity_iff (by fun_prop)
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)] at h1
  refine h1.congr ?_
  filter_upwards with omega
  rw [ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1499.d015003 m n _ omega)]
  ring



theorem d018087 (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0)
    (P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hP : _root_.GD.N0232.N0720.N1159.d014637 m n P) :
    (∫ omega, _root_.GD.N0232.N0720.N1108.d018082 g (fun omega ↦ P omega) omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ‖P‖ ^ 2 - (_root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P).toReal := by
  have hloc := _root_.GD.N0232.N0720.N1108.d018085 g hg
  have hfin : _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P ≠ ⊤ := hP _
  have hrisk := _root_.GD.N0232.N0720.N1126.d016430
    (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) P hfin
  rw [hloc] at hrisk
  simp only [sub_zero] at hrisk
  have hnorm : ‖P‖ ^ 2 = ∫ omega, (P omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n :=
    _root_.GD.N0230.N0691.d001213 (_root_.GD.N0232.N0720.N1080.d014172 m n) P
  have hsq : Integrable (fun omega ↦ (P omega) ^ 2) (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (Lp.memLp P).integrable_sq
  have hw := _root_.GD.N0232.N0720.N1108.d018086 (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) hloc P hfin
  rw [hrisk, hnorm, ← integral_sub hsq hw]
  apply integral_congr_ae
  filter_upwards with omega
  unfold _root_.GD.N0232.N0720.N1108.d018082 _root_.GD.N0232.N0720.N1108.d018077
  have hrec := _root_.GD.N0232.N0720.N1031.d017132 g omega
  unfold _root_.GD.N0232.N0720.N1037.d016512 at hrec
  have hc : 0 < _root_.GD.N0232.N0720.N1499.d015001 m n (_root_.GD.N0232.N0720.N1215.d014272 g _root_.GD.N0232.N0720.N1080.d014169) (g • omega) :=
    _root_.GD.N0232.N0720.N1499.d015005 m n _ _
  field_simp
  linear_combination (P omega ^ 2) * hrec





theorem d018088 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0) :
    (∫ omega, _root_.GD.N0232.N0720.N1108.d018082 g (fun omega ↦ _root_.GD.N0232.N0720.N1159.d014633 m n s.value omega) omega
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        (_root_.GD.N0232.N0720.N1159.d014647 m n s g + ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2) /
          g.d009239 ^ 2 := by
  have hPmem : _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hP : _root_.GD.N0232.N0720.N1159.d014637 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s _ hPmem
  rw [_root_.GD.N0232.N0720.N1108.d018087 g hg _ hP, _root_.GD.N0232.N0720.N1148.d018037 s g,
    ENNReal.toReal_ofReal]
  have hD := _root_.GD.N0232.N0720.N1159.d014650 m n s g
  have ha : (0 : ℝ) < g.d009239 ^ 2 := pow_pos g.d009240 2
  positivity




theorem d018089 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
      atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)))
    (hesc : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
        atTop atTop)
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega)))
    (G : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG : Integrable G (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega| ≤ G omega) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s
        (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i)) (candidate j).weight) atTop
      (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + _root_.GD.N0232.N0720.N1159.d014647 m n s g)) := by
  have hE := _root_.GD.N0232.N0720.N1108.d018084 g hg candidate
    (fun omega ↦ _root_.GD.N0232.N0720.N1159.d014633 m n s.value omega) hesc hcompl G hG hdom
  rw [_root_.GD.N0232.N0720.N1108.d018088 s g hg] at hE
  have hform : ∀ j, _root_.GD.N0232.N0720.N1126.d016432 s
      (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i)) (candidate j).weight =
      g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight -
        g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1031.d017143 m n g (candidate j).packet (candidate j).weight := by
    intro j
    have := _root_.GD.N0232.N0720.N1031.d017148 s g hg (candidate j).packet (candidate j).weight
      (candidate j).weight_nonneg
    linarith
  simp only [hform]
  have hlim := (hR.const_mul (g.d009239 ^ 2)).sub (hE.const_mul (g.d009239 ^ 2))
  have ha : g.d009239 ^ 2 ≠ 0 := (pow_pos g.d009240 2).ne'
  convert hlim using 2
  field_simp
  ring





theorem d018090 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
      atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)))
    (hesc : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
        atTop atTop)
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega)))
    (G : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG : Integrable G (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega| ≤ G omega) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s g = 0 := by
  have hlim := _root_.GD.N0232.N0720.N1108.d018089 s g hg candidate hR hesc hcompl G hG hdom
  have hle : ∀ j, _root_.GD.N0232.N0720.N1126.d016432 s
      (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i)) (candidate j).weight ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
    intro j
    let image : _root_.GD.N0232.N0720.N1130.d017074 :=
      { width := (candidate j).width
        packet := fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g ((candidate j).packet i)
        weight := (candidate j).weight
        weight_nonneg := (candidate j).weight_nonneg }
    exact _root_.GD.N0232.N0720.N1113.d017125 m n s image
  have hbound := le_of_tendsto' hlim hle
  have hnn := _root_.GD.N0232.N0720.N1159.d014650 m n s g
  linarith




theorem d018091 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (g : _root_.GD.N0232.N0719.N0946.d009229) (hg : g.shift = 0) (hdefect : 0 < _root_.GD.N0232.N0720.N1159.d014647 m n s g)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
      atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)))
    (hesc : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016415 (candidate j).packet (candidate j).weight omega)
        atTop atTop)
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega))) :
    ¬ ∃ G : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Integrable G (_root_.GD.N0232.N0720.N1080.d014172 m n) ∧
      ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
        |_root_.GD.N0232.N0720.N1108.d018079 g (candidate j).packet (candidate j).weight omega| ≤ G omega := by
  rintro ⟨G, hG, hdom⟩
  have := _root_.GD.N0232.N0720.N1108.d018090 s g hg candidate hR hesc hcompl G hG hdom
  linarith

end

end N1108
end N0720
end N0232
end GD
