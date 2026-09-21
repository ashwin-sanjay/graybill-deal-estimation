import GD.Module1130
import GD.Module1156



























open Filter MeasureTheory Topology
open scoped BigOperators ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1195

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0691
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1037
open _root_.GD.N0232.N0720.N1031
open _root_.GD.N0232.N0720.N1030
open _root_.GD.N0232.N0720.N1039
open _root_.GD.N0232.N0720.N1056
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1108
open _root_.GD.N0232.N0720.N1117
open _root_.GD.N0232.N0720.N1124
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1113
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1148
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1196
open _root_.GD.N0232.N0720.N1197
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}

set_option linter.unusedSectionVars false





def d018560 (g : _root_.GD.N0232.N0719.N0946.d009229) (c : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1130.d017074 :=
  { width := c.width
    packet := fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)
    weight := c.weight
    weight_nonneg := c.weight_nonneg }



theorem d018561 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g⁻¹ • omega) =
      _root_.GD.N0107.d009024 m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239 := by
  funext omega
  exact _root_.GD.N0232.N0720.N1214.d014259 m n g⁻¹ omega

theorem d018562 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g⁻¹ • omega) := by
  rw [_root_.GD.N0232.N0720.N1195.d018561]
  exact _root_.GD.N0107.d009026 m n _ _ _

theorem d018563 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g • omega) := by
  have h : (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g • omega) =
      _root_.GD.N0107.d009024 m n g.shift g.d009239 g.d009239 := by
    funext omega
    exact _root_.GD.N0232.N0720.N1214.d014259 m n g omega
  rw [h]
  exact _root_.GD.N0107.d009026 m n _ _ _



theorem d018564 (g : _root_.GD.N0232.N0719.N0946.d009229) :
    (_root_.GD.N0232.N0720.N1080.d014172 m n).map (fun omega ↦ g⁻¹ • omega) ≪ _root_.GD.N0232.N0720.N1080.d014172 m n := by
  have hmap : (_root_.GD.N0232.N0720.N1080.d014172 m n).map
      (_root_.GD.N0107.d009024 m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239) =
      _root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169) :=
    _root_.GD.N0232.N0720.N1215.d014282 m n g⁻¹ _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1195.d018561, hmap]
  exact _root_.GD.N0232.N0720.N1080.d014173 m n _



theorem d018565 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (cert : _root_.GD.N0232.N0720.N1146.d015208 m n g) (c : _root_.GD.N0232.N0720.N1130.d017074) :
    (fun omega ↦ (_root_.GD.N0232.N0720.N1146.d015212 m n cert (_root_.GD.N0232.N0720.N1130.d017075 m n c)) omega)
      =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun omega ↦ g • _root_.GD.N0232.N0720.N1126.d016416 c.packet c.weight (g⁻¹ • omega) := by
  have h1 : (fun omega ↦ (_root_.GD.N0232.N0720.N1146.d015212 m n cert (_root_.GD.N0232.N0720.N1130.d017075 m n c)) omega)
      =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1130.d017075 m n c)) := by
    unfold _root_.GD.N0232.N0720.N1146.d015212
    exact MemLp.coeFn_toLp _
  have h2 : _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1130.d017075 m n c) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1126.d016416 c.packet c.weight := by
    have ha := _root_.GD.N0232.N0720.N1214.d014267 m n (_root_.GD.N0232.N0720.N1130.d017075 m n c)
    have hb := _root_.GD.N0232.N0720.N1126.d016427 (m := m) (n := n) c.packet c.weight c.weight_nonneg
    exact ha.trans hb
  have h3 : (fun omega ↦ _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1130.d017075 m n c) (g⁻¹ • omega))
      =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      fun omega ↦ _root_.GD.N0232.N0720.N1126.d016416 c.packet c.weight (g⁻¹ • omega) :=
    ae_eq_comp' (_root_.GD.N0232.N0720.N1195.d018562 g).aemeasurable h2 (_root_.GD.N0232.N0720.N1195.d018564 g)
  filter_upwards [h1, h3] with omega e1 e3
  rw [e1]
  unfold _root_.GD.N0232.N0720.N1214.d014261
  rw [e3]






theorem d018566 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (cert : _root_.GD.N0232.N0720.N1146.d015208 m n g) (c : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1131.d017154 m n (_root_.GD.N0232.N0720.N1195.d018560 g c)
        (_root_.GD.N0232.N0720.N1146.d015212 m n cert (_root_.GD.N0232.N0720.N1130.d017075 m n c)) =
      _root_.GD.N0232.N0720.N1056.d018131 m n g c.packet c.weight := by
  unfold _root_.GD.N0232.N0720.N1131.d017154 _root_.GD.N0232.N0720.N1056.d018131
  have hq := _root_.GD.N0232.N0720.N1195.d018565 g cert c

  set F : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := fun omega ↦
    _root_.GD.N0232.N0720.N1126.d016415 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)) c.weight omega *
      (g • _root_.GD.N0232.N0720.N1126.d016416 c.packet c.weight (g⁻¹ • omega) -
        _root_.GD.N0232.N0720.N1126.d016416 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)) c.weight omega) ^ 2
    with hFdef
  have hstep1 : (∫ omega, _root_.GD.N0232.N0720.N1126.d016415 (_root_.GD.N0232.N0720.N1195.d018560 g c).packet (_root_.GD.N0232.N0720.N1195.d018560 g c).weight
      omega * ((_root_.GD.N0232.N0720.N1146.d015212 m n cert (_root_.GD.N0232.N0720.N1130.d017075 m n c)) omega -
        _root_.GD.N0232.N0720.N1126.d016416 (_root_.GD.N0232.N0720.N1195.d018560 g c).packet (_root_.GD.N0232.N0720.N1195.d018560 g c).weight
          omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = ∫ omega, F omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    apply integral_congr_ae
    filter_upwards [hq] with omega e
    show _root_.GD.N0232.N0720.N1126.d016415 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)) c.weight omega *
      ((_root_.GD.N0232.N0720.N1146.d015212 m n cert (_root_.GD.N0232.N0720.N1130.d017075 m n c)) omega -
        _root_.GD.N0232.N0720.N1126.d016416 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)) c.weight omega) ^ 2 =
      F omega
    rw [e]

  have hG := _root_.GD.N0232.N0720.N1195.d018563 (m := m) (n := n) g
  have hGinv := _root_.GD.N0232.N0720.N1195.d018562 (m := m) (n := n) g
  have hmassG : Measurable (_root_.GD.N0232.N0720.N1126.d016415 (m := m) (n := n)
      (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)) c.weight) :=
    _root_.GD.N0232.N0720.N1030.d018107 _ _
  have hraw : Measurable (_root_.GD.N0232.N0720.N1126.d016416 (m := m) (n := n) c.packet c.weight) :=
    _root_.GD.N0230.N0617.d000179 c.weight (_root_.GD.N0232.N0720.N1126.d016413 c.packet) (_root_.GD.N0232.N0720.N1126.d016414 c.packet)
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016420 (m := m) (n := n) c.packet i)
  have hrawG : Measurable (_root_.GD.N0232.N0720.N1126.d016416 (m := m) (n := n)
      (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)) c.weight) :=
    _root_.GD.N0230.N0617.d000179 c.weight (_root_.GD.N0232.N0720.N1126.d016413 _) (_root_.GD.N0232.N0720.N1126.d016414 _)
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016420 (m := m) (n := n) _ i)
  have hsmulraw : Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
      g • _root_.GD.N0232.N0720.N1126.d016416 c.packet c.weight omega) := by
    simp only [_root_.GD.N0232.N0719.N0946.d009229.d009244]
    exact measurable_const.add (measurable_const.mul hraw)
  have hFG : Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ F (g • omega)) := by
    have h1 : Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
        _root_.GD.N0232.N0720.N1126.d016415 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)) c.weight (g • omega)) :=
      hmassG.comp hG
    have h2 : Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
        g • _root_.GD.N0232.N0720.N1126.d016416 c.packet c.weight (g⁻¹ • (g • omega))) :=
      hsmulraw.comp (hGinv.comp hG)
    have h3 : Measurable (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
        _root_.GD.N0232.N0720.N1126.d016416 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)) c.weight
          (g • omega)) :=
      hrawG.comp hG
    exact h1.mul ((h2.sub h3).pow_const 2)
  rw [hstep1, _root_.GD.N0232.N0720.N1037.d016519 g F hFG.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards with omega
  unfold _root_.GD.N0232.N0720.N1056.d018130
  show _root_.GD.N0232.N0720.N1037.d016512 m n g⁻¹ omega *
      (_root_.GD.N0232.N0720.N1126.d016415 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)) c.weight (g • omega) *
        (g • _root_.GD.N0232.N0720.N1126.d016416 c.packet c.weight (g⁻¹ • (g • omega)) -
          _root_.GD.N0232.N0720.N1126.d016416 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)) c.weight
            (g • omega)) ^ 2) = _
  rw [inv_smul_smul, _root_.GD.N0232.N0720.N1124.d016508]
  have hδ := _root_.GD.N0232.N0720.N1039.d016539 g c.packet c.weight c.weight_nonneg omega
  have hsq : (g • _root_.GD.N0232.N0720.N1126.d016416 c.packet c.weight omega -
      _root_.GD.N0232.N0720.N1126.d016416 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)) c.weight
        (g • omega)) ^ 2 =
      (_root_.GD.N0232.N0720.N1126.d016416 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (c.packet i)) c.weight
        (g • omega) - g • _root_.GD.N0232.N0720.N1126.d016416 c.packet c.weight omega) ^ 2 := by
    ring
  rw [hsq, hδ]
  unfold _root_.GD.N0232.N0720.N1039.d016521
  ring


theorem d018567 (c : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1131.d017154 m n
        (_root_.GD.N0232.N0720.N1195.d018560 _root_.GD.N0232.N0720.N1482.d015130 c)
        (_root_.GD.N0232.N0720.N1146.d015228 m n (_root_.GD.N0232.N0720.N1130.d017075 m n c)) =
      _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130 c.packet
        c.weight :=
  _root_.GD.N0232.N0720.N1195.d018566 _ _ c

theorem d018568
    (c : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1131.d017154 m n
        (_root_.GD.N0232.N0720.N1195.d018560 _root_.GD.N0232.N0720.N1482.d015131 c)
        (_root_.GD.N0232.N0720.N1146.d015229 m n (_root_.GD.N0232.N0720.N1130.d017075 m n c)) =
      _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
        c.packet c.weight :=
  _root_.GD.N0232.N0720.N1195.d018566 _ _ c



theorem d018569 (g : _root_.GD.N0232.N0719.N0946.d009229) (c : _root_.GD.N0232.N0720.N1130.d017074) :
    0 ≤ _root_.GD.N0232.N0720.N1056.d018131 m n g c.packet c.weight :=
  integral_nonneg fun omega ↦ _root_.GD.N0232.N0720.N1056.d018132 g c.packet c.weight c.weight_nonneg omega



theorem d018570 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (c : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015130 c.packet
          c.weight +
        _root_.GD.N0232.N0720.N1056.d018131 m n _root_.GD.N0232.N0720.N1482.d015131
          c.packet c.weight ≤
      _root_.GD.N0232.N0720.N1117.d018540 s c
        (_root_.GD.N0232.N0720.N1195.d018560 _root_.GD.N0232.N0720.N1482.d015130 c)
        (_root_.GD.N0232.N0720.N1195.d018560 _root_.GD.N0232.N0720.N1482.d015131 c) := by
  unfold _root_.GD.N0232.N0720.N1117.d018540
  rw [_root_.GD.N0232.N0720.N1195.d018567 c,
    _root_.GD.N0232.N0720.N1195.d018568 c]
  have h1 := _root_.GD.N0232.N0720.N1117.d018539 s c
    (_root_.GD.N0232.N0720.N1195.d018560 _root_.GD.N0232.N0720.N1482.d015130 c)
  have h2 := _root_.GD.N0232.N0720.N1117.d018539 s c
    (_root_.GD.N0232.N0720.N1195.d018560 _root_.GD.N0232.N0720.N1482.d015131 c)
  linarith








theorem d018571 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
      atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)))
    (hbudget : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1117.d018540 s (candidate j)
      (_root_.GD.N0232.N0720.N1195.d018560 _root_.GD.N0232.N0720.N1482.d015130 (candidate j))
      (_root_.GD.N0232.N0720.N1195.d018560 _root_.GD.N0232.N0720.N1482.d015131 (candidate j)))
      atTop (𝓝 0))
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega)))
    (G : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG : Integrable G (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 _root_.GD.N0232.N0720.N1482.d015130 (candidate j).packet
        (candidate j).weight omega| ≤ G omega) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 = 0 := by
  apply _root_.GD.N0232.N0720.N1196.d018201 s candidate hR ?_ hcompl G hG hdom
  refine squeeze_zero (fun j ↦ add_nonneg (_root_.GD.N0232.N0720.N1195.d018569 _ _)
    (_root_.GD.N0232.N0720.N1195.d018569 _ _)) (fun j ↦ _root_.GD.N0232.N0720.N1195.d018570 s
    (candidate j)) hbudget


theorem d018572 (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hR : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
      atTop (𝓝 (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2)))
    (hbudget : ∀ j, _root_.GD.N0232.N0720.N1117.d018540 s (candidate j)
      (_root_.GD.N0232.N0720.N1195.d018560 _root_.GD.N0232.N0720.N1482.d015130 (candidate j))
      (_root_.GD.N0232.N0720.N1195.d018560 _root_.GD.N0232.N0720.N1482.d015131 (candidate j)) ≤
      1 / ((j : ℝ) + 1))
    (hcompl : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      Tendsto (fun j ↦
        _root_.GD.N0232.N0720.N1126.d016416 (candidate j).packet (candidate j).weight omega)
        atTop (𝓝 (_root_.GD.N0232.N0720.N1159.d014633 m n s.value omega)))
    (G : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hG : Integrable G (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hdom : ∀ j, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1108.d018079 _root_.GD.N0232.N0720.N1482.d015130 (candidate j).packet
        (candidate j).weight omega| ≤ G omega) :
    _root_.GD.N0232.N0720.N1159.d014647 m n s _root_.GD.N0232.N0720.N1482.d015130 = 0 := by
  apply _root_.GD.N0232.N0720.N1195.d018571 s candidate hR ?_ hcompl G hG hdom
  refine squeeze_zero (fun j ↦ _root_.GD.N0232.N0720.N1117.d018541 s _ _ _) hbudget ?_
  exact tendsto_one_div_add_atTop_nhds_zero_nat

end

end N1195
end N0720
end N0232
end GD
