import GD.Module1234
import GD.Module1233
import GD.Module1254
import GD.Module1226
import GD.Module1273










open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal

namespace GD.N0232.N0720.N1327

noncomputable section

open _root_.GD.N0232.N0720.N1290 _root_.GD.N0232.N0720.N1292
open _root_.GD.N0232.N0720.N1264 (d020244 d020248 d020252)
open _root_.GD.N0232.N0720.N1368 (d020208)
open _root_.GD.N0232.N0720.N1359 (d004246)
open _root_.GD.N0232.N0720.N1352 _root_.GD.N0232.N0720.N1351
open _root_.GD.N0232.N0720.N1270 (d020224)
open _root_.GD.N0232.N0720.N1336 _root_.GD.N0232.N0720.N1335
open _root_.GD.N0232.N0720.N1329
open _root_.GD.N0232.N0720.N1315 (d019850)
open _root_.GD.N0232.N0720.N1322
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1434 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0107
open _root_.GD.N0232.N0720.N1398 (d019599)
open _root_.GD.N0232.N0720.N1382 (d004652)

abbrev d020582 (k : ℕ) := _root_.GD.N0232.N0720.N1341.d004414 k
abbrev d020583 := Fin 4 → ℝ

variable (m n : ℕ)

def d020584 (x : _root_.GD.N0232.N0720.N1436.d013217) : _root_.GD.N0232.N0720.N1351.d002812 :=
  ![((n - 1 : ℕ) : ℝ) * x.1, ((m - 1 : ℕ) : ℝ) * (1 - x.1), x.2]

@[fun_prop] theorem d020585 : Continuous (_root_.GD.N0232.N0720.N1327.d020584 m n) := by
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [_root_.GD.N0232.N0720.N1327.d020584] <;> fun_prop

theorem d020586 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1436.d013217} (hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1327.d020584 m n x ∈ _root_.GD.N0232.N0720.N1292.d004155 := by
  have hm1 : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have hn1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  exact _root_.GD.N0232.N0720.N1292.d004160
    (mul_pos hn1 hx.1.1) (mul_pos hm1 (sub_pos.mpr hx.1.2)) hx.2.le

theorem d020587 (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1292.d004153 (_root_.GD.N0232.N0720.N1327.d020584 m n x) = _root_.GD.N0232.N0720.N1336.d013420 m n x := by
  funext t
  simp only [_root_.GD.N0232.N0720.N1292.d004153, _root_.GD.N0232.N0720.N1327.d020584, _root_.GD.N0232.N0720.N1336.d013420,
    _root_.GD.N0232.N0720.N1271.d013403,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

def d020588 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu

theorem d020589 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    ContinuousOn (_root_.GD.N0232.N0720.N1327.d020588 m n mu) _root_.GD.N0232.N0720.N1436.d013218 := by
  have hD := (_root_.GD.N0232.N0720.N1292.d004173 (_root_.GD.N0232.N0720.N1436.d013210 m n) continuous_const mu
    (phi := fun _ ↦ 1)).continuousOn.comp (_root_.GD.N0232.N0720.N1327.d020585 m n).continuousOn
      (fun _ hx ↦ _root_.GD.N0232.N0720.N1327.d020586 m n hm hn hx)
  have hT := (_root_.GD.N0232.N0720.N1292.d004173 (_root_.GD.N0232.N0720.N1436.d013210 m n) continuous_subtype_val mu).continuousOn.comp
    (_root_.GD.N0232.N0720.N1327.d020585 m n).continuousOn (fun _ hx ↦ _root_.GD.N0232.N0720.N1327.d020586 m n hm hn hx)
  apply (hT.div hD (fun x hx ↦
    (_root_.GD.N0232.N0720.N1264.d020248 (_root_.GD.N0232.N0720.N1436.d013210 m n) mu (_root_.GD.N0232.N0720.N1327.d020586 m n hm hn hx)).ne')).congr
  intro x _hx
  simp only [Pi.div_apply, _root_.GD.N0232.N0720.N1327.d020588, _root_.GD.N0232.N0720.N1290.d004140, _root_.GD.N0232.N0720.N1290.d004139,
    _root_.GD.N0232.N0720.N1292.d004162, _root_.GD.N0232.N0720.N1292.d004161, _root_.GD.N0232.N0720.N1327.d020587, Function.comp_apply, one_mul]

def d020590 (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) : _root_.GD.N0232.N0720.N1436.d013217 → ℝ := by
  classical
  exact _root_.GD.N0232.N0720.N1436.d013218.piecewise (_root_.GD.N0232.N0720.N1327.d020588 m n mu) (fun _ ↦ 0)

theorem d020591 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    Measurable (_root_.GD.N0232.N0720.N1327.d020590 m n mu) := by
  classical
  exact (_root_.GD.N0232.N0720.N1327.d020589 m n hm hn mu).measurable_piecewise
    continuousOn_const _root_.GD.N0232.N0720.N1436.d013219

theorem d020592 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] (x : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1327.d020590 m n mu x ∈ Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218
  · rw [_root_.GD.N0232.N0720.N1327.d020590, piecewise_eq_of_mem _ _ _ hx]
    exact _root_.GD.N0232.N0720.N1359.d004246 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x)
      ((_root_.GD.N0232.N0720.N1336.d013421 m n).comp (continuous_const.prodMk continuous_id))
      (_root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx) mu (ae_of_all _ fun t ↦ t.2)
  · simp [_root_.GD.N0232.N0720.N1327.d020590, hx]

theorem d020593 {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] _root_.GD.N0232.N0720.N1327.d020588 m n mu) :
    _root_.GD.N0232.N0720.N1327.d020590 m n mu =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] g := by
  have hphysical : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, x ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
    (_root_.GD.N0232.N0720.N1436.d013290 m n (1 / 2)).ae_le
      (ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219)
  filter_upwards [hpost, hphysical] with x hx hdom
  simpa [_root_.GD.N0232.N0720.N1327.d020590, hdom] using hx.symm

theorem d020594 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1425.d014719 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] _root_.GD.N0232.N0720.N1327.d020588 m n mu)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0232.N0720.N1327.d020590 m n mu) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
      _root_.GD.N0232.N0720.N1425.d014719 m n g := by
  have hdom : ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      _root_.GD.N0232.N0720.N1441.d013705 m n t (_root_.GD.N0232.N0720.N1327.d020590 m n mu) ≤ _root_.GD.N0232.N0720.N1441.d013705 m n t g := by
    intro t
    apply le_of_eq
    apply lintegral_congr_ae
    filter_upwards [(_root_.GD.N0232.N0720.N1441.d013682 hm hn t).ae_le
      (_root_.GD.N0232.N0720.N1327.d020593 m n mu hpost)] with x hx
    rw [hx]
  have hweak (q : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n q (_root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0232.N0720.N1327.d020590 m n mu)) ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n q d :=
    (_root_.GD.N0232.N0720.N1335.d020090 m n hm hn
      (_root_.GD.N0232.N0720.N1327.d020591 m n hm hn mu) hg
      (_root_.GD.N0232.N0720.N1327.d020592 m n hm hn mu) hb hdom q).trans_eq
      (_root_.GD.N0232.N0720.N1159.d014662 m n q (hrep q))
  exact (hd.2.2.2 _ (_root_.GD.N0232.N0720.N1398.d019599 m n
    (_root_.GD.N0232.N0720.N1327.d020591 m n hm hn mu)) hweak theta).trans (hrep theta).symm

variable (k : ℕ) (hdim : m + n = k + 1)



theorem d020595 {f g : _root_.GD.N0232.N0720.N1327.d020582 k → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      f ∘ _root_.GD.N0232.N0720.N1329.d019648 m n k hdim =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] g ∘ _root_.GD.N0232.N0720.N1329.d019648 m n k hdim) :
    f =ᵐ[volume] g := by
  let q : _root_.GD.N0232.N0720.N1329.d019646 := (0, ⟨1 / 2, by norm_num, by norm_num⟩)
  let p := _root_.GD.N0232.N0720.N1329.d019660 m n k hdim q
  have hraw := hfg (_root_.GD.N0232.N0720.N1326.d019915 q)
  have hmap : f =ᵐ[(_root_.GD.N0107.d009030 m n q.1 (_root_.GD.N0232.N0720.N1329.d019663 q) (_root_.GD.N0232.N0720.N1329.d019664 q)).map
      (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim)] g :=
    (ae_map_iff (_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).measurable.aemeasurable
      (measurableSet_eq_fun hf hg)).2 hraw
  rw [_root_.GD.N0232.N0720.N1329.d019669] at hmap
  have hdensity : Measurable (_root_.GD.N0232.N0720.N1316.d004445 p) := by
    unfold _root_.GD.N0232.N0720.N1316.d004445
    fun_prop
  have hh := (ae_withDensity_iff hdensity.ennreal_ofReal).1 hmap
  filter_upwards [hh] with x hx
  apply hx
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  exact mul_pos (_root_.GD.N0232.N0720.N1316.d004446 p) (Real.exp_pos _)



theorem d020596
    {g h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ}
    (hg : Measurable g) (hh : Measurable h)
    (hgr : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1425.d014719 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d)
    (hhr : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1425.d014719 m n h =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d) :
    _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g =ᵐ[volume] _root_.GD.N0232.N0720.N1329.d019671 m n k hdim h := by
  apply _root_.GD.N0232.N0720.N1327.d020595 m n k hdim
    (_root_.GD.N0232.N0720.N1329.d019672 m n k hdim hg)
    (_root_.GD.N0232.N0720.N1329.d019672 m n k hdim hh)
  intro theta
  simpa only [Function.comp_def, _root_.GD.N0232.N0720.N1329.d019673] using
    (hgr theta).trans (hhr theta).symm

theorem d020597 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1425.d014719 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] _root_.GD.N0232.N0720.N1327.d020588 m n mu) :
    _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g =ᵐ[volume]
      _root_.GD.N0232.N0720.N1329.d019671 m n k hdim (_root_.GD.N0232.N0720.N1327.d020590 m n mu) := by
  apply _root_.GD.N0232.N0720.N1327.d020595 m n k hdim
    (_root_.GD.N0232.N0720.N1329.d019672 m n k hdim hg)
    (_root_.GD.N0232.N0720.N1329.d019672 m n k hdim (_root_.GD.N0232.N0720.N1327.d020591 m n hm hn mu))
  intro theta
  have h := (_root_.GD.N0232.N0720.N1327.d020594 m n hm hn hd hg hb hrep mu hpost theta).symm
  simpa only [Function.comp_def, _root_.GD.N0232.N0720.N1329.d019673] using h

def d020598 (x : _root_.GD.N0232.N0720.N1327.d020583) : ℝ := 2 * x 2 / ((m - 1 : ℕ) : ℝ)
def d020599 (x : _root_.GD.N0232.N0720.N1327.d020583) : ℝ := 2 * x 3 / ((n - 1 : ℕ) : ℝ)
def d020600 (x : _root_.GD.N0232.N0720.N1327.d020583) : ℝ := _root_.GD.N0232.N0720.N1327.d020598 m x + _root_.GD.N0232.N0720.N1327.d020599 n x

theorem d020601 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1327.d020583} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) :
    0 < _root_.GD.N0232.N0720.N1327.d020598 m x ∧ 0 < _root_.GD.N0232.N0720.N1327.d020599 n x := by
  have hm1 : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m - 1 by omega)
  have hn1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  exact ⟨div_pos (mul_pos (by norm_num) hx.1) hm1,
    div_pos (mul_pos (by norm_num) hx.2) hn1⟩

theorem d020602 (hm : 2 ≤ m) (x : _root_.GD.N0232.N0720.N1327.d020582 k) :
    _root_.GD.N0232.N0720.N1084.d014252 m n ((_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm x) =
      _root_.GD.N0232.N0720.N1327.d020598 m (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hm1 : (((m - 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (show m - 1 ≠ 0 by omega)
  simp only [_root_.GD.N0232.N0720.N1084.d014252, _root_.GD.N0107.d009085,
    _root_.GD.N0232.N0720.N1327.d020598, _root_.GD.N0232.N0720.N1315.d019850, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp [hmR, hm1]

theorem d020603 (hn : 2 ≤ n) (x : _root_.GD.N0232.N0720.N1327.d020582 k) :
    _root_.GD.N0232.N0720.N1084.d014253 m n ((_root_.GD.N0232.N0720.N1329.d019648 m n k hdim).symm x) =
      _root_.GD.N0232.N0720.N1327.d020599 n (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
  simp only [_root_.GD.N0232.N0720.N1084.d014253, _root_.GD.N0107.d009085,
    _root_.GD.N0232.N0720.N1327.d020599, _root_.GD.N0232.N0720.N1315.d019850, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  field_simp [hnR, hn1]

def d020604 (x : _root_.GD.N0232.N0720.N1327.d020583) : _root_.GD.N0232.N0720.N1436.d013217 :=
  (_root_.GD.N0232.N0720.N1327.d020599 n x / _root_.GD.N0232.N0720.N1327.d020600 m n x,
    (x 0 - x 1) ^ 2 / _root_.GD.N0232.N0720.N1327.d020600 m n x)

theorem d020605 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1327.d020583} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) (hd : x 0 ≠ x 1) :
    _root_.GD.N0232.N0720.N1327.d020604 m n x ∈ _root_.GD.N0232.N0720.N1436.d013218 := by
  obtain ⟨hX, hY⟩ := _root_.GD.N0232.N0720.N1327.d020601 m n hm hn hx
  have hE : 0 < _root_.GD.N0232.N0720.N1327.d020600 m n x := add_pos hX hY
  refine ⟨⟨div_pos hY hE, (div_lt_one hE).2 (by unfold _root_.GD.N0232.N0720.N1327.d020600; linarith)⟩, ?_⟩
  exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hd)) hE


theorem d020606 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1327.d020583} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) :
    _root_.GD.N0232.N0720.N1368.d020208 (x 3) (x 2) ((x 1 - x 0) ^ 2 / 2) =
      fun t ↦ (_root_.GD.N0232.N0720.N1327.d020600 m n x / 2) * _root_.GD.N0232.N0720.N1336.d013420 m n (_root_.GD.N0232.N0720.N1327.d020604 m n x) t := by
  obtain ⟨hX, hY⟩ := _root_.GD.N0232.N0720.N1327.d020601 m n hm hn hx
  have hE : _root_.GD.N0232.N0720.N1327.d020600 m n x ≠ 0 := (add_pos hX hY).ne'
  have hm1 : (((m - 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (show m - 1 ≠ 0 by omega)
  have hn1 : (((n - 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (show n - 1 ≠ 0 by omega)
  funext t
  simp only [_root_.GD.N0232.N0720.N1368.d020208, _root_.GD.N0232.N0720.N1336.d013420, _root_.GD.N0232.N0720.N1327.d020604,
    _root_.GD.N0232.N0720.N1271.d013403]
  field_simp [hE]
  dsimp [_root_.GD.N0232.N0720.N1327.d020600, _root_.GD.N0232.N0720.N1327.d020598, _root_.GD.N0232.N0720.N1327.d020599]
  field_simp [hm1, hn1]
  ring

theorem d020607 (hm : 2 ≤ m) (hn : 2 ≤ n)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (x : _root_.GD.N0232.N0720.N1327.d020582 k) :
    _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x =
      _root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 1 +
        (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 0 - _root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 1) *
          g (_root_.GD.N0232.N0720.N1327.d020604 m n (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x)) := by
  unfold _root_.GD.N0232.N0720.N1329.d019671 _root_.GD.N0232.N0720.N1425.d014719
  rw [_root_.GD.N0232.N0720.N1327.d020602 m n k hdim hm,
    _root_.GD.N0232.N0720.N1327.d020603 m n k hdim hn]
  rfl

theorem d020608 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131)
    (p : _root_.GD.N0232.N0720.N1351.d002812) :
    _root_.GD.N0232.N0720.N1308.d020280 D mu p =
      1 - _root_.GD.N0232.N0720.N1290.d004140 ((D : ℝ) / 2) (_root_.GD.N0232.N0720.N1292.d004153 (_root_.GD.N0232.N0720.N1264.d020244 p)) mu := by
  simp only [_root_.GD.N0232.N0720.N1308.d020280, _root_.GD.N0232.N0720.N1290.d004140, _root_.GD.N0232.N0720.N1290.d004139,
    _root_.GD.N0232.N0720.N1292.d004162, _root_.GD.N0232.N0720.N1292.d004161, one_mul]

theorem d020609 (D : ℕ) (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1308.d020280 D mu ∘ _root_.GD.N0232.N0720.N1351.d002814)) _root_.GD.N0232.N0720.N1270.d020224 := by
  have hG := (_root_.GD.N0232.N0720.N1308.d020281 D mu).comp
    _root_.GD.N0232.N0720.N1351.d002818.contDiffOn (fun _ hx ↦ _root_.GD.N0232.N0720.N1264.d020252 hx)
  exact (show ContDiffOn ℝ ∞ (fun x : _root_.GD.N0232.N0720.N1327.d020583 ↦ x 0) _root_.GD.N0232.N0720.N1270.d020224 by fun_prop).add
    (_root_.GD.N0232.N0720.N1352.d002748.contDiffOn.mul hG)

theorem d020610 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1327.d020583} (hx : x ∈ _root_.GD.N0232.N0720.N1382.d004652) (hd : x 0 ≠ x 1)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    _root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu (_root_.GD.N0232.N0720.N1351.d002814 x) =
      1 - _root_.GD.N0232.N0720.N1327.d020588 m n mu (_root_.GD.N0232.N0720.N1327.d020604 m n x) := by
  have hq : (((m + n + 1 : ℕ) : ℝ) / 2) = _root_.GD.N0232.N0720.N1436.d013210 m n := by
    rw [_root_.GD.N0232.N0720.N1336.d013424 m n hm hn]
    simp only [Nat.cast_add, Nat.cast_one]
  have hproj := _root_.GD.N0232.N0720.N1327.d020605 m n hm hn hx hd
  obtain ⟨hX, hY⟩ := _root_.GD.N0232.N0720.N1327.d020601 m n hm hn hx
  have hc : 0 < _root_.GD.N0232.N0720.N1327.d020600 m n x / 2 := div_pos (add_pos hX hY) (by norm_num)
  rw [_root_.GD.N0232.N0720.N1327.d020608, hq]
  change 1 - _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n)
    (_root_.GD.N0232.N0720.N1368.d020208 (x 3) (x 2) ((x 1 - x 0) ^ 2 / 2)) mu = _
  rw [_root_.GD.N0232.N0720.N1327.d020606 m n hm hn hx,
    _root_.GD.N0232.N0720.N1395.d020573 (_root_.GD.N0232.N0720.N1436.d013210 m n)
      (_root_.GD.N0232.N0720.N1336.d013420 m n (_root_.GD.N0232.N0720.N1327.d020604 m n x))
      (fun t ↦ (_root_.GD.N0232.N0720.N1336.d013423 m n hm hn hproj t).le) mu hc]
  rfl



theorem d020611 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {x : _root_.GD.N0232.N0720.N1327.d020582 k} (hx : x ∈ _root_.GD.N0232.N0720.N1322.d020080 hdim)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu] :
    _root_.GD.N0232.N0720.N1329.d019671 m n k hdim (_root_.GD.N0232.N0720.N1327.d020590 m n mu) x =
      _root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu ∘ _root_.GD.N0232.N0720.N1351.d002814)
        (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) := by
  classical
  let y := _root_.GD.N0232.N0720.N1315.d019850 m n k hdim x
  have hy : y ∈ _root_.GD.N0232.N0720.N1382.d004652 := hx
  rw [_root_.GD.N0232.N0720.N1327.d020607 m n k hdim hm hn]
  change y 1 + (y 0 - y 1) * _root_.GD.N0232.N0720.N1327.d020590 m n mu (_root_.GD.N0232.N0720.N1327.d020604 m n y) =
    y 0 + (y 1 - y 0) * _root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu (_root_.GD.N0232.N0720.N1351.d002814 y)
  by_cases hd : y 0 = y 1
  · simp only [hd, sub_self, zero_mul, add_zero]
  have hproj := _root_.GD.N0232.N0720.N1327.d020605 m n hm hn hy hd
  rw [_root_.GD.N0232.N0720.N1327.d020590, piecewise_eq_of_mem _ _ _ hproj]
  have hprior := _root_.GD.N0232.N0720.N1327.d020610 m n hm hn hy hd mu
  change y 1 + (y 0 - y 1) * _root_.GD.N0232.N0720.N1327.d020588 m n mu (_root_.GD.N0232.N0720.N1327.d020604 m n y) =
    y 0 + (y 1 - y 0) * _root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu (_root_.GD.N0232.N0720.N1351.d002814 y)
  rw [hprior]
  ring

theorem d020612 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1425.d014719 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun z ↦ _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n z) mu) :
    ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1327.d020582 k)), x ∈ _root_.GD.N0232.N0720.N1322.d020080 hdim →
      _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x =
        _root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu ∘ _root_.GD.N0232.N0720.N1351.d002814)
          (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) := by
  filter_upwards [_root_.GD.N0232.N0720.N1327.d020597 m n k hdim hm hn hd hg hb hrep mu hpost]
    with x hx
  intro hphysical
  exact hx.trans (_root_.GD.N0232.N0720.N1327.d020611 m n k hdim hm hn hphysical mu)



theorem d020613 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1425.d014719 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun z ↦ _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n z) mu)
    {f : _root_.GD.N0232.N0720.N1327.d020583 → ℝ} (hf : ContinuousOn f _root_.GD.N0232.N0720.N1382.d004652)
    (hae : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1327.d020582 k)), x ∈ _root_.GD.N0232.N0720.N1322.d020080 hdim →
      f (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) = _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x) :
    EqOn f (_root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu ∘ _root_.GD.N0232.N0720.N1351.d002814)) _root_.GD.N0232.N0720.N1382.d004652 := by
  apply _root_.GD.N0232.N0720.N1322.d020086 hdim hm hn hf
    (_root_.GD.N0232.N0720.N1327.d020609 (m + n + 1) mu).continuousOn hae
  filter_upwards [_root_.GD.N0232.N0720.N1327.d020612 m n k hdim hm hn hd hg hb hrep mu hpost]
    with x hx hphysical
  exact (hx hphysical).symm

end
end GD.N0232.N0720.N1327

#print axioms _root_.GD.N0232.N0720.N1327.d020595
#print axioms _root_.GD.N0232.N0720.N1327.d020606
#print axioms _root_.GD.N0232.N0720.N1327.d020612
#print axioms _root_.GD.N0232.N0720.N1327.d020613
