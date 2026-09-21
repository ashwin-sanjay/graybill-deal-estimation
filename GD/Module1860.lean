import GD.Module1832

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators ContDiff

namespace GD.N0096.N0344

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0719.N0946

def d030491 (m n : ℕ) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  Measurable d ∧
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) => g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) => g • y) d ∧
    (∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≠ ⊤) ∧
    (∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta d) →
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d)

end GD.N0096.N0344

namespace GD.N0232.N0720.N1295

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1506 _root_.GD.N0232.N0720.N1446
open _root_.GD.N0137 _root_.GD.N0107

open _root_.GD.N0096.N0344

variable (m n : ℕ)

theorem d030492 {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030491 m n d) :
    ∃ hmem : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) (hmem.toLp d) ∧
        _root_.GD.N0232.N0720.N1159.d014638 m n (hmem.toLp d) := by
  obtain ⟨hmeas, hcov, hstrict, hterminal⟩ := hd
  have hmem : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n d hmeas
      (hstrict _root_.GD.N0232.N0720.N1080.d014169)
  let p := hmem.toLp d
  have hrisk (theta : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014182 m n theta p = _root_.GD.N0232.N0720.N1080.d014197 m n theta d :=
    (_root_.GD.N0232.N0720.N1080.d014198 m n theta d hmem).symm
  have hclass : d =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1214.d014265 m n p :=
    hmem.coeFn_toLp.symm.trans (_root_.GD.N0232.N0720.N1214.d014267 m n p).symm
  have hrep : _root_.GD.N0232.N0720.N1159.d014652 m n p :=
    ⟨d, hmeas, fun theta ↦
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq hclass, hcov⟩
  refine ⟨hmem, ?_,
    _root_.GD.N0232.N0720.N1159.d014653 m n p hrep⟩
  intro e he
  have hraw : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n e) ≤
      _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
    intro theta
    rw [_root_.GD.N0232.N0720.N1215.d014286, ← hrisk theta]
    exact he theta
  apply Lp.ext
  exact (_root_.GD.N0232.N0720.N1214.d014267 m n e).symm.trans
    ((hterminal _ (_root_.GD.N0232.N0720.N1214.d014266 m n e) hraw _root_.GD.N0232.N0720.N1080.d014169).trans
      hmem.coeFn_toLp.symm)

end
end GD.N0232.N0720.N1295

namespace GD.N0232.N0720.N1342

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0860
open _root_.GD.N0232.N0719.N1010
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1295
open _root_.GD.N0232.N0720.N1467 _root_.GD.N0232.N0720.N1501
open _root_.GD.N0232.N0720.N1475
open _root_.GD.N0232.N0720.N1476
open _root_.GD.N0232.N0720.N1209
open _root_.GD.N0232.N0720.N1041
open _root_.GD.N0232.N0720.N1459
open _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1286
open _root_.GD.N0137 _root_.GD.N0107

open _root_.GD.N0096.N0344

variable (m n : ℕ)

theorem d030493
    {d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030491 m n d)
    (he : Measurable e)
    (hecov : _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦
        g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) e)
    (hae : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d) :
    _root_.GD.N0096.N0344.d030491 m n e := by
  have hrisk (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n theta e = _root_.GD.N0232.N0720.N1080.d014197 m n theta d :=
    _root_.GD.N0232.N0720.N1159.d014662 m n theta (hae theta)
  refine ⟨he, hecov, ?_, ?_⟩
  · intro theta
    rw [hrisk]
    exact hd.2.2.1 theta
  · intro f hf hdom theta
    exact (hd.2.2.2 f hf (fun eta ↦ by
      simpa only [hrisk] using hdom eta) theta).trans (hae theta).symm

theorem d030494
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030491 m n d) :
    ∃ q : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable q ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168, (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d) ∧
      _root_.GD.N0232.N0719.N0860.d011447 q ∧
      _root_.GD.N0232.N0720.N1209.d012478 q ∧
      _root_.GD.N0096.N0344.d030491 m n (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) := by
  obtain ⟨hmem, hterminal, hcharacter⟩ := _root_.GD.N0232.N0720.N1295.d030492 m n hd
  have hfinite : _root_.GD.N0232.N0720.N1159.d014637 m n (hmem.toLp d) := by
    intro theta
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n theta d hmem]
    exact hd.2.2.1 theta
  let seed : _root_.GD.N0232.N0720.N1159.d014639 m n := ⟨hmem.toLp d, hfinite, hcharacter⟩
  obtain ⟨q, hq, hrep, haffine, hreflect⟩ :=
    _root_.GD.N0232.N0720.N1476.d019379
      m n hm hn seed hterminal
  have hae (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d :=
    (hrep theta).trans
      ((_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq hmem.coeFn_toLp)
  refine ⟨q, hq, hae, haffine, hreflect, ?_⟩
  apply _root_.GD.N0232.N0720.N1342.d030493 m n hd
    (hq.comp (_root_.GD.N0232.N0720.N1501.d016289 m n))
  · intro g omega
    simp only [Function.comp_apply,
      _root_.GD.N0232.N0720.N1475.d018975 m n (by omega) (by omega), _root_.GD.N0232.N0719.N1010.d011416,
      _root_.GD.N0232.N0719.N0946.d009229.d009244]
    exact haffine g.shift g.d009239 g.d009240 (_root_.GD.N0232.N0720.N1467.d012542 m n omega)
  · exact hae

theorem d030495
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030491 m n d) :
    ∃ g : ℝ × ℝ → ℝ, Measurable g ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g := by
  obtain ⟨q, hq, hae, haffine, hreflect, _hterminal⟩ :=
    _root_.GD.N0232.N0720.N1342.d030494 m n hm hn hd
  refine ⟨fun p ↦ _root_.GD.N0232.N0720.N1209.d012471 q p.1 p.2,
    _root_.GD.N0232.N0720.N1209.d012473 q hq, ?_⟩
  intro theta
  exact (hae theta).symm.trans
    (_root_.GD.N0232.N0720.N1342.d019639 m n hm hn q haffine hreflect theta)

theorem d030496
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030491 m n d) :
    ∃ g : ℝ × ℝ → ℝ, Measurable g ∧
      (∀ p, g p ∈ Icc (0 : ℝ) 1) ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g := by
  obtain ⟨g, hg, hae⟩ := _root_.GD.N0232.N0720.N1342.d030495 m n hm hn hd
  have hclipMeas : Measurable (_root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0232.N0720.N1286.d019582 g)) :=
    _root_.GD.N0232.N0720.N1398.d019599 m n
      (_root_.GD.N0232.N0720.N1286.d019583 hg)
  have hdom (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0232.N0720.N1286.d019582 g)) ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
    have hrisk := _root_.GD.N0232.N0720.N1159.d014662 m n theta (hae theta)
    have hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≠ ⊤ := by
      rw [← hrisk]
      exact hd.2.2.1 theta
    rw [hrisk]
    exact _root_.GD.N0232.N0720.N1398.d019600
      m n hm hn theta hg hfinite
  refine ⟨_root_.GD.N0232.N0720.N1286.d019582 g,
    _root_.GD.N0232.N0720.N1286.d019583 hg,
    _root_.GD.N0232.N0720.N1286.d019584 g, ?_⟩
  intro theta
  exact (hd.2.2.2 _ hclipMeas hdom theta).symm

end
end GD.N0232.N0720.N1342

namespace GD.N0232.N0720.N1335

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1342
open _root_.GD.N0232.N0720.N1337
open _root_.GD.N0232.N0720.N1287 _root_.GD.N0232.N0720.N1398
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0141
open _root_.GD.N0107 _root_.GD.N0137
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0556

open _root_.GD.N0096.N0344

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

theorem d030497
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030491 m n d) :
    ∃ (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (H : _root_.GD.N0232.N0720.N1441.d013681 m n),
      Measurable g ∧ (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧
      ((H : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] _root_.GD.N0232.N0720.N1441.d013686 g) ∧
      _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn) H ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1425.d014719 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d := by
  obtain ⟨seed, hseed, hseedb, hrep⟩ :=
    _root_.GD.N0232.N0720.N1342.d030496 m n hm hn hd
  let g := _root_.GD.N0232.N0720.N1441.d013701 hm hn seed hseed hseedb
  let H := _root_.GD.N0232.N0720.N1441.d013690 hm hn seed hseed hseedb
  have hg : Measurable g :=
    _root_.GD.N0232.N0720.N1441.d013702 hm hn seed hseed hseedb
  have hgb : ∀ x, g x ∈ Icc (0 : ℝ) 1 :=
    _root_.GD.N0232.N0720.N1441.d013703 hm hn seed hseed hseedb
  have hweak (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
    have hbelow := _root_.GD.N0232.N0720.N1335.d020090 m n hm hn hg hseed hgb hseedb
      (_root_.GD.N0232.N0720.N1441.d013708 hm hn seed hseed hseedb) theta
    exact hbelow.trans_eq (_root_.GD.N0232.N0720.N1159.d014662 m n theta (hrep theta)).symm
  refine ⟨g, H, hg, hgb, ?_, ?_, ?_⟩
  · exact (_root_.GD.N0232.N0720.N1441.d013704 hm hn seed hseed hseedb).symm
  · exact _root_.GD.N0232.N0720.N1335.d020091 m n hm hn seed hseed hseedb
  · exact hd.2.2.2 _ (_root_.GD.N0232.N0720.N1398.d019599 m n hg) hweak

end
end GD.N0232.N0720.N1335

namespace GD.N0232.N0720.N1303

noncomputable section

open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1337 _root_.GD.N0232.N0720.N1335
open _root_.GD.N0232.N0720.N1305 _root_.GD.N0232.N0720.N1307
open _root_.GD.N0232.N0720.N1306 _root_.GD.N0232.N0720.N1304
open _root_.GD.N0232.N0720.N1336 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1266 (d013726)
open _root_.GD.N0232.N0720.N1265
  (d020134 d020135 d020136 d020137)
open _root_.GD.N0230.N0622
open _root_.GD.N0230.N0556

open _root_.GD.N0096.N0344

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
include hm hn

theorem d030498
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030491 m n d) :
    ∃ (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131),
      Measurable g ∧ (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1425.d014719 m n g
          =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] d) ∧
      (g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x ↦
        _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x) (μ : Measure _root_.GD.N0232.N0720.N1290.d004131)) := by
  obtain ⟨g, H, hg, hb, hcenter, hadm, hrep⟩ :=
    _root_.GD.N0232.N0720.N1335.d030497 m n hm hn hd
  obtain ⟨μ, hμ⟩ := _root_.GD.N0232.N0720.N1303.d020148 m n hm hn g H hcenter hadm
  have hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      Continuous (_root_.GD.N0232.N0720.N1336.d013420 m n x) ∧ ∀ t, 0 < _root_.GD.N0232.N0720.N1336.d013420 m n x t := by
    filter_upwards [_root_.GD.N0232.N0720.N1303.d020147 m n] with x hx
    exact ⟨(_root_.GD.N0232.N0720.N1336.d013421 m n).comp (continuous_const.prodMk continuous_id),
      _root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx⟩
  obtain ⟨ν, hν⟩ := _root_.GD.N0232.N0720.N1304.d004178 (_root_.GD.N0232.N0720.N1441.d013679 m n)
    (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n) g μ hP hμ
  exact ⟨g, ν, hg, hb, hrep, hν⟩

end
end GD.N0232.N0720.N1303

namespace GD.N0232.N0720.N1326

noncomputable section

open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1329 _root_.GD.N0232.N0720.N1342
open _root_.GD.N0107 _root_.GD.N0137
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0230.N0556
open _root_.GD.N0238.N0753

open _root_.GD.N0096.N0344

variable (m n k : ℕ) (hdim : m + n = k + 1)

theorem d030499
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030491 m n d)
    (f : _root_.GD.N0232.N0720.N1341.d004414 k → ℝ) (hf : Measurable f) (hhom : _root_.GD.N0238.N0753.d004397 f)
    (C : ℝ) (hbound : ∀ u : _root_.GD.N0232.N0720.N1341.d004415 k, ‖f u‖ ≤ C)
    (hrep : ∀ theta : _root_.GD.N0232.N0720.N1326.d019882,
      f ∘ _root_.GD.N0232.N0720.N1329.d019648 m n k hdim =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d) :
    _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1326.d019892 m n k hdim) (_root_.GD.N0232.N0720.N1326.d019889 f hf C hbound) := by
  let h := _root_.GD.N0232.N0720.N1326.d019889 f hf C hbound
  have heq : ∀ theta : _root_.GD.N0232.N0720.N1326.d019882,
      _root_.GD.N0232.N0720.N1326.d019893 m n k hdim h =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d :=
    fun theta ↦ (_root_.GD.N0232.N0720.N1326.d019920 m n k hdim f hf hhom C hbound theta).trans
      (hrep theta)
  have hrisk : ∀ theta : _root_.GD.N0232.N0720.N1326.d019882,
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1326.d019893 m n k hdim h) =
        _root_.GD.N0232.N0720.N1080.d014197 m n theta d :=
    fun theta ↦ _root_.GD.N0232.N0720.N1159.d014662 m n theta (heq theta)
  apply _root_.GD.N0232.N0720.N1326.d019918
  rintro ⟨e, he, hweak, theta, hstrict⟩
  have hterm := hd.2.2.2 e he (fun q ↦ (hweak q).trans (hrisk q).le) theta
  have heRisk := _root_.GD.N0232.N0720.N1159.d014662 m n theta hterm
  rw [heRisk, hrisk theta] at hstrict
  exact lt_irrefl _ hstrict

end
end GD.N0232.N0720.N1326

namespace GD.N0232.N0720.N1330

noncomputable section

open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1329 _root_.GD.N0232.N0720.N1314
open _root_.GD.N0232.N0720.N1315 _root_.GD.N0232.N0720.N1326
open _root_.GD.N0232.N0720.N1342 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1377 _root_.GD.N0107
open _root_.GD.N0238.N0753
open _root_.GD.N0230.N0556

open _root_.GD.N0096.N0344

variable (m n k : ℕ) (hdim : m + n = k + 1)

theorem d030500 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {δ : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030491 m n δ) :
    ∃ (g : ℝ × ℝ → ℝ) (h : _root_.GD.N0232.N0720.N1341.d004417 k), Measurable g ∧
      (∀ p, g p ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        δ =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ]
          _root_.GD.N0232.N0720.N1425.d014719 m n g) ∧
      _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1314.d019711 m n k hdim) h ∧
      _root_.GD.N0232.N0720.N1341.d004418 h =ᵐ[(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k))]
        _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g := by
  obtain ⟨g, hg, hb, hae⟩ := _root_.GD.N0232.N0720.N1342.d030496 m n hm hn hd
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  let f := _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g
  have hf : Measurable f := _root_.GD.N0232.N0720.N1329.d019672 m n k hdim hg
  have hhom : _root_.GD.N0238.N0753.d004397 f :=
    _root_.GD.N0232.N0720.N1329.d019675 m n k hdim hm0 hn0 g
  have hbound : ∀ u : _root_.GD.N0232.N0720.N1341.d004415 k, ‖f u‖ ≤ 1 :=
    _root_.GD.N0232.N0720.N1329.d019679 m n k hdim hm0 hn0 hb
  have hrep : ∀ θ : _root_.GD.N0232.N0720.N1326.d019882,
      f ∘ _root_.GD.N0232.N0720.N1329.d019648 m n k hdim =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] δ := by
    intro θ
    simpa only [Function.comp_def, f, _root_.GD.N0232.N0720.N1329.d019673] using (hae θ).symm
  refine ⟨g, _root_.GD.N0232.N0720.N1326.d019889 f hf 1 hbound, hg, hb, hae, ?_, ?_⟩
  · exact _root_.GD.N0232.N0720.N1326.d030499 m n k hdim hd f hf hhom 1 hbound hrep
  · exact _root_.GD.N0232.N0720.N1326.d019891 f hf hhom 1 hbound

theorem d030501 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {δ : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030491 m n δ) :
    ∃ (g : ℝ × ℝ → ℝ) (ell : ℕ → ℕ)
      (p : ∀ j, Option (Fin (ell j)) → _root_.GD.N0232.N0720.N1315.d019832)
      (a : ∀ j, Option (Fin (ell j)) → ℝ) (ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1315.d019832),
      Measurable g ∧ (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        δ =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ]
          _root_.GD.N0232.N0720.N1425.d014719 m n g) ∧
      (∀ j i, 0 ≤ a j i) ∧ (∀ j, ∑ i, a j i = 1) ∧
      (∀ j, (ν j : Measure _root_.GD.N0232.N0720.N1315.d019832) =
        ∑ i, ENNReal.ofReal (a j i) • Measure.dirac (p j i)) ∧
      (∀ j i, (p j i).2.1 ∈ Ioo (0 : ℝ) 1) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)),
        Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1330.d020037 hdim (ν j : Measure _root_.GD.N0232.N0720.N1315.d019832) x) atTop
          (𝓝 (_root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x))) ∧
      (∀ x : _root_.GD.N0232.N0720.N1341.d004414 k, _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x ∈
        Icc (min (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 0) (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 1))
          (max (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 0) (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x 1))) := by
  obtain ⟨g, h, hg, hb, hrep, hadm, hcoordinate⟩ :=
    _root_.GD.N0232.N0720.N1330.d030500 m n k hdim hm hn hd
  obtain ⟨w, ns, hw, _hns, hlim⟩ := _root_.GD.N0232.N0720.N1314.d019732 hdim h hadm
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  let q : ∀ j, Option (Fin (ns j)) → _root_.GD.N0232.N0720.N1329.d019646 :=
    fun j ↦ _root_.GD.N0232.N0720.N1315.d019879 (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1314.d019725 i)
  let v : ∀ j, Option (Fin (ns j)) → ℝ := fun j ↦ _root_.GD.N0232.N0720.N1314.d019720 (w (ns j))
  have hv : ∀ j i, 0 ≤ v j i := fun j ↦ _root_.GD.N0232.N0720.N1314.d019721 _ (hw (ns j))
  have hp : ∀ j, ∃ i, 0 < v j i := fun j ↦ _root_.GD.N0232.N0720.N1314.d019722 _
  let ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1315.d019832 :=
    fun j ↦ _root_.GD.N0232.N0720.N1315.d019873 hdim hm0 hn0 (q j) (v j) (hv j) (hp j)
  have hlim' : ∀ᵐ u : _root_.GD.N0232.N0720.N1341.d004415 k ∂_root_.GD.N0232.N0720.N1341.d004416 k,
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1330.d020032 (fun i ↦ _root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q j i)) (v j) u)
        atTop (𝓝 (h u)) := by
    simpa only [q, v, _root_.GD.N0232.N0720.N1330.d020033, _root_.GD.N0232.N0720.N1315.d019880] using hlim
  have hraw := _root_.GD.N0232.N0720.N1330.d020026
    (fun j ↦ _root_.GD.N0232.N0720.N1330.d020032 (fun i ↦ _root_.GD.N0232.N0720.N1329.d019660 m n k hdim (q j i)) (v j))
    (fun j ↦ _root_.GD.N0232.N0720.N1330.d020036 _ (v j)) h hlim'
  refine ⟨g, ns, (fun j i ↦ _root_.GD.N0232.N0720.N1315.d019847 m n hm0 hn0 (q j i)),
    (fun j ↦ _root_.GD.N0232.N0720.N1315.d019870 hdim (q j) (v j)), ν, hg, hb, hrep,
    (fun j i ↦ _root_.GD.N0232.N0720.N1315.d019871 hdim hm0 hn0 (q j) (v j) (hv j) (hp j) i),
    (fun j ↦ _root_.GD.N0232.N0720.N1315.d019872 hdim hm0 hn0 (q j) (v j) (hv j) (hp j)),
    (fun _ ↦ rfl), (fun j i ↦ _root_.GD.N0232.N0720.N1315.d019841 hm0 hn0 (q j i)), ?_, ?_⟩
  · filter_upwards [hraw, hcoordinate] with x hx heq
    simp only [ν, _root_.GD.N0232.N0720.N1330.d020038]
    rwa [heq] at hx
  · exact _root_.GD.N0232.N0720.N1330.d020039 m n k hdim hb

end
end GD.N0232.N0720.N1330

namespace GD.N0232.N0720.N1321

noncomputable section

open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1329
open _root_.GD.N0232.N0720.N1315 _root_.GD.N0232.N0720.N1331
open _root_.GD.N0232.N0720.N1324 _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1376 _root_.GD.N0232.N0720.N1297

open _root_.GD.N0096.N0344



theorem d030502
    (m n d : ℕ) (hdim : m + n = d + 1) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {δ : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030491 m n δ) :
    ∃ (g : ℝ × ℝ → ℝ) (ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1315.d019832),
      Measurable g ∧ (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        δ =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ]
          _root_.GD.N0232.N0720.N1425.d014719 m n g) ∧
      (∀ beta : ℝ, 0 < beta → beta < 1 / 2 → ∃ B : ℝ, _root_.GD.N0232.N0720.N1297.d002706 ν beta B) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
        Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1330.d020037 hdim
          (ν j : Measure _root_.GD.N0232.N0720.N1315.d019832) x) atTop
            (𝓝 (_root_.GD.N0232.N0720.N1329.d019671 m n d hdim g x))) := by
  obtain ⟨g, ell, p, _root_.GD.N0232.N0719.N0900.d009108, ν, hg, hb, hrep, hw, hprob, hν, _hinterior, hlim, hbetween⟩ :=
    _root_.GD.N0232.N0720.N1330.d030501
      m n d hdim hm hn hd
  refine ⟨g, ν, hg, hb, hrep, ?_, hlim⟩
  intro beta hbeta hhalf
  have hlim' : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1321.d020059 d (p j) (_root_.GD.N0232.N0719.N0900.d009108 j) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x)) atTop
        (𝓝 (_root_.GD.N0232.N0720.N1329.d019671 m n d hdim g x)) := by
    simpa only [hν, _root_.GD.N0232.N0720.N1321.d020078 _ _ _ (hw _)] using hlim
  obtain ⟨B, hB⟩ := _root_.GD.N0232.N0720.N1321.d020075 hdim hm hn p _root_.GD.N0232.N0719.N0900.d009108 hw hprob
    (_root_.GD.N0232.N0720.N1329.d019671 m n d hdim g) hlim' hbetween hbeta.le hhalf
  refine ⟨B, ?_⟩
  intro j
  constructor
  · rw [hν]
    exact _root_.GD.N0232.N0720.N1321.d020076 (p j) (_root_.GD.N0232.N0719.N0900.d009108 j) (_root_.GD.N0232.N0720.N1297.d002703 beta)
  · rw [hν, _root_.GD.N0232.N0720.N1321.d020077 (p j) (_root_.GD.N0232.N0719.N0900.d009108 j) (hw j)]
    exact hB j

end
end GD.N0232.N0720.N1321

namespace GD.N0232.N0720.N1343

noncomputable section

open _root_.GD.N0232.N0720.N1315 _root_.GD.N0232.N0720.N1323
open _root_.GD.N0232.N0720.N1382 _root_.GD.N0232.N0720.N1297
open _root_.GD.N0232.N0720.N1394

open _root_.GD.N0096.N0344



theorem d030503
    (m n d : ℕ) (hdim : m + n = d + 1) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {δ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030491 m n δ) :
    ∃ (g : ℝ × ℝ → ℝ) (μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1343.d020318),
      Measurable g ∧ (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        δ =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ]
          _root_.GD.N0232.N0720.N1425.d014719 m n g) ∧
      _root_.GD.N0232.N0720.N1382.d004657 (μ : Measure _root_.GD.N0232.N0720.N1343.d020318) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
        _root_.GD.N0232.N0720.N1315.d019850 m n d hdim x ∈ _root_.GD.N0232.N0720.N1382.d004652 →
        _root_.GD.N0232.N0720.N1343.d020320 d (μ : Measure _root_.GD.N0232.N0720.N1343.d020318)
            (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x) =
          _root_.GD.N0232.N0720.N1329.d019671 m n d hdim g x) := by
  obtain ⟨g, ν, hg, hb, hrep, hmoment, hraw⟩ :=
    _root_.GD.N0232.N0720.N1321.d030502
      m n d hdim hm hn hd
  have hraw' : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 d)),
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1343.d020320 d (ν j : Measure _root_.GD.N0232.N0720.N1343.d020318)
        (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x))
        atTop (𝓝 (_root_.GD.N0232.N0720.N1329.d019671 m n d hdim g x)) := by
    exact hraw
  obtain ⟨μ, hμ, hpost⟩ := _root_.GD.N0232.N0720.N1343.d020325 d volume
    (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim)
    (_root_.GD.N0232.N0720.N1329.d019671 m n d hdim g) ν hmoment hraw'
  exact ⟨g, μ, hg, hb, hrep, hμ, hpost⟩

end
end GD.N0232.N0720.N1343

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

open _root_.GD.N0096.N0344

variable (m n : ℕ)

theorem d030504 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030491 m n d)
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

theorem d030505 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030491 m n d)
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
  have h := (_root_.GD.N0232.N0720.N1327.d030504 m n hm hn hd hg hb hrep mu hpost theta).symm
  simpa only [Function.comp_def, _root_.GD.N0232.N0720.N1329.d019673] using h

theorem d030506 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030491 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1425.d014719 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun z ↦ _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n z) mu) :
    ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1327.d020582 k)), x ∈ _root_.GD.N0232.N0720.N1322.d020080 hdim →
      _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x =
        _root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu ∘ _root_.GD.N0232.N0720.N1351.d002814)
          (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) := by
  filter_upwards [_root_.GD.N0232.N0720.N1327.d030505 m n k hdim hm hn hd hg hb hrep mu hpost]
    with x hx
  intro hphysical
  exact hx.trans (_root_.GD.N0232.N0720.N1327.d020611 m n k hdim hm hn hphysical mu)

theorem d030507 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030491 m n d)
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
  filter_upwards [_root_.GD.N0232.N0720.N1327.d030506 m n k hdim hm hn hd hg hb hrep mu hpost]
    with x hx hphysical
  exact (hx hphysical).symm

end
end GD.N0232.N0720.N1327

namespace GD.N0232.N0720.N1325

noncomputable section

open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1336 _root_.GD.N0232.N0720.N1329
open _root_.GD.N0232.N0720.N1315 (d019850)
open _root_.GD.N0232.N0720.N1327
open _root_.GD.N0232.N0720.N1322 (d020080)
open _root_.GD.N0232.N0720.N1323 _root_.GD.N0232.N0720.N1343
open _root_.GD.N0232.N0720.N1382 (d004652)
open _root_.GD.N0232.N0720.N1270 (d020238)

open _root_.GD.N0096.N0344



theorem d030508 (m n k : ℕ) (hdim : m + n = k + 1)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030491 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1425.d014719 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] d)
    (μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1325.d020614)
    (hpost : g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x ↦ _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n)
      (_root_.GD.N0232.N0720.N1336.d013420 m n x) (μ : Measure _root_.GD.N0232.N0720.N1325.d020614)) :
    Nonempty (_root_.GD.N0232.N0720.N1270.d020238 (m + n + 2)
      (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) (μ : Measure _root_.GD.N0232.N0720.N1325.d020614))) := by
  obtain ⟨gs, ν, hgs, _hbs, hrep_s, hν, hscale⟩ :=
    _root_.GD.N0232.N0720.N1343.d030503
      m n k hdim hm hn hd
  have hcommon := _root_.GD.N0232.N0720.N1327.d020596 m n k hdim hgs hg
    (fun θ ↦ (hrep_s θ).symm) hrep
  have hae : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k)),
      x ∈ _root_.GD.N0232.N0720.N1322.d020080 hdim →
      _root_.GD.N0232.N0720.N1323.d020304 (m + n) (ν : Measure _root_.GD.N0232.N0720.N1325.d020615) (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) /
          _root_.GD.N0232.N0720.N1323.d020303 (m + n) (ν : Measure _root_.GD.N0232.N0720.N1325.d020615) (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) =
        _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x := by
    filter_upwards [hscale, hcommon] with x hs hc
    intro hx
    rw [hdim, ← _root_.GD.N0232.N0720.N1343.d020323]
    exact (hs hx).trans hc
  have hcontinuous : ContinuousOn (fun x : _root_.GD.N0232.N0720.N1325.d020616 ↦
      _root_.GD.N0232.N0720.N1323.d020304 (m + n) (ν : Measure _root_.GD.N0232.N0720.N1325.d020615) x /
        _root_.GD.N0232.N0720.N1323.d020303 (m + n) (ν : Measure _root_.GD.N0232.N0720.N1325.d020615) x) _root_.GD.N0232.N0720.N1382.d004652 :=
    (_root_.GD.N0232.N0720.N1323.d020306 (m + n) _ hν).continuousOn.div
      (_root_.GD.N0232.N0720.N1323.d020305 (m + n) _ hν).continuousOn
      (fun x hx ↦ (_root_.GD.N0232.N0720.N1323.d020307 (m + n) _ hν hx).ne')
  have heq := _root_.GD.N0232.N0720.N1327.d030507 m n k hdim hm hn hd hg hb hrep
    (μ : Measure _root_.GD.N0232.N0720.N1325.d020614) hpost hcontinuous hae
  exact ⟨_root_.GD.N0232.N0720.N1323.d020317 (m + n) ν hν (fun x hx ↦ heq hx)⟩

end
end GD.N0232.N0720.N1325


namespace GD.N0096.N0344

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080

def d030509 (m n : ℕ) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  _root_.GD.N0096.N0344.d030491 m n d ∧
    ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014175 m n)

end GD.N0096.N0344

namespace GD.N0232.N0720.N1332

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1287 _root_.GD.N0232.N0720.N1396
open _root_.GD.N0232.N0720.N1424 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1434 _root_.GD.N0232.N0720.N1423
open _root_.GD.N0232.N0720.N1091 _root_.GD.N0232.N0720.N1218
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1399 (d020100 d020102
  d020101 d020103)

open _root_.GD.N0096.N0344

theorem d030510
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030509 m n d) {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 ≤ _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 t.1 := by
  have h := hd.2 (_root_.GD.N0232.N0720.N1332.d020110 m n hm hn t)
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n _ (hrep _),
    _root_.GD.N0232.N0720.N1332.d020109 m n hm hn _ hg hb,
    _root_.GD.N0232.N0720.N1080.d014199 m n hm hn,
    _root_.GD.N0232.N0720.N1287.d019529 m n hm hn] at h
  change ENNReal.ofReal (_ + _ * _root_.GD.N0232.N0720.N1332.d020106 m n g _) ≤
    ENNReal.ofReal (_ + _ * _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 _) at h
  rw [_root_.GD.N0232.N0720.N1332.d020111, _root_.GD.N0232.N0720.N1332.d020112, one_mul] at h
  simp only [one_mul] at h
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _))
      (_root_.GD.N0232.N0720.N1332.d020107 _ _ _ _))).mp h
  dsimp only [_root_.GD.N0141.d006684] at hreal
  linarith

theorem d030511
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030509 m n d) {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    {a : ℝ} (ha : 0 < a) : ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, a ≤ g x) := by
  intro hfloor
  have hloss : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020100 k).1)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (_root_.GD.N0232.N0720.N1332.d020115 hm hn _root_.GD.N0232.N0720.N1399.d020101)
      (fun k ↦ _root_.GD.N0232.N0720.N1332.d020107 _ _ _ _)
      (fun k ↦ _root_.GD.N0232.N0720.N1332.d030510 hm hn hd hg hb hrep _)
  have hsmall := hloss.eventually_lt_const (sq_pos_of_pos (half_pos ha))
  have hfrac := _root_.GD.N0232.N0720.N1399.d020101.eventually_lt_const (half_pos ha)
  obtain ⟨k, hk, ht⟩ := (hsmall.and hfrac).exists
  have hbound := _root_.GD.N0232.N0720.N1332.d020117 hm hn hg hb (_root_.GD.N0232.N0720.N1399.d020100 k)
    (a := a) (by linarith) hfloor
  have hgap : a / 2 < a - (_root_.GD.N0232.N0720.N1399.d020100 k).1 := by linarith
  have hsquare := (sq_lt_sq₀ (half_pos ha).le (by linarith)).2 hgap
  linarith

theorem d030512
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030509 m n d) {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    {b : ℝ} (hbone : b < 1) : ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x ≤ b) := by
  intro hceiling
  have hgap : 0 < (1 - b) / 2 := half_pos (sub_pos.mpr hbone)
  have hloss : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020102 k).1)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (_root_.GD.N0232.N0720.N1332.d020116 hm hn _root_.GD.N0232.N0720.N1399.d020103)
      (fun k ↦ _root_.GD.N0232.N0720.N1332.d020107 _ _ _ _)
      (fun k ↦ _root_.GD.N0232.N0720.N1332.d030510 hm hn hd hg hb hrep _)
  have hsmall := hloss.eventually_lt_const (sq_pos_of_pos hgap)
  have hfrac := _root_.GD.N0232.N0720.N1399.d020103.eventually_const_lt
    (show (1 + b) / 2 < 1 by linarith)
  obtain ⟨k, hk, ht⟩ := (hsmall.and hfrac).exists
  have hbound := _root_.GD.N0232.N0720.N1332.d020118 hm hn hg hb (_root_.GD.N0232.N0720.N1399.d020102 k)
    (b := b) (by linarith) hceiling
  have hsquare := (sq_lt_sq₀ hgap.le
    (show 0 ≤ (_root_.GD.N0232.N0720.N1399.d020102 k).1 - b by linarith)).2
    (show (1 - b) / 2 < (_root_.GD.N0232.N0720.N1399.d020102 k).1 - b by linarith)
  linarith

end
end GD.N0232.N0720.N1332

namespace GD.N0232.N0720.N1334

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1332
open _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1344 _root_.GD.N0232.N0720.N1340
open _root_.GD.N0232.N0720.N1414 (d004212)

open _root_.GD.N0096.N0344

theorem d030513
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030509 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    {mu : Measure _root_.GD.N0232.N0720.N1290.d004131} [IsProbabilityMeasure mu]
    {center r : ℝ} (hr : 0 ≤ r)
    (hclass : Measure.map (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ)) mu = _root_.GD.N0232.N0720.N1344.d013339 q hq center r)
    (P : _root_.GD.N0232.N0720.N1436.d013217 → _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, Continuous (P x) ∧ ∀ t, 0 < P x t)
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x = _root_.GD.N0232.N0720.N1290.d004140 q (P x) mu) :
    center = 1 / 2 ∧ r = 1 / 2 := by
  have hin := _root_.GD.N0232.N0720.N1340.d013353 q hq hclass
  have hcoeff := _root_.GD.N0232.N0720.N1334.d020121 q hq hr hclass P hP hpost
  have hleft : center - r ≤ 0 := by
    by_contra! hpos
    exact _root_.GD.N0232.N0720.N1332.d030511 hm hn hd hg hb hrep hpos
      (hcoeff.mono fun _ hx ↦ hx.1)
  have hright : 1 ≤ center + r := by
    by_contra! hlt
    exact _root_.GD.N0232.N0720.N1332.d030512 hm hn hd hg hb hrep hlt
      (hcoeff.mono fun _ hx ↦ hx.2)
  constructor <;> linarith [hin.1, hin.2]

theorem d030514
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030509 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hF : ∀ᶠ epsilon in nhds 0,
      _root_.GD.N0232.N0720.N1290.d004143 q (_root_.GD.N0232.N0720.N1290.d004147 (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) epsilon) mu = 0)
    (P : _root_.GD.N0232.N0720.N1436.d013217 → _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, Continuous (P x) ∧ ∀ t, 0 < P x t)
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x = _root_.GD.N0232.N0720.N1290.d004140 q (P x) mu) :
    Measure.map (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ)) mu = _root_.GD.N0232.N0720.N1344.d013339 q hq (1 / 2) (1 / 2) := by
  have hclass := _root_.GD.N0232.N0720.N1344.d013344 q hq mu hF
  have hr : 0 ≤ _root_.GD.N0232.N0720.N1344.d013342 q hq 0 1 mu := Real.sqrt_nonneg _
  obtain ⟨hc, hradius⟩ := _root_.GD.N0232.N0720.N1334.d030513 q hq hm hn
    hd hg hb hrep hr hclass P hP hpost
  simpa only [hc, hradius] using hclass

end
end GD.N0232.N0720.N1334

namespace GD.N0232.N0720.N1333

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1332 _root_.GD.N0232.N0720.N1328
open _root_.GD.N0232.N0720.N1287 _root_.GD.N0232.N0720.N1396
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1424
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141

open _root_.GD.N0096.N0344

theorem d030515
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hdesign : m ≠ 2 ∨ n ≠ 2)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030509 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g) :
    ¬ (g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n]
      fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) := by
  intro heq
  obtain ⟨sigma, tau, hs, ht, hgap⟩ := _root_.GD.N0232.N0720.N1328.d014770 hm hn hdesign 0
  let theta : _root_.GD.N0232.N0720.N1080.d014168 := ⟨0, sigma, tau, hs, ht⟩
  have hroot_meas : Measurable (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦
      _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) :=
    (_root_.GD.N0232.N0720.N1328.d014757 _ _).comp measurable_fst
  have hroot_bound (x : _root_.GD.N0232.N0720.N1436.d013217) :
      _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 ∈ Icc (0 : ℝ) 1 :=
    _root_.GD.N0232.N0720.N1328.d014758 (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn) x.1
  have hrisk := _root_.GD.N0232.N0720.N1333.d020201 hm hn hg hroot_meas hb hroot_bound heq theta
  have hmem := _root_.GD.N0232.N0720.N1287.d019517 m n hm hn theta
    (fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1)
    hroot_meas hroot_bound
  have hstrict := hd.2 theta
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n theta (hrep theta), hrisk,
    _root_.GD.N0232.N0720.N1396.d014785 m n theta hmem,
    _root_.GD.N0232.N0720.N1396.d014785 m n theta (_root_.GD.N0232.N0720.N1080.d014177 m n hm hn theta)]
      at hstrict
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg (fun _ ↦ sq_nonneg _))).mp hstrict
  exact (not_lt_of_ge hreal) hgap

theorem d030516
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030509 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g) :
    ¬ (g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n]
      fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) := by
  by_cases hdesign : m = 2 ∧ n = 2
  · rcases hdesign with ⟨rfl, rfl⟩
    intro heq
    have hroot : (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦
        _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 2) (_root_.GD.N0232.N0720.N1436.d013208 2) x.1) =
        fun x ↦ _root_.GD.N0232.N0720.N1404.d020183 x.1 := by
      funext x
      simpa only [_root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, Nat.reduceSub, Nat.cast_one] using
        _root_.GD.N0232.N0720.N1333.d020203 x.1
    rw [hroot] at heq
    have hloss := _root_.GD.N0232.N0720.N1332.d020108 hm hn heq
      _root_.GD.N0232.N0720.N1404.d020198
    have hcap := _root_.GD.N0232.N0720.N1332.d030510 hm hn hd hg hb hrep
      _root_.GD.N0232.N0720.N1404.d020198
    rw [hloss] at hcap
    exact (not_lt_of_ge hcap) _root_.GD.N0232.N0720.N1404.d020199
  · exact _root_.GD.N0232.N0720.N1333.d030515 hm hn (by tauto) hd hg hb hrep

end
end GD.N0232.N0720.N1333

namespace GD.N0232.N0720.N1345

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1334 _root_.GD.N0232.N0720.N1339
open _root_.GD.N0232.N0720.N1344 _root_.GD.N0232.N0720.N1336
open _root_.GD.N0232.N0720.N1328 _root_.GD.N0232.N0720.N1333
open _root_.GD.N0232.N0720.N1357 _root_.GD.N0232.N0720.N1368
open _root_.GD.N0232.N0720.N1414 (d004212)

open _root_.GD.N0096.N0344

theorem d030517
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030509 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x = _root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu) :
    ¬ (∀ᶠ epsilon in nhds 0,
      _root_.GD.N0232.N0720.N1290.d004143 q (_root_.GD.N0232.N0720.N1290.d004147 (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) epsilon) mu = 0) := by
  intro hF
  have hdomain : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, x ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
    _root_.GD.N0232.N0720.N1458.d018947 m n (1 / 2)
  have hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      Continuous (_root_.GD.N0232.N0720.N1336.d013420 m n x) ∧ ∀ t, 0 < _root_.GD.N0232.N0720.N1336.d013420 m n x t := by
    filter_upwards [hdomain] with x hx
    exact ⟨(_root_.GD.N0232.N0720.N1336.d013421 m n).comp (continuous_const.prodMk continuous_id),
      _root_.GD.N0232.N0720.N1336.d013423 m n hm hn hx⟩
  have hclass := _root_.GD.N0232.N0720.N1334.d030514 q hq hm hn
    hd hg hb hrep mu hF (_root_.GD.N0232.N0720.N1336.d013420 m n) hP hpost
  apply _root_.GD.N0232.N0720.N1333.d030516 hm hn hd hg hb hrep
  filter_upwards [hdomain, hpost] with x hx heq
  exact heq.trans (_root_.GD.N0232.N0720.N1345.d020328 q hq hm hn mu hclass hx)

theorem d030518
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030509 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x = _root_.GD.N0232.N0720.N1290.d004140 q (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu) :
    ∃ z w : ℝ, 0 < z ∧ 0 < w ∧
      _root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 q mu) z w 0 ≠ 0 := by
  by_contra hnone
  have hzero : ∀ z w : ℝ, 0 < z → 0 < w →
      _root_.GD.N0232.N0720.N1368.d020210 (_root_.GD.N0232.N0720.N1368.d020209 q mu) z w 0 = 0 := by
    intro z w hz hw
    by_contra hne
    exact hnone ⟨z, w, hz, hw, hne⟩
  apply _root_.GD.N0232.N0720.N1345.d030517 q hq hm hn hd hg hb hrep mu hpost
  exact _root_.GD.N0232.N0720.N1368.d020221
    q (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) mu hzero

end
end GD.N0232.N0720.N1345

namespace GD.N0232.N0720.N1317

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1345 _root_.GD.N0232.N0720.N1336
open _root_.GD.N0232.N0720.N1368 _root_.GD.N0232.N0720.N1352
open _root_.GD.N0232.N0720.N1351 _root_.GD.N0232.N0720.N1292
open _root_.GD.N0232.N0720.N1270 (d020224 d020225 d020226 d020227
  d020228 d020229 d020234
  d020238)
open _root_.GD.N0232.N0720.N1264 (d020252 d020244)
open _root_.GD.N0232.N0720.N1308

open _root_.GD.N0096.N0344

theorem d030519
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0096.N0344.d030509 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      g x = _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu)
    (m1 : _root_.GD.N0232.N0720.N1270.d020238 (m + n + 2) (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu)) : False := by
  have hqeq : (((m + n + 1 : ℕ) : ℝ) / 2) = _root_.GD.N0232.N0720.N1436.d013210 m n := by
    rw [_root_.GD.N0232.N0720.N1336.d013424 m n hm hn]
    simp only [Nat.cast_add, Nat.cast_one]
  have hq : (3 / 2 : ℝ) ≤ ((m + n + 1 : ℕ) : ℝ) / 2 := by
    have hD : (3 : ℝ) ≤ ((m + n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 3 ≤ m + n + 1 by omega)
    linarith
  have hpost' : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n,
      g x = _root_.GD.N0232.N0720.N1290.d004140 (((m + n + 1 : ℕ) : ℝ) / 2) (_root_.GD.N0232.N0720.N1336.d013420 m n x) mu := by
    simpa only [hqeq] using hpost
  obtain ⟨z, w, hz, hw, hF⟩ :=
    _root_.GD.N0232.N0720.N1345.d030518
      _ hq hm hn hd hg hb hrep mu hpost'
  let m0 := _root_.GD.N0232.N0720.N1308.d020292 (m + n + 1) mu
  let H : _root_.GD.N0232.N0720.N1352.d002739 → ℝ := fun x ↦ m1.M x / m0.M x
  have hHinf : ContDiffOn ℝ ∞ H _root_.GD.N0232.N0720.N1270.d020224 :=
    m1.smooth_M.fun_div m0.smooth_M (fun x hx ↦ (m0.positive_M x hx).ne')
  have hH : ContDiffOn ℝ 2 H _root_.GD.N0232.N0720.N1270.d020224 := (contDiffOn_infty.mp hHinf) 2
  have hx := _root_.GD.N0232.N0720.N1270.d020227 hw hz
  apply _root_.GD.N0232.N0720.N1318.d002811
    (m + n + 1) _root_.GD.N0232.N0720.N1270.d020225 (_root_.GD.N0232.N0720.N1317.d020332 (m + n + 1) mu)
    hH m0.smooth_M m1.smooth_M
    (fun x hx ↦ (m0.positive_M x hx).ne')
    (fun x hx ↦ (div_mul_cancel₀ (m1.M x) (m0.positive_M x hx).ne').symm)
    m0.numerator m1.numerator m0.pde m1.pde hx (_root_.GD.N0232.N0720.N1270.d020228 w z)
  · rw [_root_.GD.N0232.N0720.N1317.d020333 _ _ hz hw]
    exact neg_ne_zero.mpr hF
  · exact (m1.positive_M _ hx).ne'
  · filter_upwards [isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Ioi 0 by norm_num)] with r hr
    exact ⟨m0.homogeneous _ hx r hr, m1.homogeneous _ hx r hr⟩

end
end GD.N0232.N0720.N1317

namespace GD.N0096.N0344

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1303 _root_.GD.N0232.N0720.N1325
open _root_.GD.N0232.N0720.N1317

theorem d030520 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ ∃ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, _root_.GD.N0096.N0344.d030509 m n d := by
  rintro ⟨d, hd⟩
  obtain ⟨g, μ, hg, hb, hrep, hpost⟩ :=
    _root_.GD.N0232.N0720.N1303.d030498 m n hm hn hd.1
  let k := m + n - 1
  have hdim : m + n = k + 1 := by dsimp [k]; omega
  obtain ⟨m1⟩ := _root_.GD.N0232.N0720.N1325.d030508 m n k hdim hm hn hd.1 hg hb hrep μ hpost
  let prior : Measure _root_.GD.N0232.N0720.N1290.d004131 := μ
  have hpostPointwise : ∀ᵐ x ∂ _root_.GD.N0232.N0720.N1441.d013679 m n,
      g x = _root_.GD.N0232.N0720.N1290.d004140
        (_root_.GD.N0232.N0720.N1436.d013210 m n)
        (_root_.GD.N0232.N0720.N1336.d013420 m n x) prior := by
    filter_upwards [hpost] with x hx
    exact hx
  apply _root_.GD.N0232.N0720.N1317.d030519 hm hn hd hg hb
    (fun θ ↦ (hrep θ).symm) prior hpostPointwise m1

end GD.N0096.N0344

#print axioms _root_.GD.N0096.N0344.d030520

namespace GD.N0096.N0344

noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1226
open _root_.GD.N0046.N0305
open _root_.GD.N0096.N0340

theorem d030521
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hne : (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty) :
    ¬ (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton := by
  intro hsub
  obtain ⟨p, hp⟩ := hne
  have hterminal := _root_.GD.N0096.N0340.d030238 m n hm hn hp hsub
  obtain ⟨d, hdMeas, hdAE, hdEquiv⟩ :=
    _root_.GD.N0096.N0340.d030239 m n hm hn hp hsub
  have hdRisk (θ : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n θ d = _root_.GD.N0232.N0720.N1080.d014182 m n θ p := by
    rw [_root_.GD.N0232.N0720.N1159.d014662 m n θ (hdAE θ), _root_.GD.N0232.N0720.N1215.d014286]
  apply _root_.GD.N0096.N0344.d030520 m n hm hn
  refine ⟨d, ⟨hdMeas, hdEquiv, ?_, ?_⟩, ?_⟩
  · intro θ
    rw [hdRisk]
    exact _root_.GD.N0046.N0305.d030204 m n hp θ
  · intro e he hbelow θ
    have heBelow : ∀ η : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n η e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n η (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
      intro η
      rw [_root_.GD.N0232.N0720.N1215.d014286, ← hdRisk]
      exact hbelow η
    exact (_root_.GD.N0232.N0720.N1226.d015581 m n p hterminal e he heBelow θ).trans
      (hdAE θ).symm
  · intro θ
    rw [hdRisk, _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
    exact (hp θ).2

theorem d030522
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty ↔
      ¬ (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton := by
  classical
  constructor
  · exact _root_.GD.N0096.N0344.d030521 m n hm hn
  · intro hnot
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hnot
    rw [hempty]
    exact Set.subsingleton_empty

theorem d030523
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (_root_.GD.N0046.N0305.d030212 m n hm hn).Nonempty ↔ (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty := by
  rw [_root_.GD.N0096.N0340.d030233 m n hm hn,
    _root_.GD.N0096.N0344.d030522 m n hm hn]

theorem d030524
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1226.d015578 m n ↔ (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty := by
  rw [_root_.GD.N0046.N0305.d030214 m n hm hn,
    _root_.GD.N0096.N0344.d030523 m n hm hn]

end
end GD.N0096.N0344

#print axioms _root_.GD.N0096.N0344.d030521
#print axioms _root_.GD.N0096.N0344.d030522
#print axioms _root_.GD.N0096.N0344.d030523
#print axioms _root_.GD.N0096.N0344.d030524
