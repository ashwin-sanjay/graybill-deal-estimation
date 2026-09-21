import GD.Module1276
import GD.Module0983
import GD.Module1743

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators ContDiff

namespace GD.N0232.N0720.N1159

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0719.N0946

 def d028959 (m n : ℕ) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  Measurable d ∧
    _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) => g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) => g • y) d ∧
    (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
    (∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n theta e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n theta d) →
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d)

theorem d028960 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (hd.2.2.1 theta)
  rw [_root_.GD.N0232.N0720.N1080.d014199 m n hm hn, _root_.GD.N0232.N0720.N1080.d014184]
  exact ENNReal.ofReal_ne_top

end
end GD.N0232.N0720.N1159

namespace GD.N0232.N0720.N1295

noncomputable section

open MeasureTheory Filter
open scoped BigOperators
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1506 _root_.GD.N0232.N0720.N1446
open _root_.GD.N0137 _root_.GD.N0107
variable (m n : ℕ)

theorem d028961 (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d) :
    ∃ hmem : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) (hmem.toLp d) ∧
        _root_.GD.N0232.N0720.N1159.d014638 m n (hmem.toLp d) := by
  obtain ⟨hmeas, hcov, hstrict, hterminal⟩ := hd
  have hmem : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n d hmeas
      (_root_.GD.N0232.N0720.N1159.d028960 m n hm hn ⟨hmeas, hcov, hstrict, hterminal⟩ _root_.GD.N0232.N0720.N1080.d014169)
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

open MeasureTheory Set
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
variable (m n : ℕ)

theorem d028962
    {d e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d)
    (he : Measurable e)
    (hecov : _root_.GD.N0230.N0644.d000297
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) ↦
        g • omega)
      (fun (g : _root_.GD.N0232.N0719.N0946.d009229) (y : ℝ) ↦ g • y) e)
    (hae : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d) :
    _root_.GD.N0232.N0720.N1159.d028959 m n e := by
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

theorem d028963
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d) :
    ∃ q : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable q ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168, (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d) ∧
      _root_.GD.N0232.N0719.N0860.d011447 q ∧
      _root_.GD.N0232.N0720.N1209.d012478 q ∧
      _root_.GD.N0232.N0720.N1159.d028959 m n (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) := by
  obtain ⟨hmem, hterminal, hcharacter⟩ := _root_.GD.N0232.N0720.N1295.d028961 m n hm hn hd
  have hfinite : _root_.GD.N0232.N0720.N1159.d014637 m n (hmem.toLp d) := by
    intro theta
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n theta d hmem]
    exact _root_.GD.N0232.N0720.N1159.d028960 m n hm hn hd theta
  let seed : _root_.GD.N0232.N0720.N1159.d014639 m n := ⟨hmem.toLp d, hfinite, hcharacter⟩
  obtain ⟨q, hq, hrep, haffine, hreflect⟩ :=
    _root_.GD.N0232.N0720.N1476.d019379
      m n hm hn seed hterminal
  have hae (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      (q ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d :=
    (hrep theta).trans
      ((_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_eq hmem.coeFn_toLp)
  refine ⟨q, hq, hae, haffine, hreflect, ?_⟩
  apply _root_.GD.N0232.N0720.N1342.d028962 m n hd
    (hq.comp (_root_.GD.N0232.N0720.N1501.d016289 m n))
  · intro g omega
    simp only [Function.comp_apply,
      _root_.GD.N0232.N0720.N1475.d018975 m n (by omega) (by omega), _root_.GD.N0232.N0719.N1010.d011416,
      _root_.GD.N0232.N0719.N0946.d009229.d009244]
    exact haffine g.shift g.d009239 g.d009240 (_root_.GD.N0232.N0720.N1467.d012542 m n omega)
  · exact hae

theorem d028964
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d) :
    ∃ g : ℝ × ℝ → ℝ, Measurable g ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g := by
  obtain ⟨q, hq, hae, haffine, hreflect, _hterminal⟩ :=
    _root_.GD.N0232.N0720.N1342.d028963 m n hm hn hd
  refine ⟨fun p ↦ _root_.GD.N0232.N0720.N1209.d012471 q p.1 p.2,
    _root_.GD.N0232.N0720.N1209.d012473 q hq, ?_⟩
  intro theta
  exact (hae theta).symm.trans
    (_root_.GD.N0232.N0720.N1342.d019639 m n hm hn q haffine hreflect theta)

theorem d028965
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d) :
    ∃ g : ℝ × ℝ → ℝ, Measurable g ∧
      (∀ p, g p ∈ Icc (0 : ℝ) 1) ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g := by
  obtain ⟨g, hg, hae⟩ := _root_.GD.N0232.N0720.N1342.d028964 m n hm hn hd
  have hclipMeas : Measurable (_root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0232.N0720.N1286.d019582 g)) :=
    _root_.GD.N0232.N0720.N1398.d019599 m n
      (_root_.GD.N0232.N0720.N1286.d019583 hg)
  have hdom (theta : _root_.GD.N0232.N0720.N1080.d014168) :
      _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n (_root_.GD.N0232.N0720.N1286.d019582 g)) ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
    have hrisk := _root_.GD.N0232.N0720.N1159.d014662 m n theta (hae theta)
    have hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≠ ⊤ := by
      rw [← hrisk]
      exact _root_.GD.N0232.N0720.N1159.d028960 m n hm hn hd theta
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

open MeasureTheory Set Filter
open scoped ENNReal Topology
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1342
open _root_.GD.N0232.N0720.N1337
open _root_.GD.N0232.N0720.N1287 _root_.GD.N0232.N0720.N1398
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0141
open _root_.GD.N0107 _root_.GD.N0137
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0556
variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

theorem d028966
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d) :
    ∃ (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (H : _root_.GD.N0232.N0720.N1441.d013681 m n),
      Measurable g ∧ (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧
      ((H : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] _root_.GD.N0232.N0720.N1441.d013686 g) ∧
      _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1337.d013826 m n hm hn) H ∧
      ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1425.d014719 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d := by
  obtain ⟨seed, hseed, hseedb, hrep⟩ :=
    _root_.GD.N0232.N0720.N1342.d028965 m n hm hn hd
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

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
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
variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
variable {I : Type*} [Fintype I]

include hm hn in
theorem d028967
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d) :
    ∃ (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1290.d004131),
      Measurable g ∧ (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1425.d014719 m n g
          =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] d) ∧
      (g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x ↦
        _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n x) (μ : Measure _root_.GD.N0232.N0720.N1290.d004131)) := by
  obtain ⟨g, H, hg, hb, hcenter, hadm, hrep⟩ :=
    _root_.GD.N0232.N0720.N1335.d028966 m n hm hn hd
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

open MeasureTheory Set
open scoped Topology ENNReal
open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1329 _root_.GD.N0232.N0720.N1342
open _root_.GD.N0107 _root_.GD.N0137
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0230.N0556
open _root_.GD.N0238.N0753
variable {k : ℕ}
variable (m n k : ℕ) (hdim : m + n = k + 1)

theorem d028968
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d)
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

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1329 _root_.GD.N0232.N0720.N1314
open _root_.GD.N0232.N0720.N1315 _root_.GD.N0232.N0720.N1326
open _root_.GD.N0232.N0720.N1342 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1377 _root_.GD.N0107
open _root_.GD.N0238.N0753
open _root_.GD.N0230.N0556
variable {k : ℕ}
variable {I : Type*} [Fintype I]
variable {m n : ℕ} (hdim : m + n = k + 1) (hm : 0 < m) (hn : 0 < n)
variable (m n k : ℕ) (hdim : m + n = k + 1)

theorem d028969 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {δ : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d028959 m n δ) :
    ∃ (g : ℝ × ℝ → ℝ) (h : _root_.GD.N0232.N0720.N1341.d004417 k), Measurable g ∧
      (∀ p, g p ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        δ =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ]
          _root_.GD.N0232.N0720.N1425.d014719 m n g) ∧
      _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1314.d019711 m n k hdim) h ∧
      _root_.GD.N0232.N0720.N1341.d004418 h =ᵐ[(volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 k))]
        _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g := by
  obtain ⟨g, hg, hb, hae⟩ := _root_.GD.N0232.N0720.N1342.d028965 m n hm hn hd
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
  · exact _root_.GD.N0232.N0720.N1326.d028968 m n k hdim hd f hf hhom 1 hbound hrep
  · exact _root_.GD.N0232.N0720.N1326.d019891 f hf hhom 1 hbound

theorem d028970 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {δ : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d028959 m n δ) :
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
    _root_.GD.N0232.N0720.N1330.d028969 m n k hdim hm hn hd
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

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal
open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1329
open _root_.GD.N0232.N0720.N1315 _root_.GD.N0232.N0720.N1331
open _root_.GD.N0232.N0720.N1324 _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1376 _root_.GD.N0232.N0720.N1297
variable {I : Type*} [Fintype I]
variable {Index : ℕ → Type*} [∀ j, Fintype (Index j)]

theorem d028971
    (m n d : ℕ) (hdim : m + n = d + 1) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {δ : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d028959 m n δ) :
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
    _root_.GD.N0232.N0720.N1330.d028970
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

open MeasureTheory Set Filter
open scoped Topology
open _root_.GD.N0232.N0720.N1315 _root_.GD.N0232.N0720.N1323
open _root_.GD.N0232.N0720.N1382 _root_.GD.N0232.N0720.N1297
open _root_.GD.N0232.N0720.N1394

theorem d028972
    (m n d : ℕ) (hdim : m + n = d + 1) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {δ : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d028959 m n δ) :
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
    _root_.GD.N0232.N0720.N1321.d028971
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

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal
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
variable (m n : ℕ)
variable (k : ℕ) (hdim : m + n = k + 1)

theorem d028973 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d)
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

theorem d028974 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d)
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
  have h := (_root_.GD.N0232.N0720.N1327.d028973 m n hm hn hd hg hb hrep mu hpost theta).symm
  simpa only [Function.comp_def, _root_.GD.N0232.N0720.N1329.d019673] using h

theorem d028975 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1425.d014719 m n g =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] d)
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) [IsProbabilityMeasure mu]
    (hpost : g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun z ↦ _root_.GD.N0232.N0720.N1290.d004140 (_root_.GD.N0232.N0720.N1436.d013210 m n) (_root_.GD.N0232.N0720.N1336.d013420 m n z) mu) :
    ∀ᵐ x ∂(volume : Measure (_root_.GD.N0232.N0720.N1327.d020582 k)), x ∈ _root_.GD.N0232.N0720.N1322.d020080 hdim →
      _root_.GD.N0232.N0720.N1329.d019671 m n k hdim g x =
        _root_.GD.N0232.N0720.N1352.d002804 (_root_.GD.N0232.N0720.N1308.d020280 (m + n + 1) mu ∘ _root_.GD.N0232.N0720.N1351.d002814)
          (_root_.GD.N0232.N0720.N1315.d019850 m n k hdim x) := by
  filter_upwards [_root_.GD.N0232.N0720.N1327.d028974 m n k hdim hm hn hd hg hb hrep mu hpost]
    with x hx
  intro hphysical
  exact hx.trans (_root_.GD.N0232.N0720.N1327.d020611 m n k hdim hm hn hphysical mu)

theorem d028976 (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1329.d019645 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d)
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
  filter_upwards [_root_.GD.N0232.N0720.N1327.d028975 m n k hdim hm hn hd hg hb hrep mu hpost]
    with x hx hphysical
  exact (hx hphysical).symm

end
end GD.N0232.N0720.N1327

namespace GD.N0232.N0720.N1325

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff
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

theorem d028977 (m n k : ℕ) (hdim : m + n = k + 1)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d028959 m n d)
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
    _root_.GD.N0232.N0720.N1343.d028972
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
  have heq := _root_.GD.N0232.N0720.N1327.d028976 m n k hdim hm hn hd hg hb hrep
    (μ : Measure _root_.GD.N0232.N0720.N1325.d020614) hpost hcontinuous hae
  exact ⟨_root_.GD.N0232.N0720.N1323.d020317 (m + n) ν hν (fun x hx ↦ heq hx)⟩

end
end GD.N0232.N0720.N1325

#print axioms _root_.GD.N0232.N0720.N1303.d028967
#print axioms _root_.GD.N0232.N0720.N1325.d028977

namespace GD.N0034.N0300

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1303
open _root_.GD.N0232.N0720.N1325
open _root_.GD.N0232.N0720.N1226
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608

theorem d028978 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ ∃ d, _root_.GD.N0232.N0720.N1159.d028959 m n d := by
  rintro ⟨d, hd⟩
  obtain ⟨g, μ, hg, hb, hrep, hpost⟩ :=
    _root_.GD.N0232.N0720.N1303.d028967 m n hm hn hd
  let k := m + n - 1
  have hdim : m + n = k + 1 := by dsimp [k]; omega
  obtain ⟨m1⟩ := _root_.GD.N0232.N0720.N1325.d028977
    m n k hdim hm hn hd hg hb hrep μ hpost
  let prior : Measure _root_.GD.N0232.N0720.N1290.d004131 := μ
  have hpostPointwise : ∀ᵐ x ∂ _root_.GD.N0232.N0720.N1441.d013679 m n,
      g x = _root_.GD.N0232.N0720.N1290.d004140
        (_root_.GD.N0232.N0720.N1436.d013210 m n)
        (_root_.GD.N0232.N0720.N1336.d013420 m n x) prior := by
    exact hpost
  exact _root_.GD.N0034.N0298.d028958
    hm hn hd.2.2.1 hg hb (fun θ ↦ (hrep θ).symm) prior hpostPointwise m1

theorem d028979 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (_hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (hweak : ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (ht : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p) : False := by
  obtain ⟨d, hd, hclass, hcov⟩ := hrep
  have hrisk (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014197 m n θ d = _root_.GD.N0232.N0720.N1080.d014182 m n θ p :=
    (_root_.GD.N0232.N0720.N1159.d014662 m n θ (hclass θ)).trans
      (_root_.GD.N0232.N0720.N1215.d014286 m n θ p)
  apply _root_.GD.N0034.N0300.d028978 m n hm hn
  refine ⟨d, hd, hcov, ?_, ?_⟩
  · intro θ
    rw [hrisk, _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]
    exact hweak θ
  · intro e he hbelow θ
    have hbelow' (η : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014197 m n η e ≤
        _root_.GD.N0232.N0720.N1080.d014197 m n η (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
      rw [_root_.GD.N0232.N0720.N1215.d014286, ← hrisk]
      exact hbelow η
    exact (_root_.GD.N0232.N0720.N1226.d015581 m n p ht e he hbelow' θ).trans
      (hclass θ).symm

end
end GD.N0034.N0300

#print axioms _root_.GD.N0034.N0300.d028978
#print axioms _root_.GD.N0034.N0300.d028979
