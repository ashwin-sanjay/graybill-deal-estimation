import GD.Module1276

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace GD.N0034.N0298

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1287 _root_.GD.N0232.N0720.N1396
open _root_.GD.N0232.N0720.N1424 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1434 _root_.GD.N0232.N0720.N1423
open _root_.GD.N0232.N0720.N1091 _root_.GD.N0232.N0720.N1218
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1399 (d020100 d020102
  d020101 d020103)
open _root_.GD.N0232.N0720.N1332 _root_.GD.N0232.N0720.N1328
open _root_.GD.N0232.N0720.N1333 _root_.GD.N0232.N0720.N1334
open _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1344 _root_.GD.N0232.N0720.N1340
open _root_.GD.N0232.N0720.N1414 (d004212)
open _root_.GD.N0232.N0720.N1339 _root_.GD.N0232.N0720.N1345
open _root_.GD.N0232.N0720.N1336 _root_.GD.N0232.N0720.N1357
open _root_.GD.N0232.N0720.N1368 _root_.GD.N0232.N0720.N1352
open _root_.GD.N0232.N0720.N1351 _root_.GD.N0232.N0720.N1292
open _root_.GD.N0232.N0720.N1270 (d020224 d020225 d020226 d020227
  d020228 d020229 d020234
  d020238)
open _root_.GD.N0232.N0720.N1264 (d020252 d020244)
open _root_.GD.N0232.N0720.N1308 _root_.GD.N0232.N0720.N1317

theorem d028949
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hweak : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 ≤ _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 t.1 := by
  have h := hweak (_root_.GD.N0232.N0720.N1332.d020110 m n hm hn t)
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n _ (hrep _),
    _root_.GD.N0232.N0720.N1332.d020109 m n hm hn _ hg hb,
    _root_.GD.N0232.N0720.N1080.d014199 m n hm hn,
    _root_.GD.N0232.N0720.N1287.d019529 m n hm hn] at h
  change ENNReal.ofReal (_ + _ * _root_.GD.N0232.N0720.N1332.d020106 m n g _) ≤
    ENNReal.ofReal (_ + _ * _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 _) at h
  rw [_root_.GD.N0232.N0720.N1332.d020111, _root_.GD.N0232.N0720.N1332.d020112, one_mul] at h
  simp only [one_mul] at h
  have hnonneg : 0 ≤ _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1332.d020110 m n hm hn t))
      (_root_.GD.N0107.d012732 m n (_root_.GD.N0232.N0720.N1332.d020110 m n hm hn t).location t.1) +
      _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 t.1 :=
    add_nonneg (integral_nonneg (fun _ ↦ sq_nonneg _)) (_root_.GD.N0232.N0720.N1332.d020107 _ _ _ _)
  have hreal := (ENNReal.ofReal_le_ofReal_iff hnonneg).1 h
  linarith

theorem d028950
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hweak : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    {a : ℝ} (ha : 0 < a) : ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, a ≤ g x) := by
  intro hfloor
  have hloss : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020100 k).1)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (_root_.GD.N0232.N0720.N1332.d020115 hm hn _root_.GD.N0232.N0720.N1399.d020101)
      (fun k ↦ _root_.GD.N0232.N0720.N1332.d020107 _ _ _ _)
      (fun k ↦ _root_.GD.N0034.N0298.d028949 hm hn hweak hg hb hrep _)
  have hsmall := hloss.eventually_lt_const (sq_pos_of_pos (half_pos ha))
  have hfrac := _root_.GD.N0232.N0720.N1399.d020101.eventually_lt_const (half_pos ha)
  obtain ⟨k, hk, ht⟩ := (hsmall.and hfrac).exists
  have hbound := _root_.GD.N0232.N0720.N1332.d020117 hm hn hg hb (_root_.GD.N0232.N0720.N1399.d020100 k)
    (a := a) (by linarith) hfloor
  have hgap : a / 2 < a - (_root_.GD.N0232.N0720.N1399.d020100 k).1 := by linarith
  have hsquare := (sq_lt_sq₀ (half_pos ha).le (by linarith)).2 hgap
  linarith

theorem d028951
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hweak : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
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
      (fun k ↦ _root_.GD.N0034.N0298.d028949 hm hn hweak hg hb hrep _)
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

theorem d028952
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hdesign : m ≠ 2 ∨ n ≠ 2)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hweak : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n))
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
  have hstrict := hweak theta
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n theta (hrep theta), hrisk,
    _root_.GD.N0232.N0720.N1396.d014785 m n theta hmem,
    _root_.GD.N0232.N0720.N1396.d014785 m n theta (_root_.GD.N0232.N0720.N1080.d014177 m n hm hn theta)]
      at hstrict
  have hnonneg : 0 ≤ _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
      (fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - theta.location) :=
    integral_nonneg (fun _ ↦ sq_nonneg _)
  have hreal := (ENNReal.ofReal_le_ofReal_iff hnonneg).1 hstrict
  exact (not_le_of_gt hgap) hreal

theorem d028953
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hweak : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n))
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
    have hcap := _root_.GD.N0034.N0298.d028949 hm hn hweak hg hb hrep
      _root_.GD.N0232.N0720.N1404.d020198
    rw [hloss] at hcap
    exact (not_le_of_gt _root_.GD.N0232.N0720.N1404.d020199) hcap
  · exact _root_.GD.N0034.N0298.d028952 hm hn (by tauto) hweak hg hb hrep

theorem d028954
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hweak : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n))
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
    exact _root_.GD.N0034.N0298.d028950 hm hn hweak hg hb hrep hpos
      (hcoeff.mono fun _ hx ↦ hx.1)
  have hright : 1 ≤ center + r := by
    by_contra! hlt
    exact _root_.GD.N0034.N0298.d028951 hm hn hweak hg hb hrep hlt
      (hcoeff.mono fun _ hx ↦ hx.2)
  constructor <;> linarith [hin.1, hin.2]

theorem d028955
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hweak : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n))
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
  obtain ⟨hc, hradius⟩ := _root_.GD.N0034.N0298.d028954 q hq hm hn
    hweak hg hb hrep hr hclass P hP hpost
  simpa only [hc, hradius] using hclass

theorem d028956
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hweak : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n))
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
  have hclass := _root_.GD.N0034.N0298.d028955 q hq hm hn
    hweak hg hb hrep mu hF (_root_.GD.N0232.N0720.N1336.d013420 m n) hP hpost
  apply _root_.GD.N0034.N0298.d028953 hm hn hweak hg hb hrep
  filter_upwards [hdomain, hpost] with x hx heq
  exact heq.trans (_root_.GD.N0232.N0720.N1345.d020328 q hq hm hn mu hclass hx)

theorem d028957
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hweak : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n))
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
  apply _root_.GD.N0034.N0298.d028956 q hq hm hn hweak hg hb hrep mu hpost
  exact _root_.GD.N0232.N0720.N1368.d020221
    q (_root_.GD.N0232.N0720.N1414.d004212 0 1 mu) mu hzero

theorem d028958
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hweak : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n))
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
    _root_.GD.N0034.N0298.d028957
      _ hq hm hn hweak hg hb hrep mu hpost'
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
end GD.N0034.N0298

#print axioms _root_.GD.N0034.N0298.d028949
#print axioms _root_.GD.N0034.N0298.d028950
#print axioms _root_.GD.N0034.N0298.d028951
#print axioms _root_.GD.N0034.N0298.d028952
#print axioms _root_.GD.N0034.N0298.d028953
#print axioms _root_.GD.N0034.N0298.d028954
#print axioms _root_.GD.N0034.N0298.d028955
#print axioms _root_.GD.N0034.N0298.d028956
#print axioms _root_.GD.N0034.N0298.d028957
#print axioms _root_.GD.N0034.N0298.d028958
