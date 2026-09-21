import GD.Module0865
import GD.Module1236
import GD.Module0285












open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0232.N0720.N1334

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1332
open _root_.GD.N0232.N0720.N1290
open _root_.GD.N0232.N0720.N1344 _root_.GD.N0232.N0720.N1340
open _root_.GD.N0232.N0720.N1414 (d004212)

noncomputable section

theorem d020121
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ}
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} {mu : Measure _root_.GD.N0232.N0720.N1290.d004131} [IsProbabilityMeasure mu]
    {center r : ℝ} (hr : 0 ≤ r)
    (hclass : Measure.map (fun t : _root_.GD.N0232.N0720.N1290.d004131 ↦ (t : ℝ)) mu = _root_.GD.N0232.N0720.N1344.d013339 q hq center r)
    (P : _root_.GD.N0232.N0720.N1436.d013217 → _root_.GD.N0232.N0720.N1290.d004131 → ℝ)
    (hP : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, Continuous (P x) ∧ ∀ t, 0 < P x t)
    (hpost : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x = _root_.GD.N0232.N0720.N1290.d004140 q (P x) mu) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x ∈ Icc (center - r) (center + r) := by
  have hs := _root_.GD.N0232.N0720.N1340.d013354 q hq hr hclass
  filter_upwards [hP, hpost] with x hx heq
  rw [heq]
  exact _root_.GD.N0232.N0720.N1359.d004246 q (P x) hx.1 hx.2 mu hs

theorem d020122
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
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
    exact _root_.GD.N0232.N0720.N1332.d020119 hm hn hd hg hb hrep hpos
      (hcoeff.mono fun _ hx ↦ hx.1)
  have hright : 1 ≤ center + r := by
    by_contra! hlt
    exact _root_.GD.N0232.N0720.N1332.d020120 hm hn hd hg hb hrep hlt
      (hcoeff.mono fun _ hx ↦ hx.2)
  constructor <;> linarith [hin.1, hin.2]



theorem d020123
    (q : ℝ) (hq : 3 / 2 ≤ q) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d)
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
  obtain ⟨hc, hradius⟩ := _root_.GD.N0232.N0720.N1334.d020122 q hq hm hn
    hd hg hb hrep hr hclass P hP hpost
  simpa only [hc, hradius] using hclass

end
end GD.N0232.N0720.N1334

#print axioms _root_.GD.N0232.N0720.N1334.d020122
#print axioms _root_.GD.N0232.N0720.N1334.d020123
