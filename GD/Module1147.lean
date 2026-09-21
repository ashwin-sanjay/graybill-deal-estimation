import GD.Module1136
import GD.Module1118
import GD.Module0986























open Filter MeasureTheory Topology

namespace GD
namespace N0232
namespace N0720
namespace N1259

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1288

variable {m n : ℕ}









def d018425
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∃ (width : ℕ → ℕ)
      (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
      (weight : ∀ j, Fin (width j) → ℝ)
      (hweight : ∀ j i, 0 ≤ weight j i),
    (∀ j,
      _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn)
          (packet j) (weight j) ≤
        _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn)
          (packet (j + 1)) (weight (j + 1))) ∧
    (∀ j,
      0 ≤ ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn)
          (packet j) (weight j)) ∧
    Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn)
          (packet j) (weight j))
      atTop (nhds 0) ∧
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        (packet j) (weight j) (hweight j))
      atTop (nhds (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn))






theorem d018426
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1259.d018425 m n hm hn := by
  let s : _root_.GD.N0232.N0720.N1159.d014639 m n := _root_.GD.N0232.N0720.N1288.d015634 m n hm hn
  let row : _root_.GD.N0232.N0720.N1103.d018289 s :=
    _root_.GD.N0232.N0720.N1103.d018292 s
  let width : ℕ → ℕ := fun j ↦ (row.candidate j).width
  let packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168 :=
    fun j ↦ (row.candidate j).packet
  let weight : ∀ j, Fin (width j) → ℝ :=
    fun j ↦ (row.candidate j).weight
  let hweight : ∀ j i, 0 ≤ weight j i :=
    fun j ↦ (row.candidate j).weight_nonneg
  have hcanonical :
      _root_.GD.N0232.N0720.N1080.d014191 m n hm hn =
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
    simpa only [s] using
      _root_.GD.N0232.N0720.N1288.d015635 m n hm hn
  have htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0) := by
    simpa only [hcanonical, width, packet, weight, _root_.GD.N0232.N0720.N1103.d018279] using
      row.gap_tendsto_zero
  refine ⟨width, packet, weight, hweight, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa only [s, width, packet, weight, _root_.GD.N0232.N0720.N1103.d018279] using
      row.reserve_step j
  · intro j
    have hbound := _root_.GD.N0232.N0720.N1103.d018280 s (row.candidate j)
    simpa only [hcanonical, width, packet, weight, _root_.GD.N0232.N0720.N1103.d018279] using
      sub_nonneg.mpr hbound
  · simpa only [s] using htight
  · have hcompletion :=
      _root_.GD.N0232.N0720.N1122.d017966
        s packet weight hweight (by simpa only [hcanonical] using htight)
    simpa only [hcanonical] using hcompletion


theorem d018427
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ (width : ℕ → ℕ)
        (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
        (weight : ∀ j, Fin (width j) → ℝ)
        (hweight : ∀ j i, 0 ≤ weight j i),
      Antitone (fun j ↦ ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn)
          (packet j) (weight j)) ∧
      Tendsto
        (fun j ↦ ‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1288.d015634 m n hm hn)
            (packet j) (weight j))
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          (packet j) (weight j) (hweight j))
        atTop (nhds (_root_.GD.N0232.N0720.N1080.d014191 m n hm hn)) := by
  obtain ⟨width, packet, weight, hweight, hstep, _hnonneg, htight, hcompletion⟩ :=
    _root_.GD.N0232.N0720.N1259.d018426 (m := m) (n := n) hm hn
  refine ⟨width, packet, weight, hweight, ?_, htight, hcompletion⟩
  apply antitone_nat_of_succ_le
  intro j
  exact sub_le_sub_left (hstep j) (‖_root_.GD.N0232.N0720.N1080.d014191 m n hm hn‖ ^ 2)









theorem d018428
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Measurable (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn) <
          _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      ∀ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
        Measurable d →
        (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
          _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
            _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn)) →
        ∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
          d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] _root_.GD.N0232.N0720.N1080.d014194 m n hm hn := by
  exact ⟨_root_.GD.N0232.N0720.N1080.d014195 m n hm hn,
    _root_.GD.N0232.N0720.N1080.d014201 m n hm hn,
    fun d hd hdom ↦ _root_.GD.N0232.N0720.N1080.d014202 m n hm hn d hd hdom⟩






theorem d018429
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (Measurable (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
        _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn) <
          _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n)) ∧
      ∀ d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ,
        Measurable d →
        (∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
          _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
            _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014194 m n hm hn)) →
        ∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
          d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] _root_.GD.N0232.N0720.N1080.d014194 m n hm hn) ∧
      _root_.GD.N0232.N0720.N1259.d018425 m n hm hn := by
  exact ⟨_root_.GD.N0232.N0720.N1259.d018428 hm hn,
    _root_.GD.N0232.N0720.N1259.d018426 hm hn⟩

end

end N1259
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1259.d018426
#print axioms _root_.GD.N0232.N0720.N1259.d018427
#print axioms _root_.GD.N0232.N0720.N1259.d018428
#print axioms _root_.GD.N0232.N0720.N1259.d018429
