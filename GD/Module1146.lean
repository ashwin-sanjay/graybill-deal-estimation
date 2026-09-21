import GD.Module0033
import GD.Module1135
import GD.Module1137
import GD.Module1136
import GD.Module1131
import GD.Module1062






















open Filter MeasureTheory Set Topology

namespace GD
namespace N0232
namespace N0720
namespace N1206

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1116
open _root_.GD.N0232.N0720.N1121
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1210
open _root_.GD.N0232.N0720.N1302
open _root_.GD.N0232.N0720.N1444




def d018413 (C D : ℕ → ℝ) : Prop :=
  (∀ j, C j = C (j + 1) + D j) ∧
    (∀ j, 0 ≤ C j) ∧
      ∀ j, 0 ≤ D j



def d018414 : Prop :=
  ∃ width : ℕ → ℕ,
    ∃ packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168,
      ∃ weight : ∀ j, Fin (width j) → ℝ,
        ∃ hweight : ∀ j i, 0 ≤ weight j i,
          Tendsto
              (fun j ↦
                ‖_root_.GD.N0232.N0720.N1159.d014633 2 2
                    _root_.GD.N0232.N0720.N1302.d018268.value‖ ^ 2 -
                  _root_.GD.N0232.N0720.N1126.d016432 _root_.GD.N0232.N0720.N1302.d018268
                    (packet j) (weight j))
              atTop (nhds 0) ∧
            ∃ C D : ℕ → ℝ,
              _root_.GD.N0232.N0720.N1206.d018413 C D ∧
                ∃ kappa : ℝ, 0 < kappa ∧
                  ∀ j,
                    kappa * _root_.GD.N0232.N0720.N1122.d017962 2 2
                        (_root_.GD.N0232.N0720.N1126.d016426 (m := 2) (n := 2)
                          (packet j) (weight j) (hweight j)) ≤
                      D j



theorem d018415
    (h : _root_.GD.N0232.N0720.N1206.d018414) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  rcases h with
    ⟨width, packet, weight, hweight, htight, C, D,
      ⟨htower, hC, hD⟩, kappa, hkappa, hcoercive⟩
  exact _root_.GD.N0232.N0720.N1210.d018278
    (width := width) packet weight hweight htight C D htower hC hD
      hkappa hcoercive



def d018416 : Prop :=
  ∃ width : ℕ → ℕ,
    ∃ packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168,
      ∃ weight : ∀ j, Fin (width j) → ℝ,
        ∃ hweight : ∀ j i, 0 ≤ weight j i,
          Tendsto
              (fun j ↦
                ‖_root_.GD.N0232.N0720.N1159.d014633 2 2
                    _root_.GD.N0232.N0720.N1302.d018268.value‖ ^ 2 -
                  _root_.GD.N0232.N0720.N1126.d016432 _root_.GD.N0232.N0720.N1302.d018268
                    (packet j) (weight j))
              atTop (nhds 0) ∧
            ∃ C D : ℕ → ℝ,
              _root_.GD.N0232.N0720.N1206.d018413 C D ∧
                ∃ kappa : ℝ, 0 < kappa ∧
                  ∀ j,
                    kappa * _root_.GD.N0232.N0720.N1121.d018309 2 2
                        (packet j) (weight j) (hweight j) ≤
                      D j

theorem d018417
    (h : _root_.GD.N0232.N0720.N1206.d018416) :
    _root_.GD.N0232.N0720.N1206.d018414 := by
  rcases h with
    ⟨width, packet, weight, hweight, htight, C, D,
      htower, kappa, hkappa, hproduction⟩
  refine ⟨width, packet, weight, hweight, htight, C, D, htower,
    kappa, hkappa, ?_⟩
  exact _root_.GD.N0232.N0720.N1121.d018310
    packet weight hweight D hkappa.le hproduction

theorem d018418
    (h : _root_.GD.N0232.N0720.N1206.d018416) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  exact
    _root_.GD.N0232.N0720.N1206.d018415
      (_root_.GD.N0232.N0720.N1206.d018417 h)







theorem d018419
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hproduction : ∀ᶠ j in atTop,
      kappa * _root_.GD.N0232.N0720.N1121.d018305 m n
          (row.candidate j) ≤
        _root_.GD.N0232.N0720.N1103.d018294 s row j) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply
    _root_.GD.N0232.N0720.N1103.d018301
      hm hn s hstrict row hkappa
  filter_upwards [hproduction] with j hj
  have hresidual :=
    _root_.GD.N0232.N0720.N1121.d018307
      m n (row.candidate j)
  exact (mul_le_mul_of_nonneg_left hresidual hkappa.le).trans hj






def d018420 : Prop :=
  ∃ row : _root_.GD.N0232.N0720.N1103.d018289 _root_.GD.N0232.N0720.N1302.d018268,
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ j in atTop,
        kappa * _root_.GD.N0232.N0720.N1121.d018305 2 2
            (row.candidate j) ≤
          _root_.GD.N0232.N0720.N1103.d018294 _root_.GD.N0232.N0720.N1302.d018268 row j





theorem d018421
    (h : _root_.GD.N0232.N0720.N1206.d018420) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  rcases h with ⟨row, kappa, hkappa, hproduction⟩
  have hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1302.d018268.value
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) := by
    simpa only [_root_.GD.N0232.N0720.N1302.d018269] using
      _root_.GD.N0232.N0720.N1302.d018266
  exact
    _root_.GD.N0232.N0720.N1206.d018419
      (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1302.d018268 hstrict row
        hkappa hproduction





def d018422
    {m n : ℕ} {ι : Type*} [Fintype ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ scale : ℕ → ℝ,
    ∃ packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168,
      ∃ weight : ℕ → ι → ℝ,
        (∀ j, 1 ≤ scale j) ∧
          Tendsto scale atTop atTop ∧
          (∀ j,
            0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
              _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j)) ∧
          Tendsto
            (fun j ↦
              ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
                _root_.GD.N0232.N0720.N1126.d016432 s
                  (_root_.GD.N0232.N0720.N1444.d017041 (packet j))
                  (_root_.GD.N0232.N0720.N1444.d017042 (scale j) (weight j)))
            atTop (nhds 0)



theorem d018423
    {m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (h : _root_.GD.N0232.N0720.N1206.d018422 (ι := ι) s) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value := by
  rcases h with
    ⟨scale, packet, weight, hscaleOne, hscale, hbaseGap,
      hreplicatedTight⟩
  exact _root_.GD.N0232.N0720.N1444.d017054
    s scale packet weight hscaleOne hscale hbaseGap hreplicatedTight


theorem d018424
    {m n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (h : ¬ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value) :
    ¬ _root_.GD.N0232.N0720.N1206.d018422 (ι := ι) s := by
  intro hreplication
  exact h (_root_.GD.N0232.N0720.N1206.d018423
    s hreplication)

end

end N1206
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1206.d018415
#print axioms _root_.GD.N0232.N0720.N1206.d018418
#print axioms _root_.GD.N0232.N0720.N1206.d018419
#print axioms _root_.GD.N0232.N0720.N1206.d018421
#print axioms _root_.GD.N0232.N0720.N1206.d018424
