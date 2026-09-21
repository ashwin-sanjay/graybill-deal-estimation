import GD.Module1149
import GD.Module1033
import GD.Module1108
import GD.Module0191

























open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1363

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1121
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1211
open _root_.GD.N0232.N0720.N1302
open _root_.GD.N0232.N0720.N1417
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482






def d018469 : Prop :=
  ∃ row : _root_.GD.N0232.N0720.N1103.d018289 _root_.GD.N0232.N0720.N1302.d018268,
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 2 2
        (_root_.GD.N0232.N0720.N1130.d017075 2 2 (row.candidate j)))
      atTop (nhds 0)



theorem d018470
    {m n : ℕ} (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (row : _root_.GD.N0232.N0720.N1103.d018289 s) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)))
      atTop (nhds (_root_.GD.N0232.N0720.N1477.d015749 m n s)) := by
  let width : ℕ → ℕ := fun j ↦ (row.candidate j).width
  let packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168 :=
    fun j ↦ (row.candidate j).packet
  let weight : ∀ j, Fin (width j) → ℝ :=
    fun j ↦ (row.candidate j).weight
  let hweight : ∀ j i, 0 ≤ weight j i :=
    fun j ↦ (row.candidate j).weight_nonneg
  have htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0) := by
    simpa only [width, packet, weight, _root_.GD.N0232.N0720.N1103.d018279] using
      row.gap_tendsto_zero
  simpa only [_root_.GD.N0232.N0720.N1130.d017075, width, packet, weight, hweight] using
    _root_.GD.N0232.N0720.N1122.d017967
      s packet weight hweight htight



theorem d018471 :
    _root_.GD.N0232.N0720.N1363.d018469 ↔
      _root_.GD.N0232.N0720.N1477.d015749 2 2
        _root_.GD.N0232.N0720.N1302.d018268 = 0 := by
  constructor
  · rintro ⟨row, hzero⟩
    exact tendsto_nhds_unique
      (_root_.GD.N0232.N0720.N1363.d018470
        _root_.GD.N0232.N0720.N1302.d018268 row)
      hzero
  · intro hzero
    let row : _root_.GD.N0232.N0720.N1103.d018289
        _root_.GD.N0232.N0720.N1302.d018268 :=
      _root_.GD.N0232.N0720.N1103.d018292 _root_.GD.N0232.N0720.N1302.d018268
    refine ⟨row, ?_⟩
    simpa only [hzero] using
      (_root_.GD.N0232.N0720.N1363.d018470
        _root_.GD.N0232.N0720.N1302.d018268 row)






theorem d018472
    (h : _root_.GD.N0232.N0720.N1417.d018442) :
    _root_.GD.N0232.N0720.N1363.d018469 := by
  rcases h with ⟨row, hperspective⟩
  refine ⟨row, ?_⟩
  exact squeeze_zero
    (fun j ↦ _root_.GD.N0232.N0720.N1122.d017963
      (m := 2) (n := 2) (_root_.GD.N0232.N0720.N1130.d017075 2 2 (row.candidate j)))
    (fun j ↦ _root_.GD.N0232.N0720.N1121.d018307
      2 2 (row.candidate j))
    hperspective



theorem d018473
    (h : _root_.GD.N0232.N0720.N1363.d018469) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  have henergy : _root_.GD.N0232.N0720.N1477.d015749 2 2
      _root_.GD.N0232.N0720.N1302.d018268 = 0 :=
    _root_.GD.N0232.N0720.N1363.d018471.mp h
  apply
    (_root_.GD.N0232.N0720.N1482.d015173
      (m := 2) (n := 2) (by norm_num) (by norm_num)).2
  refine ⟨_root_.GD.N0232.N0720.N1302.d018268, ?_, ?_⟩
  · simpa only [_root_.GD.N0232.N0720.N1302.d018269] using
      _root_.GD.N0232.N0720.N1302.d018266
  · exact
      (_root_.GD.N0232.N0720.N1477.d015755
        (m := 2) (n := 2) _root_.GD.N0232.N0720.N1302.d018268).2 henergy







theorem d018474
    {m n : ℕ} (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (u : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hu : Tendsto u atTop (nhds q))
    (hscale : _root_.GD.N0232.N0720.N1146.d015228 m n q = q)
    (hshift : _root_.GD.N0232.N0720.N1146.d015229 m n q = q) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n (u j))
      atTop (nhds 0) := by
  have hlimit : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n (u j))
      atTop (nhds (_root_.GD.N0232.N0720.N1122.d017962 m n q)) :=
    _root_.GD.N0232.N0720.N1122.d017964.continuousAt.tendsto.comp
      hu
  have hzero : _root_.GD.N0232.N0720.N1122.d017962 m n q = 0 := by
    simp only [_root_.GD.N0232.N0720.N1122.d017962, hscale, hshift,
      sub_self, norm_zero]
    norm_num
  simpa only [hzero] using hlimit






theorem d018475 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
        _root_.GD.N0232.N0720.N1302.d018268.value
        (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) ∧
      Nonempty
        (_root_.GD.N0232.N0720.N1103.d018289 _root_.GD.N0232.N0720.N1302.d018268) := by
  constructor
  · simpa only [_root_.GD.N0232.N0720.N1302.d018269] using
      _root_.GD.N0232.N0720.N1302.d018266
  · exact _root_.GD.N0232.N0720.N1103.d018291
      _root_.GD.N0232.N0720.N1302.d018268

end

end N1363
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1363.d018470
#print axioms _root_.GD.N0232.N0720.N1363.d018471
#print axioms _root_.GD.N0232.N0720.N1363.d018472
#print axioms _root_.GD.N0232.N0720.N1363.d018473
#print axioms _root_.GD.N0232.N0720.N1363.d018474
#print axioms _root_.GD.N0232.N0720.N1363.d018475
