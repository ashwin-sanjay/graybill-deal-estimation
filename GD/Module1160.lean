import GD.Module1157
import GD.Module1153
import GD.Module0985























open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1406

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1064
open _root_.GD.N0232.N0720.N1079
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1116
open _root_.GD.N0232.N0720.N1117
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1273
open _root_.GD.N0232.N0720.N1448
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}






def d018587
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (j : ℕ) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1130.d017075 m n ((_root_.GD.N0232.N0720.N1117.d018547 s).candidate j)




theorem d018588
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Tendsto (_root_.GD.N0232.N0720.N1406.d018587 s) atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) := by
  change Tendsto
    (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n
      ((_root_.GD.N0232.N0720.N1117.d018547 s).candidate j))
    atTop (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n s.value))
  exact _root_.GD.N0232.N0720.N1448.d018476 s
    (_root_.GD.N0232.N0720.N1117.d018547 s)




def d018589
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ u : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
    Tendsto (_root_.GD.N0232.N0720.N1406.d018587 s) atTop (nhds u) ∧
      _root_.GD.N0232.N0720.N1146.d015228 m n u = u ∧
      _root_.GD.N0232.N0720.N1146.d015229 m n u = u




theorem d018590
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (u : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hu : Tendsto (_root_.GD.N0232.N0720.N1406.d018587 s) atTop (nhds u)) :
    u = _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
  exact tendsto_nhds_unique hu
    (_root_.GD.N0232.N0720.N1406.d018588 s)

private theorem d018591
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0) :
    _root_.GD.N0232.N0720.N1146.d015228 m n
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∧
      _root_.GD.N0232.N0720.N1146.d015229 m n
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  have href : _root_.GD.N0232.N0720.N1122.d017962 m n p = 0 := by
    simpa only [p, _root_.GD.N0232.N0720.N1122.d017965]
      using henergy
  unfold _root_.GD.N0232.N0720.N1122.d017962 at href
  have htwoNorm :
      ‖_root_.GD.N0232.N0720.N1146.d015228 m n p - p‖ = 0 := by
    nlinarith [sq_nonneg
      ‖_root_.GD.N0232.N0720.N1146.d015228 m n p - p‖,
      sq_nonneg
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n p - p‖,
      norm_nonneg (_root_.GD.N0232.N0720.N1146.d015228 m n p - p),
      norm_nonneg
        (_root_.GD.N0232.N0720.N1146.d015229 m n p - p)]
  have hthreeNorm :
      ‖_root_.GD.N0232.N0720.N1146.d015229 m n p - p‖ = 0 := by
    nlinarith [sq_nonneg
      ‖_root_.GD.N0232.N0720.N1146.d015228 m n p - p‖,
      sq_nonneg
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n p - p‖,
      norm_nonneg (_root_.GD.N0232.N0720.N1146.d015228 m n p - p),
      norm_nonneg
        (_root_.GD.N0232.N0720.N1146.d015229 m n p - p)]
  exact ⟨sub_eq_zero.mp (norm_eq_zero.mp htwoNorm),
    sub_eq_zero.mp (norm_eq_zero.mp hthreeNorm)⟩

private theorem d018592
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hfixed :
      _root_.GD.N0232.N0720.N1146.d015228 m n
            (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∧
        _root_.GD.N0232.N0720.N1146.d015229 m n
            (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  rw [← _root_.GD.N0232.N0720.N1122.d017965
    (m := m) (n := n) s]
  simp only [_root_.GD.N0232.N0720.N1122.d017962, hfixed.1, hfixed.2,
    sub_self, norm_zero]
  norm_num



theorem d018593
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1406.d018589 s ↔
      _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  constructor
  · rintro ⟨u, hu, htwo, hthree⟩
    have heq := _root_.GD.N0232.N0720.N1406.d018590 s u hu
    apply _root_.GD.N0232.N0720.N1406.d018592 s
    simpa only [← heq] using And.intro htwo hthree
  · intro henergy
    refine ⟨_root_.GD.N0232.N0720.N1159.d014633 m n s.value,
      _root_.GD.N0232.N0720.N1406.d018588 s, ?_⟩
    exact _root_.GD.N0232.N0720.N1406.d018591
      s henergy





def d018594
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ u : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
    Tendsto (_root_.GD.N0232.N0720.N1406.d018587 s) atTop (nhds u) ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1146.d015228 m n
              (_root_.GD.N0232.N0720.N1406.d018587 s j) -
            _root_.GD.N0232.N0720.N1406.d018587 s j‖ +
          ‖_root_.GD.N0232.N0720.N1146.d015229 m n
              (_root_.GD.N0232.N0720.N1406.d018587 s j) -
            _root_.GD.N0232.N0720.N1406.d018587 s j‖)
        atTop (nhds 0)




theorem d018595
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1406.d018594 s ↔
      _root_.GD.N0232.N0720.N1406.d018589 s := by
  constructor
  · rintro ⟨u, hu, hcurrent⟩
    refine ⟨u, hu, ?_⟩
    exact
      (_root_.GD.N0232.N0720.N1273.d015609
        u (_root_.GD.N0232.N0720.N1406.d018587 s) hu).1 hcurrent
  · rintro ⟨u, hu, htwo, hthree⟩
    refine ⟨u, hu, ?_⟩
    exact
      (_root_.GD.N0232.N0720.N1273.d015609
        u (_root_.GD.N0232.N0720.N1406.d018587 s) hu).2 ⟨htwo, hthree⟩






def d018596
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ (width : ℕ → ℕ)
      (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
      (weight : ∀ j, Fin (width j) → ℝ)
      (hweight : ∀ j i, 0 ≤ weight j i)
      (u : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)),
    Tendsto
        (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          (packet j) (weight j) (hweight j))
        atTop (nhds u) ∧
      _root_.GD.N0232.N0720.N1146.d015228 m n u = u ∧
      _root_.GD.N0232.N0720.N1146.d015229 m n u = u




def d018597
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ (width : ℕ → ℕ)
      (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
      (weight : ∀ j, Fin (width j) → ℝ)
      (hweight : ∀ j i, 0 ≤ weight j i),
    Tendsto
        (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
        atTop (nhds 0) ∧
      _root_.GD.N0232.N0720.N1146.d015228 m n
            (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∧
      _root_.GD.N0232.N0720.N1146.d015229 m n
            (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value




theorem d018598
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1406.d018596 s ↔
      _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  constructor
  · rintro ⟨width, packet, weight, hweight, u,
      htight, hstrong, htwo, hthree⟩
    have hterminal :=
      _root_.GD.N0232.N0720.N1122.d017966
        s packet weight hweight htight
    have heq : u = _root_.GD.N0232.N0720.N1159.d014633 m n s.value :=
      tendsto_nhds_unique hstrong hterminal
    apply _root_.GD.N0232.N0720.N1406.d018592 s
    simpa only [← heq] using And.intro htwo hthree
  · intro henergy
    obtain ⟨width, packet, weight, hweight, htight⟩ :=
      _root_.GD.N0232.N0720.N1116.d016457 s
    refine ⟨width, packet, weight, hweight,
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value, htight, ?_, ?_⟩
    · exact
        _root_.GD.N0232.N0720.N1122.d017966
          s packet weight hweight htight
    · exact _root_.GD.N0232.N0720.N1406.d018591
        s henergy



theorem d018599
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1406.d018596 s ↔
      _root_.GD.N0232.N0720.N1406.d018597 s := by
  constructor
  · rintro ⟨width, packet, weight, hweight, u,
      htight, hstrong, htwo, hthree⟩
    have hterminal :=
      _root_.GD.N0232.N0720.N1122.d017966
        s packet weight hweight htight
    have heq : u = _root_.GD.N0232.N0720.N1159.d014633 m n s.value :=
      tendsto_nhds_unique hstrong hterminal
    subst u
    exact ⟨width, packet, weight, hweight, htight, htwo, hthree⟩
  · rintro ⟨width, packet, weight, hweight, htight, htwo, hthree⟩
    refine ⟨width, packet, weight, hweight,
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value, htight, ?_, htwo, hthree⟩
    exact
      _root_.GD.N0232.N0720.N1122.d017966
        s packet weight hweight htight




theorem d018600
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1406.d018589 s ↔
      _root_.GD.N0232.N0720.N1406.d018596 s := by
  rw [_root_.GD.N0232.N0720.N1406.d018593,
    _root_.GD.N0232.N0720.N1406.d018598]





theorem d018601
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1406.d018589 s ↔
      _root_.GD.N0232.N0720.N1079.d018506 s := by
  rw [_root_.GD.N0232.N0720.N1406.d018593,
    _root_.GD.N0232.N0720.N1079.d018507]



theorem d018602
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1406.d018589 s ↔
      _root_.GD.N0232.N0720.N1064.d018555 s := by
  rw [_root_.GD.N0232.N0720.N1406.d018593,
    _root_.GD.N0232.N0720.N1064.d018556]







theorem d018603
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1406.d018589 s := by
  rw [_root_.GD.N0232.N0720.N1482.d015173
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hmaster⟩
    refine ⟨s, hstrict, ?_⟩
    exact
      (_root_.GD.N0232.N0720.N1406.d018593
        s).2
        ((_root_.GD.N0232.N0720.N1477.d015755
          (m := m) (n := n) s).1 hmaster)
  · rintro ⟨s, hstrict, hpacket⟩
    refine ⟨s, hstrict, ?_⟩
    exact
      (_root_.GD.N0232.N0720.N1477.d015755
        (m := m) (n := n) s).2
        ((_root_.GD.N0232.N0720.N1406.d018593
          s).1 hpacket)





theorem d018604
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1406.d018596 s := by
  rw [_root_.GD.N0232.N0720.N1406.d018603
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hcanonical⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1406.d018600
        s).1 hcanonical⟩
  · rintro ⟨s, hstrict, harbitrary⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1406.d018600
        s).2 harbitrary⟩

end

end N1406
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1406.d018590
#print axioms _root_.GD.N0232.N0720.N1406.d018593
#print axioms _root_.GD.N0232.N0720.N1406.d018595
#print axioms _root_.GD.N0232.N0720.N1406.d018598
#print axioms _root_.GD.N0232.N0720.N1406.d018599
#print axioms _root_.GD.N0232.N0720.N1406.d018600
#print axioms _root_.GD.N0232.N0720.N1406.d018601
#print axioms _root_.GD.N0232.N0720.N1406.d018602
#print axioms _root_.GD.N0232.N0720.N1406.d018603
#print axioms _root_.GD.N0232.N0720.N1406.d018604
