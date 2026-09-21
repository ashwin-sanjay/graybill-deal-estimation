import GD.Module1135
import GD.Module1068






















open Filter MeasureTheory Set Topology

namespace GD
namespace N0232
namespace N0720
namespace N1103

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1113
open _root_.GD.N0232.N0720.N1116
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1210
open _root_.GD.N0232.N0720.N1302

variable {m n : ℕ}




def d018279
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) : ℝ :=
  _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight


theorem d018280
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    _root_.GD.N0232.N0720.N1103.d018279 s candidate ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  exact _root_.GD.N0232.N0720.N1113.d017125
    m n s candidate


structure d018281 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) where
  candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074
  gap_tendsto_zero : Tendsto
    (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
      _root_.GD.N0232.N0720.N1103.d018279 s (candidate j)) atTop (nhds 0)


theorem d018282 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Nonempty (_root_.GD.N0232.N0720.N1103.d018281 s) := by
  obtain ⟨width, packet, weight, hweight, htight⟩ :=
    _root_.GD.N0232.N0720.N1116.d016457 s
  let candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074 := fun j ↦
    { width := width j
      packet := packet j
      weight := weight j
      weight_nonneg := hweight j }
  refine ⟨{ candidate := candidate, gap_tendsto_zero := ?_ }⟩
  simpa only [candidate, _root_.GD.N0232.N0720.N1103.d018279] using htight


noncomputable def d018283
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018281 s)
    (N : ℕ) : ℕ :=
  Classical.choose
    (Finset.exists_max_image (Finset.range (N + 1))
      (fun j ↦ _root_.GD.N0232.N0720.N1103.d018279 s (row.candidate j))
      ⟨0, by simp⟩)

theorem d018284
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018281 s)
    (N : ℕ) :
    _root_.GD.N0232.N0720.N1103.d018283 s row N ∈ Finset.range (N + 1) := by
  exact (Classical.choose_spec
    (Finset.exists_max_image (Finset.range (N + 1))
      (fun j ↦ _root_.GD.N0232.N0720.N1103.d018279 s (row.candidate j))
      ⟨0, by simp⟩)).1

theorem d018285
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018281 s)
    (N j : ℕ) (hj : j ≤ N) :
    _root_.GD.N0232.N0720.N1103.d018279 s (row.candidate j) ≤
      _root_.GD.N0232.N0720.N1103.d018279 s (row.candidate (_root_.GD.N0232.N0720.N1103.d018283 s row N)) := by
  have hjmem : j ∈ Finset.range (N + 1) := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
  exact (Classical.choose_spec
    (Finset.exists_max_image (Finset.range (N + 1))
      (fun i ↦ _root_.GD.N0232.N0720.N1103.d018279 s (row.candidate i))
      ⟨0, by simp⟩)).2 j hjmem


theorem d018286
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018281 s)
    (N : ℕ) :
    _root_.GD.N0232.N0720.N1103.d018279 s
        (row.candidate (_root_.GD.N0232.N0720.N1103.d018283 s row N)) ≤
      _root_.GD.N0232.N0720.N1103.d018279 s
        (row.candidate (_root_.GD.N0232.N0720.N1103.d018283 s row (N + 1))) := by
  apply _root_.GD.N0232.N0720.N1103.d018285 s row (N + 1)
  have hmem := _root_.GD.N0232.N0720.N1103.d018284 s row N
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hmem
  omega


noncomputable def d018287
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018281 s)
    (N : ℕ) : _root_.GD.N0232.N0720.N1130.d017074 :=
  row.candidate (_root_.GD.N0232.N0720.N1103.d018283 s row N)


theorem d018288
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018281 s) :
    Tendsto
      (fun N ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1103.d018279 s (_root_.GD.N0232.N0720.N1103.d018287 s row N))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro N
    exact sub_nonneg.mpr
      (_root_.GD.N0232.N0720.N1103.d018280 s
        (_root_.GD.N0232.N0720.N1103.d018287 s row N))
  · intro N
    have hreserve := _root_.GD.N0232.N0720.N1103.d018285 s row N N (le_refl N)
    simpa only [_root_.GD.N0232.N0720.N1103.d018287] using
      (sub_le_sub_left hreserve
        (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2))
  · exact row.gap_tendsto_zero


structure d018289 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) where
  candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074
  reserve_step : ∀ j,
    _root_.GD.N0232.N0720.N1103.d018279 s (candidate j) ≤
      _root_.GD.N0232.N0720.N1103.d018279 s (candidate (j + 1))
  gap_tendsto_zero : Tendsto
    (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
      _root_.GD.N0232.N0720.N1103.d018279 s (candidate j)) atTop (nhds 0)


noncomputable def d018281.d018290
    {s : _root_.GD.N0232.N0720.N1159.d014639 m n} (row : _root_.GD.N0232.N0720.N1103.d018281 s) :
    _root_.GD.N0232.N0720.N1103.d018289 s where
  candidate := _root_.GD.N0232.N0720.N1103.d018287 s row
  reserve_step := _root_.GD.N0232.N0720.N1103.d018286 s row
  gap_tendsto_zero := _root_.GD.N0232.N0720.N1103.d018288 s row


theorem d018291
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Nonempty (_root_.GD.N0232.N0720.N1103.d018289 s) := by
  exact ⟨(Nonempty.some (_root_.GD.N0232.N0720.N1103.d018282 s)).d018290⟩



noncomputable def d018292
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : _root_.GD.N0232.N0720.N1103.d018289 s :=
  Nonempty.some (_root_.GD.N0232.N0720.N1103.d018291 s)




def d018293
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    (j : ℕ) : ℝ :=
  ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
    _root_.GD.N0232.N0720.N1103.d018279 s (row.candidate j)


def d018294
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    (j : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1103.d018279 s (row.candidate (j + 1)) -
    _root_.GD.N0232.N0720.N1103.d018279 s (row.candidate j)


theorem d018295
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    (j : ℕ) :
    _root_.GD.N0232.N0720.N1103.d018293 s row j =
      _root_.GD.N0232.N0720.N1103.d018293 s row (j + 1) + _root_.GD.N0232.N0720.N1103.d018294 s row j := by
  unfold _root_.GD.N0232.N0720.N1103.d018293 _root_.GD.N0232.N0720.N1103.d018294
  ring

theorem d018296
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    (j : ℕ) :
    0 ≤ _root_.GD.N0232.N0720.N1103.d018293 s row j := by
  exact sub_nonneg.mpr
    (_root_.GD.N0232.N0720.N1103.d018280 s (row.candidate j))

theorem d018297
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    (j : ℕ) :
    0 ≤ _root_.GD.N0232.N0720.N1103.d018294 s row j := by
  exact sub_nonneg.mpr (row.reserve_step j)




theorem d018298
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018289 s) :
    Tendsto (_root_.GD.N0232.N0720.N1103.d018294 s row) atTop (nhds 0) := by
  exact _root_.GD.N0232.N0720.N1210.d018273
    (_root_.GD.N0232.N0720.N1103.d018293 s row) (_root_.GD.N0232.N0720.N1103.d018294 s row)
      (_root_.GD.N0232.N0720.N1103.d018295 s row)
      (_root_.GD.N0232.N0720.N1103.d018296 s row)
      (_root_.GD.N0232.N0720.N1103.d018297 s row)


noncomputable def d018289.d018299
    {s : _root_.GD.N0232.N0720.N1159.d014639 m n} (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    (N : ℕ) : _root_.GD.N0232.N0720.N1103.d018289 s where
  candidate := fun j ↦ row.candidate (j + N)
  reserve_step := by
    intro j
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      row.reserve_step (j + N)
  gap_tendsto_zero := by
    exact row.gap_tendsto_zero.comp (tendsto_add_atTop_nat N)





theorem d018300
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hcoercive : ∀ j,
      kappa * _root_.GD.N0232.N0720.N1122.d017962 m n
          (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)) ≤
        _root_.GD.N0232.N0720.N1103.d018294 s row j) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let width : ℕ → ℕ := fun j ↦ (row.candidate j).width
  let packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168 :=
    fun j ↦ (row.candidate j).packet
  let weight : ∀ j, Fin (width j) → ℝ :=
    fun j ↦ (row.candidate j).weight
  let hweight : ∀ j i, 0 ≤ weight j i :=
    fun j ↦ (row.candidate j).weight_nonneg
  apply _root_.GD.N0232.N0720.N1210.d018277
    (m := m) (n := n) (width := width) hm hn s hstrict
      packet weight hweight
      (C := _root_.GD.N0232.N0720.N1103.d018293 s row) (D := _root_.GD.N0232.N0720.N1103.d018294 s row)
      (kappa := kappa)
  · simpa only [width, packet, weight, _root_.GD.N0232.N0720.N1103.d018279,
      _root_.GD.N0232.N0720.N1103.d018293] using row.gap_tendsto_zero
  · exact _root_.GD.N0232.N0720.N1103.d018295 s row
  · exact _root_.GD.N0232.N0720.N1103.d018296 s row
  · exact _root_.GD.N0232.N0720.N1103.d018297 s row
  · exact hkappa
  · intro j
    simpa only [_root_.GD.N0232.N0720.N1130.d017075, width, packet, weight, hweight] using
      hcoercive j


theorem d018301
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hcoercive : ∀ᶠ j in atTop,
      kappa * _root_.GD.N0232.N0720.N1122.d017962 m n
          (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)) ≤
        _root_.GD.N0232.N0720.N1103.d018294 s row j) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hcoercive
  apply _root_.GD.N0232.N0720.N1103.d018300
    hm hn s hstrict (row.d018299 N) hkappa
  intro j
  have h := hN (j + N) (Nat.le_add_left N j)
  simpa only [_root_.GD.N0232.N0720.N1103.d018289.d018299, _root_.GD.N0232.N0720.N1103.d018294,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h



theorem d018302
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hcoercive : ∀ᶠ j in atTop,
      kappa * _root_.GD.N0232.N0720.N1122.d017962 m n
          (_root_.GD.N0232.N0720.N1130.d017075 m n
            ((_root_.GD.N0232.N0720.N1103.d018292 s).candidate j)) ≤
        _root_.GD.N0232.N0720.N1103.d018294 s (_root_.GD.N0232.N0720.N1103.d018292 s) j) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  exact
    _root_.GD.N0232.N0720.N1103.d018301
      hm hn s hstrict (_root_.GD.N0232.N0720.N1103.d018292 s)
        hkappa hcoercive



theorem d018303
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hcoercive : ∀ᶠ j in atTop,
      kappa * _root_.GD.N0232.N0720.N1122.d017962 2 2
          (_root_.GD.N0232.N0720.N1130.d017075 2 2
            ((_root_.GD.N0232.N0720.N1103.d018292
              _root_.GD.N0232.N0720.N1302.d018268).candidate j)) ≤
        _root_.GD.N0232.N0720.N1103.d018294 _root_.GD.N0232.N0720.N1302.d018268
          (_root_.GD.N0232.N0720.N1103.d018292
            _root_.GD.N0232.N0720.N1302.d018268) j) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  have hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1302.d018268.value
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) := by
    simpa only [_root_.GD.N0232.N0720.N1302.d018269] using
      _root_.GD.N0232.N0720.N1302.d018266
  exact _root_.GD.N0232.N0720.N1103.d018302
    (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1302.d018268 hstrict
      hkappa hcoercive

end

end N1103
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1103.d018291
#print axioms _root_.GD.N0232.N0720.N1103.d018295
#print axioms _root_.GD.N0232.N0720.N1103.d018298
#print axioms _root_.GD.N0232.N0720.N1103.d018301
#print axioms _root_.GD.N0232.N0720.N1103.d018302
#print axioms _root_.GD.N0232.N0720.N1103.d018303
