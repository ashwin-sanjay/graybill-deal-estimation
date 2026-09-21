import GD.Module1146





























open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1417

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1121
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1206
open _root_.GD.N0232.N0720.N1210
open _root_.GD.N0232.N0720.N1302
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}




theorem d018430
    (C D : ℕ → ℝ) (htower : ∀ j, C j = C (j + 1) + D j)
    (N : ℕ) :
    C 0 = C N + ∑ j ∈ Finset.range N, D j := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [ih, htower N, Finset.sum_range_succ]
      ring


theorem d018431
    (C D : ℕ → ℝ) (htower : ∀ j, C j = C (j + 1) + D j)
    (N M : ℕ) :
    C N = C (N + M) + ∑ j ∈ Finset.range M, D (N + j) := by
  have hshift : ∀ j,
      C (N + j) = C (N + (j + 1)) + D (N + j) := by
    intro j
    simpa only [Nat.add_assoc] using htower (N + j)
  simpa only [Nat.add_zero] using
    _root_.GD.N0232.N0720.N1417.d018430
      (fun j ↦ C (N + j)) (fun j ↦ D (N + j)) hshift M


theorem d018432
    (C D : ℕ → ℝ)
    (htower : ∀ j, C j = C (j + 1) + D j)
    (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j) :
    Summable D := by
  apply summable_of_sum_range_le hD
  intro N
  have htelescope := _root_.GD.N0232.N0720.N1417.d018430 C D htower N
  linarith [hC N]



theorem d018433
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018289 s) :
    Summable (_root_.GD.N0232.N0720.N1103.d018294 s row) := by
  exact _root_.GD.N0232.N0720.N1417.d018432
    (_root_.GD.N0232.N0720.N1103.d018293 s row) (_root_.GD.N0232.N0720.N1103.d018294 s row)
      (_root_.GD.N0232.N0720.N1103.d018295 s row)
      (_root_.GD.N0232.N0720.N1103.d018296 s row)
      (_root_.GD.N0232.N0720.N1103.d018297 s row)



theorem d018434
    (D observable : ℕ → ℝ)
    (hobservable : ∀ j, 0 ≤ observable j)
    (hDsum : Summable D) {kappa : ℝ} (hkappa : 0 < kappa)
    (hcoercive : ∀ᶠ j in atTop, kappa * observable j ≤ D j) :
    Summable observable := by
  apply (hDsum.div_const kappa).of_norm_bounded_eventually_nat
  filter_upwards [hcoercive] with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg (hobservable j)]
  exact (le_div_iff₀ hkappa).2 (by simpa only [mul_comm] using hj)




theorem d018435
    (C D observable : ℕ → ℝ)
    (htower : ∀ j, C j = C (j + 1) + D j)
    (hC : ∀ j, 0 ≤ C j)
    {kappa : ℝ} (_hkappa : 0 < kappa)
    (hcoercive : ∀ᶠ j in atTop, kappa * observable j ≤ D j) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ M,
      kappa * (∑ j ∈ Finset.range M, observable (N + j)) ≤ C N := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hcoercive
  refine ⟨N₀, fun N hN M ↦ ?_⟩
  have hterm : ∀ j ∈ Finset.range M,
      kappa * observable (N + j) ≤ D (N + j) := by
    intro j hj
    exact hN₀ (N + j) (hN.trans (Nat.le_add_right N j))
  have hsum :
      ∑ j ∈ Finset.range M, kappa * observable (N + j) ≤
        ∑ j ∈ Finset.range M, D (N + j) := by
    exact Finset.sum_le_sum hterm
  have htelescope := _root_.GD.N0232.N0720.N1417.d018431 C D htower N M
  rw [← Finset.mul_sum] at hsum
  linarith [hC (N + M)]



theorem d018436
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hproduction : ∀ᶠ j in atTop,
      kappa * _root_.GD.N0232.N0720.N1121.d018305 m n
          (row.candidate j) ≤
        _root_.GD.N0232.N0720.N1103.d018294 s row j) :
    Summable (fun j ↦
      _root_.GD.N0232.N0720.N1121.d018305 m n (row.candidate j)) := by
  exact _root_.GD.N0232.N0720.N1417.d018434
    (_root_.GD.N0232.N0720.N1103.d018294 s row)
    (fun j ↦ _root_.GD.N0232.N0720.N1121.d018305 m n
      (row.candidate j))
    (fun j ↦ _root_.GD.N0232.N0720.N1121.d018306
      m n (row.candidate j))
    (_root_.GD.N0232.N0720.N1417.d018433 s row) hkappa hproduction


theorem d018437
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hproduction : ∀ᶠ j in atTop,
      kappa * _root_.GD.N0232.N0720.N1121.d018305 m n
          (row.candidate j) ≤
        _root_.GD.N0232.N0720.N1103.d018294 s row j) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ M,
      kappa * (∑ j ∈ Finset.range M,
        _root_.GD.N0232.N0720.N1121.d018305 m n
          (row.candidate (N + j))) ≤ _root_.GD.N0232.N0720.N1103.d018293 s row N := by
  exact _root_.GD.N0232.N0720.N1417.d018435
    (_root_.GD.N0232.N0720.N1103.d018293 s row) (_root_.GD.N0232.N0720.N1103.d018294 s row)
    (fun j ↦ _root_.GD.N0232.N0720.N1121.d018305 m n
      (row.candidate j))
    (_root_.GD.N0232.N0720.N1103.d018295 s row)
    (_root_.GD.N0232.N0720.N1103.d018296 s row) hkappa hproduction



theorem d018438
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    (hnonsum : ¬ Summable (fun j ↦
      _root_.GD.N0232.N0720.N1121.d018305 m n (row.candidate j))) :
    ¬ ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ j in atTop,
        kappa * _root_.GD.N0232.N0720.N1121.d018305 m n
            (row.candidate j) ≤
          _root_.GD.N0232.N0720.N1103.d018294 s row j := by
  rintro ⟨kappa, hkappa, hproduction⟩
  exact hnonsum
    (_root_.GD.N0232.N0720.N1417.d018436
      s row hkappa hproduction)






theorem d018439
    (observable D : ℕ → ℝ)
    (hobservable : ∀ j, 0 ≤ observable j) (hD : ∀ j, 0 ≤ D j) :
    (∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ j in atTop, kappa * observable j ≤ D j) ∨
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ k, 0 < observable (φ k)) ∧
        Tendsto (fun k ↦ D (φ k) / observable (φ k))
          atTop (nhds 0) := by
  by_cases hcoercive :
      ∃ kappa : ℝ, 0 < kappa ∧
        ∀ᶠ j in atTop, kappa * observable j ≤ D j
  · exact Or.inl hcoercive
  · right
    have hfrequent : ∀ k : ℕ, ∃ᶠ j in atTop,
        D j < (1 / ((k : ℝ) + 1)) * observable j := by
      intro k
      by_contra hnot
      have heventual : ∀ᶠ j in atTop,
          (1 / ((k : ℝ) + 1)) * observable j ≤ D j := by
        have hnotfrequent : ¬ ∃ᶠ j in atTop,
            D j < (1 / ((k : ℝ) + 1)) * observable j := hnot
        filter_upwards [not_frequently.mp hnotfrequent] with j hj
        exact le_of_not_gt hj
      apply hcoercive
      exact ⟨1 / ((k : ℝ) + 1), by positivity, heventual⟩
    obtain ⟨φ, hφ, hsmall⟩ :=
      extraction_forall_of_frequently hfrequent
    have hobservablePos : ∀ k, 0 < observable (φ k) := by
      intro k
      have hepsilon : 0 < (1 / ((k : ℝ) + 1)) := by positivity
      have hsmallk := hsmall k
      nlinarith [hD (φ k), hobservable (φ k)]
    refine ⟨φ, hφ, hobservablePos, ?_⟩
    let epsilon : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
    have hepsilonZero : Tendsto epsilon atTop (nhds 0) := by
      simpa only [epsilon, Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact squeeze_zero
      (fun k ↦ div_nonneg (hD (φ k)) (hobservable (φ k)))
      (fun k ↦ by
        apply (div_le_iff₀ (hobservablePos k)).2
        simpa only [epsilon] using (hsmall k).le)
      hepsilonZero




theorem d018440
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018289 s) :
    (∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ j in atTop,
        kappa * _root_.GD.N0232.N0720.N1121.d018305 m n
            (row.candidate j) ≤ _root_.GD.N0232.N0720.N1103.d018294 s row j) ∨
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ k, 0 < _root_.GD.N0232.N0720.N1121.d018305 m n
          (row.candidate (φ k))) ∧
        Tendsto
          (fun k ↦ _root_.GD.N0232.N0720.N1103.d018294 s row (φ k) /
            _root_.GD.N0232.N0720.N1121.d018305 m n
              (row.candidate (φ k))) atTop (nhds 0) := by
  exact _root_.GD.N0232.N0720.N1417.d018439
    (fun j ↦ _root_.GD.N0232.N0720.N1121.d018305 m n
      (row.candidate j))
    (_root_.GD.N0232.N0720.N1103.d018294 s row)
    (fun j ↦ _root_.GD.N0232.N0720.N1121.d018306
      m n (row.candidate j))
    (_root_.GD.N0232.N0720.N1103.d018297 s row)






theorem d018441
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    (hperspective : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1121.d018305 m n
        (row.candidate j)) atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
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
  have henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
    apply _root_.GD.N0232.N0720.N1210.d018275
      s packet weight hweight htight
      (fun j ↦ _root_.GD.N0232.N0720.N1121.d018305 m n
        (row.candidate j)) hperspective (kappa := 1) (by norm_num)
    intro j
    simpa only [one_mul, _root_.GD.N0232.N0720.N1130.d017075, width, packet, weight,
      hweight] using
      (_root_.GD.N0232.N0720.N1121.d018307
        m n (row.candidate j))
  apply
    (_root_.GD.N0232.N0720.N1482.d015173
      (m := m) (n := n) hm hn).2
  exact ⟨s, hstrict,
    (_root_.GD.N0232.N0720.N1477.d015755
      (m := m) (n := n) s).2 henergy⟩



def d018442 : Prop :=
  ∃ row : _root_.GD.N0232.N0720.N1103.d018289 _root_.GD.N0232.N0720.N1302.d018268,
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1121.d018305 2 2
        (row.candidate j)) atTop (nhds 0)



theorem d018443
    (h : _root_.GD.N0232.N0720.N1417.d018442) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  rcases h with ⟨row, hperspective⟩
  have hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1302.d018268.value
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) := by
    simpa only [_root_.GD.N0232.N0720.N1302.d018269] using
      _root_.GD.N0232.N0720.N1302.d018266
  exact _root_.GD.N0232.N0720.N1417.d018441
    (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1302.d018268 hstrict row
      hperspective



theorem d018444
    (h : _root_.GD.N0232.N0720.N1206.d018420) :
    _root_.GD.N0232.N0720.N1417.d018442 := by
  rcases h with ⟨row, kappa, hkappa, hproduction⟩
  refine ⟨row, ?_⟩
  exact
    (_root_.GD.N0232.N0720.N1417.d018436
      _root_.GD.N0232.N0720.N1302.d018268 row hkappa hproduction).tendsto_atTop_zero





theorem d018445
    (D observable : ℕ → ℝ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hD : ∀ j, 0 ≤ D j) (hDzero : Tendsto D atTop (nhds 0))
    (hobservable : ∀ j, 0 ≤ observable j)
    (hcoercive : ∀ᶠ j in atTop,
      kappa * observable j ^ 2 ≤ D j) :
    Tendsto observable atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hDzero ⊢
  intro epsilon hepsilon
  obtain ⟨ND, hND⟩ := hDzero (kappa * epsilon ^ 2)
    (mul_pos hkappa (sq_pos_of_pos hepsilon))
  obtain ⟨NC, hNC⟩ := eventually_atTop.1 hcoercive
  refine ⟨max ND NC, fun j hj ↦ ?_⟩
  have hjD : ND ≤ j := (le_max_left ND NC).trans hj
  have hjC : NC ≤ j := (le_max_right ND NC).trans hj
  have hDsmall := hND j hjD
  have hquadratic := hNC j hjC
  rw [Real.dist_eq] at hDsmall ⊢
  simp only [sub_zero] at hDsmall ⊢
  have hupper : D j < kappa * epsilon ^ 2 := by
    simpa [abs_of_nonneg (hD j)] using hDsmall
  rw [abs_of_nonneg (hobservable j)]
  by_contra hnot
  have heps_le : epsilon ≤ observable j := le_of_not_gt hnot
  have hsquare : epsilon ^ 2 ≤ observable j ^ 2 := by
    exact (sq_le_sq₀ (le_of_lt hepsilon) (hobservable j)).2 heps_le
  have hscaled := mul_le_mul_of_nonneg_left hsquare hkappa.le
  exact (not_lt_of_ge hscaled) (hquadratic.trans_lt hupper)



theorem d018446
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hproduction : ∀ᶠ j in atTop,
      kappa * (_root_.GD.N0232.N0720.N1121.d018305 m n
          (row.candidate j)) ^ 2 ≤
        _root_.GD.N0232.N0720.N1103.d018294 s row j) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1121.d018305 m n
        (row.candidate j)) atTop (nhds 0) := by
  exact _root_.GD.N0232.N0720.N1417.d018445
    (_root_.GD.N0232.N0720.N1103.d018294 s row)
    (fun j ↦ _root_.GD.N0232.N0720.N1121.d018305 m n
      (row.candidate j)) hkappa
    (_root_.GD.N0232.N0720.N1103.d018297 s row)
    (_root_.GD.N0232.N0720.N1103.d018298 s row)
    (fun j ↦ _root_.GD.N0232.N0720.N1121.d018306
      m n (row.candidate j))
    hproduction



theorem d018447
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (row : _root_.GD.N0232.N0720.N1103.d018289 s)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hproduction : ∀ᶠ j in atTop,
      kappa * (_root_.GD.N0232.N0720.N1121.d018305 m n
          (row.candidate j)) ^ 2 ≤
        _root_.GD.N0232.N0720.N1103.d018294 s row j) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1417.d018441
    hm hn s hstrict row
  exact _root_.GD.N0232.N0720.N1417.d018446
    s row hkappa hproduction




def d018448 : Prop :=
  ∃ row : _root_.GD.N0232.N0720.N1103.d018289 _root_.GD.N0232.N0720.N1302.d018268,
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ j in atTop,
        kappa * (_root_.GD.N0232.N0720.N1121.d018305 2 2
            (row.candidate j)) ^ 2 ≤
          _root_.GD.N0232.N0720.N1103.d018294 _root_.GD.N0232.N0720.N1302.d018268 row j

theorem d018449
    (h : _root_.GD.N0232.N0720.N1417.d018448) :
    _root_.GD.N0232.N0720.N1417.d018442 := by
  rcases h with ⟨row, kappa, hkappa, hproduction⟩
  exact ⟨row,
    _root_.GD.N0232.N0720.N1417.d018446
      _root_.GD.N0232.N0720.N1302.d018268 row hkappa hproduction⟩


theorem d018450
    (h : _root_.GD.N0232.N0720.N1417.d018448) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  exact _root_.GD.N0232.N0720.N1417.d018443
    (_root_.GD.N0232.N0720.N1417.d018449 h)




def d018451 (j : ℕ) : ℝ :=
  1 / ((j + 1 : ℕ) : ℝ)


def d018452 (j : ℕ) : ℝ :=
  1 / (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ))



def d018453 (j : ℕ) : ℝ :=
  1 / ((j + 2 : ℕ) : ℝ)

theorem d018454 (j : ℕ) :
    _root_.GD.N0232.N0720.N1417.d018451 j = _root_.GD.N0232.N0720.N1417.d018451 (j + 1) + _root_.GD.N0232.N0720.N1417.d018452 j := by
  unfold _root_.GD.N0232.N0720.N1417.d018451 _root_.GD.N0232.N0720.N1417.d018452
  push_cast
  field_simp
  ring

theorem d018455 (j : ℕ) : 0 ≤ _root_.GD.N0232.N0720.N1417.d018451 j := by
  unfold _root_.GD.N0232.N0720.N1417.d018451
  positivity

theorem d018456 (j : ℕ) :
    0 ≤ _root_.GD.N0232.N0720.N1417.d018452 j := by
  unfold _root_.GD.N0232.N0720.N1417.d018452
  positivity

theorem d018457 (j : ℕ) :
    0 ≤ _root_.GD.N0232.N0720.N1417.d018453 j := by
  unfold _root_.GD.N0232.N0720.N1417.d018453
  positivity


theorem d018458 (j : ℕ) :
    _root_.GD.N0232.N0720.N1417.d018453 j ^ 2 ≤ _root_.GD.N0232.N0720.N1417.d018452 j := by
  have hfirst : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hsecond : (0 : ℝ) < ((j + 2 : ℕ) : ℝ) := by positivity
  have horder : ((j + 1 : ℕ) : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : j + 1 ≤ j + 2)
  have hdenom :
      ((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ) ≤
        ((j + 2 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right horder hsecond.le
  have hinv := one_div_le_one_div_of_le
    (mul_pos hfirst hsecond) hdenom
  calc
    _root_.GD.N0232.N0720.N1417.d018453 j ^ 2 =
        1 / (((j + 2 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) := by
      unfold _root_.GD.N0232.N0720.N1417.d018453
      ring
    _ ≤ 1 / (((j + 1 : ℕ) : ℝ) * ((j + 2 : ℕ) : ℝ)) := hinv
    _ = _root_.GD.N0232.N0720.N1417.d018452 j := rfl

theorem d018459 :
    ¬ Summable _root_.GD.N0232.N0720.N1417.d018453 := by
  intro hsummable
  apply Real.not_summable_one_div_natCast
  change Summable (fun j : ℕ ↦ 1 / ((j + 2 : ℕ) : ℝ)) at hsummable
  apply (summable_nat_add_iff
    (f := fun j : ℕ ↦ 1 / (j : ℝ)) 2).1
  exact hsummable



theorem d018460 :
    ¬ ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ j in atTop,
        kappa * _root_.GD.N0232.N0720.N1417.d018453 j ≤ _root_.GD.N0232.N0720.N1417.d018452 j := by
  rintro ⟨kappa, hkappa, hcoercive⟩
  have hperspectiveSum : Summable _root_.GD.N0232.N0720.N1417.d018453 :=
    _root_.GD.N0232.N0720.N1417.d018434
      _root_.GD.N0232.N0720.N1417.d018452 _root_.GD.N0232.N0720.N1417.d018453 _root_.GD.N0232.N0720.N1417.d018457
      (_root_.GD.N0232.N0720.N1417.d018432
        _root_.GD.N0232.N0720.N1417.d018451 _root_.GD.N0232.N0720.N1417.d018452
        _root_.GD.N0232.N0720.N1417.d018454 _root_.GD.N0232.N0720.N1417.d018455
        _root_.GD.N0232.N0720.N1417.d018456)
      hkappa hcoercive
  exact _root_.GD.N0232.N0720.N1417.d018459 hperspectiveSum




theorem d018461 :
    (∀ j, _root_.GD.N0232.N0720.N1417.d018451 j =
      _root_.GD.N0232.N0720.N1417.d018451 (j + 1) + _root_.GD.N0232.N0720.N1417.d018452 j) ∧
    (∀ j, 0 ≤ _root_.GD.N0232.N0720.N1417.d018451 j) ∧
    (∀ j, 0 ≤ _root_.GD.N0232.N0720.N1417.d018452 j) ∧
    (∀ j, 0 ≤ _root_.GD.N0232.N0720.N1417.d018453 j) ∧
    (∀ j, _root_.GD.N0232.N0720.N1417.d018453 j ^ 2 ≤ _root_.GD.N0232.N0720.N1417.d018452 j) ∧
    Tendsto _root_.GD.N0232.N0720.N1417.d018452 atTop (nhds 0) ∧
    ¬ Summable _root_.GD.N0232.N0720.N1417.d018453 ∧
    ¬ ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ j in atTop,
        kappa * _root_.GD.N0232.N0720.N1417.d018453 j ≤ _root_.GD.N0232.N0720.N1417.d018452 j := by
  refine ⟨_root_.GD.N0232.N0720.N1417.d018454, _root_.GD.N0232.N0720.N1417.d018455,
    _root_.GD.N0232.N0720.N1417.d018456, _root_.GD.N0232.N0720.N1417.d018457,
    _root_.GD.N0232.N0720.N1417.d018458, ?_, _root_.GD.N0232.N0720.N1417.d018459,
    _root_.GD.N0232.N0720.N1417.d018460⟩
  exact _root_.GD.N0232.N0720.N1210.d018273
    _root_.GD.N0232.N0720.N1417.d018451 _root_.GD.N0232.N0720.N1417.d018452 _root_.GD.N0232.N0720.N1417.d018454
      _root_.GD.N0232.N0720.N1417.d018455 _root_.GD.N0232.N0720.N1417.d018456

end

end N1417
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1417.d018433
#print axioms _root_.GD.N0232.N0720.N1417.d018436
#print axioms _root_.GD.N0232.N0720.N1417.d018437
#print axioms _root_.GD.N0232.N0720.N1417.d018440
#print axioms _root_.GD.N0232.N0720.N1417.d018441
#print axioms _root_.GD.N0232.N0720.N1417.d018443
#print axioms _root_.GD.N0232.N0720.N1417.d018444
#print axioms _root_.GD.N0232.N0720.N1417.d018446
#print axioms _root_.GD.N0232.N0720.N1417.d018450
#print axioms _root_.GD.N0232.N0720.N1417.d018461
