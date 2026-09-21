import GD.Module0606
import GD.Module0605
import GD.Module0610










open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0145

noncomputable section

open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135
open _root_.GD.N0115
open _root_.GD.N0111
open _root_.GD.N0132
open _root_.GD.N0146
open _root_.GD.N0113
open _root_.GD.N0113.d008651
open _root_.GD.N0131

variable {rhoQ : (ℚ × ℚ) → ℝ}
variable {D : _root_.GD.N0134.d006518} {k : ℕ}

theorem d014105
    (T : _root_.GD.N0113.d008651 rhoQ D k) (i : _root_.GD.N0113.d008651.d008696 T) :
    0 < T.d008653 i := by
  unfold _root_.GD.N0113.d008651.d008653
    _root_.GD.N0115.d006632.d006633 _root_.GD.N0115.d006628
  have hsum :
      0 < (T.boxes i).lower + (T.boxes i).upper :=
    add_pos (T.boxes i).lower_pos (T.d008703 i)
  positivity

theorem d014106
    (T : _root_.GD.N0113.d008651 rhoQ D k) :
    0 ≤ _root_.GD.N0113.d008667 T := by
  unfold _root_.GD.N0113.d008667
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem d014107
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    {gradientBound : ℚ} (hgradient : 0 ≤ gradientBound) :
    0 ≤ _root_.GD.N0113.d008668 T gradientBound := by
  unfold _root_.GD.N0113.d008668
  exact mul_nonneg
    (mul_nonneg T.width_pos.le hgradient)
    (_root_.GD.N0145.d014106 T)

theorem d014108
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    {carrierBound : ℚ} (hcarrier : 0 ≤ carrierBound) :
    0 ≤ _root_.GD.N0113.d008669 T carrierBound := by
  unfold _root_.GD.N0113.d008669
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (mul_nonneg (abs_nonneg _) (T.d008704 i))
    hcarrier

theorem d014109
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    {inversePower : ℚ} (hinverse : 0 ≤ inversePower) :
    0 ≤ _root_.GD.N0113.d008670 T inversePower := by
  unfold _root_.GD.N0113.d008670
  apply mul_nonneg
  · apply mul_nonneg
    · positivity
    · apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (T.d008703 i).le
  · exact hinverse

theorem d014110
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (carrier : ℝ × ℝ → ℝ)
    (hatomic : T.d008711 carrier < 0) :
    ∃ i : _root_.GD.N0113.d008651.d008696 T, T.d008699 i ≠ 0 := by
  by_contra h
  push Not at h
  have hz : T.d008711 carrier = 0 := by
    unfold _root_.GD.N0113.d008651.d008711
    apply Finset.sum_eq_zero
    intro i hi
    simp [h i]
  linarith

theorem d014111
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (carrier : ℝ × ℝ → ℝ)
    {inversePower : ℚ} (hinverse : 0 < inversePower)
    (hatomic : T.d008711 carrier < 0) :
    0 < _root_.GD.N0113.d008670 T inversePower := by
  obtain ⟨i0, hi0⟩ :=
    _root_.GD.N0145.d014110 T carrier hatomic
  have hterm_nonneg :
      ∀ i : _root_.GD.N0113.d008651.d008696 T,
        0 ≤ (T.d008652 i).weight ^ 2 * T.d008653 i ^ 2 *
          (T.boxes i).upper := by
    intro i
    exact mul_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (T.d008703 i).le
  have hterm_pos :
      0 < (T.d008652 i0).weight ^ 2 * T.d008653 i0 ^ 2 *
        (T.boxes i0).upper := by
    have hw : 0 < (T.d008652 i0).weight ^ 2 :=
      sq_pos_of_ne_zero (by simpa [_root_.GD.N0113.d008651.d008699] using hi0)
    have hm : 0 < T.d008653 i0 ^ 2 :=
      sq_pos_of_pos (_root_.GD.N0145.d014105 T i0)
    exact mul_pos (mul_pos hw hm) (T.d008703 i0)
  have hsum :
      0 <
        ∑ i : _root_.GD.N0113.d008651.d008696 T,
          (T.d008652 i).weight ^ 2 * T.d008653 i ^ 2 *
            (T.boxes i).upper := by
    apply Finset.sum_pos'
    · intro i hi
      exact hterm_nonneg i
    · exact ⟨i0, Finset.mem_univ _, hterm_pos⟩
  unfold _root_.GD.N0113.d008670
  exact mul_pos
    (mul_pos
      (div_pos (by norm_num)
        (mul_pos (by norm_num) (sq_pos_of_pos T.width_pos)))
      hsum)
    hinverse

theorem d014112
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    {eta carrierBound : ℚ}
    (heta : 0 ≤ eta) (hcarrier : 0 ≤ carrierBound)
    (hrelative : ∀ i, T.d008654 i ≤ eta) :
    _root_.GD.N0113.d008669 T carrierBound
      ≤ eta * carrierBound * _root_.GD.N0113.d008667 T := by
  unfold _root_.GD.N0113.d008669 _root_.GD.N0113.d008667
  calc
    (∑ i : _root_.GD.N0113.d008651.d008696 T,
        |(T.d008652 i).weight| * T.d008654 i * carrierBound)
        ≤
      ∑ i : _root_.GD.N0113.d008651.d008696 T,
        |(T.d008652 i).weight| * eta * carrierBound := by
          apply Finset.sum_le_sum
          intro i hi
          gcongr
          exact hrelative i
    _ = eta * carrierBound *
        ∑ i : _root_.GD.N0113.d008651.d008696 T, |(T.d008652 i).weight| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring





def d014113
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn)
    (T : _root_.GD.N0113.d008651 rhoQ (_root_.GD.N0134.d006543 m n hm hn) H.k)
    (gradientBound carrierBound inversePower : ℚ)
    (hgradient : 0 ≤ gradientBound)
    (hcarrier : 0 ≤ carrierBound)
    (hinverse : 0 < inversePower)
    (hsmear :
      _root_.GD.N0113.d008668 T gradientBound ≤ H.Cstar / 16)
    (hdensity :
      _root_.GD.N0113.d008669 T carrierBound ≤ H.Cstar / 16)
    (henergy :
      0 < _root_.GD.N0113.d008670 T inversePower) :
    _root_.GD.N0113.d008671 T where
  C := H.Cstar
  C_pos := H.Cstar_pos
  atomicError := 0
  atomicError_nonneg := le_rfl
  atomicValue := -H.Cstar
  atomic_upper := by norm_num
  atomic_error_budget := by
    have := H.Cstar_pos
    positivity
  gradientBound := gradientBound
  gradientBound_nonneg := hgradient
  carrierBound := carrierBound
  carrierBound_nonneg := hcarrier
  inversePower := inversePower
  inversePower_pos := hinverse
  smearValue := 0
  smear_bound := by
    simpa using _root_.GD.N0145.d014107 T hgradient
  smear_budget := hsmear
  densityValue := 0
  density_bound := by
    simpa using _root_.GD.N0145.d014108 T hcarrier
  density_budget := hdensity
  energyValue := 0
  energy_nonneg := le_rfl
  energy_bound := by
    simpa using _root_.GD.N0145.d014109 T hinverse.le
  energy_ceiling_pos := henergy

structure d014114
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) where
  emitted : _root_.GD.N0113.d008682 m n hm hn
  M : ℚ
  step : ℚ
  M_eq :
    M = _root_.GD.N0113.d008670 emitted.table emitted.ledger.inversePower
  step_eq : step = (emitted.ledger.C / 2) / M
  M_pos : 0 < M
  step_pos : 0 < step
  realized :
    ∀ e : ℝ, e ∈ Icc (0 : ℝ) 1 →
      _root_.GD.N0113.d008651.d008723 m n hm hn
  realized_emitted :
    ∀ e he, (realized e he).emitted = emitted
  realized_rho :
    ∀ e he,
      (realized e he).rho =
        _root_.GD.N0131.d008765 (_root_.GD.N0134.d006543 m n hm hn)
  realized_carrier :
    ∀ e he,
      (realized e he).carrier =
        _root_.GD.N0131.d008768
          (_root_.GD.N0134.d006543 m n hm hn) e
  realized_power :
    ∀ e he,
      (realized e he).power =
        _root_.GD.N0131.d008767 (_root_.GD.N0134.d006543 m n hm hn) e

namespace d014114






theorem d014115
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0145.d014114 m n hm hn) :
    ∀ (e : ℝ) (he : e ∈ Icc (0 : ℝ) 1),
      let A := U.realized e he
      A.d008724.trace =
          A.emitted.table.d008714 A.rho A.carrier
        ∧ A.d008724.energy =
          A.emitted.table.d008715 A.rho A.power
        ∧ A.d008724.trace
          ≤ -((A.emitted.ledger.C : ℝ) / 2)
        ∧ A.d008724.d008640 = U.step
        ∧ 2 * (U.step : ℝ) *
              A.emitted.table.d008714 A.rho A.carrier
            + (U.step : ℝ) ^ 2 *
              A.emitted.table.d008715 A.rho A.power
            ≤ -(((((U.emitted.ledger.C / 2 : ℚ) : ℝ) ^ 2)) /
              (U.M : ℝ))
        ∧ 2 * (U.step : ℝ) *
              A.emitted.table.d008714 A.rho A.carrier
            + (U.step : ℝ) ^ 2 *
              A.emitted.table.d008715 A.rho A.power < 0 := by
  intro e he
  let A := U.realized e he
  have hclose := A.d008727
  have hfixed : A.emitted = U.emitted := by
    simpa [A] using U.realized_emitted e he
  have hstepFixed :
      A.d008724.d008640 = U.step := by
    calc
      A.d008724.d008640 =
          (A.emitted.ledger.C / 2) /
            _root_.GD.N0113.d008670 A.emitted.table
              A.emitted.ledger.inversePower :=
        hclose.2.2.2.2.1
      _ = U.step := by
        rw [hfixed, U.step_eq, U.M_eq]
  have heffective :
      2 * (U.step : ℝ) *
            A.emitted.table.d008714 A.rho A.carrier
          + (U.step : ℝ) ^ 2 *
            A.emitted.table.d008715 A.rho A.power
        ≤ -(((((U.emitted.ledger.C / 2 : ℚ) : ℝ) ^ 2)) /
          (U.M : ℝ)) := by
    have hCfixed :
        A.emitted.ledger.C = U.emitted.ledger.C := by
      rw [hfixed]
    have hMfixed :
        U.M =
          _root_.GD.N0113.d008670 A.emitted.table
            A.emitted.ledger.inversePower := by
      calc
        U.M =
            _root_.GD.N0113.d008670 U.emitted.table
              U.emitted.ledger.inversePower := U.M_eq
        _ =
            _root_.GD.N0113.d008670 A.emitted.table
              A.emitted.ledger.inversePower := by rw [hfixed]
    rw [← hCfixed, hMfixed]
    simpa [hclose.1, hclose.2.1, hstepFixed] using
      hclose.2.2.2.2.2.1
  dsimp only
  refine ⟨hclose.1, hclose.2.1, hclose.2.2.1,
    hstepFixed, heffective, ?_⟩
  simpa [hstepFixed] using hclose.2.2.2.2.2.2

end d014114






theorem d014116
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (H : _root_.GD.N0113.d008646 m n hm hn)
    (T : _root_.GD.N0113.d008651
      (_root_.GD.N0131.d008766 (_root_.GD.N0134.d006543 m n hm hn))
      (_root_.GD.N0134.d006543 m n hm hn) H.k)
    (gradientBound carrierBound inversePower : ℚ)
    (hgradient : 0 ≤ gradientBound)
    (hcarrier : 0 ≤ carrierBound)
    (hinverse : 0 < inversePower)
    (hgradientMajorant :
      _root_.GD.N0111.d006160
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).d006524 : ℝ) 1 0
        +
      _root_.GD.N0111.d006160
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).d006524 : ℝ) 0 1
        ≤ (gradientBound : ℝ))
    (hcarrierMajorant :
      _root_.GD.N0111.d006160
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).d006524 : ℝ) 0 0
        ≤ (carrierBound : ℝ))
    (hinverseMajorant :
      _root_.GD.N0111.d006153
          (_root_.GD.N0111.d006159
            ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
            ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ))
          ((_root_.GD.N0134.d006543 m n hm hn).d006524 : ℝ) 0
        ≤ (inversePower : ℝ))
    (hatomic :
      ∀ e : ℝ, e ∈ Icc (0 : ℝ) 1 →
        T.d008711
            (_root_.GD.N0131.d008768
              (_root_.GD.N0134.d006543 m n hm hn) e)
          ≤ -(3 * (H.Cstar : ℝ) / 4))
    (hsmear :
      _root_.GD.N0113.d008668 T gradientBound ≤ H.Cstar / 16)
    (hdensity :
      _root_.GD.N0113.d008669 T carrierBound ≤ H.Cstar / 16) :
    Nonempty (_root_.GD.N0145.d014114 m n hm hn) := by
  let design := _root_.GD.N0134.d006543 m n hm hn
  have hatomic0 :
      T.d008711
          (_root_.GD.N0131.d008768 design 0) < 0 := by
    have h := hatomic 0 (by simp)
    have hC : (0 : ℝ) < H.Cstar := by
      exact_mod_cast H.Cstar_pos
    linarith
  have henergy :
      0 < _root_.GD.N0113.d008670 T inversePower :=
    _root_.GD.N0145.d014111 T
      (_root_.GD.N0131.d008768 design 0)
      hinverse hatomic0
  let ledger : _root_.GD.N0113.d008671 T :=
    _root_.GD.N0145.d014113 H T gradientBound carrierBound inversePower
      hgradient hcarrier hinverse hsmear hdensity henergy
  let emitted : _root_.GD.N0113.d008682 m n hm hn :=
    { header := H
      rho := _root_.GD.N0131.d008766 design
      table := T
      ledger := ledger
      C_matches_header := rfl }
  let M : ℚ := _root_.GD.N0113.d008670 T inversePower
  let step : ℚ := (H.Cstar / 2) / M
  have hstep : 0 < step := by
    dsimp [step, M]
    exact div_pos (div_pos H.Cstar_pos (by norm_num)) henergy
  let realized :
      ∀ e : ℝ, e ∈ Icc (0 : ℝ) 1 →
        _root_.GD.N0113.d008651.d008723 m n hm hn :=
    fun e he =>
      { emitted := emitted
        rho := _root_.GD.N0131.d008765 design
        carrier := _root_.GD.N0131.d008768 design e
        power := _root_.GD.N0131.d008767 design e
        envelope :=
          _root_.GD.N0131.d008798 T e he.1 he.2
            gradientBound carrierBound inversePower
            hgradientMajorant hcarrierMajorant hinverseMajorant
        atomic_margin := by
          simpa [design, emitted, ledger, _root_.GD.N0145.d014113] using
            hatomic e he }
  exact ⟨
    { emitted := emitted
      M := M
      step := step
      M_eq := rfl
      step_eq := rfl
      M_pos := henergy
      step_pos := hstep
      realized := realized
      realized_emitted := by intro e he; rfl
      realized_rho := by intro e he; rfl
      realized_carrier := by intro e he; rfl
      realized_power := by intro e he; rfl }⟩

end

end GD.N0145
