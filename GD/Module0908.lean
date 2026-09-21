import GD.Module0906









set_option maxHeartbeats 1200000

open MeasureTheory Set

namespace GD.N0145

noncomputable section

open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135
open _root_.GD.N0111
open _root_.GD.N0118
open _root_.GD.N0132
open _root_.GD.N0146
open _root_.GD.N0113
open _root_.GD.N0113.d008651
open _root_.GD.N0131
open _root_.GD.N0116
open _root_.GD.N0147

variable {rhoQ : (ℚ × ℚ) → ℝ}
variable {D : _root_.GD.N0134.d006518} {k : ℕ}

theorem d014120 (D : _root_.GD.N0134.d006518) :
    (D.d006524 : ℝ) =
      _root_.GD.N0116.d006509 (D.alpha : ℝ) (D.beta : ℝ) := by
  simp [_root_.GD.N0134.d006518.d006524, _root_.GD.N0134.d006518.d006519,
    _root_.GD.N0116.d006509]

theorem d014121
    (D : _root_.GD.N0134.d006518) (e : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0111.d006136 (D.d006522 : ℝ)
        ((D.beta : ℝ) - ((D.d006519 : ℚ) : ℝ) * e)
        (e * (1 - e) / 2)
        (p.1 - (D.d006520 : ℝ)) p.2 =
      (D.alpha : ℝ) * e * (1 - p.1)
        + (D.beta : ℝ) * (1 - e) * p.1
        + p.2 * e * (1 - e) / 2 := by
  have hnu :
      (D.alpha : ℝ) + (D.beta : ℝ) ≠ 0 := by
    exact ne_of_gt (add_pos
      (by exact_mod_cast D.alpha_pos)
      (by exact_mod_cast D.beta_pos))
  unfold _root_.GD.N0111.d006136 _root_.GD.N0134.d006518.d006522 _root_.GD.N0134.d006518.d006520
    _root_.GD.N0134.d006518.d006519
  push_cast
  field_simp [hnu]
  ring

theorem d014122
    (D : _root_.GD.N0134.d006518) (e : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0131.d008765 D p * _root_.GD.N0131.d008767 D e p =
      _root_.GD.N0120.d008811
        (D.alpha : ℝ) (D.beta : ℝ) e p := by
  unfold _root_.GD.N0131.d008765 _root_.GD.N0131.d008767 _root_.GD.N0120.d008811
  rw [_root_.GD.N0145.d014121,
    _root_.GD.N0145.d014120]

theorem d014123
    (D : _root_.GD.N0134.d006518) (e : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0131.d008768 D e p =
      (p.1 - e) * _root_.GD.N0131.d008767 D e p := by
  have hnu :
      (D.alpha : ℝ) + (D.beta : ℝ) ≠ 0 := by
    exact ne_of_gt (add_pos
      (by exact_mod_cast D.alpha_pos)
      (by exact_mod_cast D.beta_pos))
  have hnum :
      (D.alpha : ℝ) /
          ((D.alpha : ℝ) + (D.beta : ℝ)) - e
        + (p.1 - (D.d006520 : ℝ)) =
      p.1 - e := by
    unfold _root_.GD.N0134.d006518.d006520 _root_.GD.N0134.d006518.d006519
    push_cast
    field_simp [hnu]
    ring
  unfold _root_.GD.N0131.d008768
    _root_.GD.N0113.d008651.d008730
    _root_.GD.N0132.d006445
    _root_.GD.N0111.d006137
  unfold _root_.GD.N0131.d008767 _root_.GD.N0134.d006518.d006522 _root_.GD.N0134.d006518.d006519
  push_cast
  rw [hnum]

theorem d014124
    (D : _root_.GD.N0134.d006518) (e : ℝ) (q : ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) :
    _root_.GD.N0131.d008765 D p * q p *
        _root_.GD.N0131.d008768 D e p =
      ((p.1 - e) * q p) *
        _root_.GD.N0120.d008811
          (D.alpha : ℝ) (D.beta : ℝ) e p := by
  rw [_root_.GD.N0145.d014123,
    ← _root_.GD.N0145.d014122]
  ring

theorem d014125
    (D : _root_.GD.N0134.d006518) (e : ℝ) (q : ℝ × ℝ → ℝ)
    (p : ℝ × ℝ) :
    (_root_.GD.N0131.d008765 D p * _root_.GD.N0131.d008767 D e p) * q p ^ 2 =
      q p ^ 2 *
        _root_.GD.N0120.d008811
          (D.alpha : ℝ) (D.beta : ℝ) e p := by
  rw [_root_.GD.N0145.d014122]
  ring

theorem d014126
    {rhoQ : (ℚ × ℚ) → ℝ}
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (p : ℝ × ℝ)
    (hp : p ∉ (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ))) :
    T.d008659 p = 0 := by
  by_contra h
  obtain ⟨i, hi⟩ := T.d008721 p h
  have hgeo := _root_.GD.N0131.d008781 T i p hi
  apply hp
  exact ⟨⟨hgeo.2.1, hgeo.2.2.1⟩, hgeo.2.2.2⟩

theorem d014127
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (e : ℝ)
    (gradientBound carrierBound inversePower : ℚ)
    (hgradient : 0 ≤ gradientBound)
    (hcarrier : 0 ≤ carrierBound)
    (E : _root_.GD.N0113.d008651.d008706 T
      (_root_.GD.N0131.d008765 D)
      (_root_.GD.N0131.d008768 D e)
      (_root_.GD.N0131.d008767 D e)
      gradientBound carrierBound inversePower) :
    Integrable
      (fun p =>
        _root_.GD.N0131.d008765 D p * T.d008659 p *
          _root_.GD.N0131.d008768 D e p)
      (volume.prod volume) := by
  have hatomInt :
      ∀ i : _root_.GD.N0113.d008651.d008696 T,
        Integrable
          (fun p =>
            _root_.GD.N0131.d008765 D p *
              (T.d008699 i * T.d008700 i *
                T.d008697 i p) *
              _root_.GD.N0131.d008768 D e p)
          (volume.prod volume) := by
    intro i
    let base : ℝ × ℝ → ℝ :=
      fun p =>
        (T.d008699 i *
          _root_.GD.N0131.d008768 D e
            (T.d008698 i)) * T.d008697 i p
    let smear : ℝ × ℝ → ℝ :=
      fun p => T.d008699 i * (T.d008697 i p *
        (_root_.GD.N0131.d008768 D e p -
          _root_.GD.N0131.d008768 D e
            (T.d008698 i)))
    let density : ℝ × ℝ → ℝ :=
      fun p => T.d008699 i * (T.d008697 i p *
        ((T.d008700 i * _root_.GD.N0131.d008765 D p - 1) *
          _root_.GD.N0131.d008768 D e p))
    have hb : Integrable base (volume.prod volume) := by
      simpa [base, _root_.GD.N0113.d008651.d008697] using
        (_root_.GD.N0118.d008591
          ((T.d008652 i).ell : ℝ) ((T.d008652 i).f : ℝ)
          (T.width : ℝ)).const_mul
            (T.d008699 i *
              _root_.GD.N0131.d008768 D e
                (T.d008698 i))
    have hgR : (0 : ℝ) ≤ (gradientBound : ℝ) := by
      exact_mod_cast hgradient
    have hwR : (0 : ℝ) ≤ (T.width : ℝ) := by
      exact_mod_cast T.width_pos.le
    have hs0 :
        Integrable
          (fun p => T.d008697 i p *
            (_root_.GD.N0131.d008768 D e p -
              _root_.GD.N0131.d008768 D e
                (T.d008698 i)))
          (volume.prod volume) :=
      T.d008709 i _ _
        (mul_nonneg hgR hwR)
        (E.measurable_carrier.sub measurable_const)
        (E.carrier_lipschitz i)
    have hs : Integrable smear (volume.prod volume) := by
      simpa [smear] using hs0.const_mul (T.d008699 i)
    have hκ : (0 : ℝ) ≤ (T.d008654 i : ℝ) := by
      exact_mod_cast T.d008704 i
    have hd0 :
        Integrable
          (fun p => T.d008697 i p *
            ((T.d008700 i * _root_.GD.N0131.d008765 D p - 1) *
              _root_.GD.N0131.d008768 D e p))
          (volume.prod volume) :=
      T.d008709 i _ _
        (mul_nonneg hκ
          (show (0 : ℝ) ≤ (carrierBound : ℝ) by
            exact_mod_cast hcarrier))
        (((measurable_const.mul E.measurable_rho).sub
          measurable_const).mul E.measurable_carrier)
        (by
          intro p hp
          rw [abs_mul]
          exact mul_le_mul
            (T.d008705 (_root_.GD.N0131.d008765 D) i p
              (E.density_bounds i p hp).1
              (E.density_bounds i p hp).2)
            (E.carrier_abs i p hp) (abs_nonneg _) hκ)
    have hd : Integrable density (volume.prod volume) := by
      simpa [density] using hd0.const_mul (T.d008699 i)
    have hsum :
        Integrable (fun p => base p + smear p + density p)
          (volume.prod volume) :=
      (hb.add hs).add hd
    apply hsum.congr
    filter_upwards [] with p
    dsimp [base, smear, density]
    ring
  have hrewrite :
      (fun p =>
        _root_.GD.N0131.d008765 D p * T.d008659 p *
          _root_.GD.N0131.d008768 D e p) =
        fun p => ∑ i : _root_.GD.N0113.d008651.d008696 T,
          _root_.GD.N0131.d008765 D p *
            (T.d008699 i * T.d008700 i *
              T.d008697 i p) *
            _root_.GD.N0131.d008768 D e p := by
    funext p
    rw [T.d008701, Finset.mul_sum,
      Finset.sum_mul]
  rw [hrewrite]
  exact integrable_finset_sum Finset.univ
    (fun i hi => hatomInt i)

theorem d014128
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (e : ℝ)
    (gradientBound carrierBound inversePower : ℚ)
    (hinverse : 0 ≤ inversePower)
    (E : _root_.GD.N0113.d008651.d008706 T
      (_root_.GD.N0131.d008765 D)
      (_root_.GD.N0131.d008768 D e)
      (_root_.GD.N0131.d008767 D e)
      gradientBound carrierBound inversePower) :
    Integrable
      (fun p =>
        (_root_.GD.N0131.d008765 D p * _root_.GD.N0131.d008767 D e p) *
          T.d008659 p ^ 2)
      (volume.prod volume) := by
  let f : _root_.GD.N0113.d008651.d008696 T → (ℝ × ℝ) → ℝ :=
    fun i p =>
      (T.d008699 i * T.d008700 i) * T.d008697 i p
  have hatomInt :
      ∀ i : _root_.GD.N0113.d008651.d008696 T,
        Integrable
          (fun p =>
            (_root_.GD.N0131.d008765 D p * _root_.GD.N0131.d008767 D e p) *
              f i p ^ 2)
          (volume.prod volume) := by
    intro i
    exact T.d008710
      (_root_.GD.N0131.d008765 D) (_root_.GD.N0131.d008767 D e) i
      (((T.boxes i).upper * inversePower : ℚ) : ℝ)
      (by exact_mod_cast
        (mul_nonneg (T.d008703 i).le hinverse))
      E.measurable_rho E.measurable_power
      (E.d008708 hinverse i)
  have hdisjoint :
      ∀ i ∈ (Finset.univ : Finset (_root_.GD.N0113.d008651.d008696 T)),
        ∀ j ∈ (Finset.univ : Finset (_root_.GD.N0113.d008651.d008696 T)),
          i ≠ j → ∀ p, f i p * f j p = 0 := by
    intro i hi j hj hij p
    have ht := E.tents_pairwise_disjoint i j hij p
    dsimp [f]
    calc
      ((T.d008699 i * T.d008700 i) * T.d008697 i p) *
          ((T.d008699 j * T.d008700 j) * T.d008697 j p)
          =
        ((T.d008699 i * T.d008700 i) *
          (T.d008699 j * T.d008700 j)) *
          (T.d008697 i p * T.d008697 j p) := by ring
      _ = 0 := by rw [ht, mul_zero]
  have hsquare :
      ∀ p, (∑ i : _root_.GD.N0113.d008651.d008696 T, f i p) ^ 2 =
        ∑ i : _root_.GD.N0113.d008651.d008696 T, f i p ^ 2 :=
    _root_.GD.N0147.d008609
      (Finset.univ : Finset (_root_.GD.N0113.d008651.d008696 T)) f hdisjoint
  have hrewrite :
      (fun p =>
        (_root_.GD.N0131.d008765 D p * _root_.GD.N0131.d008767 D e p) *
          T.d008659 p ^ 2) =
        fun p => ∑ i : _root_.GD.N0113.d008651.d008696 T,
          (_root_.GD.N0131.d008765 D p * _root_.GD.N0131.d008767 D e p) *
            f i p ^ 2 := by
    funext p
    rw [T.d008701]
    change
      (_root_.GD.N0131.d008765 D p * _root_.GD.N0131.d008767 D e p) *
          (∑ i : _root_.GD.N0113.d008651.d008696 T, f i p) ^ 2 =
        ∑ i : _root_.GD.N0113.d008651.d008696 T,
          (_root_.GD.N0131.d008765 D p * _root_.GD.N0131.d008767 D e p) * f i p ^ 2
    rw [hsquare p, Finset.mul_sum]
  rw [hrewrite]
  exact integrable_finset_sum Finset.univ
    (fun i hi => hatomInt i)





theorem d014129
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (e : ℝ)
    (gradientBound carrierBound inversePower : ℚ)
    (hgradient : 0 ≤ gradientBound)
    (hcarrier : 0 ≤ carrierBound)
    (E : _root_.GD.N0113.d008651.d008706 T
      (_root_.GD.N0131.d008765 D)
      (_root_.GD.N0131.d008768 D e)
      (_root_.GD.N0131.d008767 D e)
      gradientBound carrierBound inversePower) :
    _root_.GD.N0120.d008816
        (D.alpha : ℝ) (D.beta : ℝ) e T.d008659 =
      T.d008714
        (_root_.GD.N0131.d008765 D)
        (_root_.GD.N0131.d008768 D e) := by
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)
  let f : ℝ × ℝ → ℝ := fun p =>
    _root_.GD.N0131.d008765 D p * T.d008659 p *
      _root_.GD.N0131.d008768 D e p
  have hf : Integrable f (volume.prod volume) :=
    _root_.GD.N0145.d014127 T e gradientBound carrierBound inversePower
      hgradient hcarrier E
  have hzero : ∀ p ∉ S, f p = 0 := by
    intro p hp
    have hc := _root_.GD.N0145.d014126 T p
      (by simpa [S] using hp)
    dsimp [f]
    rw [hc]
    ring
  calc
    _root_.GD.N0120.d008816
        (D.alpha : ℝ) (D.beta : ℝ) e T.d008659
        =
      ∫ L : ℝ in Ioo 0 1,
        ∫ F : ℝ in Ioi 0, f (L, F) := by
          unfold _root_.GD.N0120.d008816
            _root_.GD.N0120.d008812
          apply setIntegral_congr_fun measurableSet_Ioo
          intro L hL
          apply setIntegral_congr_fun measurableSet_Ioi
          intro F hF
          exact (_root_.GD.N0145.d014124
            D e T.d008659 (L, F)).symm
    _ = ∫ p : ℝ × ℝ in S, f p := by
      change
        (∫ L : ℝ in Ioo 0 1,
          ∫ F : ℝ in Ioi 0, f (L, F)) =
            ∫ p : ℝ × ℝ in Ioo 0 1 ×ˢ Ioi 0, f p
      exact (MeasureTheory.setIntegral_prod f hf.integrableOn).symm
    _ = ∫ p : ℝ × ℝ, f p := by
      exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    _ = T.d008714
        (_root_.GD.N0131.d008765 D)
        (_root_.GD.N0131.d008768 D e) := by
      rfl





theorem d014130
    (T : _root_.GD.N0113.d008651 rhoQ D k)
    (e : ℝ)
    (gradientBound carrierBound inversePower : ℚ)
    (hinverse : 0 ≤ inversePower)
    (E : _root_.GD.N0113.d008651.d008706 T
      (_root_.GD.N0131.d008765 D)
      (_root_.GD.N0131.d008768 D e)
      (_root_.GD.N0131.d008767 D e)
      gradientBound carrierBound inversePower) :
    _root_.GD.N0120.d008817
        (D.alpha : ℝ) (D.beta : ℝ) e T.d008659 =
      T.d008715 (_root_.GD.N0131.d008765 D) (_root_.GD.N0131.d008767 D e) := by
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)
  let f : ℝ × ℝ → ℝ := fun p =>
    (_root_.GD.N0131.d008765 D p * _root_.GD.N0131.d008767 D e p) *
      T.d008659 p ^ 2
  have hf : Integrable f (volume.prod volume) :=
    _root_.GD.N0145.d014128 T e gradientBound carrierBound inversePower
      hinverse E
  have hzero : ∀ p ∉ S, f p = 0 := by
    intro p hp
    have hc := _root_.GD.N0145.d014126 T p
      (by simpa [S] using hp)
    dsimp [f]
    rw [hc]
    ring
  calc
    _root_.GD.N0120.d008817
        (D.alpha : ℝ) (D.beta : ℝ) e T.d008659
        =
      ∫ L : ℝ in Ioo 0 1,
        ∫ F : ℝ in Ioi 0, f (L, F) := by
          unfold _root_.GD.N0120.d008817
            _root_.GD.N0120.d008812
          apply setIntegral_congr_fun measurableSet_Ioo
          intro L hL
          apply setIntegral_congr_fun measurableSet_Ioi
          intro F hF
          exact (_root_.GD.N0145.d014125
            D e T.d008659 (L, F)).symm
    _ = ∫ p : ℝ × ℝ in S, f p := by
      change
        (∫ L : ℝ in Ioo 0 1,
          ∫ F : ℝ in Ioi 0, f (L, F)) =
            ∫ p : ℝ × ℝ in Ioo 0 1 ×ˢ Ioi 0, f p
      exact (MeasureTheory.setIntegral_prod f hf.integrableOn).symm
    _ = ∫ p : ℝ × ℝ, f p := by
      exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    _ = T.d008715 (_root_.GD.N0131.d008765 D) (_root_.GD.N0131.d008767 D e) := by
      rfl

namespace d014114






theorem d014131
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0145.d014114 m n hm hn)
    (e : ℝ) (he : e ∈ Icc (0 : ℝ) 1) :
    let A := U.realized e he
    _root_.GD.N0120.d008816
        ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
        ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
        e A.emitted.table.d008659 =
      A.emitted.table.d008714 A.rho A.carrier
      ∧
    _root_.GD.N0120.d008817
        ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
        ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
        e A.emitted.table.d008659 =
      A.emitted.table.d008715 A.rho A.power := by
  let A := U.realized e he
  let D := _root_.GD.N0134.d006543 m n hm hn
  have hrho : A.rho = _root_.GD.N0131.d008765 D := by
    simpa [A, D] using U.realized_rho e he
  have hcarrier :
      A.carrier =
        _root_.GD.N0131.d008768 D e := by
    simpa [A, D] using U.realized_carrier e he
  have hpower : A.power = _root_.GD.N0131.d008767 D e := by
    simpa [A, D] using U.realized_power e he
  have Ephysical :
      _root_.GD.N0113.d008651.d008706 A.emitted.table
        (_root_.GD.N0131.d008765 D)
        (_root_.GD.N0131.d008768 D e)
        (_root_.GD.N0131.d008767 D e)
        A.emitted.ledger.gradientBound
        A.emitted.ledger.carrierBound
        A.emitted.ledger.inversePower := by
    simpa [← hrho, ← hcarrier, ← hpower] using A.envelope
  have htrace :=
    _root_.GD.N0145.d014129 A.emitted.table e
      A.emitted.ledger.gradientBound
      A.emitted.ledger.carrierBound
      A.emitted.ledger.inversePower
      A.emitted.ledger.gradientBound_nonneg
      A.emitted.ledger.carrierBound_nonneg
      Ephysical
  have henergy :=
    _root_.GD.N0145.d014130 A.emitted.table e
      A.emitted.ledger.gradientBound
      A.emitted.ledger.carrierBound
      A.emitted.ledger.inversePower
      A.emitted.ledger.inversePower_pos.le
      Ephysical
  dsimp only
  constructor
  · simpa [A, D, hrho, hcarrier] using htrace
  · simpa [A, D, hrho, hpower] using henergy





theorem d014132
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0145.d014114 m n hm hn) :
    ∀ (e : ℝ) (he : e ∈ Icc (0 : ℝ) 1),
      let A := U.realized e he
      let trace :=
        _root_.GD.N0120.d008816
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          e A.emitted.table.d008659
      let energy :=
        _root_.GD.N0120.d008817
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          e A.emitted.table.d008659
      2 * (U.step : ℝ) * trace + (U.step : ℝ) ^ 2 * energy
          ≤ -(((((U.emitted.ledger.C / 2 : ℚ) : ℝ) ^ 2)) /
            (U.M : ℝ))
        ∧
      2 * (U.step : ℝ) * trace + (U.step : ℝ) ^ 2 * energy < 0 := by
  intro e he
  have hbridge := U.d014131 e he
  have hactual := U.d014115 e he
  rcases hactual with
    ⟨htrace, henergy, hmargin, hstep, heffective, hstrict⟩
  dsimp only
  rw [hbridge.1, hbridge.2]
  exact ⟨heffective, hstrict⟩

end d014114

end

end GD.N0145
