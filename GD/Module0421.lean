import GD.Module0420
import GD.Module0419











namespace GD.N0116

open MeasureTheory Set
open _root_.GD.N0124
open _root_.GD.N0123

noncomputable section

def d006506 (α β : ℝ) : ℝ :=
  α ^ α * β ^ β /
    ((2 : ℝ) ^ ((3 : ℝ) / 2) *
      Real.Gamma α * Real.Gamma β * Real.Gamma ((3 : ℝ) / 2))

def d006507 (α β : ℝ) : ℝ :=
  _root_.GD.N0116.d006506 α β * Real.Gamma (α + β + (3 : ℝ) / 2)

def d006508 (α β e : ℝ) : ℝ :=
  e ^ (α + (3 : ℝ) / 2) * (1 - e) ^ (β + (3 : ℝ) / 2)

def d006509 (α β : ℝ) : ℝ := α + β + (3 : ℝ) / 2



def d006510 (α β : ℝ) (p : _root_.GD.N0124.d006387) : ℝ :=
  _root_.GD.N0116.d006506 α β * _root_.GD.N0123.d006499 α β p

def d006511 (α β e : ℝ) (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0116.d006507 α β * _root_.GD.N0116.d006508 α β e *
    (p.1 ^ (β - 1) * (1 - p.1) ^ (α - 1) *
      p.2 ^ ((1 : ℝ) / 2)) *
    (α * e * (1 - p.1) + β * (1 - e) * p.1 +
      p.2 * e * (1 - e) / 2) ^ (-_root_.GD.N0116.d006509 α β)

theorem d006512
    {α β e L F H : ℝ}
    (he0 : 0 < e) (he1 : e < 1)
    (hL0 : 0 < L) (hL1 : L < 1) (hF : 0 < F) (hH : 0 < H) :
    (((1 - L) * H / (1 - e)) ^ (α - 1) *
        (L * H / e) ^ (β - 1) *
        (F * H) ^ ((1 : ℝ) / 2)) *
        (H ^ 2 / (e * (1 - e)))
      =
    e ^ (-β) * (1 - e) ^ (-α) *
      (L ^ (β - 1) * (1 - L) ^ (α - 1) * F ^ ((1 : ℝ) / 2)) *
      H ^ (_root_.GD.N0116.d006509 α β - 1) := by
  have h1e : 0 < 1 - e := sub_pos.mpr he1
  have h1L : 0 < 1 - L := sub_pos.mpr hL1
  rw [Real.div_rpow (mul_pos h1L hH).le h1e.le,
    Real.div_rpow (mul_pos hL0 hH).le he0.le]
  rw [Real.mul_rpow h1L.le hH.le, Real.mul_rpow hL0.le hH.le,
    Real.mul_rpow hF.le hH.le]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [← Real.rpow_neg h1e.le, ← Real.rpow_neg he0.le]
  rw [show H ^ 2 = H ^ (2 : ℝ) by exact (Real.rpow_two H).symm]
  rw [show H ^ (2 : ℝ) / (e * (1 - e)) =
      H ^ (2 : ℝ) * (e * (1 - e))⁻¹ by rw [div_eq_mul_inv]]
  rw [mul_inv]
  rw [← Real.rpow_neg_one, ← Real.rpow_neg_one]
  have hepow :
      e ^ (-(β - 1)) * e ^ (-(1 : ℝ)) = e ^ (-β) := by
    rw [← Real.rpow_add he0]
    congr 1
    ring
  have h1epow :
      (1 - e) ^ (-(α - 1)) * (1 - e) ^ (-(1 : ℝ)) =
        (1 - e) ^ (-α) := by
    rw [← Real.rpow_add h1e]
    congr 1
    ring
  have hHpow :
      H ^ (α - 1) * H ^ (β - 1) * H ^ ((1 : ℝ) / 2) *
          H ^ (2 : ℝ) =
        H ^ (_root_.GD.N0116.d006509 α β - 1) := by
    rw [← Real.rpow_add hH, ← Real.rpow_add hH,
      ← Real.rpow_add hH]
    unfold _root_.GD.N0116.d006509
    congr 1
    ring
  calc
    (1 - L) ^ (α - 1) * H ^ (α - 1) *
          (1 - e) ^ (-(α - 1)) *
          (L ^ (β - 1) * H ^ (β - 1) * e ^ (-(β - 1))) *
          (F ^ ((1 : ℝ) / 2) * H ^ ((1 : ℝ) / 2)) *
          (H ^ (2 : ℝ) *
            (e ^ (-(1 : ℝ)) * (1 - e) ^ (-(1 : ℝ))))
        =
      (e ^ (-(β - 1)) * e ^ (-(1 : ℝ))) *
        ((1 - e) ^ (-(α - 1)) * (1 - e) ^ (-(1 : ℝ))) *
        (L ^ (β - 1) * (1 - L) ^ (α - 1) *
          F ^ ((1 : ℝ) / 2)) *
        (H ^ (α - 1) * H ^ (β - 1) * H ^ ((1 : ℝ) / 2) *
          H ^ (2 : ℝ)) := by ring
    _ = e ^ (-β) * (1 - e) ^ (-α) *
        (L ^ (β - 1) * (1 - L) ^ (α - 1) *
          F ^ ((1 : ℝ) / 2)) *
        H ^ (_root_.GD.N0116.d006509 α β - 1) := by
          rw [hepow, h1epow, hHpow]

theorem d006513
    {α β e : ℝ}
    (he0 : 0 < e) (he1 : e < 1) {p : _root_.GD.N0124.d006387}
    (hp : p ∈ _root_.GD.N0124.d006389) :
    (p.2.2 ^ 2 / (e * (1 - e))) *
        _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e p)
      =
    _root_.GD.N0116.d006506 α β * e ^ (-β) * (1 - e) ^ (-α) *
      _root_.GD.N0123.d006500 α β p * p.2.2 ^ (_root_.GD.N0116.d006509 α β - 1) *
      Real.exp (-
        (_root_.GD.N0123.d006501 α β e p / (e * (1 - e)) * p.2.2)) := by
  unfold _root_.GD.N0116.d006510 _root_.GD.N0123.d006499
  rw [_root_.GD.N0123.d006503 α β p (ne_of_gt he0)
    (ne_of_gt (sub_pos.mpr he1))]
  simp only [_root_.GD.N0124.d006392]
  calc
    p.2.2 ^ 2 / (e * (1 - e)) *
          (_root_.GD.N0116.d006506 α β *
            (((1 - p.1) * p.2.2 / (1 - e)) ^ (α - 1) *
              (p.1 * p.2.2 / e) ^ (β - 1) *
              (p.2.1 * p.2.2) ^ ((1 : ℝ) / 2) *
              Real.exp
                (-(_root_.GD.N0123.d006501 α β e p / (e * (1 - e)) *
                  p.2.2))))
        =
      _root_.GD.N0116.d006506 α β *
        (((((1 - p.1) * p.2.2 / (1 - e)) ^ (α - 1) *
          (p.1 * p.2.2 / e) ^ (β - 1) *
          (p.2.1 * p.2.2) ^ ((1 : ℝ) / 2)) *
          (p.2.2 ^ 2 / (e * (1 - e)))) *
        Real.exp
          (-(_root_.GD.N0123.d006501 α β e p / (e * (1 - e)) * p.2.2))) := by
            ring
    _ =
      _root_.GD.N0116.d006506 α β *
        (e ^ (-β) * (1 - e) ^ (-α) *
          (p.1 ^ (β - 1) * (1 - p.1) ^ (α - 1) *
            p.2.1 ^ ((1 : ℝ) / 2)) *
          p.2.2 ^ (_root_.GD.N0116.d006509 α β - 1)) *
        Real.exp
          (-(_root_.GD.N0123.d006501 α β e p / (e * (1 - e)) * p.2.2)) := by
            rw [_root_.GD.N0116.d006512 he0 he1 hp.1 hp.2.1
              hp.2.2.1 hp.2.2.2]
            ac_rfl
    _ = _root_.GD.N0116.d006506 α β * e ^ (-β) * (1 - e) ^ (-α) *
          _root_.GD.N0123.d006500 α β p * p.2.2 ^ (_root_.GD.N0116.d006509 α β - 1) *
          Real.exp
            (-(_root_.GD.N0123.d006501 α β e p / (e * (1 - e)) *
              p.2.2)) := by
            unfold _root_.GD.N0123.d006500
            ac_rfl

theorem d006514 {α β e N : ℝ}
    (he0 : 0 < e) (he1 : e < 1) (hN : 0 < N) :
    e ^ (-β) * (1 - e) ^ (-α) *
        (N / (e * (1 - e))) ^ (-(_root_.GD.N0116.d006509 α β))
      =
    _root_.GD.N0116.d006508 α β e * N ^ (-(_root_.GD.N0116.d006509 α β)) := by
  have h1e : 0 < 1 - e := sub_pos.mpr he1
  rw [Real.div_rpow hN.le (mul_pos he0 h1e).le]
  rw [div_eq_mul_inv,
    Real.rpow_neg (mul_pos he0 h1e).le, inv_inv,
    Real.mul_rpow he0.le h1e.le]
  calc
    e ^ (-β) * (1 - e) ^ (-α) *
          (N ^ (-_root_.GD.N0116.d006509 α β) *
            (e ^ _root_.GD.N0116.d006509 α β * (1 - e) ^ _root_.GD.N0116.d006509 α β))
        =
      (e ^ (-β) * e ^ _root_.GD.N0116.d006509 α β) *
        ((1 - e) ^ (-α) * (1 - e) ^ _root_.GD.N0116.d006509 α β) *
        N ^ (-_root_.GD.N0116.d006509 α β) := by ring
    _ =
      e ^ (-β + _root_.GD.N0116.d006509 α β) *
        (1 - e) ^ (-α + _root_.GD.N0116.d006509 α β) *
        N ^ (-_root_.GD.N0116.d006509 α β) := by
          rw [← Real.rpow_add he0, ← Real.rpow_add h1e]
    _ = _root_.GD.N0116.d006508 α β e * N ^ (-_root_.GD.N0116.d006509 α β) := by
          unfold _root_.GD.N0116.d006509 _root_.GD.N0116.d006508
          congr 1 <;> ring

theorem d006515 {α β e L F : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (hL0 : 0 < L) (hL1 : L < 1) (hF : 0 < F) :
    ∫ H : ℝ in Ioi 0,
      _root_.GD.N0116.d006506 α β * e ^ (-β) * (1 - e) ^ (-α) *
        (L ^ (β - 1) * (1 - L) ^ (α - 1) * F ^ ((1 : ℝ) / 2)) *
        (H ^ (_root_.GD.N0116.d006509 α β - 1) *
          Real.exp (-
            ((α * e * (1 - L) + β * (1 - e) * L +
              F * e * (1 - e) / 2) / (e * (1 - e)) * H)))
      =
    _root_.GD.N0116.d006511 α β e (L, F) := by
  let N : ℝ :=
    α * e * (1 - L) + β * (1 - e) * L +
      F * e * (1 - e) / 2
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hr : 0 < _root_.GD.N0116.d006509 α β := by
    unfold _root_.GD.N0116.d006509
    positivity
  rw [show (∫ H : ℝ in Ioi 0,
      _root_.GD.N0116.d006506 α β * e ^ (-β) * (1 - e) ^ (-α) *
        (L ^ (β - 1) * (1 - L) ^ (α - 1) * F ^ ((1 : ℝ) / 2)) *
        (H ^ (_root_.GD.N0116.d006509 α β - 1) *
          Real.exp (-(N / (e * (1 - e)) * H))))
      =
      (_root_.GD.N0116.d006506 α β * e ^ (-β) * (1 - e) ^ (-α) *
        (L ^ (β - 1) * (1 - L) ^ (α - 1) * F ^ ((1 : ℝ) / 2))) *
      Real.Gamma (_root_.GD.N0116.d006509 α β) *
        (N / (e * (1 - e))) ^ (-(_root_.GD.N0116.d006509 α β)) by
    rw [_root_.GD.N0133.d006482 hr
      (div_pos hN (mul_pos he0 (sub_pos.mpr he1)))]
    ]
  have hpow := _root_.GD.N0116.d006514
    (α := α) (β := β) he0 he1 hN
  unfold _root_.GD.N0116.d006511 _root_.GD.N0116.d006507
  dsimp [N] at hpow ⊢
  calc
    _root_.GD.N0116.d006506 α β * e ^ (-β) * (1 - e) ^ (-α) *
          (L ^ (β - 1) * (1 - L) ^ (α - 1) *
            F ^ ((1 : ℝ) / 2)) *
          Real.Gamma (_root_.GD.N0116.d006509 α β) *
          ((α * e * (1 - L) + β * (1 - e) * L +
            F * e * (1 - e) / 2) / (e * (1 - e))) ^
              (-_root_.GD.N0116.d006509 α β)
        =
      _root_.GD.N0116.d006506 α β * Real.Gamma (_root_.GD.N0116.d006509 α β) *
        (L ^ (β - 1) * (1 - L) ^ (α - 1) *
          F ^ ((1 : ℝ) / 2)) *
        (e ^ (-β) * (1 - e) ^ (-α) *
          ((α * e * (1 - L) + β * (1 - e) * L +
            F * e * (1 - e) / 2) / (e * (1 - e))) ^
              (-_root_.GD.N0116.d006509 α β)) := by ring
    _ =
      _root_.GD.N0116.d006506 α β * Real.Gamma (_root_.GD.N0116.d006509 α β) *
        (L ^ (β - 1) * (1 - L) ^ (α - 1) *
          F ^ ((1 : ℝ) / 2)) *
        (_root_.GD.N0116.d006508 α β e *
          (α * e * (1 - L) + β * (1 - e) * L +
            F * e * (1 - e) / 2) ^ (-_root_.GD.N0116.d006509 α β)) := by
              rw [hpow]
    _ =
      _root_.GD.N0116.d006506 α β * Real.Gamma (α + β + 3 / 2) *
        _root_.GD.N0116.d006508 α β e *
        (L ^ (β - 1) * (1 - L) ^ (α - 1) *
          F ^ ((1 : ℝ) / 2)) *
        (α * e * (1 - L) + β * (1 - e) * L +
          F * e * (1 - e) / 2) ^ (-_root_.GD.N0116.d006509 α β) := by
            unfold _root_.GD.N0116.d006509
            ring

theorem d006516
    {α β e L F : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (hL0 : 0 < L) (hL1 : L < 1) (hF : 0 < F)
    (φ : ℝ × ℝ → ℝ) :
    ∫ H : ℝ in Ioi 0,
      φ (L, F) * (H ^ 2 / (e * (1 - e))) *
        _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (L, F, H))
      =
    φ (L, F) * _root_.GD.N0116.d006511 α β e (L, F) := by
  calc
    (∫ H : ℝ in Ioi 0,
      φ (L, F) * (H ^ 2 / (e * (1 - e))) *
        _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (L, F, H)))
        =
      ∫ H : ℝ in Ioi 0,
        φ (L, F) *
          (_root_.GD.N0116.d006506 α β * e ^ (-β) * (1 - e) ^ (-α) *
            (L ^ (β - 1) * (1 - L) ^ (α - 1) *
              F ^ ((1 : ℝ) / 2)) *
            H ^ (_root_.GD.N0116.d006509 α β - 1) *
            Real.exp (-
              ((α * e * (1 - L) + β * (1 - e) * L +
                F * e * (1 - e) / 2) / (e * (1 - e)) * H))) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro H hH
          change
            φ (L, F) * (H ^ 2 / (e * (1 - e))) *
                _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (L, F, H))
              =
            φ (L, F) *
              (_root_.GD.N0116.d006506 α β * e ^ (-β) *
                (1 - e) ^ (-α) *
                (L ^ (β - 1) * (1 - L) ^ (α - 1) *
                  F ^ ((1 : ℝ) / 2)) *
                H ^ (_root_.GD.N0116.d006509 α β - 1) *
                Real.exp (-
                  ((α * e * (1 - L) + β * (1 - e) * L +
                    F * e * (1 - e) / 2) / (e * (1 - e)) * H)))
          have ht := _root_.GD.N0116.d006513
            (α := α) (β := β) he0 he1
            (show (L, F, H) ∈ _root_.GD.N0124.d006389 by
              exact ⟨hL0, hL1, hF, hH⟩)
          calc
            φ (L, F) * (H ^ 2 / (e * (1 - e))) *
                  _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (L, F, H))
                =
              φ (L, F) *
                ((H ^ 2 / (e * (1 - e))) *
                  _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (L, F, H))) := by ring
            _ = φ (L, F) *
                (_root_.GD.N0116.d006506 α β * e ^ (-β) *
                  (1 - e) ^ (-α) * _root_.GD.N0123.d006500 α β (L, F, H) *
                  H ^ (_root_.GD.N0116.d006509 α β - 1) *
                  Real.exp (-
                    (_root_.GD.N0123.d006501 α β e (L, F, H) /
                      (e * (1 - e)) * H))) := by rw [ht]
            _ = φ (L, F) *
              (_root_.GD.N0116.d006506 α β * e ^ (-β) *
                (1 - e) ^ (-α) *
                (L ^ (β - 1) * (1 - L) ^ (α - 1) *
                  F ^ ((1 : ℝ) / 2)) *
                H ^ (_root_.GD.N0116.d006509 α β - 1) *
                Real.exp (-
                  ((α * e * (1 - L) + β * (1 - e) * L +
                    F * e * (1 - e) / 2) / (e * (1 - e)) * H))) := by
                  unfold _root_.GD.N0123.d006500 _root_.GD.N0123.d006501
                  ring
    _ =
      φ (L, F) *
        ∫ H : ℝ in Ioi 0,
          _root_.GD.N0116.d006506 α β * e ^ (-β) * (1 - e) ^ (-α) *
            (L ^ (β - 1) * (1 - L) ^ (α - 1) *
              F ^ ((1 : ℝ) / 2)) *
            (H ^ (_root_.GD.N0116.d006509 α β - 1) *
              Real.exp (-
                ((α * e * (1 - L) + β * (1 - e) * L +
                  F * e * (1 - e) / 2) / (e * (1 - e)) * H))) := by
            rw [← MeasureTheory.integral_const_mul]
            apply setIntegral_congr_fun measurableSet_Ioi
            intro H _
            ring
    _ = φ (L, F) * _root_.GD.N0116.d006511 α β e (L, F) := by
      congr 1
      exact _root_.GD.N0116.d006515 hα hβ he0 he1 hL0 hL1 hF

theorem d006517
    {α β e : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 < e) (he1 : e < 1)
    (φ : ℝ × ℝ → ℝ) :
    ∫ L : ℝ in Ioo 0 1,
      ∫ F : ℝ in Ioi 0,
        ∫ H : ℝ in Ioi 0,
          φ (L, F) * (H ^ 2 / (e * (1 - e))) *
            _root_.GD.N0116.d006510 α β (_root_.GD.N0124.d006392 e (L, F, H))
      =
    ∫ L : ℝ in Ioo 0 1,
      ∫ F : ℝ in Ioi 0,
        φ (L, F) * _root_.GD.N0116.d006511 α β e (L, F) := by
  apply setIntegral_congr_fun measurableSet_Ioo
  intro L hL
  apply setIntegral_congr_fun measurableSet_Ioi
  intro F hF
  exact _root_.GD.N0116.d006516 hα hβ he0 he1
    hL.1 hL.2 hF φ

end

end GD.N0116
