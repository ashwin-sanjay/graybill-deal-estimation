import GD.Module0600








noncomputable section

open _root_.GD.N0111
open _root_.GD.N0132
open _root_.GD.N0146
open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0135
open _root_.GD.N0136

namespace GD.N0129

theorem d008690
    {ν Δ p r d : ℝ}
    (hν : ν ≠ 0) (hΔ : Δ ≠ 0) (hp : p ≠ 0)
    (hr : r - 1 ≠ 0) (hc : 0 < p / ν) :
    let c := p / ν
    let a := (d + Δ) / ν
    let h := (p - Δ * d - d ^ 2) / (2 * ν ^ 2)
    let v₀ := -r * ν / Δ
    let v₁ := -(r + 1) / (r - 1)
    let v₂ := p / (Δ * ν * (r - 1))
    let vt := -2 * ν ^ 2 * (r + 1) / (Δ * (r - 1))
    v₀ * _root_.GD.N0111.d006141 a c d h r 0 0 0 0
      + v₁ * _root_.GD.N0111.d006141 a c d h r 0 0 1 0
      + v₂ * _root_.GD.N0111.d006141 a c d h r 0 0 2 0
      + vt * _root_.GD.N0111.d006141 a c d h r 0 0 0 1
      = c ^ (-r) := by
  dsimp
  simp only [_root_.GD.N0111.d006141, _root_.GD.N0111.d006140, _root_.GD.N0111.d006138, _root_.GD.N0111.d006136, zero_add,
    add_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul,
    mul_zero, one_mul, pow_zero, pow_one, Nat.zero_sub,
    Nat.reduceSub, Nat.reduceAdd, sub_zero]
  let c : ℝ := p / ν
  have hcpos : 0 < c := by simpa [c] using hc
  have hc_eq : p / ν = c := rfl
  have hp_eq : p = c * ν := by
    dsimp [c]
    field_simp [hν]
  rw [hc_eq, hp_eq]
  have hpow1 :
      c ^ (-r - 1) = c ^ (-r) / c := by
    calc
      c ^ (-r - 1) =
          c ^ (-r) / c ^ (1 : ℝ) :=
        Real.rpow_sub hcpos (-r) 1
      _ = c ^ (-r) / c := by rw [Real.rpow_one]
  have hpow2 :
      c ^ (-r - 2) = c ^ (-r) / c ^ (2 : ℕ) := by
    calc
      c ^ (-r - 2) =
          c ^ (-r) / c ^ (2 : ℝ) :=
        Real.rpow_sub hcpos (-r) 2
      _ = c ^ (-r) / c ^ (2 : ℕ) :=
        congrArg (fun z => c ^ (-r) / z)
          (Real.rpow_natCast c 2)
  rw [hpow1, hpow2]
  field_simp [hν, hΔ, hr, hcpos.ne]
  ring

theorem d008691
    {γ r d : ℝ}
    (hγ : γ ≠ 0) (hr : r - 1 ≠ 0) (hc : 0 < γ / 2) :
    let c := γ / 2
    let a := d / (2 * γ)
    let h := (γ ^ 2 - d ^ 2) / (8 * γ ^ 2)
    let v₁ := -(r ^ 2 + r + 1) / (r - 1)
    let v₃ := 1 / (4 * (r - 1))
    let vst := -4 * γ * (r + 2) / (r - 1)
    v₁ * _root_.GD.N0111.d006141 a c d h r 0 0 1 0
      + v₃ * _root_.GD.N0111.d006141 a c d h r 0 0 3 0
      + vst * _root_.GD.N0111.d006141 a c d h r 0 0 1 1
      = c ^ (-r) := by
  dsimp
  simp only [_root_.GD.N0111.d006141, _root_.GD.N0111.d006140, _root_.GD.N0111.d006138, _root_.GD.N0111.d006136, zero_add,
    add_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul,
    mul_zero, one_mul, pow_zero, pow_one, Nat.zero_sub,
    Nat.reduceSub, Nat.reduceAdd, sub_zero]
  let c : ℝ := γ / 2
  have hcpos : 0 < c := by simpa [c] using hc
  have hc_eq : γ / 2 = c := rfl
  have hγ_eq : γ = 2 * c := by
    dsimp [c]
    ring
  rw [hc_eq, hγ_eq]
  have hpow1 :
      c ^ (-r - 1) = c ^ (-r) / c := by
    calc
      c ^ (-r - 1) =
          c ^ (-r) / c ^ (1 : ℝ) :=
        Real.rpow_sub hcpos (-r) 1
      _ = c ^ (-r) / c := by rw [Real.rpow_one]
  have hpow2 :
      c ^ (-r - 2) = c ^ (-r) / c ^ (2 : ℕ) := by
    calc
      c ^ (-r - 2) =
          c ^ (-r) / c ^ (2 : ℝ) :=
        Real.rpow_sub hcpos (-r) 2
      _ = c ^ (-r) / c ^ (2 : ℕ) :=
        congrArg (fun z => c ^ (-r) / z)
          (Real.rpow_natCast c 2)
  have hpow3 :
      c ^ (-r - 3) = c ^ (-r) / c ^ (3 : ℕ) := by
    calc
      c ^ (-r - 3) =
          c ^ (-r) / c ^ (3 : ℝ) :=
        Real.rpow_sub hcpos (-r) 3
      _ = c ^ (-r) / c ^ (3 : ℕ) :=
        congrArg (fun z => c ^ (-r) / z)
          (Real.rpow_natCast c 3)
  rw [hpow1, hpow2, hpow3]
  field_simp [hr, hcpos.ne]
  ring

theorem d008692
    {α β e r : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hΔ : α - β ≠ 0) (hr : r - 1 ≠ 0) :
    _root_.GD.N0146.d008630 α β e r
        (-r * (α + β) / (α - β))
        (-(r + 1) / (r - 1))
        (α * β / ((α - β) * (α + β) * (r - 1)))
        (-2 * (α + β) ^ 2 * (r + 1) /
          ((α - β) * (r - 1))) =
      (α * β / (α + β)) ^ (-r) := by
  have hν : α + β ≠ 0 := ne_of_gt (add_pos hα hβ)
  have hp : α * β ≠ 0 := ne_of_gt (mul_pos hα hβ)
  have hc : 0 < α * β / (α + β) := by positivity
  have h :=
    _root_.GD.N0129.d008690
      (ν := α + β) (Δ := α - β) (p := α * β)
      (r := r) (d := β - (α + β) * e)
      hν hΔ hp hr hc
  dsimp at h
  have ha :
      (β - (α + β) * e + (α - β)) / (α + β) =
        α / (α + β) - e := by
    field_simp [hν]
    ring
  have hh :
      (α * β - (α - β) * (β - (α + β) * e) -
          (β - (α + β) * e) ^ 2) /
          (2 * (α + β) ^ 2) =
        e * (1 - e) / 2 := by
    field_simp [hν]
    ring
  rw [ha, hh] at h
  simpa only [_root_.GD.N0146.d008630, _root_.GD.N0132.d006446] using h

theorem d008693
    {γ e r : ℝ}
    (hγ : 0 < γ) (hr : r - 1 ≠ 0) :
    _root_.GD.N0146.d008634 γ γ e r
        (-(r ^ 2 + r + 1) / (r - 1))
        (1 / (4 * (r - 1)))
        (-4 * γ * (r + 2) / (r - 1)) =
      (γ * γ / (γ + γ)) ^ (-r) := by
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hc : 0 < γ / 2 := by positivity
  have h :=
    _root_.GD.N0129.d008691
      (γ := γ) (r := r) (d := γ - 2 * γ * e)
      hγ0 hr hc
  dsimp at h
  have ha :
      (γ - 2 * γ * e) / (2 * γ) =
        γ / (γ + γ) - e := by
    field_simp [hγ0]
    ring
  have hc_eq : γ / 2 = γ * γ / (γ + γ) := by
    field_simp [hγ0]
    ring
  have hd :
      γ - 2 * γ * e = γ - (γ + γ) * e := by
    ring
  have hh :
      (γ ^ 2 - (γ - 2 * γ * e) ^ 2) / (8 * γ ^ 2) =
        e * (1 - e) / 2 := by
    field_simp [hγ0]
    ring
  rw [ha, hc_eq, hh, hd] at h
  simpa only [_root_.GD.N0146.d008634, _root_.GD.N0132.d006446] using h

theorem d008694
    (D : _root_.GD.N0134.d006518) (e : ℝ)
    (hΔ : _root_.GD.N0135.d006594 D ≠ 0) :
    _root_.GD.N0146.d008630
        (D.alpha : ℝ) (D.beta : ℝ) e (D.d006524 : ℝ)
        (_root_.GD.N0135.d006596 D : ℝ) (_root_.GD.N0135.d006597 D : ℝ)
        (_root_.GD.N0135.d006598 D : ℝ) (_root_.GD.N0135.d006599 D : ℝ) =
      (D.d006522 : ℝ) ^ (-(D.d006524 : ℝ)) := by
  have hα : (0 : ℝ) < D.alpha := by exact_mod_cast D.alpha_pos
  have hβ : (0 : ℝ) < D.beta := by exact_mod_cast D.beta_pos
  have hΔR : (D.alpha : ℝ) - D.beta ≠ 0 := by
    exact_mod_cast hΔ
  have hrR : (D.d006524 : ℝ) - 1 ≠ 0 := by
    exact_mod_cast _root_.GD.N0135.d006606 D
  have h :=
    _root_.GD.N0129.d008692
      (e := e) hα hβ hΔR hrR
  simpa [_root_.GD.N0135.d006596, _root_.GD.N0135.d006597, _root_.GD.N0135.d006598, _root_.GD.N0135.d006599,
    _root_.GD.N0136.d006584, _root_.GD.N0136.d006585, _root_.GD.N0136.d006586, _root_.GD.N0136.d006587, _root_.GD.N0135.d006594, _root_.GD.N0135.d006595,
    _root_.GD.N0134.d006518.d006519, _root_.GD.N0134.d006518.d006522] using h

theorem d008695
    (D : _root_.GD.N0134.d006518) (e : ℝ)
    (hΔ : _root_.GD.N0135.d006594 D = 0) :
    _root_.GD.N0146.d008634
        (D.alpha : ℝ) (D.beta : ℝ) e (D.d006524 : ℝ)
        (_root_.GD.N0135.d006600 D : ℝ) (_root_.GD.N0135.d006601 D : ℝ)
        (_root_.GD.N0135.d006602 D : ℝ) =
      (D.d006522 : ℝ) ^ (-(D.d006524 : ℝ)) := by
  have hαβQ : D.alpha = D.beta := sub_eq_zero.mp hΔ
  have hα : (0 : ℝ) < D.alpha := by exact_mod_cast D.alpha_pos
  have hrR : (D.d006524 : ℝ) - 1 ≠ 0 := by
    exact_mod_cast _root_.GD.N0135.d006606 D
  have h :=
    _root_.GD.N0129.d008693
      (γ := (D.alpha : ℝ)) (e := e)
      (r := (D.d006524 : ℝ)) hα hrR
  simpa [_root_.GD.N0135.d006600, _root_.GD.N0135.d006601, _root_.GD.N0135.d006602,
    _root_.GD.N0134.d006518.d006522, _root_.GD.N0134.d006518.d006519, hαβQ] using h

end GD.N0129
