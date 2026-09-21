import GD.Module0728


















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0839

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0107
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0842



def d011000
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ)
    (h : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  fun omega ↦ dilation *
    h (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation omega)

theorem d011001
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ)
    (h : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hh : Measurable h) :
    Measurable (_root_.GD.N0232.N0719.N0839.d011000 k sizes shift dilation h) := by
  unfold _root_.GD.N0232.N0719.N0839.d011000
  fun_prop



theorem d011002
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ)
    (p q : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    (fun omega ↦
      _root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation p omega -
        _root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation q omega) =
      _root_.GD.N0232.N0719.N0839.d011000 k sizes shift dilation
        (fun omega ↦ p omega - q omega) := by
  funext omega
  unfold _root_.GD.N0232.N0719.N0842.d010911 _root_.GD.N0232.N0719.N0839.d011000
  ring


theorem d011003
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ)
    (p q : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    (fun omega ↦
      (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation p omega -
        _root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation q omega) / 2) =
      _root_.GD.N0232.N0719.N0839.d011000 k sizes shift dilation
        (fun omega ↦ (p omega - q omega) / 2) := by
  funext omega
  unfold _root_.GD.N0232.N0719.N0842.d010911 _root_.GD.N0232.N0719.N0839.d011000
  ring


def d011004
    (k : ℕ) (sizes : Fin k → ℕ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (h : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : ENNReal :=
  ∫⁻ omega, ENNReal.ofReal ((h omega) ^ 2) ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta

theorem d011005
    (k : ℕ) (sizes : Fin k → ℕ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (h : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    0 ≤ _root_.GD.N0232.N0719.N0839.d011004 k sizes theta h :=
  bot_le



theorem d011006
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (h : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hh : Measurable h) :
    _root_.GD.N0232.N0719.N0839.d011004 k sizes
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta)
        (_root_.GD.N0232.N0719.N0839.d011000 k sizes shift dilation h) =
      ENNReal.ofReal (dilation ^ 2) *
        _root_.GD.N0232.N0719.N0839.d011004 k sizes theta h := by
  have hmap := _root_.GD.N0232.N0719.d009188
    k sizes shift dilation theta.location theta.scale
  unfold _root_.GD.N0232.N0719.N0839.d011004 _root_.GD.N0232.N0719.N0859.d010812
  simp only [_root_.GD.N0232.N0719.N0845.d010882]
  change
    (∫⁻ omega,
      ENNReal.ofReal
        ((_root_.GD.N0232.N0719.N0839.d011000 k sizes shift dilation h omega) ^ 2)
      ∂_root_.GD.N0232.N0719.d009176 k sizes
        (shift + dilation * theta.location)
        (fun i ↦ dilation * theta.scale i)) = _
  rw [← hmap]
  rw [lintegral_map]
  · calc
      (∫⁻ omega,
          ENNReal.ofReal
            ((_root_.GD.N0232.N0719.N0839.d011000 k sizes shift dilation h
              (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega)) ^ 2)
          ∂_root_.GD.N0232.N0719.d009176 k sizes theta.location theta.scale) =
        ∫⁻ omega,
          ENNReal.ofReal (dilation ^ 2) *
            ENNReal.ofReal ((h omega) ^ 2)
          ∂_root_.GD.N0232.N0719.d009176 k sizes theta.location theta.scale := by
            apply lintegral_congr
            intro omega
            have hinv := _root_.GD.N0232.N0719.N0842.d010909
              k sizes shift dilation hdilation.ne' omega
            unfold _root_.GD.N0232.N0719.N0839.d011000
            rw [hinv]
            rw [show (dilation * h omega) ^ 2 =
                dilation ^ 2 * (h omega) ^ 2 by ring]
            exact ENNReal.ofReal_mul (sq_nonneg dilation)
      _ = ENNReal.ofReal (dilation ^ 2) *
          ∫⁻ omega, ENNReal.ofReal ((h omega) ^ 2)
            ∂_root_.GD.N0232.N0719.d009176 k sizes theta.location theta.scale := by
        rw [lintegral_const_mul]
        exact ENNReal.measurable_ofReal.comp (hh.pow_const 2)
  · exact ENNReal.measurable_ofReal.comp
      ((_root_.GD.N0232.N0719.N0839.d011001
        k sizes shift dilation h hh).pow_const 2)
  · exact _root_.GD.N0232.N0719.N0900.d009112 k sizes shift dilation


def d011007
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : ENNReal :=
  _root_.GD.N0232.N0719.N0839.d011004 k sizes theta
      (fun omega ↦ (p omega - q omega) / 2) /
    _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta


theorem d011008
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hp : Measurable p) (hq : Measurable q) :
    _root_.GD.N0232.N0719.N0839.d011007 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta)
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation p)
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation q) =
      _root_.GD.N0232.N0719.N0839.d011007 k sizes hk hsizes theta p q := by
  unfold _root_.GD.N0232.N0719.N0839.d011007
  rw [_root_.GD.N0232.N0719.N0839.d011003]
  rw [_root_.GD.N0232.N0719.N0839.d011006
    k sizes shift dilation hdilation theta
      (fun omega ↦ (p omega - q omega) / 2)]
  · rw [_root_.GD.N0232.N0719.N0845.d010903
      k sizes hk hsizes shift dilation hdilation theta]
    exact ENNReal.mul_div_mul_left _ _
      (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hdilation)).ne'
      ENNReal.ofReal_ne_top
  · fun_prop




theorem d011009
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hp : Measurable p) (hq : Measurable q) :
    _root_.GD.N0232.N0719.N0839.d011007 k sizes hk hsizes theta p q =
      _root_.GD.N0232.N0719.N0839.d011007 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) theta)
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes
          (-(theta.location / _root_.GD.N0232.N0719.N0845.d010886 theta))
          (_root_.GD.N0232.N0719.N0845.d010886 theta)⁻¹ p)
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes
          (-(theta.location / _root_.GD.N0232.N0719.N0845.d010886 theta))
          (_root_.GD.N0232.N0719.N0845.d010886 theta)⁻¹ q) := by
  let shift := -(theta.location / _root_.GD.N0232.N0719.N0845.d010886 theta)
  let dilation := (_root_.GD.N0232.N0719.N0845.d010886 theta)⁻¹
  have hdilation : 0 < dilation :=
    inv_pos.mpr (_root_.GD.N0232.N0719.N0845.d010887 (by omega : 0 < k) theta)
  have h := _root_.GD.N0232.N0719.N0839.d011008
    k sizes hk hsizes shift dilation hdilation theta p q hp hq
  simpa [shift, dilation, _root_.GD.N0232.N0719.N0845.d010890] using h.symm

end

end N0839
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0839.d011002
#print axioms _root_.GD.N0232.N0719.N0839.d011006
#print axioms _root_.GD.N0232.N0719.N0839.d011008
#print axioms _root_.GD.N0232.N0719.N0839.d011009
