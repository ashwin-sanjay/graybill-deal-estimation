import GD.Module0726



















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0842

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0107
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0845


def d010906 (shift dilation : ℝ) : ℝ :=
  -(dilation⁻¹ * shift)


def d010907
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ) : _root_.GD.N0232.N0719.d009173 k sizes → _root_.GD.N0232.N0719.d009173 k sizes :=
  _root_.GD.N0232.N0719.N0900.d009095 k sizes (_root_.GD.N0232.N0719.N0842.d010906 shift dilation) dilation⁻¹

@[fun_prop]
theorem d010908
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation) := by
  exact _root_.GD.N0232.N0719.N0900.d009112 k sizes _ _



theorem d010909
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ) (hdilation : dilation ≠ 0)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) = omega := by
  ext i j
  simp [_root_.GD.N0232.N0719.N0842.d010907, _root_.GD.N0232.N0719.N0842.d010906,
    _root_.GD.N0232.N0719.N0900.d009095, _root_.GD.N0107.d009018]
  field_simp [hdilation]
  ring



theorem d010910
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ) (hdilation : dilation ≠ 0)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation omega) = omega := by
  ext i j
  simp [_root_.GD.N0232.N0719.N0842.d010907, _root_.GD.N0232.N0719.N0842.d010906,
    _root_.GD.N0232.N0719.N0900.d009095, _root_.GD.N0107.d009018]
  field_simp [hdilation]
  ring




def d010911
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  fun omega ↦
    shift + dilation *
      d (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation omega)

theorem d010912
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    Measurable (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) := by
  unfold _root_.GD.N0232.N0719.N0842.d010911
  fun_prop


theorem d010913
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ) (hdilation : dilation ≠ 0)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d
        (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) =
      shift + dilation * d omega := by
  unfold _root_.GD.N0232.N0719.N0842.d010911
  rw [_root_.GD.N0232.N0719.N0842.d010909
    k sizes shift dilation hdilation omega]

@[simp]
theorem d010914
    (k : ℕ) (sizes : Fin k → ℕ)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0842.d010911 k sizes 0 1 d = d := by
  funext omega
  unfold _root_.GD.N0232.N0719.N0842.d010911
  have hobs : _root_.GD.N0232.N0719.N0842.d010907 k sizes 0 1 omega = omega := by
    ext i j
    simp [_root_.GD.N0232.N0719.N0842.d010907, _root_.GD.N0232.N0719.N0842.d010906,
      _root_.GD.N0232.N0719.N0900.d009095, _root_.GD.N0107.d009018]
  rw [hobs]
  ring


theorem d010915
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift₁ dilation₁ shift₂ dilation₂ : ℝ)
    (hdilation₁ : dilation₁ ≠ 0) (hdilation₂ : dilation₂ ≠ 0)
    (omega : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0842.d010907 k sizes shift₂ dilation₂
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift₁ dilation₁ omega) =
      _root_.GD.N0232.N0719.N0842.d010907 k sizes
        (shift₁ + dilation₁ * shift₂) (dilation₁ * dilation₂) omega := by
  ext i j
  simp [_root_.GD.N0232.N0719.N0842.d010907, _root_.GD.N0232.N0719.N0842.d010906,
    _root_.GD.N0232.N0719.N0900.d009095, _root_.GD.N0107.d009018]
  field_simp [hdilation₁, hdilation₂]
  ring


theorem d010916
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift₁ dilation₁ shift₂ dilation₂ : ℝ)
    (hdilation₁ : dilation₁ ≠ 0) (hdilation₂ : dilation₂ ≠ 0)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
    _root_.GD.N0232.N0719.N0842.d010911 k sizes shift₁ dilation₁
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift₂ dilation₂ d) =
      _root_.GD.N0232.N0719.N0842.d010911 k sizes
        (shift₁ + dilation₁ * shift₂) (dilation₁ * dilation₂) d := by
  funext omega
  unfold _root_.GD.N0232.N0719.N0842.d010911
  rw [_root_.GD.N0232.N0719.N0842.d010915
    k sizes shift₁ dilation₁ shift₂ dilation₂
    hdilation₁ hdilation₂ omega]
  ring



theorem d010917
    {k : ℕ} {theta eta : _root_.GD.N0232.N0719.N0859.d010809 k}
    (hlocation : theta.location = eta.location)
    (hscale : theta.scale = eta.scale) : theta = eta := by
  cases theta
  cases eta
  cases hlocation
  cases hscale
  rfl


theorem d010918
    {k : ℕ} (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010881 (_root_.GD.N0232.N0719.N0842.d010906 shift dilation) dilation⁻¹
        (inv_pos.mpr hdilation)
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta) = theta := by
  apply _root_.GD.N0232.N0719.N0842.d010917
  · simp [_root_.GD.N0232.N0719.N0845.d010882, _root_.GD.N0232.N0719.N0842.d010906]
    field_simp [hdilation.ne']
    ring
  · funext i
    simp [_root_.GD.N0232.N0719.N0845.d010883]
    field_simp [hdilation.ne']


theorem d010919
    {k : ℕ} (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation
        (_root_.GD.N0232.N0719.N0845.d010881 (_root_.GD.N0232.N0719.N0842.d010906 shift dilation) dilation⁻¹
          (inv_pos.mpr hdilation) theta) = theta := by
  apply _root_.GD.N0232.N0719.N0842.d010917
  · simp [_root_.GD.N0232.N0719.N0845.d010882, _root_.GD.N0232.N0719.N0842.d010906]
    field_simp [hdilation.ne']
    ring
  · funext i
    simp [_root_.GD.N0232.N0719.N0845.d010883]
    field_simp [hdilation.ne']



theorem d010920
    (k : ℕ) (sizes : Fin k → ℕ)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes
        (_root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta)
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) =
      ENNReal.ofReal (dilation ^ 2) *
        _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d := by
  have hmap := _root_.GD.N0232.N0719.d009188
    k sizes shift dilation theta.location theta.scale
  unfold _root_.GD.N0232.N0719.N0859.d010840 _root_.GD.N0232.N0719.N0859.d010812
  simp only [_root_.GD.N0232.N0719.N0845.d010882]
  change
    (∫⁻ omega,
      ENNReal.ofReal
        ((_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d omega -
          (shift + dilation * theta.location)) ^ 2)
      ∂_root_.GD.N0232.N0719.d009176 k sizes
        (shift + dilation * theta.location)
        (fun i ↦ dilation * theta.scale i)) = _
  rw [← hmap]
  rw [lintegral_map]
  · calc
      (∫⁻ omega,
          ENNReal.ofReal
            ((_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d
                (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) -
              (shift + dilation * theta.location)) ^ 2)
          ∂_root_.GD.N0232.N0719.d009176 k sizes theta.location theta.scale) =
        ∫⁻ omega,
          ENNReal.ofReal (dilation ^ 2) *
            ENNReal.ofReal ((d omega - theta.location) ^ 2)
          ∂_root_.GD.N0232.N0719.d009176 k sizes theta.location theta.scale := by
            apply lintegral_congr
            intro omega
            rw [_root_.GD.N0232.N0719.N0842.d010913
              k sizes shift dilation hdilation.ne' d omega]
            have hreal :
                ((shift + dilation * d omega) -
                    (shift + dilation * theta.location)) ^ 2 =
                  dilation ^ 2 * (d omega - theta.location) ^ 2 := by
              ring
            rw [hreal, ENNReal.ofReal_mul (sq_nonneg dilation)]
      _ = ENNReal.ofReal (dilation ^ 2) *
          ∫⁻ omega, ENNReal.ofReal ((d omega - theta.location) ^ 2)
            ∂_root_.GD.N0232.N0719.d009176 k sizes theta.location theta.scale := by
        rw [lintegral_const_mul]
        fun_prop
  · exact ENNReal.measurable_ofReal.comp
      (((_root_.GD.N0232.N0719.N0842.d010912 k sizes shift dilation d hd).sub
        measurable_const).pow_const 2)
  · exact _root_.GD.N0232.N0719.N0900.d009112 k sizes shift dilation



def d010921
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) : Prop :=
  ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
    _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
      _root_.GD.N0232.N0719.N0858.d010852 k sizes hk hsizes theta



theorem d010922
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d)
    (hfeasible : _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes d) :
    _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) := by
  intro eta
  let theta : _root_.GD.N0232.N0719.N0859.d010809 k :=
    _root_.GD.N0232.N0719.N0845.d010881 (_root_.GD.N0232.N0719.N0842.d010906 shift dilation) dilation⁻¹
      (inv_pos.mpr hdilation) eta
  have heta : _root_.GD.N0232.N0719.N0845.d010881 shift dilation hdilation theta = eta := by
    exact _root_.GD.N0232.N0719.N0842.d010919 shift dilation hdilation eta
  rw [← heta]
  rw [_root_.GD.N0232.N0719.N0842.d010920
    k sizes shift dilation hdilation theta d hd]
  rw [_root_.GD.N0232.N0719.N0845.d010903
    k sizes hk hsizes shift dilation hdilation theta]
  exact mul_le_mul_left' (hfeasible theta) _



theorem d010923
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes
        (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) ↔
      _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes d := by
  constructor
  · intro htransport
    have hback := _root_.GD.N0232.N0719.N0842.d010922
      k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0842.d010906 shift dilation) dilation⁻¹
      (inv_pos.mpr hdilation)
      (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d)
      (_root_.GD.N0232.N0719.N0842.d010912 k sizes shift dilation d hd)
      htransport
    have hcollapse :
        _root_.GD.N0232.N0719.N0842.d010911 k sizes (_root_.GD.N0232.N0719.N0842.d010906 shift dilation) dilation⁻¹
            (_root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation d) = d := by
      rw [_root_.GD.N0232.N0719.N0842.d010916]
      · have hshift :
            _root_.GD.N0232.N0719.N0842.d010906 shift dilation + dilation⁻¹ * shift = 0 := by
            simp [_root_.GD.N0232.N0719.N0842.d010906]
        have hscale : dilation⁻¹ * dilation = 1 :=
          inv_mul_cancel₀ hdilation.ne'
        rw [hshift, hscale]
        exact _root_.GD.N0232.N0719.N0842.d010914 k sizes d
      · exact inv_ne_zero hdilation.ne'
      · exact hdilation.ne'
    simpa only [hcollapse] using hback
  · exact _root_.GD.N0232.N0719.N0842.d010922
      k sizes hk hsizes shift dilation hdilation d hd

end

end N0842
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0842.d010916
#print axioms _root_.GD.N0232.N0719.N0842.d010920
#print axioms _root_.GD.N0232.N0719.N0842.d010923
