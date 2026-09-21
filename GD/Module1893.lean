import GD.Module0504
import GD.Module1373
import GD.Module1886
import GD.Module1887
import GD.Module1888

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0053
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1066 _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1071 _root_.GD.N0232.N0720.N1442
open _root_.GD.N0232.N0720.N1069
open _root_.GD.N0107 _root_.GD.N0141 _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1256
open _root_.GD.N0076.N0313
open _root_.GD.N0082
open _root_.GD.N0082.N0335

abbrev d030776 (θ : _root_.GD.N0232.N0720.N1080.d014168) : ℝ := _root_.GD.N0232.N0720.N1067.d014408 2 3 θ

theorem d030777 (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0053.d030776 θ ∈ Ioo (0:ℝ) 1 :=
  ⟨_root_.GD.N0232.N0720.N1067.d014409 2 3 (by omega) (by omega) θ,
    _root_.GD.N0232.N0720.N1067.d014410 2 3 (by omega) (by omega) θ⟩

def d030778 (θ : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0107.d009045 2 3 θ.scale₁ θ.scale₂ * Real.sqrt (_root_.GD.N0053.d030776 θ) * (1-_root_.GD.N0053.d030776 θ)

theorem d030779 (θ : _root_.GD.N0232.N0720.N1080.d014168) : 0 < _root_.GD.N0053.d030778 θ :=
  mul_pos (mul_pos
    (_root_.GD.N0107.d009049 (by omega) (by omega) θ.scale₁_pos θ.scale₂_pos)
    (Real.sqrt_pos.mpr (_root_.GD.N0053.d030777 θ).1)) (sub_pos.mpr (_root_.GD.N0053.d030777 θ).2)

theorem d030780 (H : ℝ → ℝ) (hH : Measurable H)
    (hHI : ∀ u, H u ∈ Icc (0:ℝ) 1) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 3 θ) (fun ω => _root_.GD.N0082.N0335.d030724 2 3 H ω-θ.location) =
      _root_.GD.N0053.d030778 θ * (Real.sqrt (_root_.GD.N0053.d030776 θ)+_root_.GD.N0053.d007673 H (_root_.GD.N0053.d030776 θ)) := by
  have hbound : ∀ u, |H u|≤1 := fun u => by
    rw [abs_of_nonneg (hHI u).1]
    exact (hHI u).2
  have h := _root_.GD.N0082.N0335.d030730 2 3 (by omega) (by omega) H hH
    (by norm_num : (0:ℝ)≤1) hbound θ.location θ.scale₁ θ.scale₂ θ.scale₁_pos θ.scale₂_pos
  have h' : _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 3 θ) (fun ω => _root_.GD.N0082.N0335.d030724 2 3 H ω-θ.location) =
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 3 θ) (_root_.GD.N0107.d012732 2 3 θ.location (_root_.GD.N0053.d030776 θ)) +
        _root_.GD.N0107.d009045 2 3 θ.scale₁ θ.scale₂ *
          ∫ u, (H (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0053.d030776 θ/(2*(1-_root_.GD.N0053.d030776 θ))) u)-_root_.GD.N0053.d030776 θ)^2
            ∂ProbabilityTheory.betaMeasure (1/2) 1 := by
    have ho (t : ℝ) : _root_.GD.N0232.N0720.N1091.d012762 (_root_.GD.N0232.N0720.N1436.d013207 2) (_root_.GD.N0232.N0720.N1436.d013208 3) t =
        t/(2*(1-t)) := by
      norm_num [_root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, _root_.GD.N0232.N0720.N1091.d012762,
        div_eq_mul_inv, mul_inv_rev]
      ring
    rw [ho] at h
    simpa [_root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0053.d030776, _root_.GD.N0232.N0720.N1067.d014408, _root_.GD.N0232.N0720.N1436.d013207,
      _root_.GD.N0232.N0720.N1436.d013208] using h
  rw [h', _root_.GD.N0232.N0720.N1071.d014426 2 3 (by omega) (by omega) θ,
    _root_.GD.N0054.d022110 (_root_.GD.N0053.d030777 θ) H]
  change _root_.GD.N0107.d009045 2 3 θ.scale₁ θ.scale₂ * _root_.GD.N0232.N0720.N1442.d013866 (_root_.GD.N0053.d030776 θ) +
    _root_.GD.N0107.d009045 2 3 θ.scale₁ θ.scale₂ *
      (Real.sqrt (_root_.GD.N0053.d030776 θ)*(1-_root_.GD.N0053.d030776 θ)*_root_.GD.N0053.d007673 H (_root_.GD.N0053.d030776 θ)) = _
  have hf : _root_.GD.N0053.d030778 θ*Real.sqrt (_root_.GD.N0053.d030776 θ) =
      _root_.GD.N0107.d009045 2 3 θ.scale₁ θ.scale₂ * _root_.GD.N0232.N0720.N1442.d013866 (_root_.GD.N0053.d030776 θ) := by
    unfold _root_.GD.N0053.d030778 _root_.GD.N0232.N0720.N1442.d013866
    calc
      _ = _root_.GD.N0107.d009045 2 3 θ.scale₁ θ.scale₂ *
          (Real.sqrt (_root_.GD.N0053.d030776 θ)*Real.sqrt (_root_.GD.N0053.d030776 θ))*(1-_root_.GD.N0053.d030776 θ) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (_root_.GD.N0053.d030777 θ).1.le]; ring
  rw [← hf]
  unfold _root_.GD.N0053.d030778
  ring

theorem d030781 (H : ℝ → ℝ) (hH : Measurable H)
    (hHI : ∀ u, H u ∈ Icc (0:ℝ) 1) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 2 3 θ (_root_.GD.N0082.N0335.d030724 2 3 H) =
      ENNReal.ofReal (_root_.GD.N0053.d030778 θ*(Real.sqrt (_root_.GD.N0053.d030776 θ)+_root_.GD.N0053.d007673 H (_root_.GD.N0053.d030776 θ))) := by
  have hint := (_root_.GD.N0082.N0335.d030728 2 3 (by omega) (by omega) H hH hHI θ).integrable_sq
  calc
    _ = ENNReal.ofReal (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 3 θ)
        (fun ω => _root_.GD.N0082.N0335.d030724 2 3 H ω-θ.location)) :=
      (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => sq_nonneg _)).symm
    _ = _ := congrArg ENNReal.ofReal (_root_.GD.N0053.d030780 H hH hHI θ)

theorem d030782 {H G : ℝ → ℝ}
    (h : ∀ u ∈ Ioo (0:ℝ) 1, H u=G u) (t : ℝ) : _root_.GD.N0053.d007673 H t=_root_.GD.N0053.d007673 G t := by
  unfold _root_.GD.N0053.d007673
  congr 1
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0053.d005105 1 (1/2)] with u hu
  rw [h u hu]

theorem d030783 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1066.d014320 2 3 (by omega) (by omega) θ =
      ENNReal.ofReal (_root_.GD.N0053.d030778 θ*(Real.sqrt (_root_.GD.N0053.d030776 θ)+_root_.GD.N0053.d007673 id (_root_.GD.N0053.d030776 θ))) := by
  have hc : _root_.GD.N0053.d007673 _root_.GD.N0082.N0335.d030710 (_root_.GD.N0053.d030776 θ)=_root_.GD.N0053.d007673 id (_root_.GD.N0053.d030776 θ) :=
    _root_.GD.N0053.d030782 (fun _u hu => _root_.GD.N0082.N0335.d030712 ⟨hu.1.le,hu.2.le⟩) _
  rw [← hc, ← _root_.GD.N0053.d030781 _root_.GD.N0082.N0335.d030710 _root_.GD.N0082.N0335.d030713 _root_.GD.N0082.N0335.d030711 θ,
    _root_.GD.N0082.N0335.d030727]
  exact (_root_.GD.N0232.N0720.N1080.d014199
    2 3 (by omega) (by omega) θ).symm

def d030784 : _root_.GD.N0232.N0720.N1080.d014170 2 3 → ℝ := _root_.GD.N0082.N0335.d030724 2 3 _root_.GD.N0053.d007665

theorem d030785 : _root_.GD.N0053.d030784 ∈ _root_.GD.N0232.N0720.N1256.d015552 2 3 :=
  _root_.GD.N0082.N0329.d030732 2 3 (by omega) (by omega)
    _root_.GD.N0053.d007665 _root_.GD.N0053.d007668 _root_.GD.N0053.d007667

theorem d030786 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0076.N0313.d030568 2 3 (by omega) (by omega) θ _root_.GD.N0053.d030784 = ENNReal.ofReal (_root_.GD.N0053.d007688 (_root_.GD.N0053.d030776 θ)) := by
  unfold _root_.GD.N0076.N0313.d030568 _root_.GD.N0053.d030784
  rw [_root_.GD.N0053.d030781 _root_.GD.N0053.d007665 _root_.GD.N0053.d007668 _root_.GD.N0053.d007667 θ,
    _root_.GD.N0053.d030783]
  have hb : 0 < _root_.GD.N0053.d030778 θ*(Real.sqrt (_root_.GD.N0053.d030776 θ)+_root_.GD.N0053.d007673 id (_root_.GD.N0053.d030776 θ)) :=
    mul_pos (_root_.GD.N0053.d030779 θ) (_root_.GD.N0053.d007689 ⟨(_root_.GD.N0053.d030777 θ).1.le,(_root_.GD.N0053.d030777 θ).2.le⟩)
  rw [← ENNReal.ofReal_div_of_pos hb]
  congr 1
  exact mul_div_mul_left _ _ (_root_.GD.N0053.d030779 θ).ne'

theorem d030787 :
    ∃ (J : ℕ) (f : _root_.GD.N0232.N0720.N1080.d014170 2 3 → ℝ), 1≤J ∧ f ∈ _root_.GD.N0232.N0720.N1256.d015552 2 3 ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 2 3 θ f ≤
        ENNReal.ofReal (_root_.GD.N0082.d030598 J)*_root_.GD.N0232.N0720.N1066.d014320 2 3 (by omega) (by omega) θ := by
  apply _root_.GD.N0082.N0329.d030735 2 3 (by omega) (by omega)
    (_root_.GD.N0232.N0720.N1080.d014176 2 3 (by omega) (by omega)) _root_.GD.N0053.d030784
    (_root_.GD.N0232.N0720.N1221.d015562
      2 3 (by omega) (by omega)) _root_.GD.N0053.d030785
    (_root_.GD.N0232.N0720.N1069.d014352 2 3) (fun θ => _root_.GD.N0053.d030777 θ)
    (_root_.GD.N0082.N0335.d030720 2 3 (by omega) (by omega)) _root_.GD.N0053.d007688
    (fun t _ => _root_.GD.N0082.N0333.d030739 2 3 (by omega) (by omega) t)
    (fun t _ => _root_.GD.N0053.d007690 t)
    (_root_.GD.N0082.N0335.d030721 2 3 (by omega) (by omega))
    (_root_.GD.N0082.N0335.d030722 2 3 (by omega) (by omega))
    _root_.GD.N0053.d007691 (by rw [_root_.GD.N0053.d007692]; norm_num) (by rw [_root_.GD.N0053.d007693]; norm_num)
    (fun θ => (_root_.GD.N0082.N0333.d030738
      2 3 (by omega) (by omega) θ).le)
    (fun θ => (_root_.GD.N0053.d030786 θ).le)

theorem d030788 : _root_.GD.N0076.N0313.d030569 2 3 (by omega) (by omega)<1 := by
  apply (_root_.GD.N0082.d030609 2 3 (by omega) (by omega)).mp
  obtain ⟨J,f,hJ,hf,hcap⟩ := _root_.GD.N0053.d030787
  exact ⟨J,hJ,f,hf.1.1,hcap⟩

end
end GD.N0053

#print axioms _root_.GD.N0053.d030781
#print axioms _root_.GD.N0053.d030786
#print axioms _root_.GD.N0053.d030787
#print axioms _root_.GD.N0053.d030788
