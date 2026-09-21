import GD.Module1816
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0005.N0248

open Set

noncomputable section

theorem d030111 {m n a b x y u v w : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (huv : u < v) (hvw : v < w)
    (hu : ∀ z, _root_.GD.N0005.N0248.d030071 m n a b x y z ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u)
    (hv : ∀ z, _root_.GD.N0005.N0248.d030071 m n a b x y z ≤ _root_.GD.N0005.N0248.d030071 m n a b x y v)
    (hw : ∀ z, _root_.GD.N0005.N0248.d030071 m n a b x y z ≤ _root_.GD.N0005.N0248.d030071 m n a b x y w) : False := by
  classical
  obtain ⟨z, hz, hzero⟩ := exists_deriv_eq_zero huv
    (_root_.GD.N0005.N0248.d030083 ha hb).continuousOn (le_antisymm (hv u) (hu v))
  obtain ⟨S, hcard, hS⟩ := _root_.GD.N0005.N0248.d030082 hm hn ha hb (x := x) (y := y)
  have hsub : ({u,z,v,w} : Finset ℝ) ⊆ S := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact (hS _).2 (_root_.GD.N0005.N0248.d030086 hu)
    · exact (hS _).2 hzero
    · exact (hS _).2 (_root_.GD.N0005.N0248.d030086 hv)
    · exact (hS _).2 (_root_.GD.N0005.N0248.d030086 hw)
  have h4 : ({u,z,v,w} : Finset ℝ).card = 4 := by
    have huz := hz.1.ne
    have hzv := hz.2.ne
    have hzw := (hz.2.trans hvw).ne
    have huw := (huv.trans hvw).ne
    simp [huz, hzv, hzw, huw, huv.ne, hvw.ne]
  have hle := Finset.card_le_card hsub
  rw [h4] at hle
  omega

theorem d030112 {m n a b x y : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (S : Finset ℝ)
    (hS : ∀ u ∈ S, ∀ z, _root_.GD.N0005.N0248.d030071 m n a b x y z ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u) :
    S.card ≤ 2 := by
  by_contra hcard
  obtain ⟨u,v,w,hu,hv,hw,huv,huw,hvw⟩ := Finset.two_lt_card_iff.1 (lt_of_not_ge hcard)
  have hu' := hS u hu
  have hv' := hS v hv
  have hw' := hS w hw
  rcases lt_or_gt_of_ne huv with huv | hvu
  · rcases lt_or_gt_of_ne hvw with hvw | hwv
    · exact _root_.GD.N0005.N0248.d030111 hm hn ha hb huv hvw hu' hv' hw'
    · rcases lt_or_gt_of_ne huw with huw | hwu
      · exact _root_.GD.N0005.N0248.d030111 hm hn ha hb huw hwv hu' hw' hv'
      · exact _root_.GD.N0005.N0248.d030111 hm hn ha hb hwu huv hw' hu' hv'
  · rcases lt_or_gt_of_ne huw with huw | hwu
    · exact _root_.GD.N0005.N0248.d030111 hm hn ha hb hvu huw hv' hu' hw'
    · rcases lt_or_gt_of_ne hvw with hvw | hwv
      · exact _root_.GD.N0005.N0248.d030111 hm hn ha hb hvw hwu hv' hw' hu'
      · exact _root_.GD.N0005.N0248.d030111 hm hn ha hb hwv hvu hw' hv' hu'

end
end GD.N0005.N0248

#print axioms _root_.GD.N0005.N0248.d030111
#print axioms _root_.GD.N0005.N0248.d030112
