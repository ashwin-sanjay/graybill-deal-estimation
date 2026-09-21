import GD.Module1161
import GD.Module1109
import GD.Module1063































open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1354

noncomputable section

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1409
open _root_.GD.N0232.N0720.N1418
open _root_.GD.N0232.N0720.N1478
open _root_.GD.N0232.N0720.N1479

variable {m n : ℕ}






abbrev d018739
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  _root_.GD.N0232.N0720.N1036.d014669 m n p




def d018740
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∀ q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
    ¬ _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) q p



def d018741
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : Prop :=
  ∀ q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
    _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) q p →
      0 ≤ ⟪p, q - p⟫





theorem d018742
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1354.d018739 (m := m) (n := n) p ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p := by
  constructor
  · exact _root_.GD.N0232.N0720.N1478.d017820 m n
  · intro h q hq theta
    rw [h q hq]





theorem d018743
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1354.d018741 (m := m) (n := n) p ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p := by
  constructor
  · intro hbar q hq
    have href := hq _root_.GD.N0232.N0720.N1080.d014169
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
    have href' : ENNReal.ofReal (‖q‖ ^ 2) ≤
        ENNReal.ofReal (‖p‖ ^ 2) := by
      simpa only [zero_sub, norm_neg] using href
    have hnorm : ‖q‖ ^ 2 ≤ ‖p‖ ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖p‖)).mp href'
    have hinner := hbar q hq
    have hdecomp := norm_add_sq_real p (q - p)
    have hadd : p + (q - p) = q := by abel
    rw [hadd] at hdecomp
    have hdiff : ‖q - p‖ = 0 := by
      nlinarith [norm_nonneg (q - p)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hdiff)
  · intro hterminal q hq
    rw [hterminal q hq]
    simp


theorem d018744
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1354.d018741 (m := m) (n := n) p ↔
      _root_.GD.N0232.N0720.N1159.d014633 m n p = p := by
  rw [_root_.GD.N0232.N0720.N1354.d018743,
    _root_.GD.N0232.N0720.N1159.d014635]





theorem d018745 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014172 m n ≪ _root_.GD.N0232.N0720.N1080.d014171 m n theta := by
  simpa [_root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
    (_root_.GD.N0232.N0720.d009063
      m n theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos).2




theorem d018746
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    (hne : q ≠ p) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < ∫ omega, (q omega - p omega) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  have hpMem := _root_.GD.N0232.N0720.N1418.d017030 m n theta p (hp theta)
  have hqMem := _root_.GD.N0232.N0720.N1418.d017030 m n theta q (hq theta)
  have hdiffMem : MemLp (fun omega ↦ q omega - p omega) 2
      (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    have h := hqMem.sub hpMem
    simpa [_root_.GD.N0232.N0720.N1418.d017027, Pi.sub_def, sub_sub_sub_cancel_right] using h
  have hint : Integrable (fun omega ↦ (q omega - p omega) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := hdiffMem.integrable_sq
  have hnonneg :
      0 ≤ ∫ omega, (q omega - p omega) ^ 2 ∂(_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    integral_nonneg fun omega ↦ sq_nonneg _
  apply lt_of_le_of_ne hnonneg
  intro hzero
  have hsquareAE :
      (fun omega ↦ (q omega - p omega) ^ 2) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun omega ↦ sq_nonneg _) hint).1 hzero.symm
  have hqpLaw :
      (fun omega ↦ q omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
        (fun omega ↦ p omega) := by
    filter_upwards [hsquareAE] with omega hsquare
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  have hqpReference :
      (fun omega ↦ q omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        (fun omega ↦ p omega) :=
    (_root_.GD.N0232.N0720.N1354.d018745 (m := m) (n := n) theta).ae_le
      hqpLaw
  exact hne (Lp.ext hqpReference)




theorem d018747
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) q p)
    (hne : q ≠ p) :
    ∃ b : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) b p := by
  let b : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    p + (1 / 2 : ℝ) • (q - p)
  have hqFinite : _root_.GD.N0232.N0720.N1159.d014637 m n q := fun theta ↦
    ne_top_of_le_ne_top (hp theta) (hdom theta)
  have hbFinite : _root_.GD.N0232.N0720.N1159.d014637 m n b := by
    intro theta
    exact _root_.GD.N0232.N0720.N1479.d017056 m n theta p q (1 / 2 : ℝ)
      (hp theta) (hqFinite theta)
  refine ⟨b, ?_⟩
  intro theta
  have hmargin := _root_.GD.N0232.N0720.N1479.d017057 m n theta p q
    (hp theta) (hdom theta) (1 / 2 : ℝ) (by norm_num)
  have henergy := _root_.GD.N0232.N0720.N1354.d018746 p q hp hqFinite hne theta
  have hreal : (_root_.GD.N0232.N0720.N1080.d014182 m n theta b).toReal < (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal := by
    change (_root_.GD.N0232.N0720.N1080.d014182 m n theta
      (p + (1 / 2 : ℝ) • (q - p))).toReal <
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta p).toReal
    norm_num at hmargin
    linarith
  exact (ENNReal.toReal_lt_toReal (hbFinite theta) (hp theta)).1 hreal




theorem d018748
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1354.d018740 (m := m) (n := n) p ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p := by
  constructor
  · intro hnone q hq
    by_contra hne
    obtain ⟨b, hb⟩ :=
      _root_.GD.N0232.N0720.N1354.d018747
        p q hp hq hne
    exact hnone b hb
  · intro hterminal q hstrict
    have heq := hterminal q (fun theta ↦ (hstrict theta).le)
    subst q
    exact (lt_irrefl (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p))
      (hstrict _root_.GD.N0232.N0720.N1080.d014169)






def d018749 (_ : Unit) (_ : Bool) : ENNReal := 0


theorem d018750 :
    ∀ q : Bool,
      ¬ _root_.GD.N0230.N0608.d000675 _root_.GD.N0232.N0720.N1354.d018749 q false := by
  intro q hstrict
  have := hstrict ()
  simp [_root_.GD.N0232.N0720.N1354.d018749] at this



theorem d018751 :
    ¬ _root_.GD.N0230.N0608.d000674 _root_.GD.N0232.N0720.N1354.d018749 false := by
  intro hterminal
  have heq : true = false := hterminal true (by
    intro theta
    simp [_root_.GD.N0232.N0720.N1354.d018749])
  simp at heq



theorem d018752 :
    (∀ q : Bool,
      ¬ _root_.GD.N0230.N0608.d000675 _root_.GD.N0232.N0720.N1354.d018749 q false) ∧
      ¬ _root_.GD.N0230.N0608.d000674 _root_.GD.N0232.N0720.N1354.d018749 false :=
  ⟨_root_.GD.N0232.N0720.N1354.d018750,
    _root_.GD.N0232.N0720.N1354.d018751⟩





theorem d018753
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1354.d018739 s.value := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  apply exists_congr
  intro s
  rw [_root_.GD.N0232.N0720.N1354.d018742]



theorem d018754
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1354.d018740 s.value := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  apply exists_congr
  intro s
  rw [_root_.GD.N0232.N0720.N1354.d018748 s.value s.finiteRisk]




theorem d018755
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1354.d018741 s.value := by
  rw [_root_.GD.N0232.N0720.N1409.d018620
    (m := m) (n := n) hm hn]
  apply exists_congr
  intro s
  rw [_root_.GD.N0232.N0720.N1354.d018743]

end

end N1354
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1354.d018742
#print axioms _root_.GD.N0232.N0720.N1354.d018743
#print axioms _root_.GD.N0232.N0720.N1354.d018746
#print axioms _root_.GD.N0232.N0720.N1354.d018747
#print axioms _root_.GD.N0232.N0720.N1354.d018748
#print axioms _root_.GD.N0232.N0720.N1354.d018752
#print axioms _root_.GD.N0232.N0720.N1354.d018753
#print axioms _root_.GD.N0232.N0720.N1354.d018754
#print axioms _root_.GD.N0232.N0720.N1354.d018755
