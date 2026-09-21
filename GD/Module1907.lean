import GD.Module1451
import GD.Module0457
import GD.Module1521
import GD.Module1905

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set
open scoped BigOperators

namespace GD.N0056
noncomputable section
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0059 _root_.GD.N0060
open _root_.GD.N0062 _root_.GD.N0061
open _root_.GD.N0057 _root_.GD.N0025
open _root_.GD.N0014


def d030906 (i : Fin 7) (x : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0014.d030876 i * _root_.GD.N0062.d023641 (_root_.GD.N0014.d030875 i) x

theorem d030907 (i : Fin 7) :
    (_root_.GD.N0014.d030875 i : ℝ) = _root_.GD.N0061.d022974 i := rfl

theorem d030908 (i : Fin 7) : _root_.GD.N0014.d030876 i = _root_.GD.N0061.d022975 i := by
  fin_cases i <;> norm_num [_root_.GD.N0014.d030876, _root_.GD.N0061.d022975, _root_.GD.N0059.d006977]

theorem d030909 (i : Fin 7) (x : _root_.GD.N0232.N0720.N1436.d013217)
    (hx : x ∈ _root_.GD.N0062.d023638) :
    _root_.GD.N0056.d030906 i x = _root_.GD.N0057.d022150 (_root_.GD.N0061.d022974 i) (_root_.GD.N0061.d022975 i) x.1 x.2 := by
  rw [_root_.GD.N0056.d030906, _root_.GD.N0062.d023641, indicator_of_mem hx,
    _root_.GD.N0056.d030908, _root_.GD.N0057.d022165]
  rfl

theorem d030910 (i : Fin 7) (x : _root_.GD.N0232.N0720.N1436.d013217) :
    0 ≤ _root_.GD.N0056.d030906 i x :=
  mul_nonneg (_root_.GD.N0014.d030879 i) (_root_.GD.N0062.d023642 _ _)

theorem d030911 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0:ℝ) 1) :
    Integrable (fun x => ∑ i, _root_.GD.N0056.d030906 i x *
      (g (_root_.GD.N0062.d023632 x) - (_root_.GD.N0059.d006976 i : ℝ) / _root_.GD.N0059.d006973)^2)
      (volume.prod volume) := by
  exact _root_.GD.N0062.d023646 _root_.GD.N0014.d030875 _root_.GD.N0014.d030876 g hg
    (B := 1) (fun x => by rw [abs_of_nonneg (hb x).1]; exact (hb x).2)

theorem d030912 (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0:ℝ) 1) :
    _root_.GD.N0014.d030878 g = ∫ x, ∑ i, _root_.GD.N0056.d030906 i x *
      (g (_root_.GD.N0062.d023632 x) - (_root_.GD.N0059.d006976 i : ℝ) / _root_.GD.N0059.d006973)^2
      ∂volume.prod volume := by
  exact _root_.GD.N0062.d023647 _root_.GD.N0014.d030875 _root_.GD.N0014.d030876 g hg
    (B := 1) (fun x => by rw [abs_of_nonneg (hb x).1]; exact (hb x).2)

theorem d030913 (c : _root_.GD.N0059.d006978) (hc : c.d006994) :
    _root_.GD.N0060.d007105 c ⊆ _root_.GD.N0062.d023638 := by
  intro x hx
  have hu0 : 0 ≤ _root_.GD.N0060.d007101 c := by unfold _root_.GD.N0060.d007101; positivity
  have hu1 : _root_.GD.N0060.d007102 c ≤ 1 := by
    apply (div_le_one (by norm_num [_root_.GD.N0059.d006974] : (0:ℝ)<_root_.GD.N0059.d006974)).mpr
    exact_mod_cast hc.2.2.2.1
  have hz0 : 0 ≤ _root_.GD.N0060.d007103 c := by unfold _root_.GD.N0060.d007103; positivity
  exact ⟨⟨hu0.trans_lt hx.1.1, hx.1.2.trans hu1⟩, hz0.trans_lt hx.2.1⟩


theorem d030914 (c : _root_.GD.N0059.d006978) (hc : c.d006994)
    (x : _root_.GD.N0232.N0720.N1436.d013217) (hx : x ∈ _root_.GD.N0060.d007105 c) (i : Fin 7) :
    (∑ j : _root_.GD.N0025.d005225, _root_.GD.N0025.d005231 (_root_.GD.N0060.d007101 c) (_root_.GD.N0060.d007102 c) (_root_.GD.N0060.d007103 c) (_root_.GD.N0060.d007104 c) j x *
      ((c.density (_root_.GD.N0060.d007106 j) i : ℝ) / _root_.GD.N0059.d006971)) ≤ _root_.GD.N0056.d030906 i x := by
  rw [_root_.GD.N0056.d030909 i x (_root_.GD.N0056.d030913 c hc hx)]
  exact _root_.GD.N0061.d022996 c hc i x hx



theorem d030915 (cs : List _root_.GD.N0059.d006978)
    (hvalid : ∀ c ∈ cs, c.d006994)
    (hmatch : ∀ c ∈ cs, c.d006995 _root_.GD.N0059.d007016 _root_.GD.N0059.d007017)
    (hkey : (cs.map _root_.GD.N0059.d006978.d006979).IsChain (· < ·))
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0:ℝ) 1) :
    (_root_.GD.N0059.d007000 cs : ℝ) / (2:ℝ)^141 ≤ _root_.GD.N0014.d030878 g := by
  have hu (i : Fin cs.length) : _root_.GD.N0060.d007101 (cs.get i) < _root_.GD.N0060.d007102 (cs.get i) :=
    div_lt_div_of_pos_right (by exact_mod_cast (hvalid _ (List.get_mem cs i)).2.2.1)
      (by norm_num [_root_.GD.N0059.d006974])
  have hz0 (i : Fin cs.length) : 0 ≤ _root_.GD.N0060.d007103 (cs.get i) := by unfold _root_.GD.N0060.d007103; positivity
  have hz (i : Fin cs.length) : _root_.GD.N0060.d007103 (cs.get i) < _root_.GD.N0060.d007104 (cs.get i) :=
    div_lt_div_of_pos_right (by exact_mod_cast (hvalid _ (List.get_mem cs i)).2.2.2.2.2.1)
      (by norm_num [_root_.GD.N0059.d006975])
  have hA (i : Fin cs.length) (j : _root_.GD.N0025.d005225) : 0 < ∑ k, (cs.get i).density (_root_.GD.N0060.d007106 j) k :=
    ((hvalid _ (List.get_mem cs i)).2.2.2.2.2.2.2 (_root_.GD.N0060.d007106 j)).1
  have hdisc (i : Fin cs.length) (j : _root_.GD.N0025.d005225) :
      (∑ k, (cs.get i).density (_root_.GD.N0060.d007106 j) k * _root_.GD.N0059.d006976 k)^2 +
        (∑ k, (cs.get i).density (_root_.GD.N0060.d007106 j) k) * (cs.get i).quadratic (_root_.GD.N0060.d007106 j) ≤
      (∑ k, (cs.get i).density (_root_.GD.N0060.d007106 j) k) *
        (∑ k, (cs.get i).density (_root_.GD.N0060.d007106 j) k * _root_.GD.N0059.d006976 k^2) :=
    ((hvalid _ (List.get_mem cs i)).2.2.2.2.2.2.2 (_root_.GD.N0060.d007106 j)).2
  have h := _root_.GD.N0025.d005245 _root_.GD.N0059.d006976 _root_.GD.N0059.d006971 _root_.GD.N0059.d006973
    (by norm_num [_root_.GD.N0059.d006971]) (by norm_num [_root_.GD.N0059.d006973]) _root_.GD.N0056.d030906
    (fun x => g (_root_.GD.N0062.d023632 x))
    (fun i : Fin cs.length => _root_.GD.N0060.d007101 (cs.get i))
    (fun i => _root_.GD.N0060.d007102 (cs.get i)) (fun i => _root_.GD.N0060.d007103 (cs.get i)) (fun i => _root_.GD.N0060.d007104 (cs.get i))
    hu hz0 hz (_root_.GD.N0060.d007116 cs hvalid hmatch hkey)
    (fun i j k => (cs.get i).density (_root_.GD.N0060.d007106 j) k)
    (fun i j => (cs.get i).quadratic (_root_.GD.N0060.d007106 j)) hA hdisc
    (fun i x hx k => _root_.GD.N0056.d030914 (cs.get i) (hvalid _ (List.get_mem cs i)) x hx k)
    (_root_.GD.N0056.d030911 g hg hb)
    (ae_of_all _ (fun x => Finset.sum_nonneg (fun i _ =>
      mul_nonneg (_root_.GD.N0056.d030910 i x) (sq_nonneg _))))
  rw [_root_.GD.N0060.d007120 cs hvalid, ← _root_.GD.N0056.d030912 g hg hb] at h
  exact h

end
end GD.N0056

#print axioms _root_.GD.N0056.d030909
#print axioms _root_.GD.N0056.d030911
#print axioms _root_.GD.N0056.d030912
#print axioms _root_.GD.N0056.d030913
#print axioms _root_.GD.N0056.d030914
#print axioms _root_.GD.N0056.d030915
