import GD.Module1882
import GD.Module1322

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace GD.N0206.N0447
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1257
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441 _root_.GD.N0232.N0720.N1328
open _root_.GD.N0232.N0720.N1332
open _root_.GD.N0232.N0720.N1303 _root_.GD.N0232.N0720.N1325
open _root_.GD.N0096.N0344
open _root_.GD.N0206.N0449 _root_.GD.N0206.N0446

theorem d030695
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030491 m n d)
    {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ,
      Measurable g ∧ (∀ x, g x ∈ Icc (0 : ℝ) 1) ∧
      (∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g) ∧
      g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] fun x =>
        _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 := by
  obtain ⟨g, mu, hg, hb, hrep, hpost⟩ :=
    _root_.GD.N0232.N0720.N1303.d030498 m n hm hn hd
  have hdim : m + n = (m + n - 1) + 1 := by omega
  obtain ⟨m1⟩ := _root_.GD.N0232.N0720.N1325.d030508 m n (m + n - 1)
    hdim hm hn hd hg hb hrep mu hpost
  have hrep' := fun theta => (hrep theta).symm
  have hbound := _root_.GD.N0206.N0446.d021609 hm hn hg hb hrep' hC hcap
  obtain ⟨hleft, hright⟩ := _root_.GD.N0206.N0446.d021613 hbound
  refine ⟨g, hg, hb, hrep', ?_⟩
  exact _root_.GD.N0206.N0449.d030694 hm hn
    (mu : Measure _root_.GD.N0232.N0720.N1290.d004131) hpost m1
    (fun a ha => _root_.GD.N0206.N0446.d021611 hm hn hg hb hleft ha)
    (fun b hb' => _root_.GD.N0206.N0446.d021612 hm hn hg hb hright hb')

theorem d030696
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0096.N0344.d030491 m n d)
    {C : ℝ} (hC : 0 ≤ C)
    (hcap : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta))
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1332.d020106 m n
      (fun x => _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) t.1 ≤
      (C - 1) * t.1 * (1 - t.1) := by
  obtain ⟨g, hg, hb, hrep, hroot⟩ :=
    _root_.GD.N0206.N0447.d030695 hm hn hd hC hcap
  have hbound := _root_.GD.N0206.N0446.d021609 hm hn hg hb hrep hC hcap t
  rw [_root_.GD.N0232.N0720.N1332.d020108 hm hn hroot t] at hbound
  exact hbound

end
end GD.N0206.N0447

#print axioms _root_.GD.N0206.N0447.d030695
#print axioms _root_.GD.N0206.N0447.d030696
