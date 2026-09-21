import GD.Module1821
import GD.Module1817

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0005.N0247

open Set _root_.GD.N0005.N0248
open _root_.GD.N0232.N0719.N1011

noncomputable section

def d030136 (A v : ℝ) : ℝ := _root_.GD.N0005.N0248.d030118 A v - _root_.GD.N0005.N0248.d030118 A A

theorem d030137 {A v : ℝ} (hA : 0 < A) (hv : 0 < v) :
    _root_.GD.N0005.N0247.d030136 A v = A / v - 1 - Real.log (A / v) := by
  rw [Real.log_div hA.ne' hv.ne']
  dsimp [_root_.GD.N0005.N0247.d030136, _root_.GD.N0005.N0248.d030118]
  rw [div_self hA.ne']
  ring

theorem d030138 {A v : ℝ} (hA : 0 < A) (hv : 0 < v) :
    0 ≤ _root_.GD.N0005.N0247.d030136 A v :=
  sub_nonneg.2 (_root_.GD.N0005.N0248.d030119 hA hv)

theorem d030139 {A v : ℝ} (hA : 0 < A) (hv : 0 < v) :
    _root_.GD.N0005.N0247.d030136 A v = 0 ↔ v = A := by
  rw [_root_.GD.N0005.N0247.d030136, sub_eq_zero, eq_comm]
  exact _root_.GD.N0005.N0248.d030121 hA hv

theorem d030140
    (m n a b x y u v w : ℝ) (ha : 0 < a) (hb : 0 < b) :
    _root_.GD.N0005.N0248.d030122 m n a b x y u v w =
      _root_.GD.N0005.N0248.d030071 m n a b x y u - (m + n) / 2 -
        (m * _root_.GD.N0005.N0247.d030136 (_root_.GD.N0005.N0248.d030070 a x u) v +
          n * _root_.GD.N0005.N0247.d030136 (_root_.GD.N0005.N0248.d030070 b y u) w) / 2 := by
  rw [← _root_.GD.N0005.N0248.d030123 m n a b x y u ha hb]
  dsimp [_root_.GD.N0005.N0248.d030122, _root_.GD.N0005.N0247.d030136]
  ring

theorem d030141
    {m n a b x y : ℝ} (hm : 0 < m) (hn : 0 < n)
    (ha : 0 < a) (hb : 0 < b) :
    ∃ S : Finset ℝ, S.Nonempty ∧ S.card ≤ 2 ∧
      ∀ u : ℝ, u ∈ S ↔
        ∀ v : ℝ, _root_.GD.N0005.N0248.d030071 m n a b x y v ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u := by
  classical
  obtain ⟨C, _, hC⟩ := _root_.GD.N0005.N0248.d030082 hm hn ha hb (x := x) (y := y)
  let S := C.filter fun u => ∀ v : ℝ,
    _root_.GD.N0005.N0248.d030071 m n a b x y v ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u
  have hS (u : ℝ) : u ∈ S ↔
      ∀ v : ℝ, _root_.GD.N0005.N0248.d030071 m n a b x y v ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u := by
    constructor
    · intro hu
      exact (Finset.mem_filter.1 hu).2
    · intro hu
      exact Finset.mem_filter.2 ⟨(hC u).2 (_root_.GD.N0005.N0248.d030086 hu), hu⟩
  obtain ⟨u, _, hu⟩ := _root_.GD.N0005.N0248.d030085 hm.le hn.le ha hb (x := x) (y := y)
  exact ⟨S, ⟨u, (hS u).2 hu⟩,
    _root_.GD.N0005.N0248.d030112 hm hn ha hb S (fun u hu => (hS u).1 hu), hS⟩

theorem d030142
    {m n a b x y : ℝ} (hm : 0 < m) (hn : 0 < n)
    (ha : 0 < a) (hb : 0 < b) :
    ∃ u v w : ℝ, 0 < v ∧ 0 < w ∧ u ∈ Icc (min x y) (max x y) ∧
      ∀ u' v' w' : ℝ, 0 < v' → 0 < w' →
        _root_.GD.N0005.N0248.d030122 m n a b x y u' v' w' ≤
          _root_.GD.N0005.N0248.d030122 m n a b x y u v w := by
  obtain ⟨u, hu, hmax⟩ := _root_.GD.N0005.N0248.d030085 hm.le hn.le ha hb
  refine ⟨u, _root_.GD.N0005.N0248.d030070 a x u, _root_.GD.N0005.N0248.d030070 b y u,
    _root_.GD.N0005.N0248.d030074 ha x u, _root_.GD.N0005.N0248.d030074 hb y u, hu, ?_⟩
  exact (_root_.GD.N0005.N0248.d030126 hm hn ha hb
    (_root_.GD.N0005.N0248.d030074 ha x u) (_root_.GD.N0005.N0248.d030074 hb y u)).2 ⟨rfl, rfl, hmax⟩

theorem d030143
    (m n : ℕ) (u x y zX zY : ℝ) {v w : ℝ} (hv : 0 < v) (hw : 0 < w) :
    0 < _root_.GD.N0232.N0719.N1011.d011284 m u (Real.sqrt v) x zX *
      _root_.GD.N0232.N0719.N1011.d011284 n u (Real.sqrt w) y zY := by
  unfold _root_.GD.N0232.N0719.N1011.d011284
  positivity

theorem d030144
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (x y : ℝ) {zX zY : ℝ} (hX : 0 < zX) (hY : 0 < zY) :
    ∃ u v w : ℝ, 0 < v ∧ 0 < w ∧ u ∈ Icc (min x y) (max x y) ∧
      ∀ u' v' w' : ℝ, 0 < v' → 0 < w' →
        _root_.GD.N0232.N0719.N1011.d011284 m u' (Real.sqrt v') x zX *
            _root_.GD.N0232.N0719.N1011.d011284 n u' (Real.sqrt w') y zY ≤
          _root_.GD.N0232.N0719.N1011.d011284 m u (Real.sqrt v) x zX *
            _root_.GD.N0232.N0719.N1011.d011284 n u (Real.sqrt w) y zY := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm1 : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < m - 1)
  have hn1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < n - 1)
  obtain ⟨u, v, w, hv, hw, hu, hmax⟩ :=
    _root_.GD.N0005.N0247.d030142 (x := x) (y := y) hm0 hn0 (mul_pos hm1 hX) (mul_pos hn1 hY)
  refine ⟨u, v, w, hv, hw, hu, ?_⟩
  intro u' v' w' hv' hw'
  apply (Real.log_le_log_iff
    (_root_.GD.N0005.N0247.d030143 m n u' x y zX zY hv' hw')
    (_root_.GD.N0005.N0247.d030143 m n u x y zX zY hv hw)).1
  rw [_root_.GD.N0005.N0248.d030135 m n u' v' w' x y zX zY hv' hw',
    _root_.GD.N0005.N0248.d030135 m n u v w x y zX zY hv hw]
  exact add_le_add le_rfl (hmax u' v' w' hv' hw')

end
end GD.N0005.N0247

#print axioms _root_.GD.N0005.N0247.d030142
#print axioms _root_.GD.N0005.N0247.d030144
#print axioms _root_.GD.N0005.N0247.d030141
#print axioms _root_.GD.N0005.N0247.d030137
#print axioms _root_.GD.N0005.N0247.d030138
#print axioms _root_.GD.N0005.N0247.d030139
#print axioms _root_.GD.N0005.N0247.d030140
