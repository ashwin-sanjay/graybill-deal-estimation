



















import Mathlib

namespace GD.N0155
open MeasureTheory ProbabilityTheory


abbrev d006184 : Type := (Fin 11 → ℝ) × (Fin 11 → ℝ)



noncomputable def d006185 (m v1 v2 : ℝ) : Measure _root_.GD.N0155.d006184 :=
  (Measure.pi fun _ : Fin 11 => gaussianReal m v1.toNNReal).prod
    (Measure.pi fun _ : Fin 11 => gaussianReal m v2.toNNReal)


noncomputable def d006186 (x : _root_.GD.N0155.d006184) : ℝ := (∑ i, x.1 i) / 11


noncomputable def d006187 (x : _root_.GD.N0155.d006184) : ℝ := (∑ i, x.2 i) / 11


noncomputable def d006188 (x : _root_.GD.N0155.d006184) : ℝ := (∑ i, (x.1 i - _root_.GD.N0155.d006186 x) ^ 2) / 10


noncomputable def d006189 (x : _root_.GD.N0155.d006184) : ℝ := (∑ i, (x.2 i - _root_.GD.N0155.d006187 x) ^ 2) / 10


noncomputable def d006190 (x : _root_.GD.N0155.d006184) : ℝ := _root_.GD.N0155.d006186 x - _root_.GD.N0155.d006187 x



noncomputable def d006191 (x : _root_.GD.N0155.d006184) : ℝ :=
  11 * _root_.GD.N0155.d006189 x / (11 * _root_.GD.N0155.d006189 x + 11 * _root_.GD.N0155.d006188 x)


noncomputable def d006192 (x : _root_.GD.N0155.d006184) : ℝ :=
  _root_.GD.N0155.d006190 x ^ 2 / (_root_.GD.N0155.d006188 x / 11 + _root_.GD.N0155.d006189 x / 11)


noncomputable def d006193 (l : ℝ) : ℝ := l * (1 - l) * (l - 1 / 2)


noncomputable def d006194 (x : _root_.GD.N0155.d006184) : ℝ := _root_.GD.N0155.d006187 x + _root_.GD.N0155.d006191 x * _root_.GD.N0155.d006190 x



noncomputable def d006195 (x : _root_.GD.N0155.d006184) : ℝ :=
  _root_.GD.N0155.d006187 x + (_root_.GD.N0155.d006191 x + 11 / 250 * _root_.GD.N0155.d006193 (_root_.GD.N0155.d006191 x) * (_root_.GD.N0155.d006192 x - 7 / 2)) * _root_.GD.N0155.d006190 x


noncomputable def d006196 (m v1 v2 : ℝ) (d : _root_.GD.N0155.d006184 → ℝ) : ℝ :=
  ∫ x, (d x - m) ^ 2 ∂(_root_.GD.N0155.d006185 m v1 v2)


noncomputable def d006197 (m v1 v2 : ℝ) : ℝ := _root_.GD.N0155.d006196 m v1 v2 _root_.GD.N0155.d006194


noncomputable def d006198 (m v1 v2 : ℝ) : ℝ := _root_.GD.N0155.d006196 m v1 v2 _root_.GD.N0155.d006195

end GD.N0155
