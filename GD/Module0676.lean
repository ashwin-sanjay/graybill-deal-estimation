import GD.Module0673





























open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0927

noncomputable section

open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0954



def d009897 (sizes : Fin 3 → ℕ) : ℝ :=
  _root_.GD.N0232.N0719.N0928.d009415 (_root_.GD.N0232.N0719.N0954.d009355 sizes) (5 / 2)



def d009898
    (sizes : Fin 3 → ℕ) (retained : Fin 3) : ℝ :=
  (∑ i ∈ (Finset.univ.erase retained), (sizes i : ℝ) / 2) + 1


def d009899
    (sizes : Fin 3 → ℕ) (retained : Fin 3) : ℝ :=
  _root_.GD.N0232.N0719.N0927.d009898 sizes retained - _root_.GD.N0232.N0719.N0927.d009897 sizes



def d009900
    (sizes : Fin 3 → ℕ) (retained : Fin 3) : ℝ :=
  _root_.GD.N0232.N0719.N0927.d009899 sizes retained + 1



theorem d009901
    (sizes : Fin 3 → ℕ) (hsizes : ∀ i, 1 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0927.d009897 sizes =
      (∑ i, (sizes i : ℝ) / 2) + 1 := by
  unfold _root_.GD.N0232.N0719.N0927.d009897 _root_.GD.N0232.N0719.N0928.d009415
  rw [_root_.GD.N0232.N0719.N0928.d009418 sizes hsizes]
  ring





theorem d009902
    (sizes : Fin 3 → ℕ) (hsizes : ∀ i, 1 ≤ sizes i)
    (retained : Fin 3) :
    _root_.GD.N0232.N0719.N0927.d009899 sizes retained =
      -((sizes retained : ℝ) / 2) := by
  unfold _root_.GD.N0232.N0719.N0927.d009899 _root_.GD.N0232.N0719.N0927.d009898
  rw [_root_.GD.N0232.N0719.N0927.d009901 sizes hsizes]
  have hsum := Finset.sum_erase_add
    (s := Finset.univ) (f := fun i : Fin 3 ↦ (sizes i : ℝ) / 2)
    (Finset.mem_univ retained)
  linarith



theorem d009903
    (sizes : Fin 3 → ℕ) (hsizes : ∀ i, 1 ≤ sizes i)
    (retained : Fin 3) :
    _root_.GD.N0232.N0719.N0927.d009900 sizes retained =
      1 - (sizes retained : ℝ) / 2 := by
  unfold _root_.GD.N0232.N0719.N0927.d009900
  rw [_root_.GD.N0232.N0719.N0927.d009902 sizes hsizes retained]
  ring



theorem d009904
    (sizes : Fin 3 → ℕ) (hsizes : ∀ i, 1 ≤ sizes i)
    (retained : Fin 3) (hsize : sizes retained = 2) :
    _root_.GD.N0232.N0719.N0927.d009899 sizes retained = -1 := by
  rw [_root_.GD.N0232.N0719.N0927.d009902 sizes hsizes retained, hsize]
  norm_num



theorem d009905
    (sizes : Fin 3 → ℕ) (hsizes : ∀ i, 1 ≤ sizes i)
    (retained : Fin 3) (hsize : sizes retained = 2) :
    _root_.GD.N0232.N0719.N0927.d009900 sizes retained = 0 := by
  rw [_root_.GD.N0232.N0719.N0927.d009903 sizes hsizes retained, hsize]
  norm_num



theorem d009906
    (sizes : Fin 3 → ℕ) (hsizes : ∀ i, 1 ≤ sizes i)
    (retained : Fin 3) :
    _root_.GD.N0232.N0719.N0927.d009899 sizes retained = -1 ↔
      sizes retained = 2 := by
  rw [_root_.GD.N0232.N0719.N0927.d009902 sizes hsizes retained]
  constructor
  · intro h
    have hreal : (sizes retained : ℝ) = 2 := by linarith
    exact_mod_cast hreal
  · intro h
    norm_num [h]



theorem d009907
    (sizes : Fin 3 → ℕ) (hsizes : ∀ i, 1 ≤ sizes i)
    (retained : Fin 3) :
    _root_.GD.N0232.N0719.N0927.d009900 sizes retained = 0 ↔
      sizes retained = 2 := by
  rw [_root_.GD.N0232.N0719.N0927.d009903 sizes hsizes retained]
  constructor
  · intro h
    have hreal : (sizes retained : ℝ) = 2 := by linarith
    exact_mod_cast hreal
  · intro h
    norm_num [h]



theorem d009908
    (sizes : Fin 3 → ℕ) (hsizes : ∀ i, 1 ≤ sizes i)
    (retained : Fin 3) (hsize : 2 < sizes retained) :
    _root_.GD.N0232.N0719.N0927.d009899 sizes retained < -1 := by
  rw [_root_.GD.N0232.N0719.N0927.d009902 sizes hsizes retained]
  have hsizeReal : (2 : ℝ) < sizes retained := by exact_mod_cast hsize
  linarith






def d009909 : Fin 3 → ℕ := ![2, 6, 6]

theorem d009910 (i : Fin 3) : 1 ≤ _root_.GD.N0232.N0719.N0927.d009909 i := by
  fin_cases i <;> norm_num [_root_.GD.N0232.N0719.N0927.d009909]


theorem d009911 : _root_.GD.N0232.N0719.N0927.d009897 _root_.GD.N0232.N0719.N0927.d009909 = 8 := by
  rw [_root_.GD.N0232.N0719.N0927.d009901 _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0927.d009910]
  norm_num [_root_.GD.N0232.N0719.N0927.d009909, Fin.sum_univ_succ]



theorem d009912 :
    _root_.GD.N0232.N0719.N0927.d009898 _root_.GD.N0232.N0719.N0927.d009909 0 = 7 := by
  norm_num [_root_.GD.N0232.N0719.N0927.d009898, _root_.GD.N0232.N0719.N0927.d009909, Fin.sum_univ_succ]


theorem d009913 :
    _root_.GD.N0232.N0719.N0927.d009899 _root_.GD.N0232.N0719.N0927.d009909 0 = -1 := by
  exact _root_.GD.N0232.N0719.N0927.d009904
    _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0927.d009910 0 (by norm_num [_root_.GD.N0232.N0719.N0927.d009909])



theorem d009914 :
    _root_.GD.N0232.N0719.N0927.d009900 _root_.GD.N0232.N0719.N0927.d009909 0 = 0 := by
  exact _root_.GD.N0232.N0719.N0927.d009905
    _root_.GD.N0232.N0719.N0927.d009909 _root_.GD.N0232.N0719.N0927.d009910 0 (by norm_num [_root_.GD.N0232.N0719.N0927.d009909])

end

end N0927
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0927.d009902
#print axioms _root_.GD.N0232.N0719.N0927.d009906
#print axioms _root_.GD.N0232.N0719.N0927.d009907
#print axioms _root_.GD.N0232.N0719.N0927.d009913
