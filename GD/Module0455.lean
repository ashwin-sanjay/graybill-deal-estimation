import GD.Module0453

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32000
set_option maxHeartbeats 0
namespace GD.N0059

def d007016 : List ℕ := [0, 1, 2, 3, 4, 11, 18, 25, 32, 56, 80, 104, 128, 224, 320, 416, 512, 896, 1280, 1664, 2048, 2432, 2816, 3200, 3584, 3680, 3776, 3872, 3968, 3992, 4016, 4040, 4064, 4071, 4078, 4085, 4092, 4093, 4094, 4095, 4096]

def d007017 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 32, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 88, 96, 104, 112, 120, 128, 144, 160, 176, 192, 208, 224, 240, 256, 288, 320, 352, 384, 416, 448, 480, 512, 576, 640, 704, 768, 832, 896, 960, 1024, 1152, 1280, 1408, 1536, 1664, 1792, 1920, 2048, 2304, 2560, 2816, 3072, 3328, 3584, 3840, 4096, 4608, 5120, 5632, 6144, 6656, 7168, 7680, 8192, 9216, 10240, 11264, 12288, 13312, 14336, 15360, 16384, 18432, 20480, 22528, 24576, 26624, 28672, 30720, 32768, 36864, 40960, 45056, 49152, 53248, 57344, 61440, 65536, 73728, 81920, 90112, 98304, 106496, 114688, 122880, 131072]

theorem d007018 : _root_.GD.N0059.d007016.length = 41 := by decide
theorem d007019 : _root_.GD.N0059.d007017.length = 113 := by decide
theorem d007020 : _root_.GD.N0059.d007016.IsChain (· < ·) := by decide
theorem d007021 : _root_.GD.N0059.d007017.IsChain (· < ·) := by decide
theorem d007022 : ∀ u ∈ _root_.GD.N0059.d007016, u ≤ _root_.GD.N0059.d006974 := by decide
theorem d007023 : ∀ z ∈ _root_.GD.N0059.d007017, 0 < z := by decide

end GD.N0059

#print axioms _root_.GD.N0059.d007018
#print axioms _root_.GD.N0059.d007019
#print axioms _root_.GD.N0059.d007020
#print axioms _root_.GD.N0059.d007021
#print axioms _root_.GD.N0059.d007022
#print axioms _root_.GD.N0059.d007023
