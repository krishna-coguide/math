import Std

namespace E272

/-- Bit i denotes the integer i+1 in the original question. -/
abbrev Mask := BitVec 14

/-- The first argument is a subset of the second. -/
def sub (t a : Mask) : Bool := (t &&& a) == t

/-- Generate the successive extensions of a progression, one new point at a time. -/
def extensions (step : Nat) : Nat → Nat → Mask → List Mask
  | 0, _, _ => []
  | k+1, atBit, prev =>
    let next := prev ||| ((1 : Mask) <<< atBit)
    next :: extensions step k (atBit + step) next

/-- All singletons, followed by all longer progressions of positive step. -/
def fromProgressions : List Mask :=
  (List.range 14).map (fun i => (1 : Mask) <<< i) ++
  (List.range 14).flatMap fun i => (List.range 13).flatMap fun d =>
    extensions (d+1) ((13-i)/(d+1)) (i+d+1) ((1 : Mask) <<< i)

/-- A precomputed copy so that symbolic proofs do not have to evaluate the enumerator. -/
def apMasks : List Mask := [
  1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048,
  4096, 8192, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047,
  4095, 8191, 16383, 5, 21, 85, 341, 1365, 5461, 9, 73, 585,
  4681, 17, 273, 4369, 33, 1057, 65, 4161, 129, 257, 513, 1025,
  2049, 4097, 8193, 6, 14, 30, 62, 126, 254, 510, 1022, 2046,
  4094, 8190, 16382, 10, 42, 170, 682, 2730, 10922, 18, 146, 1170,
  9362, 34, 546, 8738, 66, 2114, 130, 8322, 258, 514, 1026, 2050,
  4098, 8194, 12, 28, 60, 124, 252, 508, 1020, 2044, 4092, 8188,
  16380, 20, 84, 340, 1364, 5460, 36, 292, 2340, 68, 1092, 132,
  4228, 260, 516, 1028, 2052, 4100, 8196, 24, 56, 120, 248, 504,
  1016, 2040, 4088, 8184, 16376, 40, 168, 680, 2728, 10920, 72, 584,
  4680, 136, 2184, 264, 8456, 520, 1032, 2056, 4104, 8200, 48, 112,
  240, 496, 1008, 2032, 4080, 8176, 16368, 80, 336, 1360, 5456, 144,
  1168, 9360, 272, 4368, 528, 1040, 2064, 4112, 8208, 96, 224, 480,
  992, 2016, 4064, 8160, 16352, 160, 672, 2720, 10912, 288, 2336, 544,
  8736, 1056, 2080, 4128, 8224, 192, 448, 960, 1984, 4032, 8128, 16320,
  320, 1344, 5440, 576, 4672, 1088, 2112, 4160, 8256, 384, 896, 1920,
  3968, 8064, 16256, 640, 2688, 10880, 1152, 9344, 2176, 4224, 8320, 768,
  1792, 3840, 7936, 16128, 1280, 5376, 2304, 4352, 8448, 1536, 3584, 7680,
  15872, 2560, 10752, 4608, 8704, 3072, 7168, 15360, 5120, 9216, 6144, 14336,
  10240, 12288
]

theorem apMasks_correct : apMasks = fromProgressions := by decide +kernel

def ap (a : Mask) : Bool := apMasks.contains a

def sevens : List Mask := [
  127, 254, 508, 1016, 2032, 4064, 5461, 8128, 10922, 16256
]

def short (a : Mask) : Bool := !(sevens.any (fun t => sub t a))

def pos : List Mask := [
  0, 3, 5, 6, 9, 10, 12, 17, 18, 20, 24, 33,
  34, 36, 40, 48, 65, 66, 68, 72, 80, 96, 129, 130,
  132, 136, 144, 160, 192, 257, 258, 260, 264, 272, 288, 320,
  384, 513, 514, 516, 520, 528, 544, 576, 640, 768, 1025, 1026,
  1028, 1032, 1040, 1056, 1088, 1152, 1280, 1536, 2049, 2050, 2052, 2056,
  2064, 2080, 2112, 2176, 2304, 2560, 3072, 4097, 4098, 4100, 4104, 4112,
  4128, 4160, 4224, 4352, 4608, 5120, 6144, 8193, 8194, 8196, 8200, 8208,
  8224, 8256, 8320, 8448, 8704, 9216, 10240, 12288
]

def neg : List Mask := [
  1, 2, 4, 7, 8, 14, 15, 16, 21, 28, 30, 32,
  42, 56, 60, 63, 64, 73, 84, 85, 112, 120, 126, 128,
  146, 168, 170, 224, 240, 252, 256, 273, 292, 336, 340, 448,
  480, 504, 512, 546, 584, 585, 672, 680, 896, 960, 1008, 1024,
  1057, 1092, 1168, 1170, 1344, 1360, 1365, 1792, 1920, 2016, 2048, 2114,
  2184, 2336, 2340, 2688, 2720, 2730, 3584, 3840, 4032, 4096, 4161, 4228,
  4368, 4369, 4672, 4680, 5376, 5440, 5460, 7168, 7680, 8064, 8192, 8322,
  8456, 8736, 8738, 9344, 9360, 10752, 10880, 10920, 14336, 15360, 16128
]

def score (a : Mask) : Int :=
  (pos.countP (fun t => sub t a) : Int) - (neg.countP (fun t => sub t a) : Int)

theorem sub_inter {t a b : Mask} : sub t (a &&& b) = true ↔
    sub t a = true ∧ sub t b = true := by
  simp only [sub, beq_iff_eq]
  constructor
  · intro h
    have left : t &&& a = t := by
      calc
        t &&& a = (t &&& (a &&& b)) &&& a := congrArg (· &&& a) h.symm
        _ = (t &&& b) &&& (a &&& a) := by ac_rfl
        _ = t &&& (a &&& b) := by rw [BitVec.and_self]; ac_rfl
        _ = t := h
    have right : t &&& b = t := by
      calc
        t &&& b = (t &&& (a &&& b)) &&& b := congrArg (· &&& b) h.symm
        _ = (t &&& a) &&& (b &&& b) := by ac_rfl
        _ = t &&& (a &&& b) := by rw [BitVec.and_self]; ac_rfl
        _ = t := h
    exact ⟨left,right⟩
  · rintro ⟨h1,h2⟩
    rwa [← BitVec.and_assoc, h1]

theorem short_inter_left {a b : Mask} (hs : short a = true) : short (a &&& b) = true := by
  simp only [short, Bool.not_eq_true', List.any_eq_false] at *
  intro t ht
  specialize hs t ht
  exact fun he => hs (sub_inter.mp he).1

end E272
