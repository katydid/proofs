-- TODO: This is just an example, we need to use @[simp] in Lists.lean

-- https://github.com/leanprover-community/mathlib4/blob/56c1ca9832bdd85620d6b0bbd37ef56818e6b667/Mathlib/Data/Matrix/Basis.lean

@[simp] theorem nat_min_zero {n: Nat}: min 0 n = 0 := by
  unfold min
  unfold instMinNat
  unfold minOfLe
  simp

theorem nat_min_zero' {n: Nat}: min 0 n = 0 := by
  simp
