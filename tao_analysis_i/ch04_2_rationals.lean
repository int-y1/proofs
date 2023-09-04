import Mathlib.Data.Int.Order.Basic

structure XRatBase where
  a : Int
  b : Int
  hb : b ≠ 0

instance ratSetoid : Setoid XRatBase where
  r x y := x.1 * y.2 = y.1 * x.2
  iseqv := by
    refine ⟨fun x => rfl, fun h => h.symm, fun {x y z} h₁ h₂ => ?_⟩
    apply mul_right_cancel₀
    simp [h₁, h₂]
    sorry


example : Nat := 4
