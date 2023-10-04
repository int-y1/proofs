import SquarePyramid.even_sol
import SquarePyramid.odd_sol

/-!
# Solution to the cannonball problem

The cannonball problem asks for all positive integers that are both square and square pyramidal.
Square numbers are of the form `x^2`, and square pyramidal numbers are of the form
`1^2 + 2^2 + ... + x^2 = x * (x+1) * (2x+1) / 6`.

This file shows that the only positive integer solutions to `x * (x+1) * (2x+1) = 6y^2` are
`(x, y) = (1, 1), (24, 70)`. As a corollary, 1 and 4900 are the only positive integers that are both
square and square pyramidal.

## Main statements

* `cannonball`: The only positive integer solutions to the cannonball problem are `(1, 1)` and
  `(24, 70)`.
* `cannonball'`: 1 and 4900 are the only positive integers that are both square and square
  pyramidal.

## References

* [Wikipedia, *Cannonball problem*](https://en.wikipedia.org/wiki/Cannonball_problem)
* [W. S. Anglin, *The Square Pyramid Puzzle*]. doi:10.2307/2323911
-/

theorem cannonball_aux {x y : ℤ} (h : x * (x + 1) * (2 * x + 1) = 6 * y ^ 2) (hx : x > 0) :
    x = 1 ∨ x = 24 := by
  cases' x.even_or_odd with hx_even hx_odd
  · right; exact cannonball_even_24 h hx hx_even
  · left; exact cannonball_odd_1 h hx hx_odd

/-- The only positive integer solutions to the cannonball problem are `(1, 1)` and `(24, 70)`. -/
theorem cannonball {x y : ℤ} (hx : x > 0) (hy : y > 0) :
    x * (x + 1) * (2 * x + 1) = 6 * y ^ 2 ↔ x = 1 ∧ y = 1 ∨ x = 24 ∧ y = 70 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases cannonball_aux h hx with rfl | rfl
    · change 6 * 1 ^ 2 = 6 * y ^ 2 at h
      rw [mul_left_cancel_iff_of_pos (by decide), sq_eq_sq (by decide) hy.le] at h
      exact Or.inl ⟨rfl, h.symm⟩
    · change 6 * 70 ^ 2 = 6 * y ^ 2 at h
      rw [mul_left_cancel_iff_of_pos (by decide), sq_eq_sq (by decide) hy.le] at h
      exact Or.inr ⟨rfl, h.symm⟩
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- 1 and 4900 are the only positive integers that are both square and square pyramidal. -/
theorem cannonball' {n : ℤ} (hn : n > 0) :
    ((∃ y, y > 0 ∧ n = y ^ 2) ∧ (∃ x, x > 0 ∧ x * (x + 1) * (2 * x + 1) = 6 * n)) ↔
    n = 1 ∨ n = 4900 := by
  refine ⟨fun ⟨⟨y, hy₀, hy⟩, ⟨x, hx₀, hx⟩⟩ ↦ ?_, fun h ↦ ?_⟩
  · rcases (cannonball hx₀ hy₀).1 (hy ▸ hx) with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [hy]
  · rcases h with rfl | rfl
    · exact ⟨⟨1, by decide, rfl⟩, ⟨1, by decide, rfl⟩⟩
    · exact ⟨⟨70, by decide, rfl⟩, ⟨24, by decide, rfl⟩⟩
