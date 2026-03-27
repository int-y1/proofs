import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #331: [18/35, 65/33, 14/3, 11/13, 39/2]

Vector representation:
```
 1  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  1  0  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_331

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | _ => none

theorem r4_loop : ∀ k a d e, ⟨a, 0, 0, d, e, k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · rw [Nat.add_zero]; exists 0
  · step fm; apply stepStar_trans (ih a d (e + 1)); ring_nf; finish

theorem mid_loop : ∀ j a b, ⟨a, b + 1, 0, j + 1, j + 1, b + 1⟩ [fm]⊢* ⟨a + j + 1, b + j + 2, 0, 0, 0, b + j + 2⟩ := by
  intro j; induction' j with j ih <;> intro a b
  · step fm; step fm; ring_nf; finish
  · step fm; step fm
    rw [show b + 1 + 1 = (b + 1) + 1 from rfl]
    apply stepStar_trans (ih (a + 1) (b + 1))
    ring_nf; finish

theorem r3_loop : ∀ k a d f, ⟨a, k, 0, d, 0, f⟩ [fm]⊢* ⟨a + k, 0, 0, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · step fm; apply stepStar_trans (ih (a + 1) (d + 1) f); ring_nf; finish

theorem main_trans_zero : ∀ a, ⟨a + 1, 0, 0, 1, 0, 1⟩ [fm]⊢⁺ ⟨a + 3, 0, 0, 2, 0, 2⟩ := by
  intro a; execute fm 6

theorem main_trans_succ : ∀ n a, ⟨a + 1, 0, 0, n + 2, 0, n + 2⟩ [fm]⊢⁺ ⟨a + 2 * n + 5, 0, 0, n + 3, 0, n + 3⟩ := by
  intro n a
  -- r4 loop: (a+1, 0, 0, n+2, 0, n+2) ⊢* (a+1, 0, 0, n+2, n+2, 0)
  apply stepStar_stepPlus_stepPlus (r4_loop (n + 2) (a + 1) (n + 2) 0)
  rw [Nat.zero_add]
  -- r5: (a+1, 0, 0, n+2, n+2, 0) → (a, 1, 0, n+2, n+2, 1)
  -- r2: (a, 1, 0, n+2, n+2, 1) → (a, 0, 1, n+2, n+1, 2)
  -- r1: (a, 0, 1, n+2, n+1, 2) → (a+1, 2, 0, n+1, n+1, 2)
  step fm; step fm; step fm
  -- mid_loop: (a+1, 2, 0, n+1, n+1, 2) ⊢* (a+n+2, n+3, 0, 0, 0, n+3)
  rw [show (2 : ℕ) = 1 + 1 from rfl]
  apply stepStar_trans (mid_loop n (a + 1) 1)
  -- r3_loop: (a+n+2, n+3, 0, 0, 0, n+3) ⊢* (a+2n+5, 0, 0, n+3, 0, n+3)
  apply stepStar_trans (r3_loop (1 + n + 2) (a + 1 + n + 1) 0 (1 + n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 0, 1⟩)
  · execute fm 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n a, q = ⟨a + 1, 0, 0, n + 1, 0, n + 1⟩)
  · intro c ⟨n, a, hq⟩; subst hq
    rcases n with _ | n
    · exact ⟨⟨a + 3, 0, 0, 2, 0, 2⟩, ⟨1, a + 2, by ring_nf⟩, main_trans_zero a⟩
    · exact ⟨⟨a + 2 * n + 5, 0, 0, n + 3, 0, n + 3⟩,
             ⟨n + 2, a + 2 * n + 4, by ring_nf⟩, main_trans_succ n a⟩
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_331
