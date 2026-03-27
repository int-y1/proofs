import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #332: [18/35, 65/33, 7/3, 11/13, 195/2]

Vector representation:
```
 1  2 -1 -1  0  0
 0 -1  1  0 -1  1
 0 -1  0  1  0  0
 0  0  0  0  1 -1
-1  1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_332

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c+1, d, e, f+1⟩
  | _ => none

theorem r4_loop : ∀ k a d e,
    ⟨a, 0, 0, d, e, k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, 0⟩ := by
  intro k; induction k with
  | zero => intro a d e; simp; exists 0
  | succ k ih =>
    intro a d e; step fm
    apply stepStar_trans (ih a d (e + 1)); ring_nf; finish

theorem r3_loop : ∀ k a d f,
    ⟨a, k, 0, d, 0, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, 0, f⟩ := by
  intro k; induction k with
  | zero => intro a d f; simp; exists 0
  | succ k ih =>
    intro a d f; step fm
    apply stepStar_trans (ih a (d + 1) f); ring_nf; finish

-- One round of r2+r1: (a, b+1, 0, d+1, e+1, f) → (a+1, b+2, 0, d, e, f+1) (but actually b+1→b→b+2)
-- Full r2r1 loop: k+1 rounds
-- (a, b+1, 0, d+k+1, k+1, f) ⊢* (a+k+1, b+k+2, 0, d, 0, f+k+1)
theorem r2r1_loop : ∀ k a b d f,
    ⟨a, b + 1, 0, d + k + 1, k + 1, f⟩ [fm]⊢* ⟨a + k + 1, b + k + 2, 0, d, 0, f + k + 1⟩ := by
  intro k; induction k with
  | zero =>
    intro a b d f
    -- State: (a, b+1, 0, d+1, 1, f)
    -- r2: (a, b, 1, d+1, 0, f+1)
    -- r1: (a+1, b+2, 0, d, 0, f+1)
    step fm; step fm; finish
  | succ k ih =>
    intro a b d f
    -- State: (a, b+1, 0, d+k+2, k+2, f)
    -- r2: (a, b, 1, d+k+2, k+1, f+1)
    -- r1: (a+1, b+2, 0, d+k+1, k+1, f+1)
    step fm; step fm
    -- Now: (a+1, b+2, 0, d+k+1, k+1, f+1) = (a+1, (b+1)+1, 0, d+k+1, k+1, f+1)
    rw [show b + 2 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (b + 1) d (f + 1))
    ring_nf; finish

theorem main_f0 : ∀ a, ⟨a + 1, 0, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a + 1, 0, 0, 2, 0, 1⟩ := by
  intro a; execute fm 5

theorem main_fsucc : ∀ n a,
    ⟨a + 1, 0, 0, 2 * n + 2, 0, n + 1⟩ [fm]⊢⁺ ⟨a + n + 2, 0, 0, 2 * n + 4, 0, n + 2⟩ := by
  intro n a
  -- Phase 1: r4 loop, move n+1 from f to e
  have h1 : ⟨a + 1, 0, 0, 2 * n + 2, 0, n + 1⟩ [fm]⊢*
             ⟨a + 1, 0, 0, 2 * n + 2, n + 1, 0⟩ := by
    have := r4_loop (n + 1) (a + 1) (2 * n + 2) 0
    simpa using this
  apply stepStar_stepPlus_stepPlus h1
  -- Phase 2: r5 + r1
  -- (a+1, 0, 0, 2n+2, n+1, 0)
  -- r5: (a, 1, 1, 2n+2, n+1, 1)
  -- r1: (a+1, 3, 0, 2n+1, n+1, 1)
  step fm; step fm
  -- Phase 3: r2r1 loop (n+1 rounds)
  -- Need: (a+1, 3, 0, 2n+1, n+1, 1)
  -- Template: (A, B+1, 0, D+K+1, K+1, F)
  -- With A=a+1, B=2, D=n, K=n, F=1:
  -- (a+1, 3, 0, n+n+1, n+1, 1) ⊢* (a+1+n+1, 2+n+2, 0, n, 0, 1+n+1)
  -- = (a+n+2, n+4, 0, n, 0, n+2)
  rw [show (3 : ℕ) = 2 + 1 from by ring,
      show 2 * n + 1 = n + n + 1 from by ring,
      show n + 1 = n + 1 from rfl]
  apply stepStar_trans (r2r1_loop n (a + 1) 2 n 1)
  -- Phase 4: r3 loop, drain n+4 into d
  rw [show a + 1 + n + 1 = a + n + 2 from by ring,
      show 2 + n + 2 = n + 4 from by ring,
      show 1 + n + 1 = n + 2 from by ring]
  apply stepStar_trans (r3_loop (n + 4) (a + n + 2) n (n + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩)
  · exists 0
  · apply progress_nonhalt (fun q ↦ ∃ a n, q = (⟨a + 1, 0, 0, 2 * n, 0, n⟩ : Q))
    · intro c ⟨a, n, hc⟩
      subst hc
      cases n with
      | zero =>
        exact ⟨⟨a + 1, 0, 0, 2, 0, 1⟩, ⟨a, 1, by ring_nf⟩, main_f0 a⟩
      | succ n =>
        exact ⟨⟨a + n + 2, 0, 0, 2 * n + 4, 0, n + 2⟩,
               ⟨a + n + 1, n + 2, by ring_nf⟩,
               main_fsucc n a⟩
    · exact ⟨0, 0, by ring_nf⟩

end Sz22_2003_unofficial_332
