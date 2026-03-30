import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #815: [35/6, 8/55, 1001/2, 3/7, 5/13]

Vector representation:
```
-1 -1  1  1  0  0
 3  0 -1  0 -1  0
-1  0  0  1  1  1
 0  1  0 -1  0  0
 0  0  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_815

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R3 chain: (k, 0, 0, d, e, f) ->* (0, 0, 0, d+k, e+k, f+k)
-- b=0 so R1 doesn't fire, c=0 so R2 doesn't fire.
theorem r3_chain : ∀ k d e f, ⟨k, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d + k, e + k, f + k⟩ := by
  intro k; induction k with
  | zero => intro d e f; exists 0
  | succ k ih =>
    intro d e f; step fm
    apply stepStar_trans (ih (d + 1) (e + 1) (f + 1)); ring_nf; finish

-- R4 chain: (0, b, 0, k, e, f) ->* (0, b+k, 0, 0, e, f)
-- a=0 so R1/R3 don't fire, c=0 so R2 doesn't fire.
theorem r4_chain : ∀ k b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction k with
  | zero => intro b e f; exists 0
  | succ k ih =>
    intro b e f; step fm
    apply stepStar_trans (ih (b + 1) e f); ring_nf; finish

-- R2 drain: (a, 0, c+k, d, k, f) ->* (a+3k, 0, c, d, 0, f)
-- b=0 so R1 doesn't fire, R2 fires because c+k >= 1 and k >= 1.
theorem r2_drain : ∀ k a c d f, ⟨a, 0, c + k, d, k, f⟩ [fm]⊢* ⟨a + 3 * k, 0, c, d, 0, f⟩ := by
  intro k; induction k with
  | zero => intro a c d f; exists 0
  | succ k ih =>
    intro a c d f
    -- State: (a, 0, c+(k+1), d, k+1, f)
    -- Need to show c+(k+1) = (c+k)+1 for R2 pattern, and k+1 for e+1.
    rw [show c + (k + 1) = c + k + 1 from by ring]
    step fm
    -- After R2: (a+3, 0, c+k, d, k, f)
    apply stepStar_trans (ih (a + 3) c d f); ring_nf; finish

-- Inner loop: R1x3 + R2 chain.
-- (3, b+3k, c, d, e+k, f) ->* (3, b, c+2k, d+3k, e, f)
theorem inner_loop : ∀ k b c d e f,
    ⟨(3 : ℕ), b + 3 * k, c, d, e + k, f⟩ [fm]⊢* ⟨3, b, c + 2 * k, d + 3 * k, e, f⟩ := by
  intro k; induction k with
  | zero => intro b c d e f; exists 0
  | succ k ih =>
    intro b c d e f
    rw [show b + 3 * (k + 1) = b + 3 * k + 3 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    -- State: (3, (b+3k)+3, c, d, (e+k)+1, f)
    -- R1: (3, (b+3k)+3, ...) matches a+1=3, b+1=(b+3k)+3
    step fm -- R1: (2, b+3k+2, c+1, d+1, e+k+1, f)
    step fm -- R1: (1, b+3k+1, c+2, d+2, e+k+1, f)
    step fm -- R1: (0, b+3k, c+3, d+3, e+k+1, f)
    -- R2: c+3 >= 1, e+k+1 >= 1
    rw [show c + 3 = c + 2 + 1 from by ring,
        show e + k + 1 = e + k + 1 from rfl]
    step fm -- R2: (3, b+3k, c+2, d+3, e+k, f)
    apply stepStar_trans (ih b (c + 2) (d + 3) e f)
    ring_nf; finish

-- R3+R2 alternating: (a+1, 0, k, d, 0, f) ->* (a+2k+1, 0, 0, d+k, 0, f+k)
-- R3 fires (a+1 >= 1, b=0, c might be > 0 but e=0 so R2 doesn't fire first).
-- After R3: (a, 0, k, d+1, 1, f+1). Now R2 fires (c=k >= 1, e=1 >= 1).
-- After R2: (a+3, 0, k-1, d+1, 0, f+1). Net: a += 2, c -= 1, d += 1, f += 1.
theorem r3r2_alt : ∀ k a d f, ⟨a + 1, 0, k, d, 0, f⟩ [fm]⊢*
    ⟨a + 2 * k + 1, 0, 0, d + k, 0, f + k⟩ := by
  intro k; induction k with
  | zero => intro a d f; exists 0
  | succ k ih =>
    intro a d f
    -- (a+1, 0, k+1, d, 0, f). R3 fires.
    step fm -- R3: (a, 0, k+1, d+1, 1, f+1)
    -- R2: c=k+1 >= 1, e=1 >= 1.
    step fm -- R2: (a+3, 0, k, d+1, 0, f+1)
    rw [show a + 3 = (a + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) (d + 1) (f + 1)); ring_nf; finish

-- Phase 3 for m mod 3 = 0 (m = 3j).
theorem phase3_mod0 (j n : ℕ) :
    ⟨(3 : ℕ), 6 * j + 3 * n + 1, 0, 0, 3 * j + 2 * n, 6 * j + 2 * n⟩ [fm]⊢*
    ⟨3 * j + 3 * n + 2, 0, 3 * j + n + 1, 6 * j + 3 * n + 1, 0, 6 * j + 2 * n⟩ := by
  rw [show 6 * j + 3 * n + 1 = 1 + 3 * (2 * j + n) from by ring,
      show 3 * j + 2 * n = (j + n) + (2 * j + n) from by ring]
  apply stepStar_trans (inner_loop (2 * j + n) 1 0 0 (j + n) (6 * j + 2 * n))
  -- (3, 1, 2*(2j+n), 3*(2j+n), j+n, 6j+2n)
  rw [show 0 + 2 * (2 * j + n) = 4 * j + 2 * n from by ring]
  step fm -- R1: (2, 0, 4j+2n+1, 6j+3n+1, j+n, 6j+2n)
  -- Apply r2_drain
  rw [show 4 * j + 2 * n + 1 = (3 * j + n + 1) + (j + n) from by ring,
      show 0 + 3 * (2 * j + n) + 1 = 6 * j + 3 * n + 1 from by ring]
  apply stepStar_trans (r2_drain (j + n) 2 (3 * j + n + 1) (6 * j + 3 * n + 1) (6 * j + 2 * n))
  ring_nf; finish

-- Phase 3 for m mod 3 = 1 (m = 3j+1).
theorem phase3_mod1 (j n : ℕ) :
    ⟨(3 : ℕ), 6 * j + 3 * n + 3, 0, 0, 3 * j + 2 * n + 1, 6 * j + 2 * n + 2⟩ [fm]⊢*
    ⟨3 * j + 3 * n + 3, 0, 3 * j + n + 2, 6 * j + 3 * n + 3, 0, 6 * j + 2 * n + 2⟩ := by
  rw [show 6 * j + 3 * n + 3 = 0 + 3 * (2 * j + n + 1) from by ring,
      show 3 * j + 2 * n + 1 = (j + n) + (2 * j + n + 1) from by ring]
  apply stepStar_trans (inner_loop (2 * j + n + 1) 0 0 0 (j + n) (6 * j + 2 * n + 2))
  -- (3, 0, 2*(2j+n+1), 3*(2j+n+1), j+n, 6j+2n+2)
  rw [show 0 + 2 * (2 * j + n + 1) = (3 * j + n + 2) + (j + n) from by ring,
      show 0 + 3 * (2 * j + n + 1) = 6 * j + 3 * n + 3 from by ring]
  apply stepStar_trans (r2_drain (j + n) 3 (3 * j + n + 2) (6 * j + 3 * n + 3) (6 * j + 2 * n + 2))
  ring_nf; finish

-- Phase 3 for m mod 3 = 2 (m = 3j+2).
theorem phase3_mod2 (j n : ℕ) :
    ⟨(3 : ℕ), 6 * j + 3 * n + 5, 0, 0, 3 * j + 2 * n + 2, 6 * j + 2 * n + 4⟩ [fm]⊢*
    ⟨3 * j + 3 * n + 4, 0, 3 * j + n + 3, 6 * j + 3 * n + 5, 0, 6 * j + 2 * n + 4⟩ := by
  rw [show 6 * j + 3 * n + 5 = 2 + 3 * (2 * j + n + 1) from by ring,
      show 3 * j + 2 * n + 2 = (j + n + 1) + (2 * j + n + 1) from by ring]
  apply stepStar_trans (inner_loop (2 * j + n + 1) 2 0 0 (j + n + 1) (6 * j + 2 * n + 4))
  -- (3, 2, 2*(2j+n+1), 3*(2j+n+1), j+n+1, 6j+2n+4)
  rw [show 0 + 2 * (2 * j + n + 1) = 4 * j + 2 * n + 2 from by ring]
  step fm -- R1: (2, 1, 4j+2n+3, 3*(2j+n+1)+1, j+n+1, 6j+2n+4)
  step fm -- R1: (1, 0, 4j+2n+4, 3*(2j+n+1)+2, j+n+1, 6j+2n+4)
  rw [show 4 * j + 2 * n + 2 + 1 + 1 = (3 * j + n + 3) + (j + n + 1) from by ring,
      show 0 + 3 * (2 * j + n + 1) + 1 + 1 = 6 * j + 3 * n + 5 from by ring]
  apply stepStar_trans (r2_drain (j + n + 1) 1 (3 * j + n + 3) (6 * j + 3 * n + 5) (6 * j + 2 * n + 4))
  ring_nf; finish

-- Main transition
theorem main_transition (n m : ℕ) :
    ⟨m + 2 * n + 1, 0, 0, m + n, 0, m⟩ [fm]⊢⁺
    ⟨3 * m + 5 * n + 4, 0, 0, 3 * m + 4 * n + 2, 0, 3 * m + 3 * n + 1⟩ := by
  -- Phase 1: R3 chain
  have phase1 : ⟨m + 2 * n + 1, 0, 0, m + n, 0, m⟩ [fm]⊢*
      ⟨0, 0, 0, 2 * m + 3 * n + 1, m + 2 * n + 1, 2 * m + 2 * n + 1⟩ := by
    have := r3_chain (m + 2 * n + 1) (m + n) 0 m
    rw [show m + n + (m + 2 * n + 1) = 2 * m + 3 * n + 1 from by ring,
        show 0 + (m + 2 * n + 1) = m + 2 * n + 1 from by ring,
        show m + (m + 2 * n + 1) = 2 * m + 2 * n + 1 from by ring] at this
    exact this
  -- Phase 2: R4 chain
  have phase2 : ⟨0, 0, 0, 2 * m + 3 * n + 1, m + 2 * n + 1, 2 * m + 2 * n + 1⟩ [fm]⊢*
      ⟨0, 2 * m + 3 * n + 1, 0, 0, m + 2 * n + 1, 2 * m + 2 * n + 1⟩ := by
    have := r4_chain (2 * m + 3 * n + 1) 0 (m + 2 * n + 1) (2 * m + 2 * n + 1)
    rw [show 0 + (2 * m + 3 * n + 1) = 2 * m + 3 * n + 1 from by ring] at this
    exact this
  -- Phase 3a: R5 + R2
  have phase3a : ⟨0, 2 * m + 3 * n + 1, 0, 0, m + 2 * n + 1, 2 * m + 2 * n + 1⟩ [fm]⊢⁺
      ⟨3, 2 * m + 3 * n + 1, 0, 0, m + 2 * n, 2 * m + 2 * n⟩ := by
    step fm; step fm; finish
  -- Phase 3b: inner_loop + R1 + R2 drain (m mod 3 dispatch)
  have phase3b : ⟨3, 2 * m + 3 * n + 1, 0, 0, m + 2 * n, 2 * m + 2 * n⟩ [fm]⊢*
      ⟨m + 3 * n + 2, 0, m + n + 1, 2 * m + 3 * n + 1, 0, 2 * m + 2 * n⟩ := by
    obtain ⟨j, rfl | rfl | rfl⟩ : ∃ j, m = 3 * j ∨ m = 3 * j + 1 ∨ m = 3 * j + 2 := ⟨m / 3, by omega⟩
    · -- m = 3j
      rw [show 2 * (3 * j) + 3 * n + 1 = 6 * j + 3 * n + 1 from by ring,
          show 3 * j + 2 * n = 3 * j + 2 * n from rfl,
          show 2 * (3 * j) + 2 * n = 6 * j + 2 * n from by ring,
          show 3 * j + 3 * n + 2 = 3 * j + 3 * n + 2 from rfl,
          show 3 * j + n + 1 = 3 * j + n + 1 from rfl]
      exact phase3_mod0 j n
    · -- m = 3j+1
      rw [show 2 * (3 * j + 1) + 3 * n + 1 = 6 * j + 3 * n + 3 from by ring,
          show 3 * j + 1 + 2 * n = 3 * j + 2 * n + 1 from by ring,
          show 2 * (3 * j + 1) + 2 * n = 6 * j + 2 * n + 2 from by ring,
          show 3 * j + 1 + 3 * n + 2 = 3 * j + 3 * n + 3 from by ring,
          show 3 * j + 1 + n + 1 = 3 * j + n + 2 from by ring]
      exact phase3_mod1 j n
    · -- m = 3j+2
      rw [show 2 * (3 * j + 2) + 3 * n + 1 = 6 * j + 3 * n + 5 from by ring,
          show 3 * j + 2 + 2 * n = 3 * j + 2 * n + 2 from by ring,
          show 2 * (3 * j + 2) + 2 * n = 6 * j + 2 * n + 4 from by ring,
          show 3 * j + 2 + 3 * n + 2 = 3 * j + 3 * n + 4 from by ring,
          show 3 * j + 2 + n + 1 = 3 * j + n + 3 from by ring]
      exact phase3_mod2 j n
  -- Phase 4: R3+R2 alternating
  have phase4 : ⟨m + 3 * n + 2, 0, m + n + 1, 2 * m + 3 * n + 1, 0, 2 * m + 2 * n⟩ [fm]⊢*
      ⟨3 * m + 5 * n + 4, 0, 0, 3 * m + 4 * n + 2, 0, 3 * m + 3 * n + 1⟩ := by
    rw [show m + 3 * n + 2 = (m + 3 * n + 1) + 1 from by ring]
    have := r3r2_alt (m + n + 1) (m + 3 * n + 1) (2 * m + 3 * n + 1) (2 * m + 2 * n)
    rw [show m + 3 * n + 1 + 2 * (m + n + 1) + 1 = 3 * m + 5 * n + 4 from by ring,
        show 2 * m + 3 * n + 1 + (m + n + 1) = 3 * m + 4 * n + 2 from by ring,
        show 2 * m + 2 * n + (m + n + 1) = 3 * m + 3 * n + 1 from by ring] at this
    exact this
  -- Compose
  apply stepStar_stepPlus_stepPlus phase1
  apply stepStar_stepPlus_stepPlus phase2
  apply stepPlus_stepStar_stepPlus phase3a
  apply stepStar_trans phase3b
  exact phase4

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.2 + 2 * p.1 + 1, 0, 0, p.2 + p.1, 0, p.2⟩) ⟨0, 0⟩
  intro ⟨n, m⟩
  refine ⟨⟨n + 1, 3 * m + 3 * n + 1⟩, ?_⟩
  show ⟨m + 2 * n + 1, 0, 0, m + n, 0, m⟩ [fm]⊢⁺
    ⟨3 * m + 3 * n + 1 + 2 * (n + 1) + 1, 0, 0, 3 * m + 3 * n + 1 + (n + 1), 0, 3 * m + 3 * n + 1⟩
  rw [show 3 * m + 3 * n + 1 + 2 * (n + 1) + 1 = 3 * m + 5 * n + 4 from by ring,
      show 3 * m + 3 * n + 1 + (n + 1) = 3 * m + 4 * n + 2 from by ring]
  exact main_transition n m

end Sz22_2003_unofficial_815
