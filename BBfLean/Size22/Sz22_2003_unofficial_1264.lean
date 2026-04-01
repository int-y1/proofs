import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1264: [5/6, 8/35, 77/2, 9/7, 14/11]

Vector representation:
```
-1 -1  1  0  0
 3  0 -1 -1  0
-1  0  0  1  1
 0  2  0 -1  0
 1  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1264

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- R3 drain: (k, 0, 0, d, e) ->* (0, 0, 0, d+k, e+k)
theorem r3_drain : ∀ k d e, ⟨k, (0 : ℕ), (0 : ℕ), d, e⟩ [fm]⊢* ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), d + k, e + k⟩ := by
  intro k; induction' k with k ih
  · intro d e; exists 0
  · intro d e; step fm
    apply stepStar_trans (ih (d + 1) (e + 1)); ring_nf; finish

-- R4 drain: (0, b, 0, k, e) ->* (0, b+2k, 0, 0, e)
theorem r4_drain : ∀ k b e, ⟨(0 : ℕ), b, (0 : ℕ), k, e⟩ [fm]⊢* ⟨(0 : ℕ), b + 2 * k, (0 : ℕ), (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih
  · intro b e; simp; exists 0
  · intro b e; step fm
    apply stepStar_trans (ih (b + 2) e); ring_nf; finish

-- One round of Phase 3: (0, b+4, c, 0, e+1) ->* (0, b, c+3, 0, e)
theorem phase3_round (b c e : ℕ) :
    ⟨(0 : ℕ), b + 4, c, (0 : ℕ), e + 1⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 3, (0 : ℕ), e⟩ := by
  execute fm 6

-- Phase 3 chain: k rounds
theorem phase3 : ∀ k, ∀ b c e, ⟨(0 : ℕ), b + 4 * k, c, (0 : ℕ), e + k⟩ [fm]⊢* ⟨(0 : ℕ), b, c + 3 * k, (0 : ℕ), e⟩ := by
  intro k; induction' k with k ih
  · intro b c e; simp; exists 0
  · intro b c e
    rw [show b + 4 * (k + 1) = (b + 4) + 4 * k from by ring,
        show e + (k + 1) = (e + 1) + k from by ring]
    apply stepStar_trans (ih (b + 4) c (e + 1))
    apply stepStar_trans (phase3_round b (c + 3 * k) e)
    ring_nf; finish

-- One round of R3+R2: (a+1, 0, c+1, 0, e) ->* (a+3, 0, c, 0, e+1)
theorem r3r2_round (a c e : ℕ) :
    ⟨a + 1, (0 : ℕ), c + 1, (0 : ℕ), e⟩ [fm]⊢* ⟨a + 3, (0 : ℕ), c, (0 : ℕ), e + 1⟩ := by
  execute fm 2

-- R3+R2 chain: k rounds
theorem r3r2_chain : ∀ k, ∀ a e, ⟨a + 1, (0 : ℕ), k, (0 : ℕ), e⟩ [fm]⊢* ⟨a + 2 * k + 1, (0 : ℕ), (0 : ℕ), (0 : ℕ), e + k⟩ := by
  intro k; induction' k with k ih
  · intro a e; simp; exists 0
  · intro a e
    apply stepStar_trans (r3r2_round a k e)
    apply stepStar_trans (ih (a + 2) (e + 1))
    ring_nf; finish

-- R5+R2 opening: (0, 0, c+1, 0, e+1) ->* (4, 0, c, 0, e)
theorem phase4_open (c e : ℕ) :
    ⟨(0 : ℕ), (0 : ℕ), c + 1, (0 : ℕ), e + 1⟩ [fm]⊢* ⟨(4 : ℕ), (0 : ℕ), c, (0 : ℕ), e⟩ := by
  execute fm 2

-- Main transition: compose all phases
-- (2*(a+2), 0, 0, 0, e+1) ->+ (2*(3*a+7), 0, 0, 0, 4*a+e+7)
theorem main_transition (a e : ℕ) :
    ⟨2 * (a + 2), (0 : ℕ), (0 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢⁺
    ⟨2 * (3 * a + 7), (0 : ℕ), (0 : ℕ), (0 : ℕ), 4 * a + e + 7⟩ := by
  -- Use step fm to get the first R3 step for ⊢⁺
  rw [show 2 * (a + 2) = (2 * a + 3) + 1 from by ring]
  step fm
  -- After first R3: goal is ⊢* from (2*a+3, 0, 0, 1, e+2) to target
  -- Remaining R3 drain
  apply stepStar_trans (r3_drain (2 * a + 3) 1 (e + 2))
  rw [show 1 + (2 * a + 3) = 2 * a + 4 from by ring,
      show (e + 2) + (2 * a + 3) = e + 2 * a + 5 from by ring]
  -- R4 drain
  apply stepStar_trans (r4_drain (2 * a + 4) 0 (e + 2 * a + 5))
  rw [show 0 + 2 * (2 * a + 4) = 4 * a + 8 from by ring]
  -- Phase 3
  apply stepStar_trans
  · rw [show 4 * a + 8 = 0 + 4 * (a + 2) from by ring,
        show e + 2 * a + 5 = (e + a + 3) + (a + 2) from by ring]
    exact phase3 (a + 2) 0 0 (e + a + 3)
  rw [show 0 + 3 * (a + 2) = 3 * a + 6 from by ring]
  -- Phase 4: R5+R2 opening
  apply stepStar_trans
  · rw [show 3 * a + 6 = (3 * a + 5) + 1 from by ring,
        show e + a + 3 = (e + a + 2) + 1 from by ring]
    exact phase4_open (3 * a + 5) (e + a + 2)
  -- R3+R2 chain
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (r3r2_chain (3 * a + 5) 3 (e + a + 2))
  rw [show 3 + 2 * (3 * a + 5) + 1 = 2 * (3 * a + 7) from by ring,
      show (e + a + 2) + (3 * a + 5) = 4 * a + e + 7 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 0, 1⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨2 * (a + 2), 0, 0, 0, e + 1⟩) ⟨0, 0⟩
  intro ⟨a, e⟩
  exact ⟨⟨3 * a + 5, 4 * a + e + 6⟩, main_transition a e⟩

end Sz22_2003_unofficial_1264
