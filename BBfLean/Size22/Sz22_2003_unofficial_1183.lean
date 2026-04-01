import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1183: [5/6, 49/2, 44/35, 9/11, 22/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  2  0  0 -1
 1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1183

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 repeated: move e to b. (0, b, 0, d, e+k) →* (0, b+2*k, 0, d, e)
theorem e_to_b : ∀ k, ∀ b d e, ⟨(0 : ℕ), b, 0, d, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

-- R3,R2,R2 chain: (0, 0, c+k, d+1, e) →* (0, 0, c, d+3*k+1, e+k)
theorem r3r2r2_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), 0, c + k, d + 1, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + 3 * k + 1, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 1))
    ring_nf; finish

-- Interleave R3,R1,R1: (0, b+2, c+1, d+1, e) → (0, b, c+2, d, e+1)
-- After k rounds: (0, b+2*k, c+1, d+k, e) →* (0, b, c+k+1, d, e+k)
theorem interleave : ∀ k, ∀ b c d e, ⟨(0 : ℕ), b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    rw [show c + k + 1 = (c + k + 1) from rfl]
    step fm
    step fm
    step fm
    rw [show c + (k + 1) + 1 = c + k + 2 from by ring,
        show e + (k + 1) = e + k + 1 from by ring]
    finish

-- Main transition for e >= 1: (0, 0, 0, D + e + 1, e + 1) →⁺ (0, 0, 0, D + 2*e + 3, 2*e + 3)
-- where D = d - e - 1 >= 1 (i.e., d >= e + 2)
-- Let's use D for d-e-1 so d = D + e + 1.
-- Phase 1: R4 x (e+1): (0, 0, 0, D+e+1, e+1) -> (0, 2e+2, 0, D+e+1, 0)
-- Phase 2a: R5: (1, 2e+2, 0, D+e, 1), R1: (0, 2e+1, 1, D+e, 1)
-- Phase 2b: interleave e rounds:
--   (0, 2e+1, 1, D+e, 1) = (0, 1+2*e, 0+1, D+e, 1)
--   After e rounds: (0, 1, e+1, D, e+1)
-- Phase 2c: R3: (2, 1, e, D-1, e+2), R1: (1, 0, e+1, D-1, e+2), R2: (0, 0, e+1, D+1, e+2)
-- Phase 3: R3R2R2 x (e+1):
--   (0, 0, e+1, D+1, e+2) = (0, 0, 0+(e+1), D+1, e+2)
--   After (e+1) rounds: (0, 0, 0, D+1+3*(e+1), e+2+(e+1)) = (0, 0, 0, D+3e+4, 2e+3)
-- But we want (0, 0, 0, D+2e+3, 2e+3). D+3e+4 != D+2e+3. Something's wrong.

-- Let me re-derive. With d = D+e+1, e_old = e+1:
-- Target: (0,0,0, d+2*e_old+1, 2*e_old+1) = (0,0,0, D+e+1+2*(e+1)+1, 2*(e+1)+1)
--        = (0,0,0, D+3e+4, 2e+3)
-- OK so the target IS D+3e+4. Let me fix the theorem statement.

-- Actually let me just parameterize by (d, e) directly.
-- Canonical: (0,0,0,d,e) with d >= e+2, e >= 1
-- Next: (0,0,0,d+2e+1,2e+1)

-- Phase 2b: interleave (e-1) rounds (NOT e):
-- (0, 2e-1, 1, d-1, 1) = (0, 1+2*(e-1), 0+1, (d-e)+(e-1), 1)
-- After (e-1) rounds: (0, 1, e, d-e, e)
-- Phase 2c: R3: (2, 1, e-1, d-e-1, e+1), R1: (1, 0, e, d-e-1, e+1), R2: (0, 0, e, d-e+1, e+1)
-- Phase 3: R3R2R2 x e:
-- (0, 0, e, d-e+1, e+1) = (0, 0, 0+e, (d-e)+1, e+1)
-- After e rounds: (0, 0, 0, d-e+1+3e, e+1+e) = (0, 0, 0, d+2e+1, 2e+1)
-- That's correct!

-- So the interleave is (e-1) rounds, not e. And the R3R2R2 is e rounds.
-- Let's use: e_param = e - 1, so e = e_param + 1.
-- d >= e + 2 means d >= e_param + 3.
-- Let D = d - e - 1 = d - e_param - 2. So d = D + e_param + 2, D >= 1.

-- Rewrite with e' = e-1 (so e = e'+1, e' >= 0):
-- d = D + e' + 2, D >= 1
-- Phase 1: R4 x (e'+1): (0,0,0,D+e'+2,e'+1) -> (0, 2e'+2, 0, D+e'+2, 0)
-- Phase 2a: R5: (1, 2e'+2, 0, D+e'+1, 1), R1: (0, 2e'+1, 1, D+e'+1, 1)
-- Phase 2b: interleave e' rounds:
--   (0, 2e'+1, 1, D+e'+1, 1) = (0, 1+2*e', 0+1, (D+1)+e', 1)
--   After e' rounds: (0, 1, e'+1, D+1, e'+1)
-- Phase 2c: R3: (2, 1, e', D, e'+2), R1: (1, 0, e'+1, D, e'+2), R2: (0, 0, e'+1, D+2, e'+2)
-- Phase 3: R3R2R2 x (e'+1):
--   (0, 0, (e'+1), D+2, e'+2) = (0, 0, 0+(e'+1), (D+1)+1, e'+2)
--   After (e'+1) rounds: (0, 0, 0, D+1+3*(e'+1)+1, e'+2+(e'+1))
--   Hmm wait. r3r2r2_chain says (0,0,c+k,d+1,e) ->* (0,0,c,d+3k+1,e+k)
--   So (0, 0, 0+(e'+1), (D+1)+1, e'+2):
--     c=0, k=e'+1, d_param=D+1, e_param2=e'+2
--     Result: (0, 0, 0, D+1+3*(e'+1)+1, e'+2+(e'+1)) = (0, 0, 0, D+3e'+5, 2e'+3)
-- Target: (0,0,0, (D+e'+2)+2*(e'+1)+1, 2*(e'+1)+1) = (0,0,0, D+3e'+5, 2e'+3). Matches!

-- But wait, in Phase 2c, I need D >= 1 for R3 to fire (d component is D, need D >= 1, i.e. D = D'+1).
-- Actually R3 needs c >= 1 AND d >= 1. At (2, 1, e', D, e'+2), R1 fires (a>=1, b>=1).
-- Then (1, 0, e'+1, D, e'+2): a >= 1, b = 0, so R2 fires. R2 gives (0, 0, e'+1, D+2, e'+2).
-- OK, R2 always fires. Good, no constraint on D for Phase 2c actually.
-- Actually wait: at (2, 1, e', D, e'+2), we have a=2, b=1, so R1 fires regardless of c,d,e.
-- Need e' >= 1 for c component? No, (2, 1, e', D, e'+2) with a=2, b=1 -> R1: (1, 0, e'+1, D, e'+2).
-- Then a=1, b=0, R2: (0, 0, e'+1, D+2, e'+2). Good.
-- For Phase 3 we need D+2 >= 1, which is always true.

-- For Phase 2b, D + 1 >= 1 always (since D >= 0 from d >= e+1... but we actually need d >= e+1).
-- Hmm actually the R3 step in Phase 2c: at (0, 1, e'+1, D+1, e'+1):
-- a=0, b=1, c=e'+1 >= 1, d=D+1 >= 1, so R3 fires: (2, 1, e', D, e'+2). Yes, D can be 0.

-- Wait but I wrote the wrong state. Let me recheck Phase 2c:
-- After interleave e' rounds: (0, 1, e'+1, D+1, e'+1)
-- R3 needs c >= 1 and d >= 1: c = e'+1 >= 1, d = D+1 >= 1. Yes: (2, 1, e', D, e'+2).
-- R1: a=2, b=1: (1, 0, e'+1, D, e'+2)
-- R2: a=1, b=0: (0, 0, e'+1, D+2, e'+2). Good.

-- So D >= 0 suffices. Since d = D + e' + 2 and e = e' + 1, D = d - e - 1.
-- For D >= 0 we need d >= e + 1.
-- In our canonical states: d - e = 2, 2, 3, 6, 13, ... always >= 2. So D >= 1 always.

-- Let me use simpler parameterization: just (d, e) with the transition
-- (0,0,0,d,e) ->+ (0,0,0,d+2e+1,2e+1) for e >= 1, d >= e+1.

-- For the main theorem, let me use progress_nonhalt with P.

-- Full transition for e >= 1, d >= e + 1:
theorem full_trans (D e' : ℕ) : ⟨(0 : ℕ), 0, 0, D + e' + 2, e' + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, D + 3 * e' + 5, 2 * e' + 3⟩ := by
  -- Phase 1: R4 x (e'+1)
  apply stepStar_stepPlus_stepPlus
  · rw [show (e' + 1 : ℕ) = 0 + (e' + 1) from by ring]
    exact e_to_b (e' + 1) 0 (D + e' + 2) 0
  rw [show 0 + 2 * (e' + 1) = 2 * e' + 2 from by ring]
  -- Phase 2a: R5, R1
  step fm
  step fm
  -- Now at (0, 2*e'+1, 1, D+e'+1, 1)
  rw [show 2 * e' + 1 = 1 + 2 * e' from by ring,
      show D + e' + 1 = (D + 1) + e' from by ring]
  -- Phase 2b: interleave e' rounds
  apply stepStar_trans (interleave e' 1 0 (D + 1) 1)
  rw [show 0 + e' + 1 = e' + 1 from by ring,
      show 1 + e' = e' + 1 from by ring]
  -- Now at (0, 1, e'+1, D+1, e'+1)
  -- Phase 2c: R3, R1, R2
  step fm
  step fm
  step fm
  -- Now at (0, 0, e'+1, D+2, e'+2)
  rw [show e' + 1 + 1 = e' + 2 from by ring,
      show D + 2 = (D + 1) + 1 from by ring,
      show (e' + 1 : ℕ) = 0 + (e' + 1) from by ring]
  apply stepStar_trans (r3r2r2_chain (e' + 1) 0 (D + 1) (e' + 2))
  rw [show (D + 1) + 3 * (e' + 1) + 1 = D + 3 * e' + 5 from by ring,
      show (e' + 2) + (e' + 1) = 2 * e' + 3 from by ring]
  finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 1⟩)
  · execute fm 3
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D e', q = ⟨(0 : ℕ), 0, 0, D + e' + 2, e' + 1⟩)
  · intro c ⟨D, e', hq⟩
    subst hq
    exact ⟨⟨0, 0, 0, D + 3 * e' + 5, 2 * e' + 3⟩,
      ⟨D + e' + 1, 2 * e' + 2, by ring_nf⟩, full_trans D e'⟩
  · exact ⟨1, 0, by ring_nf⟩

end Sz22_2003_unofficial_1183
