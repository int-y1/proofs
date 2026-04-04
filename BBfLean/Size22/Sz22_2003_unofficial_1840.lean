import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1840: [9/20, 245/2, 2/21, 11/7, 4/11]

Vector representation:
```
-2  2 -1  0  0
-1  0  1  2  0
 1 -1  0 -1  0
 0  0  0 -1  1
 2  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1840

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+2, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+2, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | _ => none

-- Phase 1: R5/R1 chain. Converts c and e into b.
-- (0, b, c+k, 0, e+k) →* (0, b+2k, c, 0, e)
theorem r5r1_chain : ∀ k, ∀ b c e, ⟨0, b, c + k, 0, e + k⟩ [fm]⊢* ⟨(0 : ℕ), b + 2 * k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih (b + 2) c e)
    ring_nf; finish

-- Phase 2+3: From (0, 2c, 0, 0, n+1), do R5, R2, R2 to get (0, 2c, 2, 4, n).
-- But we'll express as: (2, B, 0, 0, n) →⁺ (0, B, 2, 4, n)
-- Actually let's just do 3 explicit steps from (0, B, 0, 0, n+1).
theorem r5r2r2 : ⟨0, B, 0, 0, n + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), B, 2, 4, n⟩ := by
  step fm; step fm; step fm; finish

-- Phase 3: R3/R2 spiral. Each round: b-=1, c+=1, d+=1.
-- (0, b+k, c, d, n) →* (0, b, c+k, d+k, n) when d >= 1 throughout.
-- We need d >= 1 for R3. d starts >= 4 and increases, so fine.
-- Actually we need to be more precise: R3 fires on (0, b+1, c, d+1, n).
-- After R3: (1, b, c, d, n). Then R2: (0, b, c+1, d+2, n).
-- Net: b-=1, c+=1, d+=1.
theorem spiral : ∀ k, ∀ b c d n, ⟨0, b + k, c, d + 1, n⟩ [fm]⊢* ⟨(0 : ℕ), b, c + k, d + k + 1, n⟩ := by
  intro k; induction' k with k ih <;> intro b c d n
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    step fm
    rw [show d + 2 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih b (c + 1) (d + 1) n)
    ring_nf; finish

-- Phase 4: R4 drain. Move d to e.
-- (0, 0, c, d+k, e) →* (0, 0, c, d, e+k)
theorem r4_drain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c d (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, c+1, 0, c+n+2) →⁺ (0, 0, 2c+4, 0, 2c+n+6)
theorem main_trans : ⟨0, 0, c + 1, 0, c + n + 2⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 2 * c + 4, 0, 2 * c + n + 6⟩ := by
  -- Phase 1: R5/R1 chain with k = c+1 rounds
  -- State: (0, 0, c+1, 0, c+n+2) = (0, 0, 0+(c+1), 0, (n+1)+(c+1))
  rw [show c + 1 = 0 + (c + 1) from by ring,
      show c + n + 2 = (n + 1) + (c + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r5r1_chain (c + 1) 0 0 (n + 1))
  -- Now at (0, 2*(c+1), 0, 0, n+1) = (0, 2*c+2, 0, 0, n+1)
  -- Phase 2+3: R5, R2, R2
  rw [show 0 + 2 * (c + 1) = 2 * c + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r5r2r2 (B := 2 * c + 2) (n := n))
  -- Now at (0, 2*c+2, 2, 4, n)
  -- Phase 3: spiral with k = 2*c+2 rounds
  -- (0, 0 + (2*c+2), 2, 3+1, n) →* (0, 0, 2+(2*c+2), 3+(2*c+2)+1, n)
  rw [show (2 * c + 2 : ℕ) = 0 + (2 * c + 2) from by ring,
      show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (spiral (2 * c + 2) 0 2 3 n)
  -- Now at (0, 0, 2*c+4, 2*c+6, n)
  -- Phase 4: R4 drain with k = 2*c+6 rounds
  rw [show 2 + (2 * c + 2) = 2 * c + 4 from by ring,
      show 3 + (2 * c + 2) + 1 = 0 + (2 * c + 6) from by ring]
  apply stepStar_trans (r4_drain (2 * c + 6) (2 * c + 4) 0 n)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨c, n⟩ ↦ ⟨0, 0, c + 1, 0, c + n + 2⟩) ⟨0, 0⟩
  intro ⟨c, n⟩; exists ⟨2 * c + 3, n + 1⟩
  show ⟨0, 0, c + 1, 0, c + n + 2⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 3 + 1, 0, 2 * c + 3 + (n + 1) + 2⟩
  rw [show 2 * c + 3 + 1 = 2 * c + 4 from by ring,
      show 2 * c + 3 + (n + 1) + 2 = 2 * c + n + 6 from by ring]
  exact main_trans
