import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #256: [14/15, 1/242, 273/2, 55/7, 2/143]

Vector representation:
```
 1 -1 -1  1  0  0
-1  0  0  0 -2  0
-1  1  0  1  0  1
 0  0  1 -1  1  0
 1  0  0  0 -1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_256

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e+2, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d+1, e, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | ⟨a, b, c, d, e+1, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- R5/R2 pair: (0,0,c,0,e+3,f+1) → (0,0,c,0,e,f) when a=0,b=0,d=0
-- R5: (0,0,c,0,(e+2)+1,(f)+1) → (1,0,c,0,e+2,f)
-- R2: ((0)+1,0,c,0,(e)+2,f) → (0,0,c,0,e,f)
theorem r5r2_pair : ⟨0, 0, c, 0, e+3, f+1⟩ [fm]⊢* ⟨0, 0, c, 0, e, f⟩ := by
  step fm; step fm; finish

-- R5/R2 repeated: (0,0,c,0,e+3*k,f+k) →* (0,0,c,0,e,f)
theorem r5r2_chain : ⟨0, 0, c, 0, e+3*k, f+k⟩ [fm]⊢* ⟨0, 0, c, 0, e, f⟩ := by
  induction k generalizing e f with
  | zero => exists 0
  | succ k ih =>
    rw [show e + 3 * (k + 1) = (e + 3) + 3 * k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    exact stepStar_trans (ih (e := e + 3)) r5r2_pair

-- Phase 1 final: after R5/R2 chain, do R5 then R3
-- (0,0,c,0,2,f+1) → R5 → (1,0,c,0,1,f) → R3 → (0,1,c,1,1,f+1)
theorem r5r3_step : ⟨0, 0, c, 0, 2, f+1⟩ [fm]⊢* ⟨0, 1, c, 1, 1, f+1⟩ := by
  step fm; step fm; finish

-- Phase 1 complete: (0,0,c,0,3k+2,f+k+1) ⊢⁺ (0,1,c,1,1,f+1)
theorem phase1 : ⟨0, 0, c, 0, 3*k+2, f+k+1⟩ [fm]⊢⁺ ⟨0, 1, c, 1, 1, f+1⟩ := by
  rw [show 3 * k + 2 = 2 + 3 * k from by ring,
      show f + k + 1 = (f + 1) + k from by ring]
  apply stepStar_stepPlus_stepPlus (r5r2_chain (e := 2) (k := k))
  -- r5r3_step is ⊢*, need ⊢⁺. It does 2 steps.
  step fm; step fm; finish

-- R1/R3 pair: (0,1,c+1,d,1,f) → R1 → (1,0,c,d+1,1,f) → R3 → (0,1,c,d+2,1,f+1)
theorem r1r3_pair : ⟨0, 1, c+1, d, 1, f⟩ [fm]⊢* ⟨0, 1, c, d+2, 1, f+1⟩ := by
  step fm; step fm; finish

-- R1/R3 chain: (0,1,n,d,1,f) →* (0,1,0,d+2*n,1,f+n)
theorem r1r3_chain : ⟨0, 1, n, d, 1, f⟩ [fm]⊢* ⟨0, 1, 0, d+2*n, 1, f+n⟩ := by
  induction n generalizing d f with
  | zero => exists 0
  | succ n ih =>
    apply stepStar_trans (r1r3_pair (c := n) (d := d) (f := f))
    apply stepStar_trans (ih (d := d+2) (f := f+1))
    ring_nf; finish

-- Phase 2: R1/R3 chain then final R3
-- (0,1,n,1,1,f) →* (0,1,0,2n+1,1,f+n) → R3-like step
-- Actually (0,1,0,2n+1,1,f+n): b=1, c=0, so R1 pattern (b+1,c+1) needs c≥1. Fails.
-- a=0, so R2/R3 fail. d=2n+1≥1, so R4 applies: (0,1,1,2n,2,f+n)
-- Then R1 (b=1,c=1): (1,0,0,2n+1,2,f+n)
-- Then R2 (a=1,e=2): (0,0,0,2n+1,0,f+n)
theorem phase2 : ⟨0, 1, n, 1, 1, f⟩ [fm]⊢* ⟨0, 0, 0, 2*n+1, 0, f+n⟩ := by
  apply stepStar_trans (r1r3_chain (n := n) (d := 1) (f := f))
  rw [show 1 + 2 * n = (2 * n) + 1 from by ring]
  step fm; step fm; step fm; finish

-- Phase 4: R4 repeated: (0,0,c,d,e,f) →* (0,0,c+d,0,e+d,f) when a=0,b=0
theorem r4_chain : ⟨0, 0, c, d, e, f⟩ [fm]⊢* ⟨0, 0, c+d, 0, e+d, f⟩ := by
  induction d generalizing c e with
  | zero => exists 0
  | succ d ih =>
    step fm
    apply stepStar_trans (ih (c := c+1) (e := e+1))
    ring_nf; finish

-- Main cycle: (0,0,3k+2,0,3k+2,k+1+m) ⊢⁺ (0,0,6k+5,0,6k+5,3k+3+m)
theorem main_cycle : ⟨0, 0, 3*k+2, 0, 3*k+2, k+1+m⟩ [fm]⊢⁺
    ⟨0, 0, 6*k+5, 0, 6*k+5, 3*k+3+m⟩ := by
  rw [show k + 1 + m = m + k + 1 from by ring]
  -- Phase 1 (⊢⁺): →⁺ (0, 1, 3k+2, 1, 1, m+1)
  apply stepPlus_stepStar_stepPlus (phase1 (c := 3*k+2) (k := k) (f := m))
  -- Phase 2 (⊢*): →* (0, 0, 0, 6k+5, 0, m+1+(3k+2))
  apply stepStar_trans (phase2 (n := 3*k+2) (f := m+1))
  rw [show 2 * (3 * k + 2) + 1 = 6 * k + 5 from by ring]
  -- Phase 4 (⊢*): →* (0, 0, 6k+5, 0, 6k+5, m+1+(3k+2))
  apply stepStar_trans (r4_chain (c := 0) (d := 6*k+5) (e := 0) (f := m+1+(3*k+2)))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0, 2, 2⟩)
  · execute fm 9
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ k m, q = ⟨0, 0, 3*k+2, 0, 3*k+2, k+1+m⟩)
  · intro c ⟨k, m, hq⟩; subst hq
    exact ⟨⟨0, 0, 6*k+5, 0, 6*k+5, 3*k+3+m⟩,
           ⟨2*k+1, m+k+1, by ring_nf⟩, main_cycle⟩
  · exact ⟨0, 1, by ring_nf⟩
