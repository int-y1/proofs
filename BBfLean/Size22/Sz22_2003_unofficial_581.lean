import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #581: [35/6, 11/2, 4/55, 3/7, 70/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 1  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_581

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b
  · exists 0
  rw [← Nat.add_assoc]
  step fm
  apply stepStar_trans (h _)
  ring_nf; finish

-- R3,R2,R2 drain: convert c to e (requires e >= 1)
theorem drain : ∀ k c e, ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+1+k⟩ := by
  intro k; induction' k with k h <;> intro c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1,R1,R3 chain: each round b -= 2, c += 1, d += 2, e -= 1
theorem r1r1r3_chain : ∀ k c d e, ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+2*k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Combined phase: opening + chain + close + drain for even n
-- From (0, 2*m+3, 0, 0, 2*m+4) to (0, 0, 0, 2*m+4, 2*m+5)
theorem even_phase (m : ℕ) : ⟨0, 2*m+3, 0, 0, 2*m+4⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+4, 2*m+5⟩ := by
  -- R5, R1, R3: (0,2m+3,0,0,2m+4) → (1,2m+3,1,1,2m+3) → (0,2m+2,2,2,2m+3) → (2,2m+2,1,2,2m+2)
  rw [show 2*m+4 = (2*m+3) + 1 from by ring]
  step fm; step fm; step fm
  -- Chain: (2, 2+2*m, 1, 2, (m+2)+m) →* (2, 2, 1+m, 2+2*m, m+2)
  have hchain := @r1r1r3_chain 2 m 1 2 (m+2)
  rw [show 2 + 2*m = 2*m+2 from by ring, show (m+2)+m = 2*m+2 from by ring] at hchain
  apply stepStar_trans hchain
  -- State: (2, 2, 1+m, 2+2*m, m+2) = (2, 2, m+1, 2*m+2, m+2)
  -- R1: (1, 1, m+2, 2*m+3, m+2). R1: (0, 0, m+3, 2*m+4, m+2)
  step fm; step fm
  -- State from Lean: (0, 0, 1+m+1+1, 2*m+2+1+1, m+2)
  -- Need to match drain: (0, 0, c+k, d, e+1) with c=0, k=m+3, e=m+1
  -- So target: (0, 0, 0+(m+3), 2*m+4, (m+1)+1)
  rw [show 1+m+1+1 = 0+(m+3) from by ring,
      show 2*m+2+1+1 = 2*m+4 from by ring,
      show m+2 = (m+1)+1 from by ring]
  apply stepStar_trans (drain (d := 2*m+4) (m+3) 0 (m+1))
  ring_nf; finish

-- Combined phase: opening + chain + close + drain for odd n
-- From (0, 2*m+4, 0, 0, 2*m+5) to (0, 0, 0, 2*m+5, 2*m+6)
theorem odd_phase (m : ℕ) : ⟨0, 2*m+4, 0, 0, 2*m+5⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+5, 2*m+6⟩ := by
  -- R5, R1, R3
  rw [show 2*m+5 = (2*m+4) + 1 from by ring]
  step fm; step fm; step fm
  -- Chain: (2, 2*m+3, 1, 2, 2*m+3). b=1, k=m+1
  have hchain := @r1r1r3_chain 1 (m+1) 1 2 (m+2)
  rw [show 1 + 2*(m+1) = 2*m+3 from by ring, show (m+2)+(m+1) = 2*m+3 from by ring] at hchain
  apply stepStar_trans hchain
  -- State: (2, 1, 1+(m+1), 2+2*(m+1), m+2) = (2, 1, m+2, 2*m+4, m+2)
  -- R1: (1, 0, m+3, 2*m+5, m+2). R2: (0, 0, m+3, 2*m+5, m+3)
  step fm; step fm
  -- Match drain
  rw [show 1+(m+1)+1 = 0+(m+3) from by ring,
      show 2+2*(m+1)+1 = 2*m+5 from by ring,
      show m+2+1 = (m+2)+1 from by ring]
  apply stepStar_trans (drain (d := 2*m+5) (m+3) 0 (m+2))
  ring_nf; finish

-- Even case: (0,0,0,2*m+3,2*m+4) →⁺ (0,0,0,2*m+4,2*m+5)
theorem even_trans : ⟨0, 0, 0, 2*m+3, 2*m+4⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+4, 2*m+5⟩ := by
  rw [show 2*m+3 = 0 + (2*m+3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2*m+3) 0 (d := 0))
  simp only [Nat.zero_add]
  exact even_phase m

-- Odd case: (0,0,0,2*m+4,2*m+5) →⁺ (0,0,0,2*m+5,2*m+6)
theorem odd_trans : ⟨0, 0, 0, 2*m+4, 2*m+5⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+5, 2*m+6⟩ := by
  rw [show 2*m+4 = 0 + (2*m+4) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (2*m+4) 0 (d := 0))
  simp only [Nat.zero_add]
  exact odd_phase m

-- Base cases
theorem base1 : ⟨0, 0, 0, 1, 2⟩ [fm]⊢⁺ ⟨0, 0, 0, 2, 3⟩ := by execute fm 9
theorem base2 : ⟨0, 0, 0, 2, 3⟩ [fm]⊢⁺ ⟨0, 0, 0, 3, 4⟩ := by execute fm 13

-- Main transition
theorem main_trans (n : ℕ) : ⟨0, 0, 0, n+1, n+2⟩ [fm]⊢⁺ ⟨0, 0, 0, n+2, n+3⟩ := by
  rcases n with _ | _ | n
  · exact base1
  · exact base2
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show m+m+1+1+1 = 2*m+3 from by ring,
        show m+m+1+1+2 = 2*m+4 from by ring,
        show m+m+1+1+3 = 2*m+5 from by ring]
    exact even_trans
  · subst hm
    rw [show 2*m+1+1+1+1 = 2*m+4 from by ring,
        show 2*m+1+1+1+2 = 2*m+5 from by ring,
        show 2*m+1+1+1+3 = 2*m+6 from by ring]
    exact odd_trans

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n+1, n+2⟩) 0
  intro n; exists n+1; exact main_trans n
