import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #667: [35/6, 28/55, 121/2, 3/7, 25/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  1 -1
-1  0  0  0  2
 0  1  0 -1  0
 0  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_667

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- R4 repeated: (0, b, 0, d+k, e) →* (0, b+k, 0, d, e)
theorem d_to_b : ∀ k b d, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [Nat.add_succ d k]; step fm
    apply stepStar_trans (ih (b + 1) d); ring_nf; finish

-- R3 repeated: (a+k, 0, 0, d, e) →* (a, 0, 0, d, e+2*k)
theorem drain_a : ∀ k a e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]; step fm
    apply stepStar_trans (ih a (e + 2)); ring_nf; finish

-- R2 repeated when b=0: (a, 0, c+k, d, e+k) →* (a+2*k, 0, c, d+k, e)
theorem r2_chain : ∀ k a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c (d + 1) e); ring_nf; finish

-- n rounds of (R1,R1,R2): (2, 2*n, c, d, e+n) →* (2, 0, c+n, d+3*n, e)
theorem r1r1r2_chain : ∀ n c d e, ⟨2, 2 * n, c, d, e + n⟩ [fm]⊢* ⟨2, 0, c + n, d + 3 * n, e⟩ := by
  intro n; induction' n with n ih <;> intro c d e
  · exists 0
  · rw [show 2 * (n + 1) = (2 * n) + 2 from by ring,
        show e + (n + 1) = (e + n) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 3) e); ring_nf; finish

-- Phases 2-5: from (0, 2n+2, 0, 0, e'+2n+5) to (2n+6, 0, 0, 4n+6, e')
theorem middle_phase (n : ℕ) (e' : ℕ) :
    ⟨0, 2 * n + 2, 0, 0, e' + 2 * n + 5⟩ [fm]⊢⁺ ⟨2 * n + 6, 0, 0, 4 * n + 6, e'⟩ := by
  -- R5
  rw [show e' + 2 * n + 5 = (e' + 2 * n + 4) + 1 from by ring]
  step fm
  -- R2
  rw [show e' + 2 * n + 4 = (e' + 2 * n + 3) + 1 from by ring]
  step fm
  -- R1R1R2 x (n+1)
  rw [show e' + 2 * n + 3 = (e' + n + 2) + (n + 1) from by ring,
      show (2 * n + 2 : ℕ) = 2 * (n + 1) from by ring]
  apply stepStar_trans (r1r1r2_chain (n + 1) 1 1 (e' + n + 2))
  -- R2 x (n+2)
  rw [show 1 + (n + 1) = 0 + (n + 2) from by ring,
      show e' + n + 2 = e' + (n + 2) from by ring]
  apply stepStar_trans (r2_chain (n + 2) 2 0 (1 + 3 * (n + 1)) e')
  ring_nf; finish

-- Phase 1: R4 x (2n+2) then middle_phase then drain.
-- (0, 0, 0, 2n+2, e'+2n+5) ⊢⁺ (0, 0, 0, 4n+6, e'+4n+12)
theorem main_trans (n : ℕ) (e' : ℕ) :
    ⟨0, 0, 0, 2 * n + 2, e' + 2 * n + 5⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * n + 6, e' + 4 * n + 12⟩ := by
  -- First R4 step
  rw [show (2 * n + 2 : ℕ) = (2 * n + 1) + 1 from by ring]
  step fm
  -- Remaining R4 x (2n+1)
  rw [show (2 * n + 1 : ℕ) = 0 + (2 * n + 1) from by ring]
  apply stepStar_trans (d_to_b (2 * n + 1) 1 0 (e := e' + 2 * n + 5))
  rw [show 1 + (2 * n + 1) = 2 * n + 2 from by ring]
  -- Phases 2-5
  apply stepStar_trans (stepPlus_stepStar (middle_phase n e'))
  -- Phase 6: R3 x (2n+6)
  rw [show (2 * n + 6 : ℕ) = 0 + (2 * n + 6) from by ring]
  apply stepStar_trans (drain_a (2 * n + 6) 0 e' (d := 4 * n + 6))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 7⟩)
  · execute fm 8
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n e', q = ⟨0, 0, 0, 2 * n + 2, e' + 2 * n + 5⟩)
  · intro c ⟨n, e', hq⟩; subst hq
    exact ⟨⟨0, 0, 0, 4 * n + 6, e' + 4 * n + 12⟩,
      ⟨2 * n + 2, e' + 3, by ring_nf⟩,
      main_trans n e'⟩
  · exact ⟨0, 2, by ring_nf⟩

end Sz22_2003_unofficial_667
