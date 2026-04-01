import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1512: [7/15, 99/14, 2/3, 5/11, 1617/2]

Vector representation:
```
 0 -1 -1  1  0
-1  2  0 -1  1
 1 -1  0  0  0
 0  0  1  0 -1
-1  1  0  2  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1512

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e+1⟩
  | _ => none

-- R4: transfer e to c (b=0, d=0)
theorem e_to_c : ∀ k, ∀ a c e, ⟨a, 0, c, 0, e + k⟩ [fm]⊢* ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [Nat.add_succ]; step fm
    apply stepStar_trans (ih a (c + 1) e); ring_nf; finish

-- R2+R1+R1 chain: (a+j, 0, c+2j, d+1, e) -> (a, 0, c, d+j+1, e+j)
theorem r2r1r1_chain : ∀ j, ∀ a c d e,
    ⟨a + j, 0, c + 2 * j, d + 1, e⟩ [fm]⊢* ⟨a, 0, c, d + j + 1, e + j⟩ := by
  intro j; induction' j with j ih <;> intro a c d e
  · exists 0
  · rw [show a + (j + 1) = (a + j) + 1 from by ring,
        show c + 2 * (j + 1) = (c + 2 * j) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 1) (e + 1)); ring_nf; finish

-- R2 chain (c=0, works with any b)
theorem r2_chain : ∀ k, ∀ a b d e,
    ⟨a + k, b, 0, d + k, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) d (e + 1)); ring_nf; finish

-- R3+R2 alternation (a=0, c=0, drains d)
theorem r3r2_chain : ∀ k, ∀ b d e,
    ⟨0, b + 1, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k + 1, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (b + 1) d (e + 1)); ring_nf; finish

-- R3 drain (c=0, d=0)
theorem r3_drain : ∀ k, ∀ a e,
    ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm
    apply stepStar_trans (ih (a + 1) e); ring_nf; finish

-- Even case: (4k+3, 0, 0, 0, 6k+3) ⊢⁺ (4k+5, 0, 0, 0, 6k+6)
theorem main_even (k : ℕ) :
    ⟨4 * k + 3, 0, 0, 0, 6 * k + 3⟩ [fm]⊢⁺ ⟨4 * k + 5, 0, 0, 0, 6 * k + 6⟩ := by
  -- Phase 1: R4 transfer
  rw [show (6 * k + 3 : ℕ) = 0 + (6 * k + 3) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (6 * k + 3) (4 * k + 3) 0 0)
  rw [show (0 + (6 * k + 3) : ℕ) = 6 * k + 3 from by ring]
  -- Phase 2: R5 + R1
  rw [show 4 * k + 3 = (4 * k + 2) + 1 from by ring,
      show 6 * k + 3 = (6 * k + 2) + 1 from by ring]
  step fm; step fm
  -- Phase 3: R2R1R1 chain (3k+1 rounds)
  rw [show 4 * k + 2 = (k + 1) + (3 * k + 1) from by ring,
      show 6 * k + 2 = 0 + 2 * (3 * k + 1) from by ring,
      show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (r2r1r1_chain (3 * k + 1) (k + 1) 0 2 1)
  rw [show 2 + (3 * k + 1) + 1 = 3 * k + 4 from by ring,
      show 1 + (3 * k + 1) = 3 * k + 2 from by ring]
  -- Phase 4a: R2 chain (k+1 steps)
  rw [show (k + 1 : ℕ) = 0 + (k + 1) from by ring,
      show 3 * k + 4 = (2 * k + 3) + (k + 1) from by ring]
  apply stepStar_trans (r2_chain (k + 1) 0 0 (2 * k + 3) (3 * k + 2))
  rw [show 0 + 2 * (k + 1) = 2 * k + 2 from by ring,
      show 3 * k + 2 + (k + 1) = 4 * k + 3 from by ring]
  -- Phase 4b: R3+R2 alternation (2k+3 steps)
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring,
      show 2 * k + 3 = 0 + (2 * k + 3) from by ring]
  apply stepStar_trans (r3r2_chain (2 * k + 3) (2 * k + 1) 0 (4 * k + 3))
  rw [show (2 * k + 1) + (2 * k + 3) + 1 = 4 * k + 5 from by ring,
      show 4 * k + 3 + (2 * k + 3) = 6 * k + 6 from by ring]
  -- Phase 4c: R3 drain
  apply stepStar_trans (r3_drain (4 * k + 5) 0 (6 * k + 6))
  ring_nf; finish

-- Odd case: (4k+5, 0, 0, 0, 6k+6) ⊢⁺ (4k+7, 0, 0, 0, 6k+9)
theorem main_odd (k : ℕ) :
    ⟨4 * k + 5, 0, 0, 0, 6 * k + 6⟩ [fm]⊢⁺ ⟨4 * k + 7, 0, 0, 0, 6 * k + 9⟩ := by
  -- Phase 1: R4 transfer
  rw [show (6 * k + 6 : ℕ) = 0 + (6 * k + 6) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_c (6 * k + 6) (4 * k + 5) 0 0)
  rw [show (0 + (6 * k + 6) : ℕ) = 6 * k + 6 from by ring]
  -- Phase 2: R5 + R1
  rw [show 4 * k + 5 = (4 * k + 4) + 1 from by ring,
      show 6 * k + 6 = (6 * k + 5) + 1 from by ring]
  step fm; step fm
  -- Phase 3: R2R1R1 chain (3k+2 rounds, leaves c=1)
  rw [show 4 * k + 4 = (k + 2) + (3 * k + 2) from by ring,
      show 6 * k + 5 = 1 + 2 * (3 * k + 2) from by ring,
      show (2 : ℕ) = 0 + 2 from by ring]
  apply stepStar_trans (r2r1r1_chain (3 * k + 2) (k + 2) 1 2 1)
  rw [show 2 + (3 * k + 2) + 1 = 3 * k + 5 from by ring,
      show 1 + (3 * k + 2) = 3 * k + 3 from by ring]
  -- Phase 3b: clear remaining c=1 via R2+R1
  rw [show (k + 2 : ℕ) = (k + 1) + 1 from by ring,
      show 3 * k + 5 = (3 * k + 4) + 1 from by ring]
  step fm; step fm
  -- Now at (k+1, 1, 0, 3k+5, 3k+4)
  -- Phase 4a: R2 chain (k+1 steps)
  rw [show (k + 1 : ℕ) = 0 + (k + 1) from by ring,
      show 3 * k + 5 = (2 * k + 4) + (k + 1) from by ring]
  apply stepStar_trans (r2_chain (k + 1) 0 1 (2 * k + 4) (3 * k + 4))
  rw [show 1 + 2 * (k + 1) = 2 * k + 3 from by ring,
      show 3 * k + 4 + (k + 1) = 4 * k + 5 from by ring]
  -- Phase 4b: R3+R2 alternation (2k+4 steps)
  rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring,
      show 2 * k + 4 = 0 + (2 * k + 4) from by ring]
  apply stepStar_trans (r3r2_chain (2 * k + 4) (2 * k + 2) 0 (4 * k + 5))
  rw [show (2 * k + 2) + (2 * k + 4) + 1 = 4 * k + 7 from by ring,
      show 4 * k + 5 + (2 * k + 4) = 6 * k + 9 from by ring]
  -- Phase 4c: R3 drain
  apply stepStar_trans (r3_drain (4 * k + 7) 0 (6 * k + 9))
  ring_nf; finish

-- Combined transition
theorem main_trans (n : ℕ) :
    ⟨2 * n + 3, 0, 0, 0, 3 * n + 3⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, 0, 0, 3 * n + 6⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    rw [show 2 * (2 * k) + 3 = 4 * k + 3 from by ring,
        show 3 * (2 * k) + 3 = 6 * k + 3 from by ring,
        show 2 * (2 * k) + 5 = 4 * k + 5 from by ring,
        show 3 * (2 * k) + 6 = 6 * k + 6 from by ring]
    exact main_even k
  · subst hk
    rw [show 2 * (2 * k + 1) + 3 = 4 * k + 5 from by ring,
        show 3 * (2 * k + 1) + 3 = 6 * k + 6 from by ring,
        show 2 * (2 * k + 1) + 5 = 4 * k + 7 from by ring,
        show 3 * (2 * k + 1) + 6 = 6 * k + 9 from by ring]
    exact main_odd k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 3⟩)
  · execute fm 8
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, 0, 0, 3 * n + 3⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1512
