import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #620: [35/6, 1331/2, 28/55, 3/7, 5/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  3
 2  0 -1  1 -1
 0  1  0 -1  0
 0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_620

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+3⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

-- R4 repeated: transfer d to b
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have h : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k ih <;> intro b
    · exists 0
    rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih _)
    ring_nf; finish
  exact h k b

-- R5+R3 opening: 2 fixed steps
theorem r5r3_open : ⟨0, b, 0, 0, e+2⟩ [fm]⊢⁺ ⟨2, b, 0, 1, e⟩ := by
  step fm; step fm; finish

-- R1,R1,R3 interleaved chain: consumes b in pairs
theorem r1r1r3_chain : ∀ k, ∀ b c d e,
    ⟨2, b+2*k, c, d, e+k⟩ [fm]⊢* ⟨2, b, c+k, d+3*k, e⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _ _)
  ring_nf; finish

-- R3,R2,R2 chain: drains c (note: uses e+1 to ensure R3 can fire)
theorem r3r2r2_chain_aux : ∀ k, ∀ c d e,
    ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d+k, e+5*k+1⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm; step fm; step fm
  rw [show e + 5 + 1 = (e + 5) + 1 from by ring]
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Specialized version: drain k from c starting at 0
theorem r3r2r2_drain (k d e : ℕ) :
    ⟨0, 0, k, d, e+1⟩ [fm]⊢* ⟨0, 0, 0, d+k, e+5*k+1⟩ := by
  have := r3r2r2_chain_aux k 0 d e
  simp only [Nat.zero_add] at this
  exact this

-- Full transition for even D = 2*K
-- (0,0,0,2K,E+K+2) → d_to_b → (0,2K,0,0,E+K+2)
-- → R5,R3 → (2,2K,0,1,E+K) → r1r1r3 K → (2,0,K,1+3K,E)
-- → R2,R2 → (0,0,K,1+3K,E+6) → r3r2r2 K → (0,0,0,1+4K,E+5K+6)
theorem even_trans : ⟨0, 0, 0, 2*K, E+K+2⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*K+1, E+5*K+6⟩ := by
  rw [show 2 * K = 0 + 2 * K from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0))
  simp only [Nat.zero_add]
  apply stepPlus_stepStar_stepPlus (r5r3_open (b := 2 * K))
  rw [show (2 : ℕ) * K = 0 + 2 * K from by ring]
  apply stepStar_trans (r1r1r3_chain K 0 0 1 E)
  simp only [Nat.zero_add]
  -- Now at: (2, 0, K, 1 + 3 * K, E) ⊢* target
  -- R2: (1, 0, K, 1+3K, E+3), R2: (0, 0, K, 1+3K, E+6)
  step fm; step fm
  -- Now at: (0, 0, K, 1 + 3 * K, E + 6) ⊢* (0, 0, 0, 4*K+1, E+5*K+6)
  -- Need: (0, 0, 0+K, 1+3*K, (E+5)+1) ⊢* (0, 0, 0, 1+3*K+K, (E+5)+5*K+1)
  -- Goal: (0, 0, K, 1+3*K, E+3+3) ⊢* (0, 0, 0, 4*K+1, E+5*K+6)
  rw [show E + 3 + 3 = (E + 5) + 1 from by ring]
  apply stepStar_trans (r3r2r2_drain K (1 + 3 * K) (E + 5))
  ring_nf; finish

-- Full transition for odd D = 2*K+1
-- (0,0,0,2K+1,E+K+3) → d_to_b → (0,2K+1,0,0,E+K+3)
-- → R5,R3 → (2,2K+1,0,1,E+K+1) → r1r1r3 K → (2,1,K,1+3K,E+1)
-- → R1 → (1,0,K+1,2+3K,E+1) → R2 → (0,0,K+1,2+3K,E+4)
-- → r3r2r2 (K+1) → (0,0,0,3+4K,E+5K+9)
theorem odd_trans : ⟨0, 0, 0, 2*K+1, E+K+3⟩ [fm]⊢⁺ ⟨0, 0, 0, 4*K+3, E+5*K+9⟩ := by
  rw [show 2 * K + 1 = 0 + (2 * K + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0))
  simp only [Nat.zero_add]
  rw [show E + K + 3 = (E + K + 1) + 2 from by ring]
  apply stepPlus_stepStar_stepPlus (r5r3_open (b := 2 * K + 1))
  rw [show 2 * K + 1 = 1 + 2 * K from by ring,
      show E + K + 1 = (E + 1) + K from by ring]
  apply stepStar_trans (r1r1r3_chain K 1 0 1 (E + 1))
  simp only [Nat.zero_add]
  -- Now at: (2, 1, K, 1+3K, E+1) ⊢* target
  -- R1: (1, 0, K+1, 2+3K, E+1), R2: (0, 0, K+1, 2+3K, E+4)
  step fm; step fm
  -- Now at: (0, 0, K+1, 1+3K+1, E+1+3) ⊢* (0, 0, 0, 4*K+3, E+5*K+9)
  -- Need: (0, 0, 0+(K+1), 2+3K, (E+3)+1) ⊢* (0, 0, 0, 2+3K+(K+1), (E+3)+5*(K+1)+1)
  -- Goal: (0, 0, K+1, 1+3*K+1, E+1+3) ⊢* (0, 0, 0, 4*K+3, E+5*K+9)
  rw [show (1 : ℕ) + 3 * K + 1 = 2 + 3 * K from by ring,
      show E + 1 + 3 = (E + 3) + 1 from by ring]
  apply stepStar_trans (r3r2r2_drain (K + 1) (2 + 3 * K) (E + 3))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 3⟩)
  · execute fm 1
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ D E, q = ⟨0, 0, 0, D, E⟩ ∧ E ≥ D + 2)
  · intro c ⟨D, E, hq, hE⟩; subst hq
    rcases Nat.even_or_odd D with ⟨K, hK⟩ | ⟨K, hK⟩
    · rw [show K + K = 2 * K from by ring] at hK; subst hK
      obtain ⟨E', rfl⟩ : ∃ E', E = E' + K + 2 := ⟨E - K - 2, by omega⟩
      refine ⟨⟨0, 0, 0, 4 * K + 1, E' + 5 * K + 6⟩,
        ⟨4 * K + 1, E' + 5 * K + 6, rfl, ?_⟩, even_trans⟩
      omega
    · subst hK
      obtain ⟨E', rfl⟩ : ∃ E', E = E' + K + 3 := ⟨E - K - 3, by omega⟩
      refine ⟨⟨0, 0, 0, 4 * K + 3, E' + 5 * K + 9⟩,
        ⟨4 * K + 3, E' + 5 * K + 9, rfl, ?_⟩, odd_trans⟩
      omega
  · exact ⟨0, 3, rfl, by omega⟩

end Sz22_2003_unofficial_620
