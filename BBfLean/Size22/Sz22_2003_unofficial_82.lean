import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #82: [1/30, 12/77, 21/2, 5/7, 242/5]

Vector representation:
```
-1 -1 -1  0  0
 2  1  0 -1 -1
-1  1  0  1  0
 0  0  1 -1  0
 1  0 -1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_82

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+2, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | _ => none

-- R3 chain: (a+k, b, 0, d, 0) →* (a, b+k, 0, d+k, 0) when c=0, e=0
theorem r3_chain : ∀ k, ∀ a b d, ⟨a+k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b+k, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · simp; exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h a (b + 1) (d + 1))
  ring_nf; finish

-- R4 chain: (0, b, c, k, 0) →* (0, b, c+k, 0, 0)
theorem r4_chain : ∀ k, ∀ b c, ⟨0, b, c, k, 0⟩ [fm]⊢* ⟨0, b, c+k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro b c
  · simp; exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  apply stepStar_trans (h b (c + 1))
  ring_nf; finish

-- R5+R1 chain: (0, B+K, 2K+1, 0, E) →* (1, B, 0, 0, E+2K+2)
theorem r5r1_chain : ∀ K, ∀ B E, ⟨0, B+K, 2*K+1, 0, E⟩ [fm]⊢* ⟨1, B, 0, 0, E+2*K+2⟩ := by
  intro K; induction' K with K h <;> intro B E
  · step fm; ring_nf; finish
  rw [show 2 * (K + 1) + 1 = (2 * K + 1) + 2 from by ring,
      show B + (K + 1) = (B + K) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h B (E + 2))
  ring_nf; finish

-- R3+R2 chain: (A+1, X, 0, 0, E+1) →* (A+E+2, X+2*E+2, 0, 0, 0)
theorem r3r2_chain : ∀ E, ∀ A X, ⟨A+1, X, 0, 0, E+1⟩ [fm]⊢* ⟨A+E+2, X+2*E+2, 0, 0, 0⟩ := by
  intro E; induction' E with E h <;> intro A X
  · step fm; step fm; ring_nf; finish
  rw [show (E + 1) + 1 = E + 2 from by ring]
  step fm
  step fm
  apply stepStar_trans (h (A + 1) (X + 2))
  ring_nf; finish

-- Main transition: (2m+1, b, 0, 0, 0) ⊢⁺ (2m+3, b+5*m+5, 0, 0, 0)
theorem main_trans (m b : ℕ) :
    ⟨2*m+1, b, 0, 0, 0⟩ [fm]⊢⁺ ⟨2*m+3, b+5*m+5, 0, 0, 0⟩ := by
  -- Phase 1: R3 chain: (2m+1, b, 0, 0, 0) →* (0, b+2m+1, 0, 2m+1, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, b+2*m+1, 0, 2*m+1, 0⟩)
  · have h := r3_chain (2*m+1) 0 b 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 2: R4 chain: (0, b+2m+1, 0, 2m+1, 0) →* (0, b+2m+1, 2m+1, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, b+2*m+1, 2*m+1, 0, 0⟩)
  · have h := r4_chain (2*m+1) (b+2*m+1) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase 3: R5+R1 chain: (0, b+2m+1, 2m+1, 0, 0) →* (1, b+m+1, 0, 0, 2m+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, b+m+1, 0, 0, 2*m+2⟩)
  · have h := r5r1_chain m (b+m+1) 0
    rw [show (b + m + 1) + m = b + 2 * m + 1 from by ring,
        show 0 + 2 * m + 2 = 2 * m + 2 from by ring] at h
    exact h
  -- Phase 4: R3+R2 chain: (1, b+m+1, 0, 0, 2m+2) →* (2m+3, b+5m+5, 0, 0, 0)
  have h := r3r2_chain (2*m+1) 0 (b+m+1)
  rw [show 0 + 1 = 1 from by ring,
      show 0 + (2 * m + 1) + 2 = 2 * m + 3 from by ring,
      show (b + m + 1) + 2 * (2 * m + 1) + 2 = b + 5 * m + 5 from by ring,
      show (2 * m + 1) + 1 = 2 * m + 2 from by ring] at h
  exact stepStar_stepPlus h (by
    intro heq
    have h1 := congr_arg (fun q : Q => q.1) heq
    simp at h1)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 5, 0, 0, 0⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨m, b⟩ ↦ ⟨2*m+1, b, 0, 0, 0⟩) ⟨1, 5⟩
  intro ⟨m, b⟩; exact ⟨⟨m+1, b+5*m+5⟩, by
    show ⟨2*m+1, b, 0, 0, 0⟩ [fm]⊢⁺ ⟨2*(m+1)+1, b+5*m+5, 0, 0, 0⟩
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 from by ring]
    exact main_trans m b⟩

end Sz22_2003_unofficial_82
