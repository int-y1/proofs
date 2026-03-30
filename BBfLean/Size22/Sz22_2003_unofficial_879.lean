import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #879: [4/15, 1029/2, 11/147, 5/11, 3/7]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0  3  0
 0 -1  0 -2  1
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_879

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+3, e⟩
  | ⟨a, b+1, c, d+2, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R2 chain: (a+k, b, 0, d, 0) →* (a, b+k, 0, d+3*k, 0)
theorem r2_chain : ∀ k a b d, ⟨a + k, b, 0, d, 0⟩ [fm]⊢* ⟨a, b + k, 0, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  · rw [Nat.add_succ a k]
    step fm
    apply stepStar_trans (ih a (b + 1) (d + 3))
    ring_nf; finish

-- R3 chain: (0, b+k, 0, d+2*k, e) →* (0, b, 0, d, e+k)
theorem r3_chain : ∀ k b d e, ⟨0, b + k, 0, d + 2 * k, e⟩ [fm]⊢* ⟨0, b, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring,
        show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring]
    step fm
    apply stepStar_trans (ih b d (e + 1))
    ring_nf; finish

-- R4 chain: (0, 0, c, d, e+k) →* (0, 0, c+k, d, e)
theorem r4_chain : ∀ k c d e, ⟨0, 0, c, d, e + k⟩ [fm]⊢* ⟨0, 0, c + k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R2+R1 chain: (a+1, 0, k, d, 0) →* (a+1+k, 0, 0, d+3*k, 0)
theorem r2r1_chain : ∀ k a d, ⟨a + 1, 0, k, d, 0⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, d + 3 * k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · step fm  -- R2
    step fm  -- R1
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (d + 3))
    ring_nf; finish

-- Main transition: C(n) = (n+2, 0, 0, 2*n*(n+1), 0) →⁺ C(n+1)
theorem main_trans (n : ℕ) :
    ⟨n + 2, 0, 0, 2 * n * (n + 1), 0⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 2 * (n + 1) * (n + 2), 0⟩ := by
  -- Phase 1: R2 chain, k=n+2
  have h1 : ⟨n + 2, 0, 0, 2 * n * (n + 1), 0⟩ [fm]⊢*
      ⟨0, n + 2, 0, 2 * n * (n + 1) + 3 * (n + 2), 0⟩ := by
    have := r2_chain (n + 2) 0 0 (2 * n * (n + 1))
    simpa using this
  -- Phase 2: R3 chain, k=n+2
  have h2 : ⟨0, n + 2, 0, 2 * n * (n + 1) + 3 * (n + 2), 0⟩ [fm]⊢*
      ⟨0, 0, 0, 2 * n * (n + 1) + (n + 2), n + 2⟩ := by
    rw [show 2 * n * (n + 1) + 3 * (n + 2) = (2 * n * (n + 1) + (n + 2)) + 2 * (n + 2) from by ring]
    have := r3_chain (n + 2) 0 (2 * n * (n + 1) + (n + 2)) 0
    simpa using this
  -- Phase 3: R4 chain, k=n+2
  have h3 : ⟨0, 0, 0, 2 * n * (n + 1) + (n + 2), n + 2⟩ [fm]⊢*
      ⟨0, 0, n + 2, 2 * n * (n + 1) + (n + 2), 0⟩ := by
    have := r4_chain (n + 2) 0 (2 * n * (n + 1) + (n + 2)) 0
    simpa using this
  -- Phase 4: R5+R1 + R2R1 chain
  have h4 : ⟨0, 0, n + 2, 2 * n * (n + 1) + (n + 2), 0⟩ [fm]⊢*
      ⟨n + 3, 0, 0, 2 * (n + 1) * (n + 2), 0⟩ := by
    rw [show 2 * n * (n + 1) + (n + 2) = (2 * n * (n + 1) + (n + 1)) + 1 from by ring]
    step fm  -- R5
    step fm  -- R1
    have := r2r1_chain (n + 1) 1 (2 * n * (n + 1) + (n + 1))
    simp at this
    apply stepStar_trans this
    ring_nf; finish
  exact stepStar_stepPlus_stepPlus
    (stepStar_trans h1 (stepStar_trans h2 h3))
    (stepStar_stepPlus h4 (by simp [Q]))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 0, 0, 2 * n * (n + 1), 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩
