import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1938: [9/70, 35/33, 10/3, 11/5, 9/2]

Vector representation:
```
-1  2 -1 -1  0
 0 -1  1  1 -1
 1 -1  1  0  0
 0  0 -1  0  1
-1  2  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1938

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+1, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

-- R2+R1 drain: (k+1, b+2, 0, 0, e+k+1) →* (0, b+k+3, 0, 0, e)
theorem r2r1_drain : ∀ k b e, ⟨k + 1, b + 2, 0, 0, e + k + 1⟩ [fm]⊢* ⟨0, b + k + 3, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · step fm; step fm; finish
  · rw [show (k + 1) + 1 = k + 2 from by ring,
        show e + (k + 1) + 1 = e + k + 2 from by ring]
    step fm; step fm
    rw [show b + 3 = (b + 1) + 2 from by ring]
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- R2 drain: (0, B+k, c, d, e+k) →* (0, B, c+k, d+k, e)
theorem r2_drain : ∀ k c d, ⟨0, B + k, c, d, e + k⟩ [fm]⊢* ⟨0, B, c + k, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show B + (k + 1) = (B + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 1) (d + 1))
    ring_nf; finish

-- R3+R1 chain: (0, b+2, n+1, k+1, 0) →* (0, b+k+3, n+1, 0, 0)
theorem r3r1_chain : ∀ k b, ⟨0, b + 2, n + 1, k + 1, 0⟩ [fm]⊢* ⟨0, b + k + 3, n + 1, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro b
  · step fm; step fm; finish
  · step fm; step fm
    rw [show b + 3 = (b + 1) + 2 from by ring]
    apply stepStar_trans (ih (b + 1))
    ring_nf; finish

-- R3 chain: (a, b+k, c, 0, 0) →* (a+k, b, c+k, 0, 0)
theorem r3_chain : ∀ k, ⟨a, b + k, c, 0, 0⟩ [fm]⊢* ⟨a + k, b, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih generalizing a b c
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 1) (b := b) (c := c + 1))
    ring_nf; finish

-- R4 chain: (a, 0, c+k, 0, e) →* (a, 0, c, 0, e+k)
theorem r4_chain : ∀ k, ⟨a, 0, c + k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c := c) (e := e + 1))
    ring_nf; finish

-- Main transition: (n+2, 0, 0, 0, 2n+2) →⁺ (n+3, 0, 0, 0, 2n+4)
theorem main_trans : ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ [fm]⊢⁺ ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
  -- Phase 1: R5 + R2R1 drain: (n+2, 0, 0, 0, 2n+2) →⁺ (0, n+3, 0, 0, n+1)
  step fm
  show ⟨n + 1, 0 + 2, 0, 0, 2 * n + 2⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 2 * n + 4⟩
  rw [show 2 * n + 2 = (n + 1) + n + 1 from by ring]
  have h1 := r2r1_drain n 0 (n + 1)
  apply stepStar_trans h1
  -- now at (0, n+3, 0, 0, n+1). Goal: ... →* (n+3, 0, 0, 0, 2n+4)
  -- But the actual form is (0, 0+n+3, 0, 0, n+1).
  -- Phase 2: R2 drain: (0, n+3, 0, 0, n+1) →* (0, 2, n+1, n+1, 0)
  have h2 : ⟨0, 0 + n + 3, 0, 0, n + 1⟩ [fm]⊢* ⟨0, 2, n + 1, n + 1, 0⟩ := by
    have := r2_drain (n + 1) (B := 2) 0 0 (e := 0)
    simp only [Nat.zero_add] at this
    rw [show 0 + n + 3 = 2 + (n + 1) from by ring]
    exact this
  apply stepStar_trans h2
  -- Phase 3: R3R1 chain: (0, 2, n+1, n+1, 0) →* (0, n+3, n+1, 0, 0)
  have h3 : ⟨0, 2, n + 1, n + 1, 0⟩ [fm]⊢* ⟨0, n + 3, n + 1, 0, 0⟩ := by
    rcases n with _ | n'
    · step fm; step fm; finish
    · rw [show (2 : ℕ) = 0 + 2 from by ring]
      have := r3r1_chain (n' + 1) (n := n' + 1) (b := 0)
      rw [show 0 + (n' + 1) + 3 = n' + 1 + 3 from by ring] at this
      exact this
  apply stepStar_trans h3
  -- Phase 4: R3 chain + R4 chain: (0, n+3, n+1, 0, 0) →* (n+3, 0, 0, 0, 2n+4)
  have h4 : ⟨0, n + 3, n + 1, 0, 0⟩ [fm]⊢* ⟨n + 3, 0, 0, 0, 2 * n + 4⟩ := by
    have ha := r3_chain (n + 3) (a := 0) (b := 0) (c := n + 1)
    simp only [Nat.zero_add] at ha
    apply stepStar_trans ha
    rw [show n + 1 + (n + 3) = 2 * n + 4 from by ring]
    have hb := r4_chain (2 * n + 4) (a := n + 3) (c := 0) (e := 0)
    simp only [Nat.zero_add] at hb
    exact hb
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩) 0
  intro n; exact ⟨n + 1, main_trans⟩

end Sz22_2003_unofficial_1938
