import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #96: [63/10, 2/33, 121/2, 5/7, 10/11]

Vector representation:
```
-1  2 -1  1  0
 1 -1  0  0 -1
-1  0  0  0  2
 0  0  1 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_96

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R3 repeated with general e: (a+k, 0, 0, d, e) →* (a, 0, 0, d, e+2*k)
theorem r3_repeat : ∀ k, ∀ a e, ⟨(a : ℕ)+k, 0, 0, (d : ℕ), e⟩ [fm]⊢* ⟨a, 0, 0, d, e+2*k⟩ := by
  intro k; induction' k with k h <;> intro a e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show (a + k) + 1 = (a + k) + 1 from rfl]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R4 repeated (a=0, b=0, c accumulates): (0, 0, c, d+k, e) →* (0, 0, c+k, d, e)
theorem r4_repeat : ∀ k, ∀ c d, ⟨0, 0, c, (d : ℕ)+k, (e : ℕ)⟩ [fm]⊢* ⟨0, 0, c+k, d, e⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1R2 chain: (1, b, c+k, d, k) →* (1, b+k, c, d+k, 0)
theorem r1r2_chain : ∀ k, ∀ b c d, ⟨1, (b : ℕ), c+k, (d : ℕ), k⟩ [fm]⊢* ⟨1, b+k, c, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro b c d
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3R2R2 drain: (a+1, b+2*k, 0, d, 0) →* (a+1+k, b, 0, d, 0)
theorem r3r2r2_chain : ∀ k, ∀ a b d, ⟨(a : ℕ)+1, b+2*k, 0, (d : ℕ), 0⟩ [fm]⊢* ⟨a+1+k, b, 0, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k + 1) + 1 from by ring]
  step fm
  step fm
  rw [show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Odd drain: (1, 2*n+1, 0, d, 0) →* (0, 0, 0, d, 2*n+3)
theorem odd_drain (n d : ℕ) : ⟨1, 2*n+1, 0, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d, 2*n+3⟩ := by
  -- R3R2R2 x n: → (n+1, 1, 0, d, 0)
  apply stepStar_trans (c₂ := ⟨n+1, 1, 0, d, 0⟩)
  · have h := r3r2r2_chain n 0 1 d
    rw [show 1 + 2 * n = 2 * n + 1 from by ring,
        show (0 : ℕ) + 1 + n = n + 1 from by ring] at h
    exact h
  -- R3: (n+1, 1, 0, d, 0) → (n, 1, 0, d, 2)
  -- R2: (n, 1, 0, d, 2) → (n+1, 0, 0, d, 1)
  apply stepStar_trans (c₂ := ⟨n+1, 0, 0, d, 1⟩)
  · rw [show n + 1 = n + 1 from rfl]
    step fm; step fm; finish
  -- R3 x (n+1): (n+1, 0, 0, d, 1) → (0, 0, 0, d, 2n+3)
  have h := r3_repeat (n+1) 0 1 (d := d)
  rw [show (0 : ℕ) + (n + 1) = n + 1 from by ring,
      show 1 + 2 * (n + 1) = 2 * n + 3 from by ring] at h
  exact h

-- Even drain: (1, 2*m, 0, d, 0) →* (m+1, 0, 0, d, 0)
theorem even_drain (m d : ℕ) : ⟨1, 2*m, 0, d, 0⟩ [fm]⊢* ⟨m+1, 0, 0, d, 0⟩ := by
  have h := r3r2r2_chain m 0 0 d
  rw [show (0 : ℕ) + 2 * m = 2 * m from by ring,
      show (0 : ℕ) + 1 + m = m + 1 from by ring] at h
  exact h

-- Half-cycle: (0, 0, 0, d, d+2) →* (1, d+1, 0, d+1, 0)
-- R4*d → R5 → R1R2*(d+1)
theorem half_cycle (d : ℕ) : ⟨0, 0, 0, d, d+2⟩ [fm]⊢* ⟨1, d+1, 0, d+1, 0⟩ := by
  -- R4*d: → (0, 0, d, 0, d+2)
  apply stepStar_trans (c₂ := ⟨0, 0, d, 0, d+2⟩)
  · have h := r4_repeat d 0 0 (e := d+2)
    simp only [Nat.zero_add] at h; exact h
  -- R5: → (1, 0, d+1, 0, d+1)
  apply stepStar_trans (c₂ := ⟨1, 0, d+1, 0, d+1⟩)
  · rw [show d + 2 = (d + 1) + 1 from by ring]
    step fm; finish
  -- R1R2*(d+1): → (1, d+1, 0, d+1, 0)
  have h := r1r2_chain (d+1) 0 0 0
  simp only [Nat.zero_add] at h; exact h

-- Main transition: (n+1, 0, 0, 2*n, 0) →⁺ (n+2, 0, 0, 2*n+2, 0)
theorem main_trans (n : ℕ) : ⟨n+1, 0, 0, 2*n, 0⟩ [fm]⊢⁺ ⟨n+2, 0, 0, 2*n+2, 0⟩ := by
  -- First R3 step gives stepPlus
  apply step_stepStar_stepPlus (c₂ := ⟨n, 0, 0, 2*n, 2⟩)
  · show fm ⟨n + 1, 0, 0, 2 * n, 0⟩ = some ⟨n, 0, 0, 2 * n, 2⟩; simp [fm]
  -- R3*n: → (0, 0, 0, 2n, 2n+2)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2*n, 2*n+2⟩)
  · have h := r3_repeat n 0 2 (d := 2*n)
    rw [show (0 : ℕ) + n = n from by ring,
        show 2 + 2 * n = 2 * n + 2 from by ring] at h
    exact h
  -- Half-cycle 1: → (1, 2n+1, 0, 2n+1, 0)
  apply stepStar_trans (c₂ := ⟨1, 2*n+1, 0, 2*n+1, 0⟩)
  · have h := half_cycle (2*n)
    rw [show 2 * n + 2 = 2 * n + 2 from rfl,
        show 2 * n + 1 = 2 * n + 1 from rfl] at h
    exact h
  -- Odd drain: → (0, 0, 0, 2n+1, 2n+3)
  apply stepStar_trans (c₂ := ⟨0, 0, 0, 2*n+1, 2*n+3⟩)
  · exact odd_drain n (2*n+1)
  -- Half-cycle 2: → (1, 2n+2, 0, 2n+2, 0)
  apply stepStar_trans (c₂ := ⟨1, 2*n+2, 0, 2*n+2, 0⟩)
  · have h := half_cycle (2*n+1)
    rw [show 2 * n + 1 + 2 = 2 * n + 3 from by ring,
        show 2 * n + 1 + 1 = 2 * n + 2 from by ring] at h
    exact h
  -- Even drain: → (n+2, 0, 0, 2n+2, 0)
  have h := even_drain (n+1) (2*n+2)
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
      show n + 1 + 1 = n + 2 from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 0⟩) (by execute fm 16)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1, 0, 0, 2*n, 0⟩) 1
  intro n; exact ⟨n+1, main_trans n⟩
