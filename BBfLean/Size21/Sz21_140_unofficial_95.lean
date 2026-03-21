import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #95: [5/6, 99/35, 4/5, 7/11, 55/2]

Vector representation:
```
-1 -1  1  0  0
 0  2 -1 -1  1
 2  0 -1  0  0
 0  0  0  1 -1
-1  0  1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_95

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | _ => none

-- R4 repeated: e → d
theorem e_to_d : ∀ k, ∀ a d, ⟨a, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d+k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  rw [show d + (k + 1) = (d + 1) + k from by ring]
  step fm
  apply stepStar_trans (ih a (d + 1))
  ring_nf; finish

-- R2,R1,R1 rounds: drains a by 2, d by 1, increases c by 1, e by 1 per round
-- (a+2k, 0, c+1, d+k, e) →* (a, 0, c+1+k, d, e+k)
theorem r2r1r1_rounds : ∀ k, ∀ a c d e, ⟨a+2*k, 0, c+1, d+k, e⟩ [fm]⊢* ⟨a, 0, c+1+k, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show a + 2 * (k + 1) = (a + 2 * k) + 1 + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  -- R2: (a+2k+2, 0, c+1, dk+1, e) → (a+2k+2, 2, c, dk, e+1)
  step fm
  rw [show a + 2 * k + 1 + 1 = (a + 2 * k + 1) + 1 from by ring,
      show (2 : ℕ) = 1 + 1 from by ring]
  -- R1: (a+2k+2, 2, c, dk, e+1) → (a+2k+1, 1, c+1, dk, e+1)
  step fm
  rw [show a + 2 * k + 1 = (a + 2 * k) + 1 from by ring,
      show (1 : ℕ) = 0 + 1 from by ring]
  -- R1: (a+2k+1, 1, c+1, dk, e+1) → (a+2k, 0, c+2, dk, e+1)
  step fm
  rw [show c + 2 = (c + 1) + 1 from by ring,
      show e + (k + 1) = (e + 1) + k from by ring,
      show c + 1 + (k + 1) = (c + 1) + 1 + k from by ring]
  exact ih a (c + 1) d (e + 1)

-- R2 chain: (0, b, c+k, d+k, e) →* (0, b+2*k, c, d, e+k)
theorem r2_chain : ∀ k, ∀ b c d e, ⟨0, b, c+k, d+k, e⟩ [fm]⊢* ⟨0, b+2*k, c, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
      show e + (k + 1) = (e + 1) + k from by ring]
  exact ih (b + 2) c d (e + 1)

-- R3,R1,R1 drain: drains b by 2 per round, increases c by 1
-- (0, b+2k, c+1, 0, e) →* (0, b, c+1+k, 0, e)
theorem r3r1r1_drain : ∀ k, ∀ b c e, ⟨0, b+2*k, c+1, 0, e⟩ [fm]⊢* ⟨0, b, c+1+k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring]
  -- R3: (0, b+2k+2, c+1, 0, e) → (2, b+2k+2, c, 0, e)
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show b + 2 * k + 1 + 1 = (b + 2 * k + 1) + 1 from by ring]
  -- R1: (2, b+2k+2, c, 0, e) → (1, b+2k+1, c+1, 0, e)
  step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring,
      show b + 2 * k + 1 = (b + 2 * k) + 1 from by ring]
  -- R1: (1, b+2k+1, c+1, 0, e) → (0, b+2k, c+2, 0, e)
  step fm
  rw [show c + 2 = (c + 1) + 1 from by ring,
      show c + 1 + (k + 1) = (c + 1) + 1 + k from by ring]
  exact ih b (c + 1) e

-- R3 chain: (a, 0, c+k, 0, e) →* (a+2*k, 0, c, 0, e)
theorem r3_chain : ∀ k, ∀ a c e, ⟨a, 0, c+k, 0, e⟩ [fm]⊢* ⟨a+2*k, 0, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring]
  exact ih (a + 2) c e

-- Phase C for even b: (0, 2m, 1, 0, e) →* (2m+2, 0, 0, 0, e)
theorem phaseC_even (m : ℕ) : ⟨0, 2*m, 1, 0, e⟩ [fm]⊢* ⟨2*m+2, 0, 0, 0, e⟩ := by
  apply stepStar_trans (c₂ := ⟨0, 0, m + 1, 0, e⟩)
  · have h := r3r1r1_drain m 0 0 e
    simp only [Nat.zero_add] at h
    convert h using 2 ; ring_nf
  have h := r3_chain (m + 1) 0 0 e
  simp only [Nat.zero_add] at h
  convert h using 2

-- Phase C for odd b: (0, 2m+1, 1, 0, e) →* (2m+3, 0, 0, 0, e)
theorem phaseC_odd (m : ℕ) : ⟨0, 2*m+1, 1, 0, e⟩ [fm]⊢* ⟨2*m+3, 0, 0, 0, e⟩ := by
  apply stepStar_trans (c₂ := ⟨0, 1, m + 1, 0, e⟩)
  · have h := r3r1r1_drain m 1 0 e
    simp only [Nat.zero_add] at h
    convert h using 2 ; ring_nf
  -- (0, 1, m+1, 0, e): R3 → (2, 1, m, 0, e) → R1 → (1, 0, m+1, 0, e) → R3 chain
  apply stepStar_trans (c₂ := ⟨1, 0, m + 1, 0, e⟩)
  · rw [show m + 1 = m + 1 from rfl]
    step fm  -- R3: (0, 1, m+1, 0, e) → (2, 1, m, 0, e)
    rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring]
    step fm  -- R1: (2, 1, m, 0, e) → (1, 0, m+1, 0, e)
    finish
  -- (1, 0, m+1, 0, e): R3 chain
  have h := r3_chain (m + 1) 1 0 e
  simp only [Nat.zero_add] at h
  convert h using 2 ; ring_nf

-- Phase B for even n: (2m, 0, 1, 2m, 1) →* (0, 2m, 1, 0, 2m+1)
theorem phaseB_even (m : ℕ) : ⟨2*m, 0, 1, 2*m, 1⟩ [fm]⊢* ⟨0, 2*m, 1, 0, 2*m+1⟩ := by
  -- r2r1r1_rounds with k=m: (0+2*m, 0, 0+1, 0+m, 1) →* (0, 0, 0+1+m, 0, 1+m) = (0, 0, m+1, 0, m+1)
  apply stepStar_trans (c₂ := ⟨0, 0, m + 1, m, m + 1⟩)
  · have h := r2r1r1_rounds m 0 0 m 1
    simp only [Nat.zero_add] at h
    convert h using 2 ; ring_nf
  -- r2_chain with k=m: (0, 0, 1+m, 0+m, m+1) →* (0, 2m, 1, 0, 2m+1)
  have h := r2_chain m 0 1 0 (m + 1)
  simp only [Nat.zero_add] at h
  convert h using 2 ; ring_nf

-- Phase B for odd n: (2m+1, 0, 1, 2m+1, 1) →* (0, 2m+1, 1, 0, 2m+2)
theorem phaseB_odd (m : ℕ) : ⟨2*m+1, 0, 1, 2*m+1, 1⟩ [fm]⊢* ⟨0, 2*m+1, 1, 0, 2*m+2⟩ := by
  -- r2r1r1_rounds with k=m: (1+2*m, 0, 0+1, 1+m, 1) →* (1, 0, 0+1+m, 1, 1+m) = (1, 0, m+1, m+1, m+1)
  apply stepStar_trans (c₂ := ⟨1, 0, m + 1, m + 1, m + 1⟩)
  · have h := r2r1r1_rounds m 1 0 (m + 1) 1
    simp only [Nat.zero_add] at h
    convert h using 2 ; ring_nf
  -- (1, 0, m+1, m+1, m+1): R2 → (1, 2, m, m, m+2) → R1 → (0, 1, m+1, m, m+2)
  apply stepStar_trans (c₂ := ⟨0, 1, m + 1, m, m + 2⟩)
  · rw [show m + 1 = m + 1 from rfl]
    step fm  -- R2
    rw [show (2 : ℕ) = 1 + 1 from by ring, show (1 : ℕ) = 0 + 1 from by ring,
        show m + 1 + 1 = m + 2 from by ring]
    step fm  -- R1
    finish
  -- r2_chain with k=m: (0, 1, 1+m, 0+m, m+2) →* (0, 1+2m, 1, 0, m+2+m) = (0, 2m+1, 1, 0, 2m+2)
  have h := r2_chain m 1 1 0 (m + 2)
  simp only [Nat.zero_add] at h
  convert h using 2 ; ring_nf

-- Main transition: (n+1, 0, 0, n, 0) ⊢⁺ (n+2, 0, 0, n+1, 0)
theorem main_trans : ⟨n+1, 0, 0, n, 0⟩ [fm]⊢⁺ ⟨n+2, 0, 0, n+1, 0⟩ := by
  -- Phase A: R5 step: (n+1, 0, 0, n, 0) → (n, 0, 1, n, 1)
  apply step_stepStar_stepPlus (c₂ := ⟨n, 0, 1, n, 1⟩)
  · show fm (n + 1, 0, 0, n, 0) = some (n, 0, 1, n, 1)
    unfold fm; rfl
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2m (even)
    rw [show m + m = 2 * m from by ring] at hm; subst hm
    apply stepStar_trans (phaseB_even m)
    apply stepStar_trans (phaseC_even m)
    have h := e_to_d (2 * m + 1) (2 * m + 2) 0
    simp only [Nat.zero_add] at h
    convert h using 2
  · -- n = 2m+1 (odd)
    subst hm
    apply stepStar_trans (phaseB_odd m)
    apply stepStar_trans (phaseC_odd m)
    have h := e_to_d (2 * m + 2) (2 * m + 3) 0
    simp only [Nat.zero_add] at h
    convert h using 2

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun n ↦ ⟨n+1+1, 0, 0, n+1, 0⟩) 0
  intro n
  exact ⟨n+1, by
    rw [show n + 1 + 1 + 1 = (n + 1) + 1 + 1 from by ring,
        show n + 1 + 1 = (n + 1) + 1 from by ring]
    exact main_trans⟩

end Sz21_140_unofficial_95
