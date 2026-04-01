import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1274: [54/35, 1/33, 5/3, 11/25, 147/2]

Vector representation:
```
 1  3 -1 -1  0
 0 -1  0  0 -1
 0 -1  1  0  0
 0  0 -2  0  1
-1  1  0  2  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1274

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+1, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+2, e⟩
  | _ => none

-- R1/R3 chain: (a, b, 1, k+1, 0) ⊢* (a+k+1, b+2*k+3, 0, 0, 0)
theorem r1r3_chain : ∀ k, ∀ a b,
    ⟨a, b, 1, k + 1, (0 : ℕ)⟩ [fm]⊢* ⟨a + k + 1, b + 2 * k + 3, 0, 0, (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a b
  · step fm; finish
  · rw [show k + 1 + 1 = (k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) (b + 2))
    ring_nf; finish

-- R3 chain: move b to c (when d=0, e=0)
theorem b_to_c : ∀ k, ∀ a c,
    ⟨a, k, c, (0 : ℕ), (0 : ℕ)⟩ [fm]⊢* ⟨a, (0 : ℕ), c + k, (0 : ℕ), (0 : ℕ)⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  · rw [show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (c + 1))
    ring_nf; finish

-- R4 chain: (a, 0, 2*k+1, 0, e) ⊢* (a, 0, 1, 0, e+k)
theorem r4_chain : ∀ k, ∀ a e,
    ⟨a, (0 : ℕ), 2 * k + 1, (0 : ℕ), e⟩ [fm]⊢* ⟨a, (0 : ℕ), 1, (0 : ℕ), e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (e + 1))
    ring_nf; finish

-- R2 chain: drain b using e
theorem r2_chain : ∀ k, ∀ a d e,
    ⟨a, k, (0 : ℕ), d, e + k⟩ [fm]⊢* ⟨a, (0 : ℕ), (0 : ℕ), d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring,
        show (k + 1 : ℕ) = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a d e)
    finish

-- R5+R2 chain: (a+k, 0, 0, d, e+k) ⊢* (a, 0, 0, d+2*k, e)
theorem r5r2_chain : ∀ k, ∀ a d e,
    ⟨a + k, (0 : ℕ), (0 : ℕ), d, e + k⟩ [fm]⊢* ⟨a, (0 : ℕ), (0 : ℕ), d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · simp; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (d + 2) e)
    ring_nf; finish

-- Main transition: (3*n, 0, 1, 2^n+5, 0) ⊢⁺ (3*(n+1), 0, 1, 2^(n+1)+5, 0)
theorem main_trans (n : ℕ) :
    ⟨3 * n, (0 : ℕ), 1, 2 ^ n + 5, (0 : ℕ)⟩ [fm]⊢⁺
    ⟨3 * (n + 1), (0 : ℕ), 1, 2 ^ (n + 1) + 5, (0 : ℕ)⟩ := by
  have h2n : 2 ^ n ≥ 1 := Nat.one_le_pow _ _ (by omega)
  -- Phase 1: R1/R3 chain consuming d = 2^n+5
  -- (3*n, 0, 1, 2^n+5, 0) ⊢* (3*n+2^n+5, 2*(2^n+4)+3, 0, 0, 0)
  -- = (3*n+2^n+5, 2^(n+1)+11, 0, 0, 0)
  have phase1 : ⟨3 * n, (0 : ℕ), 1, 2 ^ n + 5, (0 : ℕ)⟩ [fm]⊢*
      ⟨3 * n + 2 ^ n + 5, 2 ^ (n + 1) + 11, 0, 0, (0 : ℕ)⟩ := by
    rw [show 2 ^ n + 5 = (2 ^ n + 4) + 1 from by omega]
    have h := r1r3_chain (2 ^ n + 4) (3 * n) 0
    rw [show 3 * n + (2 ^ n + 4) + 1 = 3 * n + 2 ^ n + 5 from by ring,
        show 0 + 2 * (2 ^ n + 4) + 3 = 2 ^ (n + 1) + 11 from by
          rw [show 2 ^ (n + 1) = 2 * 2 ^ n from by ring]; ring] at h
    exact h
  -- Phase 2: R3 chain (b to c)
  -- (3*n+2^n+5, 2^(n+1)+11, 0, 0, 0) ⊢* (3*n+2^n+5, 0, 2^(n+1)+11, 0, 0)
  have phase2 : ⟨3 * n + 2 ^ n + 5, 2 ^ (n + 1) + 11, 0, 0, (0 : ℕ)⟩ [fm]⊢*
      ⟨3 * n + 2 ^ n + 5, (0 : ℕ), 2 ^ (n + 1) + 11, 0, (0 : ℕ)⟩ := by
    have h := b_to_c (2 ^ (n + 1) + 11) (3 * n + 2 ^ n + 5) 0
    simp at h; exact h
  -- Phase 3: R4 chain
  -- 2^(n+1)+11 = 2*(2^n+5)+1, so k = 2^n+5
  -- (3*n+2^n+5, 0, 2*(2^n+5)+1, 0, 0) ⊢* (3*n+2^n+5, 0, 1, 0, 2^n+5)
  have phase3 : ⟨3 * n + 2 ^ n + 5, (0 : ℕ), 2 ^ (n + 1) + 11, 0, (0 : ℕ)⟩ [fm]⊢*
      ⟨3 * n + 2 ^ n + 5, (0 : ℕ), 1, (0 : ℕ), 2 ^ n + 5⟩ := by
    rw [show 2 ^ (n + 1) + 11 = 2 * (2 ^ n + 5) + 1 from by
          rw [show 2 ^ (n + 1) = 2 * 2 ^ n from by ring]; ring]
    have h := r4_chain (2 ^ n + 5) (3 * n + 2 ^ n + 5) 0
    simp at h; exact h
  -- Phase 4: R5 + R1 (2 steps)
  -- (3*n+2^n+5, 0, 1, 0, 2^n+5) -> R5 -> (3*n+2^n+4, 1, 1, 2, 2^n+5)
  -- -> R1 -> (3*n+2^n+5, 4, 0, 1, 2^n+5)
  have phase4 : ⟨3 * n + 2 ^ n + 5, (0 : ℕ), 1, (0 : ℕ), 2 ^ n + 5⟩ [fm]⊢⁺
      ⟨3 * n + 2 ^ n + 5, 4, 0, 1, 2 ^ n + 5⟩ := by
    rw [show 3 * n + 2 ^ n + 5 = (3 * n + 2 ^ n + 4) + 1 from by ring]
    step fm; step fm; finish
  -- Phase 5: R2 chain x4
  -- (3*n+2^n+5, 4, 0, 1, 2^n+5) ⊢* (3*n+2^n+5, 0, 0, 1, 2^n+1)
  have phase5 : ⟨3 * n + 2 ^ n + 5, 4, 0, 1, 2 ^ n + 5⟩ [fm]⊢*
      ⟨3 * n + 2 ^ n + 5, (0 : ℕ), (0 : ℕ), 1, 2 ^ n + 1⟩ := by
    rw [show 2 ^ n + 5 = (2 ^ n + 1) + 4 from by ring]
    exact r2_chain 4 (3 * n + 2 ^ n + 5) 1 (2 ^ n + 1)
  -- Phase 6: R5+R2 chain x(2^n+1)
  -- (3*n+2^n+5, 0, 0, 1, 2^n+1) ⊢* (3*n+4, 0, 0, 2^(n+1)+3, 0)
  have phase6 : ⟨3 * n + 2 ^ n + 5, (0 : ℕ), (0 : ℕ), 1, 2 ^ n + 1⟩ [fm]⊢*
      ⟨3 * n + 4, (0 : ℕ), (0 : ℕ), 2 ^ (n + 1) + 3, (0 : ℕ)⟩ := by
    rw [show 3 * n + 2 ^ n + 5 = (3 * n + 4) + (2 ^ n + 1) from by ring]
    have h := r5r2_chain (2 ^ n + 1) (3 * n + 4) 1 0
    simp at h
    rw [show 1 + 2 * (2 ^ n + 1) = 2 ^ (n + 1) + 3 from by
          rw [show 2 ^ (n + 1) = 2 * 2 ^ n from by ring]; ring] at h
    exact h
  -- Phase 7: R5 + R3 (2 steps)
  -- (3*n+4, 0, 0, 2^(n+1)+3, 0) -> R5 -> (3*n+3, 1, 0, 2^(n+1)+5, 0)
  -- -> R3 -> (3*n+3, 0, 1, 2^(n+1)+5, 0) = (3*(n+1), 0, 1, 2^(n+1)+5, 0)
  have phase7 : ⟨3 * n + 4, (0 : ℕ), (0 : ℕ), 2 ^ (n + 1) + 3, (0 : ℕ)⟩ [fm]⊢*
      ⟨3 * (n + 1), (0 : ℕ), 1, 2 ^ (n + 1) + 5, (0 : ℕ)⟩ := by
    rw [show 3 * n + 4 = (3 * n + 3) + 1 from by ring]
    step fm; step fm
    rw [show 3 * n + 3 = 3 * (n + 1) from by ring]
    finish
  -- Compose all phases
  exact stepStar_stepPlus_stepPlus phase1
    (stepStar_stepPlus_stepPlus phase2
      (stepStar_stepPlus_stepPlus phase3
        (stepPlus_stepStar_stepPlus phase4
          (stepStar_trans phase5
            (stepStar_trans phase6 phase7)))))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 6, 0⟩) (by execute fm 30)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨3 * n, 0, 1, 2 ^ n + 5, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1274
