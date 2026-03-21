import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #103: [7/15, 3/77, 242/3, 5/11, 63/2]

Vector representation:
```
 0 -1 -1  1  0
 0  1  0 -1 -1
 1 -1  0  0  2
 0  0  1  0 -1
-1  2  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_103

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | _ => none

-- R4 repeated: e → c (when b=0, d=0)
theorem e_to_c : ∀ k : ℕ, ∀ a c e, ⟨a, 0, c, 0, e+k⟩ [fm]⊢* ⟨a, 0, c+k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R5/R1/R1 chain: each round a-=1, c-=2, d+=3
theorem r5r1r1_chain : ∀ k : ℕ, ∀ a c d,
    ⟨a+k, 0, c+2*k, d, 0⟩ [fm]⊢* ⟨a, 0, c, d+3*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- R3 chain: b → a,e (when c=0, d=0)
theorem r3_chain : ∀ k : ℕ, ∀ a b e,
    ⟨a, b+k, 0, 0, e⟩ [fm]⊢* ⟨a+k, b, 0, 0, e+2*k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _ _)
  ring_nf; finish

-- Phase CD: (α, B+1, 0, D, 0) →* (α+B+D+1, 0, 0, 0, 2*B+D+2)
-- Induction on D with step D+2.
theorem phase_cd : ∀ D : ℕ, ∀ α B,
    ⟨α, B+1, 0, D, 0⟩ [fm]⊢* ⟨α+B+D+1, 0, 0, 0, 2*B+D+2⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih
  rcases D with _ | _ | D
  · -- D = 0: R3 chain
    intro α B
    have h := r3_chain (B+1) α 0 0
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  · -- D = 1: R3 → R2 → then R3 chain
    intro α B
    step fm; step fm
    have h := r3_chain (B+1) (α+1) 0 1
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_
    ring_nf; finish
  · -- D+2: R3, R2, R2, then IH with D, α+1, B+1
    intro α B
    rw [show (D + 2 : ℕ) = (D + 1) + 1 from by ring]
    step fm
    rw [show D + 2 = (D + 1) + 1 from by ring]
    step fm; step fm
    have h := ih D (by omega) (α+1) (B+1)
    refine stepStar_trans h ?_
    ring_nf; finish

-- Even transition: (A, 0, 0, 0, 2n) →⁺ (A+2n+2, 0, 0, 0, 3n+5) for A ≥ n+1
theorem trans_even : ∀ n : ℕ, ∀ a,
    ⟨a+n+1, 0, 0, 0, 2*n⟩ [fm]⊢⁺ ⟨a+3*n+3, 0, 0, 0, 3*n+5⟩ := by
  intro n a
  -- Phase A: R4 * 2n
  apply stepStar_stepPlus_stepPlus
  · have h := e_to_c (2*n) (a+n+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase B: R5/R1/R1 * n
  apply stepStar_stepPlus_stepPlus
  · have h := r5r1r1_chain n (a+1) 0 0
    simp only [Nat.zero_add] at h
    rw [show a + 1 + n = a + n + 1 from by ring] at h
    exact h
  -- R5 step: (a+1, 0, 0, 3n, 0) → (a, 2, 0, 3n+1, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 0, 3 * n, 0⟩ = some ⟨a, 0 + 2, 0, 3 * n + 1, 0⟩
    simp [fm]
  -- Phase CD: (a, 2, 0, 3n+1, 0) →* (a+3n+3, 0, 0, 0, 3n+5)
  have h := phase_cd (3*n+1) a 1
  refine stepStar_trans h ?_
  ring_nf; finish

-- Odd transition: (A, 0, 0, 0, 2n+1) →⁺ (A+2n+2, 0, 0, 0, 3n+4) for A ≥ n+1
theorem trans_odd : ∀ n : ℕ, ∀ a,
    ⟨a+n+1, 0, 0, 0, 2*n+1⟩ [fm]⊢⁺ ⟨a+3*n+3, 0, 0, 0, 3*n+4⟩ := by
  intro n a
  -- Phase A: R4 * (2n+1)
  apply stepStar_stepPlus_stepPlus
  · have h := e_to_c (2*n+1) (a+n+1) 0 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase B: R5/R1/R1 * n → (a+1, 0, 1, 3n, 0)
  apply stepStar_stepPlus_stepPlus
  · have h := r5r1r1_chain n (a+1) 1 0
    simp only [Nat.zero_add] at h
    rw [show a + 1 + n = a + n + 1 from by ring,
        show 1 + 2 * n = 2 * n + 1 from by ring] at h
    exact h
  -- R5 step from odd remainder: (a+1, 0, 1, 3n, 0) → R5 → (a, 2, 1, 3n+1, 0)
  apply step_stepStar_stepPlus
  · show fm ⟨a + 1, 0, 1, 3 * n, 0⟩ = some ⟨a, 0 + 2, 1, 3 * n + 1, 0⟩
    simp [fm]
  -- (a, 2, 1, 3n+1, 0) → R1 → (a, 1, 0, 3n+2, 0) → R3 → (a+1, 0, 0, 3n+2, 2)
  -- → R2 → (a+1, 1, 0, 3n+1, 1) → R2 → (a+1, 2, 0, 3n, 0)
  apply stepStar_trans
  · have h1 : ⟨a, 2, 1, 3*n+1, 0⟩ [fm]⊢ ⟨a, 1, 0, 3*n+2, 0⟩ := by
      show fm ⟨a, 1+1, 0+1, 3*n+1, 0⟩ = some ⟨a, 1, 0, 3*n+1+1, 0⟩
      simp [fm]
    have h2 : ⟨a, 1, 0, 3*n+2, 0⟩ [fm]⊢ ⟨a+1, 0, 0, 3*n+2, 2⟩ := by
      show fm ⟨a, 0+1, 0, 3*n+2, 0⟩ = some ⟨a+1, 0, 0, 3*n+2, 0+2⟩
      simp [fm]
    have h3 : ⟨a+1, 0, 0, 3*n+2, 2⟩ [fm]⊢ ⟨a+1, 1, 0, 3*n+1, 1⟩ := by
      show fm ⟨a+1, 0, 0, (3*n+1)+1, 1+1⟩ = some ⟨a+1, 0+1, 0, 3*n+1, 1⟩
      simp [fm]
    have h4 : ⟨a+1, 1, 0, 3*n+1, 1⟩ [fm]⊢ ⟨a+1, 2, 0, 3*n, 0⟩ := by
      show fm ⟨a+1, 1, 0, (3*n)+1, 0+1⟩ = some ⟨a+1, 1+1, 0, 3*n, 0⟩
      simp [fm]
    exact stepStar_trans (step_stepStar h1)
      (stepStar_trans (step_stepStar h2)
        (stepStar_trans (step_stepStar h3) (step_stepStar h4)))
  -- Phase CD: (a+1, 2, 0, 3n, 0) →* (a+3n+3, 0, 0, 0, 3n+4)
  have h := phase_cd (3*n) (a+1) 1
  refine stepStar_trans h ?_
  ring_nf; finish

-- Use progress_nonhalt
theorem nonhalt : ¬halts fm c₀ := by
  -- c₀ = (1,0,0,0,0) reaches (3, 0, 0, 0, 5) in 5 steps.
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 5⟩) (by execute fm 5)
  -- Invariant: (A, 0, 0, 0, e) with A ≥ e/2 + 1 and e ≥ 2
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ A e, q = ⟨A, 0, 0, 0, e⟩ ∧ A ≥ e / 2 + 1 ∧ e ≥ 2)
  · intro c ⟨A, e, hq, hA, he⟩; subst hq
    rcases Nat.even_or_odd e with ⟨n, hn⟩ | ⟨n, hn⟩
    · -- Even: e = n + n
      subst hn
      obtain ⟨a, rfl⟩ : ∃ a, A = a + n + 1 := ⟨A - n - 1, by omega⟩
      refine ⟨⟨a + 3*n + 3, 0, 0, 0, 3*n + 5⟩,
              ⟨a + 3*n + 3, 3*n + 5, rfl, ?_, ?_⟩, ?_⟩
      · omega
      · omega
      · have h := trans_even n a
        rw [show 2 * n = n + n from by ring] at h
        exact h
    · -- Odd: e = 2*n + 1
      subst hn
      obtain ⟨a, rfl⟩ : ∃ a, A = a + n + 1 := ⟨A - n - 1, by omega⟩
      refine ⟨⟨a + 3*n + 3, 0, 0, 0, 3*n + 4⟩,
              ⟨a + 3*n + 3, 3*n + 4, rfl, ?_, ?_⟩, ?_⟩
      · omega
      · omega
      · exact trans_odd n a
  · exact ⟨3, 5, rfl, by omega, by omega⟩

end Sz21_140_unofficial_103
