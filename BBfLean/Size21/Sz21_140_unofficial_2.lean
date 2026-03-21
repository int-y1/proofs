import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #2: [1/15, 9/77, 98/3, 5/7, 847/2]

Vector representation:
```
 0 -1 -1  0  0
 0  2  0 -1 -1
 1 -1  0  2  0
 0  0  1 -1  0
-1  0  0  1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_2

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | _ => none

-- R4 chain: d → c (generalized with c offset)
theorem d_to_c : ∀ k, ∀ a c d, ⟨a, 0, c, d + k, 0⟩ [fm]⊢* ⟨a, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro a c d
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R3 chain: b → a,d
theorem b_to_ad : ∀ k, ∀ a b d, ⟨a, b + k, 0, d, 0⟩ [fm]⊢* ⟨a + k, b, 0, d + 2 * k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm; apply stepStar_trans (h _ _ _); ring_nf; finish

-- Mix rounds: R5,R2,R1,R1 repeated
theorem mix_rounds : ∀ k, ∀ a c e, ⟨a + k, 0, c + 2 * k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k + 1) + 1 from by ring]
  step fm
  rw [show c + 2 * k + 1 + 1 = (c + 2 * k) + 1 + 1 from by ring]
  step fm; step fm
  rw [show c + 2 * k + 1 = (c + 2 * k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _); ring_nf; finish

-- Odd c end: R5,R2,R1,R3
theorem odd_end : ∀ a e, ⟨a + 1, 0, 1, 0, e⟩ [fm]⊢* ⟨a + 1, 0, 0, 2, e + 1⟩ := by
  intro a e; step fm; step fm; step fm; step fm; finish

-- Tail phase with B >= 1:
-- (A, B+1, 0, 2, n) →* (A+B+1+2*n, 0, 0, 2*B+3*n+4, 0)
theorem tail_phase_pos : ∀ n, ∀ B A,
    ⟨A, B + 1, 0, 2, n⟩ [fm]⊢* ⟨A + B + 1 + 2 * n, 0, 0, 2 * B + 3 * n + 4, 0⟩ := by
  intro n; induction' n using Nat.strongRecOn with n ih; intro B A
  rcases n with _ | _ | n
  · rw [show B + 1 = 0 + (B + 1) from by ring]
    apply stepStar_trans (b_to_ad (B + 1) _ _ _); ring_nf; finish
  · step fm
    rw [show B + 1 + 2 = 0 + (B + 3) from by ring]
    apply stepStar_trans (b_to_ad (B + 3) _ _ _); ring_nf; finish
  · rw [show n + 2 = (n + 1) + 1 from by ring]
    step fm; step fm
    rw [show B + 1 + 2 + 2 = (B + 3) + 1 + 1 from by ring]
    step fm
    apply stepStar_trans (ih n (by omega) (B + 3) (A + 1)); ring_nf; finish

-- Tail phase with B = 0, n >= 1:
-- (A, 0, 0, 2, n+1) →* (A+2*n+2, 0, 0, 3*n+5, 0)
theorem tail_phase0 : ∀ n, ∀ A,
    ⟨A, 0, 0, 2, n + 1⟩ [fm]⊢* ⟨A + 2 * n + 2, 0, 0, 3 * n + 5, 0⟩ := by
  intro n A
  rcases n with _ | n
  · -- (A, 0, 0, 2, 1) → R2 → (A, 2, 0, 1, 0) → R3 chain
    step fm
    -- Goal: (A, 2, 0, 1, 0) ⊢* (A + 2*0 + 2, 0, 0, 3*0 + 5, 0)
    have h := b_to_ad 2 A 0 1
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish
  · -- (A, 0, 0, 2, n+2): R2,R2,R3 → (A+1, 3, 0, 2, n) = (A+1, 2+1, 0, 2, n)
    rw [show n + 1 + 1 = (n + 1) + 1 from by ring]
    step fm -- R2: (A, 2, 0, 1, n+1)
    step fm -- R2: (A, 4, 0, 0, n)
    -- Need to rewrite 4 = (2+1)+1 for R3 step
    show ⟨A, (2 + 1) + 1, 0, 0, n⟩ [fm]⊢* ⟨A + 2 * (n + 1) + 2, 0, 0, 3 * (n + 1) + 5, 0⟩
    step fm -- R3: (A+1, 2+1, 0, 2, n)
    have h := tail_phase_pos n 2 (A + 1)
    refine stepStar_trans h ?_; ring_nf; finish

-- Main transition for odd d = 2k+1, a = x+k+1 (x >= 0):
theorem main_trans_odd (k x : ℕ) :
    ⟨x + k + 1, 0, 0, 2 * k + 1, 0⟩ [fm]⊢⁺ ⟨x + 2 * k + 3, 0, 0, 3 * k + 5, 0⟩ := by
  -- Phase 1: first R4 step (gives stepPlus)
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
  apply step_stepStar_stepPlus
    (c₂ := ⟨x + k + 1, 0, 1, 2 * k, 0⟩)
  · show fm ⟨x + k + 1, 0, 0, 2 * k + 1, 0⟩ = some ⟨x + k + 1, 0, 1, 2 * k, 0⟩
    simp [fm]
  -- Remaining R4 steps
  apply stepStar_trans (c₂ := ⟨x + k + 1, 0, 2 * k + 1, 0, 0⟩)
  · have h := d_to_c (2 * k) (x + k + 1) 1 0
    rw [show (0 : ℕ) + 2 * k = 2 * k from by ring,
        show 1 + 2 * k = 2 * k + 1 from by ring] at h; exact h
  -- Phase 2: mix_rounds k → (x+1, 0, 1, 0, k)
  apply stepStar_trans (c₂ := ⟨x + 1, 0, 1, 0, k⟩)
  · have h := mix_rounds k (x + 1) 1 0
    rw [show (x + 1) + k = x + k + 1 from by ring,
        show 1 + 2 * k = 2 * k + 1 from by ring,
        show 0 + k = k from by ring] at h; exact h
  -- Phase 3: odd_end → (x+1, 0, 0, 2, k+1)
  apply stepStar_trans (c₂ := ⟨x + 1, 0, 0, 2, k + 1⟩)
  · exact odd_end x k
  -- Phase 4: tail_phase0
  apply stepStar_trans (tail_phase0 k (x + 1)); ring_nf; finish

-- Main transition for even d = 2*(m+1), a = x+m+2 (x >= 0):
theorem main_trans_even (m x : ℕ) :
    ⟨x + m + 2, 0, 0, 2 * m + 2, 0⟩ [fm]⊢⁺ ⟨x + 2 * m + 6, 0, 0, 3 * m + 10, 0⟩ := by
  -- Phase 1: first R4 step
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  apply step_stepStar_stepPlus
    (c₂ := ⟨x + m + 2, 0, 1, 2 * m + 1, 0⟩)
  · show fm ⟨x + m + 2, 0, 0, (2 * m + 1) + 1, 0⟩ = some ⟨x + m + 2, 0, 1, 2 * m + 1, 0⟩
    simp [fm]
  -- Remaining R4 steps
  apply stepStar_trans (c₂ := ⟨x + m + 2, 0, 2 * m + 2, 0, 0⟩)
  · have h := d_to_c (2 * m + 1) (x + m + 2) 1 0
    rw [show (0 : ℕ) + (2 * m + 1) = 2 * m + 1 from by ring,
        show 1 + (2 * m + 1) = 2 * m + 2 from by ring] at h; exact h
  -- Phase 2: mix_rounds (m+1)
  apply stepStar_trans (c₂ := ⟨x + 1, 0, 0, 0, m + 1⟩)
  · have h := mix_rounds (m + 1) (x + 1) 0 0
    rw [show (x + 1) + (m + 1) = x + m + 2 from by ring,
        show 0 + 2 * (m + 1) = 2 * m + 2 from by ring,
        show 0 + (m + 1) = m + 1 from by ring] at h; exact h
  -- Phase 3: bridge (R5, R2, R3) → (x+1, 1, 0, 2, m+2)
  apply stepStar_trans (c₂ := ⟨x + 1, 1, 0, 2, m + 2⟩)
  · step fm; step fm; step fm; finish
  -- Phase 4: tail_phase_pos with B=0, n=m+2
  apply stepStar_trans (tail_phase_pos (m + 2) 0 (x + 1)); ring_nf; finish

-- Final theorem
theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 7, 0⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ a ≥ 1 ∧ d ≥ 1 ∧ 2 * a > d)
  · intro q ⟨a, d, hq, ha, hd, hinv⟩
    subst hq
    rcases Nat.even_or_odd d with ⟨M, hM⟩ | ⟨K, hK⟩
    · -- Even d = M + M
      rcases M with _ | m
      · omega
      · -- d = (m+1) + (m+1) = 2*m+2
        have ham : a ≥ m + 2 := by omega
        obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le ham
        refine ⟨⟨x + 2 * m + 6, 0, 0, 3 * m + 10, 0⟩,
                ⟨x + 2 * m + 6, 3 * m + 10, rfl, by omega, by omega, by omega⟩,
                ?_⟩
        rw [hx, hM]
        have h := main_trans_even m x
        rw [show x + m + 2 = m + 2 + x from by ring,
            show 2 * m + 2 = (m + 1) + (m + 1) from by ring] at h
        exact h
    · -- Odd d = 2*K + 1
      have haK : a ≥ K + 1 := by omega
      obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le haK
      refine ⟨⟨x + 2 * K + 3, 0, 0, 3 * K + 5, 0⟩,
              ⟨x + 2 * K + 3, 3 * K + 5, rfl, by omega, by omega, by omega⟩,
              ?_⟩
      rw [hx, hK]
      have h := main_trans_odd K x
      rw [show x + K + 1 = K + 1 + x from by ring] at h
      exact h
  · exact ⟨4, 7, rfl, by omega, by omega, by omega⟩

end Sz21_140_unofficial_2
