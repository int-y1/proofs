import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz22_2003_unofficial #453: [28/15, 1/6, 27/49, 25/2, 3/5]

Vector representation:
```
 2 -1 -1  1
-1 -1  0  0
 0  3  0 -2
-1  0  2  0
 0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_453

def Q := ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d⟩ => some ⟨a+2, b, c, d+1⟩
  | ⟨a+1, b+1, c, d⟩ => some ⟨a, b, c, d⟩
  | ⟨a, b, c, d+2⟩ => some ⟨a, b+3, c, d⟩
  | ⟨a+1, b, c, d⟩ => some ⟨a, b, c+2, d⟩
  | ⟨a, b, c+1, d⟩ => some ⟨a, b+1, c, d⟩
  | _ => none

-- R4 chain: (a+k, 0, c, 0) ⊢* (a, 0, c+2*k, 0)
theorem r4_chain : ∀ k, ∀ a c, ⟨a+(k : ℕ), 0, c, 0⟩ [fm]⊢* ⟨a, 0, c+2*k, 0⟩ := by
  intro k; induction' k with k h <;> intro a c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Setup: (0, 0, c+2, 0) ⊢* (2, 3, c+2, 0) in 7 steps
theorem setup (c : ℕ) : ⟨0, 0, c+2, 0⟩ [fm]⊢* ⟨2, 3, c+2, 0⟩ := by
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm -- R5
  step fm -- R1
  step fm -- R4
  rw [show c + 2 = (c + 1) + 1 from by ring]
  step fm -- R4
  rw [show c + 4 = (c + 3) + 1 from by ring]
  step fm -- R5
  rw [show c + 3 = (c + 2) + 1 from by ring]
  step fm -- R1
  step fm -- R3
  finish

-- One round of R1x3 + R3: (a, 3, c+3, d) ⊢* (a+6, 3, c, d+1)
theorem one_round (a c d : ℕ) : ⟨a, (3 : ℕ), c+3, d⟩ [fm]⊢* ⟨a+6, 3, c, d+1⟩ := by
  rw [show c + 3 = (c + 2) + 1 from by ring,
      show (3 : ℕ) = (2 : ℕ) + 1 from rfl]
  step fm
  rw [show c + 2 = (c + 1) + 1 from by ring,
      show (2 : ℕ) = (1 : ℕ) + 1 from rfl]
  step fm -- R1: (a+4, 1, c+1, d+2)
  rw [show c + 1 = c + 1 from rfl,
      show (1 : ℕ) = (0 : ℕ) + 1 from rfl]
  step fm -- R1: (a+6, 0, c, d+3)
  rw [show d + 3 = (d + 1) + 2 from by ring]
  step fm -- R3: (a+6, 3, c, d+1)
  finish

-- Interleaved rounds: (a, 3, c+3*k, d) ⊢* (a+6*k, 3, c, d+k)
theorem interleaved : ∀ k, ∀ a c d, ⟨a, (3 : ℕ), c+3*k, d⟩ [fm]⊢* ⟨a+6*k, 3, c, d+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d
  · exists 0
  rw [show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring]
  apply stepStar_trans (one_round _ _ _)
  rw [show a + 6 * (k + 1) = (a + 6) + 6 * k from by ring,
      show d + (k + 1) = (d + 1) + k from by ring]
  exact ih _ _ _

-- R3+R2x3 drain: (a+3*k, 0, 0, 2*k) ⊢* (a, 0, 0, 0)
theorem drain : ∀ k, ∀ a, ⟨a+3*k, 0, 0, 2*k⟩ [fm]⊢* ⟨a, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a
  · exists 0
  rw [show 2 * (k + 1) = (2 * k) + 2 from by ring,
      show a + 3 * (k + 1) = (a + 3 * k) + 3 from by ring]
  step fm
  rw [show a + 3 * k + 3 = (a + 3 * k + 2) + 1 from by ring,
      show (3 : ℕ) = (2 : ℕ) + 1 from rfl]
  step fm -- R2
  rw [show a + 3 * k + 2 = (a + 3 * k + 1) + 1 from by ring,
      show (2 : ℕ) = (1 : ℕ) + 1 from rfl]
  step fm -- R2
  rw [show a + 3 * k + 1 = (a + 3 * k) + 1 from by ring,
      show (1 : ℕ) = (0 : ℕ) + 1 from rfl]
  step fm -- R2: (a+3*k, 0, 0, 2*k)
  apply stepStar_trans (ih _)
  ring_nf; finish

-- Tail for remainder 0: (a+3, 3, 0, d) ⊢* (a, 0, 0, d)
theorem tail_r0 (a d : ℕ) : ⟨a+3, (3 : ℕ), 0, d⟩ [fm]⊢* ⟨a, 0, 0, d⟩ := by
  rw [show a + 3 = (a + 2) + 1 from by ring,
      show (3 : ℕ) = (2 : ℕ) + 1 from rfl]
  step fm -- R2
  rw [show a + 2 = (a + 1) + 1 from by ring,
      show (2 : ℕ) = (1 : ℕ) + 1 from rfl]
  step fm -- R2
  rw [show a + 1 = a + 1 from rfl,
      show (1 : ℕ) = (0 : ℕ) + 1 from rfl]
  step fm -- R2
  finish

-- Tail for remainder 1: (a, 3, 1, d) ⊢* (a, 0, 0, d+1)
theorem tail_r1 (a d : ℕ) : ⟨a, (3 : ℕ), 1, d⟩ [fm]⊢* ⟨a, 0, 0, d+1⟩ := by
  rw [show (3 : ℕ) = (2 : ℕ) + 1 from rfl,
      show (1 : ℕ) = (0 : ℕ) + 1 from rfl]
  step fm -- R1: (a+2, 2, 0, d+1)
  rw [show a + 2 = (a + 1) + 1 from by ring,
      show (2 : ℕ) = (1 : ℕ) + 1 from rfl]
  step fm -- R2
  rw [show a + 1 = a + 1 from rfl,
      show (1 : ℕ) = (0 : ℕ) + 1 from rfl]
  step fm -- R2
  finish

-- Tail for remainder 2: (a, 3, 2, d) ⊢* (a+3, 0, 0, d+2)
theorem tail_r2 (a d : ℕ) : ⟨a, (3 : ℕ), 2, d⟩ [fm]⊢* ⟨a+3, 0, 0, d+2⟩ := by
  rw [show (3 : ℕ) = (2 : ℕ) + 1 from rfl,
      show (2 : ℕ) = (1 : ℕ) + 1 from rfl]
  step fm -- R1: (a+2, 2, 1, d+1)
  rw [show (2 : ℕ) = (1 : ℕ) + 1 from rfl,
      show (1 : ℕ) = (0 : ℕ) + 1 from rfl]
  step fm -- R1: (a+4, 1, 0, d+2)
  rw [show a + 4 = (a + 3) + 1 from by ring,
      show (1 : ℕ) = (0 : ℕ) + 1 from rfl]
  step fm -- R2
  finish

-- n ≡ 0 mod 3: n = 3*k
-- (0, 0, 6*k+2, 0) ⊢⁺ (0, 0, 18*k+4, 0)
theorem trans_mod0 (k : ℕ) : ⟨0, 0, 6*k+2, 0⟩ [fm]⊢⁺ ⟨0, 0, 18*k+4, 0⟩ := by
  -- Setup: (0, 0, 6*k+2, 0) ⊢* (2, 3, 6*k+2, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 3, 6*k+2, 0⟩)
  · have h := setup (6*k); rw [show 6 * k + 2 = 6 * k + 2 from rfl] at h; exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨12*k+2, 3, 2, 2*k⟩)
  · have h := interleaved (2*k) 2 2 0
    rw [show 2 + 3 * (2 * k) = 6 * k + 2 from by ring,
        show 2 + 6 * (2 * k) = 12 * k + 2 from by ring,
        show 0 + 2 * k = 2 * k from by ring] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨12*k+5, 0, 0, 2*k+2⟩)
  · have h := tail_r2 (12*k+2) (2*k)
    rw [show 12 * k + 2 + 3 = 12 * k + 5 from by ring,
        show 2 * k + 2 = 2 * k + 2 from rfl] at h
    exact h
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨9*k+2, 0, 0, 0⟩)
  · have h := drain (k+1) (9*k+2)
    rw [show 9 * k + 2 + 3 * (k + 1) = 12 * k + 5 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring] at h
    exact h
  have h := r4_chain (9*k+2) 0 0
  rw [show (0 : ℕ) + (9 * k + 2) = 9 * k + 2 from by ring,
      show 0 + 2 * (9 * k + 2) = 18 * k + 4 from by ring] at h
  exact step_stepStar_stepPlus (by show fm ⟨9 * k + 2, 0, 0, 0⟩ = some ⟨9 * k + 1, 0, 2, 0⟩; simp [fm])
    (by apply stepStar_trans
        · have h2 := r4_chain (9*k+1) 0 2
          rw [show (0 : ℕ) + (9 * k + 1) = 9 * k + 1 from by ring] at h2; exact h2
        ring_nf; finish)

-- n ≡ 1 mod 3: n = 3*k+1
-- (0, 0, 6*k+4, 0) ⊢⁺ (0, 0, 18*k+10, 0)
theorem trans_mod1 (k : ℕ) : ⟨0, 0, 6*k+4, 0⟩ [fm]⊢⁺ ⟨0, 0, 18*k+10, 0⟩ := by
  -- Setup
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 3, 6*k+4, 0⟩)
  · have h := setup (6*k+2); rw [show 6 * k + 2 + 2 = 6 * k + 4 from by ring] at h; exact h
  -- Interleaved: 2*k+1 rounds
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨12*k+8, 3, 1, 2*k+1⟩)
  · have h := interleaved (2*k+1) 2 1 0
    rw [show 1 + 3 * (2 * k + 1) = 6 * k + 4 from by ring,
        show 2 + 6 * (2 * k + 1) = 12 * k + 8 from by ring,
        show 0 + (2 * k + 1) = 2 * k + 1 from by ring] at h
    exact h
  -- Tail r=1
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨12*k+8, 0, 0, 2*k+2⟩)
  · have h := tail_r1 (12*k+8) (2*k+1)
    rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring] at h; exact h
  -- Drain
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨9*k+5, 0, 0, 0⟩)
  · have h := drain (k+1) (9*k+5)
    rw [show 9 * k + 5 + 3 * (k + 1) = 12 * k + 8 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring] at h
    exact h
  -- R4 chain
  have h := r4_chain (9*k+5) 0 0
  rw [show (0 : ℕ) + (9 * k + 5) = 9 * k + 5 from by ring,
      show 0 + 2 * (9 * k + 5) = 18 * k + 10 from by ring] at h
  exact step_stepStar_stepPlus (by show fm ⟨9 * k + 5, 0, 0, 0⟩ = some ⟨9 * k + 4, 0, 2, 0⟩; simp [fm])
    (by apply stepStar_trans
        · have h2 := r4_chain (9*k+4) 0 2
          rw [show (0 : ℕ) + (9 * k + 4) = 9 * k + 4 from by ring] at h2; exact h2
        ring_nf; finish)

-- n ≡ 2 mod 3: n = 3*k+2
-- (0, 0, 6*k+6, 0) ⊢⁺ (0, 0, 18*k+16, 0)
theorem trans_mod2 (k : ℕ) : ⟨0, 0, 6*k+6, 0⟩ [fm]⊢⁺ ⟨0, 0, 18*k+16, 0⟩ := by
  -- Setup
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 3, 6*k+6, 0⟩)
  · have h := setup (6*k+4); rw [show 6 * k + 4 + 2 = 6 * k + 6 from by ring] at h; exact h
  -- Interleaved: 2*k+2 rounds
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨12*k+14, 3, 0, 2*k+2⟩)
  · have h := interleaved (2*k+2) 2 0 0
    rw [show 0 + 3 * (2 * k + 2) = 6 * k + 6 from by ring,
        show 2 + 6 * (2 * k + 2) = 12 * k + 14 from by ring,
        show 0 + (2 * k + 2) = 2 * k + 2 from by ring] at h
    exact h
  -- Tail r=0
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨12*k+11, 0, 0, 2*k+2⟩)
  · have h := tail_r0 (12*k+11) (2*k+2)
    rw [show 12 * k + 11 + 3 = 12 * k + 14 from by ring] at h; exact h
  -- Drain
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨9*k+8, 0, 0, 0⟩)
  · have h := drain (k+1) (9*k+8)
    rw [show 9 * k + 8 + 3 * (k + 1) = 12 * k + 11 from by ring,
        show 2 * (k + 1) = 2 * k + 2 from by ring] at h
    exact h
  -- R4 chain
  have h := r4_chain (9*k+8) 0 0
  rw [show (0 : ℕ) + (9 * k + 8) = 9 * k + 8 from by ring,
      show 0 + 2 * (9 * k + 8) = 18 * k + 16 from by ring] at h
  exact step_stepStar_stepPlus (by show fm ⟨9 * k + 8, 0, 0, 0⟩ = some ⟨9 * k + 7, 0, 2, 0⟩; simp [fm])
    (by apply stepStar_trans
        · have h2 := r4_chain (9*k+7) 0 2
          rw [show (0 : ℕ) + (9 * k + 7) = 9 * k + 7 from by ring] at h2; exact h2
        ring_nf; finish)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n, q = ⟨0, 0, 2*n+2, 0⟩)
  · intro c ⟨n, hq⟩; subst hq
    have hmod := Nat.div_add_mod n 3
    set q := n / 3
    set r := n % 3
    have hr : r < 3 := Nat.mod_lt n (by omega)
    interval_cases r
    · rw [show 2 * n + 2 = 6 * q + 2 from by omega]
      exact ⟨⟨0, 0, 18*q+4, 0⟩, ⟨9*q+1, by ring_nf⟩, trans_mod0 q⟩
    · rw [show 2 * n + 2 = 6 * q + 4 from by omega]
      exact ⟨⟨0, 0, 18*q+10, 0⟩, ⟨9*q+4, by ring_nf⟩, trans_mod1 q⟩
    · rw [show 2 * n + 2 = 6 * q + 6 from by omega]
      exact ⟨⟨0, 0, 18*q+16, 0⟩, ⟨9*q+7, by ring_nf⟩, trans_mod2 q⟩
  · exact ⟨0, rfl⟩

end Sz22_2003_unofficial_453
