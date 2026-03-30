import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1118: [5/6, 4/35, 77/2, 9/7, 98/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  0
-1  0  0  1  1
 0  2  0 -1  0
 1  0  0  2 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1118

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d+2, e⟩
  | _ => none

-- R4 chain: drain d to b.
theorem r4_chain : ∀ k, ∀ b d e,
    ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · simp; exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

-- Spiral round: 8 steps.
theorem spiral_round : ∀ b c e,
    ⟨(0 : ℕ), b + 5, c, 0, e + 1⟩ [fm]⊢* ⟨0, b, c + 3, 0, e⟩ := by
  intro b c e
  step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  ring_nf; finish

-- Multiple spiral rounds.
theorem spiral_rounds : ∀ n, ∀ b c e,
    ⟨(0 : ℕ), b + 5 * n, c, 0, e + n⟩ [fm]⊢* ⟨0, b, c + 3 * n, 0, e⟩ := by
  intro n; induction' n with n ih <;> intro b c e
  · simp; exists 0
  · rw [show b + 5 * (n + 1) = (b + 5) + 5 * n from by ring,
        show e + (n + 1) = (e + 1) + n from by ring]
    apply stepStar_trans (ih (b + 5) c (e + 1))
    apply stepStar_trans (spiral_round b (c + 3 * n) e)
    ring_nf; finish

-- R3/R2 chain.
theorem r3r2_chain : ∀ c, ∀ a e,
    ⟨a + 1, (0 : ℕ), c, 0, e⟩ [fm]⊢* ⟨a + c + 1, 0, 0, 0, e + c⟩ := by
  intro c; induction' c with c ih <;> intro a e
  · simp; exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1))
    ring_nf; finish

-- R3 drain.
theorem r3_drain : ∀ k, ∀ a d e,
    ⟨a + k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (d + 1) (e + 1))
    ring_nf; finish

-- Combined exit + chain for r=0: (0, 0, c+3, 0, e+1) →⁺ (c+6, 0, 0, 0, e+c+1)
theorem exit_chain_r0 : ∀ c e,
    ⟨(0 : ℕ), 0, c + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨c + 6, 0, 0, 0, e + c + 1⟩ := by
  intro c e
  -- 5 steps: R5, R2, R2, R3, R2 → (6, 0, c, 0, e+1)
  step fm; step fm; step fm; step fm; step fm
  -- Then r3r2 chain
  apply stepStar_trans (r3r2_chain c 5 (e + 1))
  ring_nf; finish

-- Combined exit + chain for r=1: (0, 1, c+3, 0, e+1) →⁺ (c+6, 0, 0, 0, e+c+2)
theorem exit_chain_r1 : ∀ c e,
    ⟨(0 : ℕ), 1, c + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨c + 6, 0, 0, 0, e + c + 2⟩ := by
  intro c e
  -- 4 steps: R5, R1, R2, R2 → (4, 0, c+2, 0, e)
  step fm; step fm; step fm; step fm
  -- Then r3r2 chain of c+2
  apply stepStar_trans (r3r2_chain (c + 2) 3 e)
  ring_nf; finish

-- Combined exit + chain for r=2: (0, 2, c+3, 0, e+1) →⁺ (c+6, 0, 0, 0, e+c+3)
theorem exit_chain_r2 : ∀ c e,
    ⟨(0 : ℕ), 2, c + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨c + 6, 0, 0, 0, e + c + 3⟩ := by
  intro c e
  -- 5 steps: R5, R1, R2, R1, R2 → (3, 0, c+3, 0, e)
  step fm; step fm; step fm; step fm; step fm
  -- Then r3r2 chain of c+3
  apply stepStar_trans (r3r2_chain (c + 3) 2 e)
  ring_nf; finish

-- Combined exit + chain for r=3: (0, 3, c+3, 0, e+1) →⁺ (c+6, 0, 0, 0, e+c+4)
theorem exit_chain_r3 : ∀ c e,
    ⟨(0 : ℕ), 3, c + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨c + 6, 0, 0, 0, e + c + 4⟩ := by
  intro c e
  -- 6 steps: R5, R1, R2, R1, R1, R2 → (2, 0, c+4, 0, e)
  step fm; step fm; step fm; step fm; step fm; step fm
  -- Then r3r2 chain of c+4
  apply stepStar_trans (r3r2_chain (c + 4) 1 e)
  ring_nf; finish

-- Combined exit + chain for r=4: (0, 4, c+3, 0, e+1) →⁺ (c+6, 0, 0, 0, e+c+5)
theorem exit_chain_r4 : ∀ c e,
    ⟨(0 : ℕ), 4, c + 3, 0, e + 1⟩ [fm]⊢⁺ ⟨c + 6, 0, 0, 0, e + c + 5⟩ := by
  intro c e
  -- 9 steps: R5, R1, R2, R1, R1, R2, R1, R3, R2 → (2, 0, c+4, 0, e+1)
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm
  -- Then r3r2 chain of c+4
  apply stepStar_trans (r3r2_chain (c + 4) 1 (e + 1))
  ring_nf; finish

-- d ≡ 3 mod 5: d = 5q+3 (q >= 0)
-- n = 2q+1, r = 1. d' = 6q+6, e' = e + 15q + 9
theorem trans_mod3 : ∀ q e,
    ⟨(0 : ℕ), 0, 0, 5 * q + 3, e + 5 * q + 3⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * q + 6, e + 15 * q + 9⟩ := by
  intro q e
  apply stepStar_stepPlus_stepPlus
  · -- R4 drain
    have h := r4_chain (5 * q + 3) 0 0 (e + 5 * q + 3)
    rw [show 0 + (5 * q + 3) = 5 * q + 3 from by ring,
        show 0 + 2 * (5 * q + 3) = 10 * q + 6 from by ring] at h
    exact h
  apply stepPlus_stepStar_stepPlus
  · -- Spiral 2q+1 rounds then exit r=1
    apply stepStar_stepPlus_stepPlus
    · have h := spiral_rounds (2 * q + 1) 1 0 (e + 3 * q + 2)
      rw [show 1 + 5 * (2 * q + 1) = 10 * q + 6 from by ring,
          show 0 + 3 * (2 * q + 1) = 6 * q + 3 from by ring,
          show (e + 3 * q + 2) + (2 * q + 1) = e + 5 * q + 3 from by ring] at h
      exact h
    · have h := exit_chain_r1 (6 * q) (e + 3 * q + 1)
      rw [show 6 * q + 3 = 6 * q + 3 from rfl,
          show (e + 3 * q + 1) + 1 = e + 3 * q + 2 from by ring,
          show 6 * q + 6 = 6 * q + 6 from rfl,
          show (e + 3 * q + 1) + 6 * q + 2 = e + 9 * q + 3 from by ring] at h
      exact h
  · -- R3 drain
    rw [show e + 15 * q + 9 = (e + 9 * q + 3) + (6 * q + 6) from by ring]
    have h := r3_drain (6 * q + 6) 0 0 (e + 9 * q + 3)
    simp only [Nat.zero_add] at h; exact h

-- d ≡ 4 mod 5: d = 5q+4 (q >= 0)
-- n = 2q+1, r = 3. d' = 6q+6, e' = e + 15q + 12
theorem trans_mod4 : ∀ q e,
    ⟨(0 : ℕ), 0, 0, 5 * q + 4, e + 5 * q + 4⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * q + 6, e + 15 * q + 12⟩ := by
  intro q e
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (5 * q + 4) 0 0 (e + 5 * q + 4)
    rw [show 0 + (5 * q + 4) = 5 * q + 4 from by ring,
        show 0 + 2 * (5 * q + 4) = 10 * q + 8 from by ring] at h
    exact h
  apply stepPlus_stepStar_stepPlus
  · apply stepStar_stepPlus_stepPlus
    · have h := spiral_rounds (2 * q + 1) 3 0 (e + 3 * q + 3)
      rw [show 3 + 5 * (2 * q + 1) = 10 * q + 8 from by ring,
          show 0 + 3 * (2 * q + 1) = 6 * q + 3 from by ring,
          show (e + 3 * q + 3) + (2 * q + 1) = e + 5 * q + 4 from by ring] at h
      exact h
    · have h := exit_chain_r3 (6 * q) (e + 3 * q + 2)
      rw [show 6 * q + 3 = 6 * q + 3 from rfl,
          show (e + 3 * q + 2) + 1 = e + 3 * q + 3 from by ring,
          show 6 * q + 6 = 6 * q + 6 from rfl,
          show (e + 3 * q + 2) + 6 * q + 4 = e + 9 * q + 6 from by ring] at h
      exact h
  · rw [show e + 15 * q + 12 = (e + 9 * q + 6) + (6 * q + 6) from by ring]
    have h := r3_drain (6 * q + 6) 0 0 (e + 9 * q + 6)
    simp only [Nat.zero_add] at h; exact h

-- d ≡ 0 mod 5: d = 5(q+1) (q >= 0, so d >= 5)
-- n = 2(q+1), r = 0. d' = 6q+9, e' = e + 15q + 15
theorem trans_mod0 : ∀ q e,
    ⟨(0 : ℕ), 0, 0, 5 * (q + 1), e + 5 * (q + 1)⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * q + 9, e + 15 * q + 15⟩ := by
  intro q e
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (5 * (q + 1)) 0 0 (e + 5 * (q + 1))
    rw [show 0 + 5 * (q + 1) = 5 * (q + 1) from by ring,
        show 0 + 2 * (5 * (q + 1)) = 10 * q + 10 from by ring] at h
    exact h
  apply stepPlus_stepStar_stepPlus
  · apply stepStar_stepPlus_stepPlus
    · have h := spiral_rounds (2 * q + 2) 0 0 (e + 3 * q + 3)
      rw [show 0 + 5 * (2 * q + 2) = 10 * q + 10 from by ring,
          show 0 + 3 * (2 * q + 2) = 6 * q + 6 from by ring,
          show (e + 3 * q + 3) + (2 * q + 2) = e + 5 * (q + 1) from by ring] at h
      exact h
    · have h := exit_chain_r0 (6 * q + 3) (e + 3 * q + 2)
      rw [show 6 * q + 3 + 3 = 6 * q + 6 from by ring,
          show (e + 3 * q + 2) + 1 = e + 3 * q + 3 from by ring,
          show 6 * q + 3 + 6 = 6 * q + 9 from by ring,
          show (e + 3 * q + 2) + (6 * q + 3) + 1 = e + 9 * q + 6 from by ring] at h
      exact h
  · rw [show e + 15 * q + 15 = (e + 9 * q + 6) + (6 * q + 9) from by ring]
    have h := r3_drain (6 * q + 9) 0 0 (e + 9 * q + 6)
    simp only [Nat.zero_add] at h; exact h

-- d ≡ 1 mod 5: d = 5(q+1)+1 (q >= 0, so d >= 6)
-- n = 2(q+1), r = 2. d' = 6q+9, e' = e + 15q + 18
theorem trans_mod1 : ∀ q e,
    ⟨(0 : ℕ), 0, 0, 5 * (q + 1) + 1, e + 5 * (q + 1) + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * q + 9, e + 15 * q + 18⟩ := by
  intro q e
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (5 * (q + 1) + 1) 0 0 (e + 5 * (q + 1) + 1)
    rw [show 0 + (5 * (q + 1) + 1) = 5 * (q + 1) + 1 from by ring,
        show 0 + 2 * (5 * (q + 1) + 1) = 10 * q + 12 from by ring] at h
    exact h
  apply stepPlus_stepStar_stepPlus
  · apply stepStar_stepPlus_stepPlus
    · have h := spiral_rounds (2 * q + 2) 2 0 (e + 3 * q + 4)
      rw [show 2 + 5 * (2 * q + 2) = 10 * q + 12 from by ring,
          show 0 + 3 * (2 * q + 2) = 6 * q + 6 from by ring,
          show (e + 3 * q + 4) + (2 * q + 2) = e + 5 * (q + 1) + 1 from by ring] at h
      exact h
    · have h := exit_chain_r2 (6 * q + 3) (e + 3 * q + 3)
      rw [show 6 * q + 3 + 3 = 6 * q + 6 from by ring,
          show (e + 3 * q + 3) + 1 = e + 3 * q + 4 from by ring,
          show 6 * q + 3 + 6 = 6 * q + 9 from by ring,
          show (e + 3 * q + 3) + (6 * q + 3) + 3 = e + 9 * q + 9 from by ring] at h
      exact h
  · rw [show e + 15 * q + 18 = (e + 9 * q + 9) + (6 * q + 9) from by ring]
    have h := r3_drain (6 * q + 9) 0 0 (e + 9 * q + 9)
    simp only [Nat.zero_add] at h; exact h

-- d ≡ 2 mod 5: d = 5(q+1)+2 (q >= 0, so d >= 7)
-- n = 2(q+1), r = 4. d' = 6q+9, e' = e + 15q + 21
theorem trans_mod2 : ∀ q e,
    ⟨(0 : ℕ), 0, 0, 5 * (q + 1) + 2, e + 5 * (q + 1) + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 6 * q + 9, e + 15 * q + 21⟩ := by
  intro q e
  apply stepStar_stepPlus_stepPlus
  · have h := r4_chain (5 * (q + 1) + 2) 0 0 (e + 5 * (q + 1) + 2)
    rw [show 0 + (5 * (q + 1) + 2) = 5 * (q + 1) + 2 from by ring,
        show 0 + 2 * (5 * (q + 1) + 2) = 10 * q + 14 from by ring] at h
    exact h
  apply stepPlus_stepStar_stepPlus
  · apply stepStar_stepPlus_stepPlus
    · have h := spiral_rounds (2 * q + 2) 4 0 (e + 3 * q + 5)
      rw [show 4 + 5 * (2 * q + 2) = 10 * q + 14 from by ring,
          show 0 + 3 * (2 * q + 2) = 6 * q + 6 from by ring,
          show (e + 3 * q + 5) + (2 * q + 2) = e + 5 * (q + 1) + 2 from by ring] at h
      exact h
    · have h := exit_chain_r4 (6 * q + 3) (e + 3 * q + 4)
      rw [show 6 * q + 3 + 3 = 6 * q + 6 from by ring,
          show (e + 3 * q + 4) + 1 = e + 3 * q + 5 from by ring,
          show 6 * q + 3 + 6 = 6 * q + 9 from by ring,
          show (e + 3 * q + 4) + (6 * q + 3) + 5 = e + 9 * q + 12 from by ring] at h
      exact h
  · rw [show e + 15 * q + 21 = (e + 9 * q + 12) + (6 * q + 9) from by ring]
    have h := r3_drain (6 * q + 9) 0 0 (e + 9 * q + 12)
    simp only [Nat.zero_add] at h; exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 3⟩)
  · execute fm 10
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 3 ∧ e ≥ d)
  · intro c ⟨d, e, hq, hd, he⟩; subst hq
    obtain ⟨q, rfl | rfl | rfl | rfl | rfl⟩ : ∃ q, d = 5 * q + 3 ∨ d = 5 * q + 4 ∨
        d = 5 * (q + 1) ∨ d = 5 * (q + 1) + 1 ∨ d = 5 * (q + 1) + 2 := by
      exact ⟨(d - 3) / 5, by omega⟩
    · -- d = 5q+3
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 5 * q + 3 := ⟨e - 5 * q - 3, by omega⟩
      exact ⟨_, ⟨6 * q + 6, e' + 15 * q + 9,
        rfl, by omega, by omega⟩, trans_mod3 q e'⟩
    · -- d = 5q+4
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 5 * q + 4 := ⟨e - 5 * q - 4, by omega⟩
      exact ⟨_, ⟨6 * q + 6, e' + 15 * q + 12,
        rfl, by omega, by omega⟩, trans_mod4 q e'⟩
    · -- d = 5(q+1)
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 5 * (q + 1) := ⟨e - 5 * (q + 1), by omega⟩
      exact ⟨_, ⟨6 * q + 9, e' + 15 * q + 15,
        rfl, by omega, by omega⟩, trans_mod0 q e'⟩
    · -- d = 5(q+1)+1
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 5 * (q + 1) + 1 := ⟨e - 5 * (q + 1) - 1, by omega⟩
      exact ⟨_, ⟨6 * q + 9, e' + 15 * q + 18,
        rfl, by omega, by omega⟩, trans_mod1 q e'⟩
    · -- d = 5(q+1)+2
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 5 * (q + 1) + 2 := ⟨e - 5 * (q + 1) - 2, by omega⟩
      exact ⟨_, ⟨6 * q + 9, e' + 15 * q + 21,
        rfl, by omega, by omega⟩, trans_mod2 q e'⟩
  · exact ⟨3, 3, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_1118
