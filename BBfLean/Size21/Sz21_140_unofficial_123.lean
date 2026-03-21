import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz21_140_unofficial #123: [8/15, 3/14, 55/2, 7/5, 10/11]

Vector representation:
```
 3 -1 -1  0  0
-1  1  0 -1  0
-1  0  1  0  1
 0  0 -1  1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_123

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R3 repeated: a → c, e
theorem a_to_ce : ∀ k, ∀ a c e, ⟨a+k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c+k, 0, e+k⟩ := by
  intro k; induction' k with k h <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 repeated: c → d
theorem c_to_d : ∀ k, ∀ c d e, ⟨0, 0, c+k, d, e⟩ [fm]⊢* ⟨0, 0, c, d+k, e⟩ := by
  intro k; induction' k with k h <;> intro c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Phases 1+2 combined
theorem phases12 (n : ℕ) (e : ℕ) : ⟨n, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, n, e+n⟩ := by
  apply stepStar_trans (c₂ := ⟨0, 0, n, 0, e+n⟩)
  · have h := a_to_ce n 0 0 e; simp only [Nat.zero_add] at h; exact h
  · have h := c_to_d n 0 0 (e+n); simp only [Nat.zero_add] at h; exact h

-- R2 repeated: a → b, consuming d
theorem r2_repeat : ∀ k, ∀ a b d e, ⟨a+k, b, 0, d+k, e⟩ [fm]⊢* ⟨a, b+k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro a b d e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R3R1 drain
theorem drain : ∀ b, ∀ a e, ⟨a+1, b, 0, 0, e⟩ [fm]⊢* ⟨a+1+2*b, 0, 0, 0, e+b⟩ := by
  intro b; induction' b with b h <;> intro a e
  · exists 0
  step fm
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- Big round for b=0
theorem big_round_b0 : ∀ d e, ⟨0, 0, 0, d+4, e+1⟩ [fm]⊢* ⟨0, 3, 0, d, e⟩ := by
  intro d e
  step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Big round for b>=1
theorem big_round_bn : ∀ b d e, ⟨0, b+1, 0, d+4, e+1⟩ [fm]⊢* ⟨0, b+4, 0, d, e⟩ := by
  intro b d e
  step fm; step fm
  have h := r2_repeat 4 0 b d e
  simp only [Nat.zero_add] at h
  rw [show b + 4 = b + 4 from rfl] at h
  exact h

-- General big round
theorem big_round_one (b d e : ℕ) : ⟨0, b, 0, d+4, e+1⟩ [fm]⊢* ⟨0, b+3, 0, d, e⟩ := by
  rcases b with _ | b
  · exact big_round_b0 d e
  · have h := big_round_bn b d e
    rw [show b + 4 = b + 1 + 3 from by ring] at h; exact h

-- Big rounds by induction
theorem big_rounds : ∀ k, ∀ b d e, ⟨0, b, 0, d+4*k, e+k⟩ [fm]⊢* ⟨0, b+3*k, 0, d, e⟩ := by
  intro k; induction' k with k h <;> intro b d e
  · exists 0
  rw [show d + 4 * (k + 1) = (d + 4 * k) + 4 from by ring,
      show e + (k + 1) = (e + k) + 1 from by ring]
  apply stepStar_trans (big_round_one _ _ _)
  rw [show b + 3 * (k + 1) = (b + 3) + 3 * k from by ring]
  exact h _ _ _

-- Tail for d=1 with b=0
theorem tail_1_b0 : ∀ e, ⟨0, 0, 0, 1, e+1⟩ [fm]⊢⁺ ⟨3, 0, 0, 0, e⟩ := by
  intro e
  step fm; step fm; step fm; finish

-- Tail for d=1 with b>=1
theorem tail_1_bn : ∀ b e, ⟨0, b+1, 0, 1, e+1⟩ [fm]⊢⁺ ⟨2*b+5, 0, 0, 0, e+b+1⟩ := by
  intro b e
  step fm; step fm; step fm
  have h := drain (b+1) 2 e
  rw [show 2 + 1 + 2 * (b + 1) = 2 * b + 5 from by ring,
      show e + (b + 1) = e + b + 1 from by ring] at h
  exact h

-- Tail for d=2 with b=0
theorem tail_2_b0 : ∀ e, ⟨0, 0, 0, 2, e+1⟩ [fm]⊢⁺ ⟨4, 0, 0, 0, e+1⟩ := by
  intro e
  step fm; step fm; step fm; step fm; step fm; step fm; finish

-- Tail for d=2 with b>=1
theorem tail_2_bn : ∀ b e, ⟨0, b+1, 0, 2, e+1⟩ [fm]⊢⁺ ⟨2*b+6, 0, 0, 0, e+b+2⟩ := by
  intro b e
  step fm; step fm; step fm; step fm; step fm; step fm
  have h := drain (b+1) 3 (e+1)
  rw [show 3 + 1 + 2 * (b + 1) = 2 * b + 6 from by ring,
      show e + 1 + (b + 1) = e + b + 2 from by ring] at h
  exact h

-- Tail for d=3 with b=0
theorem tail_3_b0 : ∀ e, ⟨0, 0, 0, 3, e+1⟩ [fm]⊢⁺ ⟨5, 0, 0, 0, e+2⟩ := by
  intro e
  step fm; step fm; step fm; step fm; step fm
  step fm; step fm; step fm; step fm; finish

-- Tail for d=3 with b>=1
theorem tail_3_bn : ∀ b e, ⟨0, b+1, 0, 3, e+1⟩ [fm]⊢⁺ ⟨2*b+7, 0, 0, 0, e+b+3⟩ := by
  intro b e
  step fm; step fm; step fm; step fm; step fm; step fm; step fm
  have h := drain (b+2) 2 (e+1)
  rw [show 2 + 1 + 2 * (b + 2) = 2 * b + 7 from by ring,
      show e + 1 + (b + 2) = e + b + 3 from by ring] at h
  exact h

-- Tail for d=0 with b>=1
theorem tail_0 : ∀ b e, ⟨0, b+1, 0, 0, e+1⟩ [fm]⊢⁺ ⟨2*b+4, 0, 0, 0, e+b⟩ := by
  intro b e
  step fm; step fm
  have h := drain b 3 e
  rw [show 3 + 1 + 2 * b = 2 * b + 4 from by ring] at h; exact h

-- Full transition for a=4k+1
theorem trans_r1 (k : ℕ) (e : ℕ) : ⟨4*k+1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨6*k+3, 0, 0, 0, e+6*k⟩ := by
  apply stepStar_stepPlus_stepPlus (phases12 (4*k+1) e)
  rcases k with _ | k
  · have h := tail_1_b0 e
    rw [show 6 * 0 + 3 = 3 from by ring, show e + 6 * 0 = e from by ring]
    rw [show 4 * 0 + 1 = 1 from by ring, show e + (4 * 0 + 1) = e + 1 from by ring]; exact h
  · apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*(k+1), 0, 1, e+3*(k+1)+1⟩)
    · have h := big_rounds (k+1) 0 1 (e+3*(k+1)+1)
      rw [show 1 + 4 * (k + 1) = 4 * (k + 1) + 1 from by ring,
          show e + 3 * (k + 1) + 1 + (k + 1) = e + (4 * (k + 1) + 1) from by ring,
          show 0 + 3 * (k + 1) = 3 * (k + 1) from by ring] at h; exact h
    have h := tail_1_bn (3*(k+1)-1) (e+3*(k+1))
    rw [show 3 * (k + 1) - 1 + 1 = 3 * (k + 1) from by omega,
        show e + 3 * (k + 1) + 1 = (e + 3 * (k + 1)) + 1 from by ring,
        show 2 * (3 * (k + 1) - 1) + 5 = 6 * (k + 1) + 3 from by omega,
        show e + 3 * (k + 1) + (3 * (k + 1) - 1) + 1 = e + 6 * (k + 1) from by omega] at h
    exact h

-- Full transition for a=4k+2
theorem trans_r2 (k : ℕ) (e : ℕ) : ⟨4*k+2, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨6*k+4, 0, 0, 0, e+6*k+2⟩ := by
  apply stepStar_stepPlus_stepPlus (phases12 (4*k+2) e)
  rcases k with _ | k
  · rw [show 4 * 0 + 2 = 2 from by ring, show e + (4 * 0 + 2) = e + 2 from by ring,
         show 6 * 0 + 4 = 4 from by ring, show e + 6 * 0 + 2 = e + 2 from by ring]
    have h := tail_2_b0 (e+1)
    rw [show e + 2 = (e + 1) + 1 from by ring,
        show e + 1 + 1 = e + 2 from by ring] at h; exact h
  · apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*(k+1), 0, 2, e+3*(k+1)+2⟩)
    · have h := big_rounds (k+1) 0 2 (e+3*(k+1)+2)
      rw [show 2 + 4 * (k + 1) = 4 * (k + 1) + 2 from by ring,
          show e + 3 * (k + 1) + 2 + (k + 1) = e + (4 * (k + 1) + 2) from by ring,
          show 0 + 3 * (k + 1) = 3 * (k + 1) from by ring] at h; exact h
    have h := tail_2_bn (3*(k+1)-1) (e+3*(k+1)+1)
    rw [show 3 * (k + 1) - 1 + 1 = 3 * (k + 1) from by omega,
        show e + 3 * (k + 1) + 2 = (e + 3 * (k + 1) + 1) + 1 from by ring,
        show 2 * (3 * (k + 1) - 1) + 6 = 6 * (k + 1) + 4 from by omega,
        show e + 3 * (k + 1) + 1 + (3 * (k + 1) - 1) + 2 = e + 6 * (k + 1) + 2 from by omega] at h
    exact h

-- Full transition for a=4k+3
theorem trans_r3 (k : ℕ) (e : ℕ) : ⟨4*k+3, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨6*k+5, 0, 0, 0, e+6*k+4⟩ := by
  apply stepStar_stepPlus_stepPlus (phases12 (4*k+3) e)
  rcases k with _ | k
  · rw [show 4 * 0 + 3 = 3 from by ring, show e + (4 * 0 + 3) = e + 3 from by ring,
         show 6 * 0 + 5 = 5 from by ring, show e + 6 * 0 + 4 = e + 4 from by ring]
    have h := tail_3_b0 (e+2)
    rw [show e + 2 + 1 = e + 3 from by ring,
        show e + 2 + 2 = e + 4 from by ring] at h; exact h
  · apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*(k+1), 0, 3, e+3*(k+1)+3⟩)
    · have h := big_rounds (k+1) 0 3 (e+3*(k+1)+3)
      rw [show 3 + 4 * (k + 1) = 4 * (k + 1) + 3 from by ring,
          show e + 3 * (k + 1) + 3 + (k + 1) = e + (4 * (k + 1) + 3) from by ring,
          show 0 + 3 * (k + 1) = 3 * (k + 1) from by ring] at h; exact h
    have h := tail_3_bn (3*(k+1)-1) (e+3*(k+1)+2)
    rw [show 3 * (k + 1) - 1 + 1 = 3 * (k + 1) from by omega,
        show e + 3 * (k + 1) + 3 = (e + 3 * (k + 1) + 2) + 1 from by ring,
        show 2 * (3 * (k + 1) - 1) + 7 = 6 * (k + 1) + 5 from by omega,
        show e + 3 * (k + 1) + 2 + (3 * (k + 1) - 1) + 3 = e + 6 * (k + 1) + 4 from by omega] at h
    exact h

-- Full transition for a=4(k+1)
theorem trans_r0 (k : ℕ) (e : ℕ) : ⟨4*k+4, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨6*k+8, 0, 0, 0, e+6*k+4⟩ := by
  apply stepStar_stepPlus_stepPlus (phases12 (4*k+4) e)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3*(k+1), 0, 0, e+3*(k+1)⟩)
  · have h := big_rounds (k+1) 0 0 (e+3*(k+1))
    rw [show 0 + 4 * (k + 1) = 4 * k + 4 from by ring,
        show e + 3 * (k + 1) + (k + 1) = e + (4 * k + 4) from by ring,
        show 0 + 3 * (k + 1) = 3 * (k + 1) from by ring] at h; exact h
  have h := tail_0 (3*(k+1)-1) (e+3*(k+1)-1)
  rw [show 3 * (k + 1) - 1 + 1 = 3 * (k + 1) from by omega,
      show e + 3 * (k + 1) - 1 + 1 = e + 3 * (k + 1) from by omega,
      show 2 * (3 * (k + 1) - 1) + 4 = 6 * k + 8 from by omega,
      show e + 3 * (k + 1) - 1 + (3 * (k + 1) - 1) = e + 6 * k + 4 from by omega] at h
  exact h

-- Combined transition
theorem main_trans : ∀ a e, a ≥ 1 → ∃ a' e', a' ≥ 1 ∧ ⟨a, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨a', 0, 0, 0, e'⟩ := by
  intro a e ha
  have hmod := Nat.div_add_mod a 4
  set q := a / 4
  set r := a % 4
  have hr : r < 4 := Nat.mod_lt a (by omega)
  interval_cases r
  · rcases q with _ | k
    · omega
    rw [show a = 4 * k + 4 from by omega]
    exact ⟨6*k+8, e+6*k+4, by omega, trans_r0 k e⟩
  · rw [show a = 4 * q + 1 from by omega]
    exact ⟨6*q+3, e+6*q, by omega, trans_r1 q e⟩
  · rw [show a = 4 * q + 2 from by omega]
    exact ⟨6*q+4, e+6*q+2, by omega, trans_r2 q e⟩
  · rw [show a = 4 * q + 3 from by omega]
    exact ⟨6*q+5, e+6*q+4, by omega, trans_r3 q e⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a, 0, 0, 0, e⟩ ∧ a ≥ 1)
  · intro c ⟨a, e, hq, ha⟩
    subst hq
    obtain ⟨a', e', ha', htrans⟩ := main_trans a e ha
    exact ⟨⟨a', 0, 0, 0, e'⟩, ⟨a', e', rfl, ha'⟩, htrans⟩
  · exact ⟨1, 0, rfl, by omega⟩

end Sz21_140_unofficial_123
