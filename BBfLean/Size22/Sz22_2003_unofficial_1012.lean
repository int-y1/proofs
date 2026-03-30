import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1012: [4/15, 9/14, 55/2, 7/5, 50/11]

Vector representation:
```
 2 -1 -1  0  0
-1  2  0 -1  0
-1  0  1  0  1
 0  0 -1  1  0
 1  0  2  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1012

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

-- R3 chain: drain a, build c and e
theorem r3_chain : ∀ k, ∀ a c e,
    ⟨a + k, (0 : ℕ), c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 1))
    ring_nf; finish

-- R4 chain: drain c, build d
theorem r4_chain : ∀ k, ∀ c d e,
    ⟨(0 : ℕ), 0, c + k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih c (d + 1) e)
    ring_nf; finish

-- R2 chain: drain a and d, build b
theorem r2_chain : ∀ k, ∀ a b d e,
    ⟨a + k, b, (0 : ℕ), d + k, e⟩ [fm]⊢* ⟨a, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a b d e
  · simp; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (b + 2) d e)
    ring_nf; finish

-- R5,R1 chain: drain b, build a and e
theorem r5r1_chain : ∀ k, ∀ a b e,
    ⟨a + 1, b + k, (0 : ℕ), 0, e⟩ [fm]⊢* ⟨a + k + 1, b, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · simp; exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) b (e + 1))
    ring_nf; finish

-- Phase 1+2: R3 chain then R4 chain
theorem phase12 : ∀ a e,
    ⟨a, (0 : ℕ), 0, 0, e⟩ [fm]⊢* ⟨0, 0, 0, a, e + a⟩ := by
  intro a e
  have h1 := r3_chain a 0 0 e
  rw [show 0 + a = a from by ring] at h1
  apply stepStar_trans h1
  have h2 := r4_chain a 0 0 (e + a)
  rw [show 0 + a = a from by ring] at h2
  exact h2

-- Drain opening: R5,R1,R1,R2 = 4 steps
theorem drain_open : ∀ d e,
    ⟨(0 : ℕ), 0, 0, d + 1, e + 1⟩ [fm]⊢* ⟨4, 0, 0, d, e⟩ := by
  intro d e; step fm; step fm; step fm; step fm; finish

-- Drain opening + 4 R2 steps
theorem drain_open_r2x4 : ∀ d e,
    ⟨(0 : ℕ), 0, 0, d + 5, e + 1⟩ [fm]⊢* ⟨0, 8, 0, d, e⟩ := by
  intro d e
  have h1 := drain_open (d + 4) e
  rw [show (d + 4) + 1 = d + 5 from by ring] at h1
  apply stepStar_trans h1
  have h2 := r2_chain 4 0 0 d e
  rw [show 0 + 4 = 4 from by ring, show 0 + 2 * 4 = 8 from by ring] at h2
  exact h2

-- One drain round: R5,R1,R1 then R2x5
theorem drain_round : ∀ b d e,
    ⟨(0 : ℕ), b + 8, 0, d + 5, e + 1⟩ [fm]⊢* ⟨0, b + 16, 0, d, e⟩ := by
  intro b d e
  rw [show d + 5 = (d + 4) + 1 from by ring]
  step fm; step fm; step fm
  rw [show d + 4 + 1 = d + 5 from by ring]
  have h := r2_chain 5 0 (b + 6) d e
  rw [show 0 + 5 = 5 from by ring,
      show (b + 6) + 2 * 5 = b + 16 from by ring] at h
  exact h

-- Multiple drain rounds
theorem drain_rounds : ∀ n, ∀ b d e,
    ⟨(0 : ℕ), b + 8, 0, d + 5 * n, e + n⟩ [fm]⊢* ⟨0, b + 8 + 8 * n, 0, d, e⟩ := by
  intro n; induction' n with n ih <;> intro b d e
  · simp; exists 0
  · have h1 := drain_round b (d + 5 * n) (e + n)
    rw [show d + 5 * n + 5 = d + 5 * (n + 1) from by ring,
        show e + n + 1 = e + (n + 1) from by ring] at h1
    apply stepStar_trans h1
    have h2 := ih (b + 8) d e
    rw [show (b + 8) + 8 = b + 16 from by ring,
        show (b + 8) + 8 + 8 * n = b + 8 + 8 * (n + 1) from by ring] at h2
    exact h2

-- a0 fixup: R5,R1,R1 then R5R1 chain
theorem a0_fixup : ∀ b e,
    ⟨(0 : ℕ), b + 2, 0, 0, e + 1⟩ [fm]⊢* ⟨b + 5, 0, 0, 0, e + b⟩ := by
  intro b e
  step fm; step fm; step fm
  have h := r5r1_chain b 4 0 e
  rw [show 4 + 1 = 5 from by ring,
      show 0 + b = b from by ring,
      show 4 + b + 1 = b + 5 from by ring] at h
  exact h

-- Drain round opening: R5,R1,R1 (keeps d)
theorem drain_round_open : ∀ b d e,
    ⟨(0 : ℕ), b + 2, 0, d + 1, e + 1⟩ [fm]⊢* ⟨5, b, 0, d + 1, e⟩ := by
  intro b d e; step fm; step fm; step fm; finish

-- phase12 as stepPlus
theorem phase12_plus : ∀ a e,
    ⟨a + 1, (0 : ℕ), 0, 0, e⟩ [fm]⊢⁺ ⟨0, 0, 0, a + 1, e + a + 1⟩ := by
  intro a e
  have h := phase12 (a + 1) e
  rw [show e + (a + 1) = e + a + 1 from by ring] at h
  exact stepStar_stepPlus h (by
    intro hc
    have := congr_arg (fun q : Q => q.1) hc
    simp at this)

-- Tail: R2 chain then R5R1 chain, for residual r+1
theorem tail_0 : ∀ n e,
    ⟨(5 : ℕ), 8 * n + 6, 0, 1, e⟩ [fm]⊢* ⟨8 * n + 12, 0, 0, 0, e + 8 * n + 8⟩ := by
  intro n e
  have h1 := r2_chain 1 4 (8 * n + 6) 0 e
  rw [show 4 + 1 = 5 from by ring, show 0 + 1 = 1 from by ring,
      show (8 * n + 6) + 2 * 1 = 8 * n + 8 from by ring] at h1
  apply stepStar_trans h1
  have h2 := r5r1_chain (8 * n + 8) 3 0 e
  rw [show 3 + 1 = 4 from by ring, show 0 + (8 * n + 8) = 8 * n + 8 from by ring,
      show 3 + (8 * n + 8) + 1 = 8 * n + 12 from by ring,
      show e + (8 * n + 8) = e + 8 * n + 8 from by ring] at h2
  exact h2

theorem tail_1 : ∀ n e,
    ⟨(5 : ℕ), 8 * n + 6, 0, 2, e⟩ [fm]⊢* ⟨8 * n + 13, 0, 0, 0, e + 8 * n + 10⟩ := by
  intro n e
  have h1 := r2_chain 2 3 (8 * n + 6) 0 e
  rw [show 3 + 2 = 5 from by ring, show 0 + 2 = 2 from by ring,
      show (8 * n + 6) + 2 * 2 = 8 * n + 10 from by ring] at h1
  apply stepStar_trans h1
  have h2 := r5r1_chain (8 * n + 10) 2 0 e
  rw [show 2 + 1 = 3 from by ring, show 0 + (8 * n + 10) = 8 * n + 10 from by ring,
      show 2 + (8 * n + 10) + 1 = 8 * n + 13 from by ring,
      show e + (8 * n + 10) = e + 8 * n + 10 from by ring] at h2
  exact h2

theorem tail_2 : ∀ n e,
    ⟨(5 : ℕ), 8 * n + 6, 0, 3, e⟩ [fm]⊢* ⟨8 * n + 14, 0, 0, 0, e + 8 * n + 12⟩ := by
  intro n e
  have h1 := r2_chain 3 2 (8 * n + 6) 0 e
  rw [show 2 + 3 = 5 from by ring, show 0 + 3 = 3 from by ring,
      show (8 * n + 6) + 2 * 3 = 8 * n + 12 from by ring] at h1
  apply stepStar_trans h1
  have h2 := r5r1_chain (8 * n + 12) 1 0 e
  rw [show 1 + 1 = 2 from by ring, show 0 + (8 * n + 12) = 8 * n + 12 from by ring,
      show 1 + (8 * n + 12) + 1 = 8 * n + 14 from by ring,
      show e + (8 * n + 12) = e + 8 * n + 12 from by ring] at h2
  exact h2

theorem tail_3 : ∀ n e,
    ⟨(5 : ℕ), 8 * n + 6, 0, 4, e⟩ [fm]⊢* ⟨8 * n + 15, 0, 0, 0, e + 8 * n + 14⟩ := by
  intro n e
  have h1 := r2_chain 4 1 (8 * n + 6) 0 e
  rw [show 1 + 4 = 5 from by ring, show 0 + 4 = 4 from by ring,
      show (8 * n + 6) + 2 * 4 = 8 * n + 14 from by ring] at h1
  apply stepStar_trans h1
  have h2 := r5r1_chain (8 * n + 14) 0 0 e
  rw [show 0 + 1 = 1 from by ring, show 0 + (8 * n + 14) = 8 * n + 14 from by ring,
      show 8 * n + 14 + 1 = 8 * n + 15 from by ring,
      show e + (8 * n + 14) = e + 8 * n + 14 from by ring] at h2
  exact h2

-- Small cases D=1..4
theorem trans_D1 : ∀ e, ⟨(1 : ℕ), 0, 0, 0, e⟩ [fm]⊢⁺ ⟨4, 0, 0, 0, e⟩ := by
  intro e
  apply stepPlus_stepStar_stepPlus (phase12_plus 0 e)
  rw [show e + 0 + 1 = e + 1 from by ring, show 0 + 1 = 0 + 1 from rfl]
  exact drain_open 0 e

theorem trans_D2 : ∀ e, ⟨(2 : ℕ), 0, 0, 0, e⟩ [fm]⊢⁺ ⟨5, 0, 0, 0, e + 3⟩ := by
  intro e
  apply stepPlus_stepStar_stepPlus (phase12_plus 1 e)
  rw [show e + 1 + 1 = e + 2 from by ring, show 1 + 1 = 1 + 1 from rfl]
  apply stepStar_trans (drain_open 1 (e + 1))
  have h := r2_chain 1 3 0 0 (e + 1)
  rw [show 3 + 1 = 4 from by ring, show 0 + 1 = 1 from by ring,
      show 0 + 2 * 1 = 2 from by ring] at h
  apply stepStar_trans h
  have h2 := r5r1_chain 2 2 0 (e + 1)
  rw [show 2 + 1 = 3 from by ring, show 0 + 2 = 2 from by ring,
      show 2 + 2 + 1 = 5 from by ring, show (e + 1) + 2 = e + 3 from by ring] at h2
  exact h2

theorem trans_D3 : ∀ e, ⟨(3 : ℕ), 0, 0, 0, e⟩ [fm]⊢⁺ ⟨6, 0, 0, 0, e + 6⟩ := by
  intro e
  apply stepPlus_stepStar_stepPlus (phase12_plus 2 e)
  rw [show e + 2 + 1 = e + 3 from by ring, show 2 + 1 = 2 + 1 from rfl]
  apply stepStar_trans (drain_open 2 (e + 2))
  apply stepStar_trans (r2_chain 2 2 0 0 (e + 2))
  have h2 := r5r1_chain 4 1 0 (e + 2)
  rw [show 1 + 1 = 2 from by ring, show 0 + 4 = 4 from by ring,
      show 1 + 4 + 1 = 6 from by ring, show (e + 2) + 4 = e + 6 from by ring] at h2
  exact h2

theorem trans_D4 : ∀ e, ⟨(4 : ℕ), 0, 0, 0, e⟩ [fm]⊢⁺ ⟨7, 0, 0, 0, e + 9⟩ := by
  intro e
  apply stepPlus_stepStar_stepPlus (phase12_plus 3 e)
  rw [show e + 3 + 1 = e + 4 from by ring, show 3 + 1 = 3 + 1 from rfl]
  apply stepStar_trans (drain_open 3 (e + 3))
  have h := r2_chain 3 1 0 0 (e + 3)
  rw [show 1 + 3 = 4 from by ring, show 0 + 3 = 3 from by ring,
      show 0 + 2 * 3 = 6 from by ring] at h
  apply stepStar_trans h
  have h2 := r5r1_chain 6 0 0 (e + 3)
  rw [show 0 + 1 = 1 from by ring, show 0 + 6 = 6 from by ring,
      show 0 + 6 + 1 = 7 from by ring, show (e + 3) + 6 = e + 9 from by ring] at h2
  exact h2

-- D = 5n+5 (n >= 0): only drain rounds + a0_fixup
theorem trans_big_r0 : ∀ n e,
    ⟨5 * n + 5, (0 : ℕ), 0, 0, e⟩ [fm]⊢⁺ ⟨8 * n + 11, 0, 0, 0, e + 12 * n + 9⟩ := by
  intro n e
  have hp := phase12_plus (5 * n + 4) e
  rw [show 5 * n + 4 + 1 = 5 * n + 5 from by ring,
      show e + (5 * n + 4) + 1 = e + 5 * n + 5 from by ring] at hp
  apply stepPlus_stepStar_stepPlus hp
  have h1 := drain_open_r2x4 (5 * n) (e + 5 * n + 4)
  rw [show (e + 5 * n + 4) + 1 = e + 5 * n + 5 from by ring] at h1
  apply stepStar_trans h1
  have h2 := drain_rounds n 0 0 (e + 4 * n + 4)
  rw [show 0 + 8 = 8 from by ring,
      show 0 + 5 * n = 5 * n from by ring,
      show (e + 4 * n + 4) + n = e + 5 * n + 4 from by ring,
      show 0 + 8 + 8 * n = 8 + 8 * n from by ring] at h2
  apply stepStar_trans h2
  have h3 := a0_fixup (8 * n + 6) (e + 4 * n + 3)
  rw [show (8 * n + 6) + 2 = 8 + 8 * n from by ring,
      show (e + 4 * n + 3) + 1 = e + 4 * n + 4 from by ring,
      show (8 * n + 6) + 5 = 8 * n + 11 from by ring,
      show (e + 4 * n + 3) + (8 * n + 6) = e + 12 * n + 9 from by ring] at h3
  exact h3

-- D = 5n+6 (n >= 0): drain_rounds(n) then drain_round_open then tail_0
theorem trans_big_r1 : ∀ n e,
    ⟨5 * n + 6, (0 : ℕ), 0, 0, e⟩ [fm]⊢⁺ ⟨8 * n + 12, 0, 0, 0, e + 12 * n + 12⟩ := by
  intro n e
  have hp := phase12_plus (5 * n + 5) e
  rw [show 5 * n + 5 + 1 = 5 * n + 6 from by ring,
      show e + (5 * n + 5) + 1 = e + 5 * n + 6 from by ring] at hp
  apply stepPlus_stepStar_stepPlus hp
  have h1 := drain_open_r2x4 (5 * n + 1) (e + 5 * n + 5)
  rw [show (5 * n + 1) + 5 = 5 * n + 6 from by ring,
      show (e + 5 * n + 5) + 1 = e + 5 * n + 6 from by ring] at h1
  apply stepStar_trans h1
  have h2 := drain_rounds n 0 1 (e + 4 * n + 5)
  rw [show 0 + 8 = 8 from by ring,
      show 1 + 5 * n = 5 * n + 1 from by ring,
      show (e + 4 * n + 5) + n = e + 5 * n + 5 from by ring,
      show 0 + 8 + 8 * n = 8 + 8 * n from by ring] at h2
  apply stepStar_trans h2
  have h3 := drain_round_open (8 * n + 6) 0 (e + 4 * n + 4)
  rw [show (8 * n + 6) + 2 = 8 + 8 * n from by ring,
      show 0 + 1 = 1 from by ring,
      show (e + 4 * n + 4) + 1 = e + 4 * n + 5 from by ring] at h3
  apply stepStar_trans h3
  have h4 := tail_0 n (e + 4 * n + 4)
  rw [show (e + 4 * n + 4) + 8 * n + 8 = e + 12 * n + 12 from by ring] at h4
  exact h4

-- D = 5n+7 (n >= 0)
theorem trans_big_r2 : ∀ n e,
    ⟨5 * n + 7, (0 : ℕ), 0, 0, e⟩ [fm]⊢⁺ ⟨8 * n + 13, 0, 0, 0, e + 12 * n + 15⟩ := by
  intro n e
  have hp := phase12_plus (5 * n + 6) e
  rw [show 5 * n + 6 + 1 = 5 * n + 7 from by ring,
      show e + (5 * n + 6) + 1 = e + 5 * n + 7 from by ring] at hp
  apply stepPlus_stepStar_stepPlus hp
  have h1 := drain_open_r2x4 (5 * n + 2) (e + 5 * n + 6)
  rw [show (5 * n + 2) + 5 = 5 * n + 7 from by ring,
      show (e + 5 * n + 6) + 1 = e + 5 * n + 7 from by ring] at h1
  apply stepStar_trans h1
  have h2 := drain_rounds n 0 2 (e + 4 * n + 6)
  rw [show 0 + 8 = 8 from by ring,
      show 2 + 5 * n = 5 * n + 2 from by ring,
      show (e + 4 * n + 6) + n = e + 5 * n + 6 from by ring,
      show 0 + 8 + 8 * n = 8 + 8 * n from by ring] at h2
  apply stepStar_trans h2
  have h3 := drain_round_open (8 * n + 6) 1 (e + 4 * n + 5)
  rw [show (8 * n + 6) + 2 = 8 + 8 * n from by ring,
      show 1 + 1 = 2 from by ring,
      show (e + 4 * n + 5) + 1 = e + 4 * n + 6 from by ring] at h3
  apply stepStar_trans h3
  have h4 := tail_1 n (e + 4 * n + 5)
  rw [show (e + 4 * n + 5) + 8 * n + 10 = e + 12 * n + 15 from by ring] at h4
  exact h4

-- D = 5n+8 (n >= 0)
theorem trans_big_r3 : ∀ n e,
    ⟨5 * n + 8, (0 : ℕ), 0, 0, e⟩ [fm]⊢⁺ ⟨8 * n + 14, 0, 0, 0, e + 12 * n + 18⟩ := by
  intro n e
  have hp := phase12_plus (5 * n + 7) e
  rw [show 5 * n + 7 + 1 = 5 * n + 8 from by ring,
      show e + (5 * n + 7) + 1 = e + 5 * n + 8 from by ring] at hp
  apply stepPlus_stepStar_stepPlus hp
  have h1 := drain_open_r2x4 (5 * n + 3) (e + 5 * n + 7)
  rw [show (5 * n + 3) + 5 = 5 * n + 8 from by ring,
      show (e + 5 * n + 7) + 1 = e + 5 * n + 8 from by ring] at h1
  apply stepStar_trans h1
  have h2 := drain_rounds n 0 3 (e + 4 * n + 7)
  rw [show 0 + 8 = 8 from by ring,
      show 3 + 5 * n = 5 * n + 3 from by ring,
      show (e + 4 * n + 7) + n = e + 5 * n + 7 from by ring,
      show 0 + 8 + 8 * n = 8 + 8 * n from by ring] at h2
  apply stepStar_trans h2
  have h3 := drain_round_open (8 * n + 6) 2 (e + 4 * n + 6)
  rw [show (8 * n + 6) + 2 = 8 + 8 * n from by ring,
      show 2 + 1 = 3 from by ring,
      show (e + 4 * n + 6) + 1 = e + 4 * n + 7 from by ring] at h3
  apply stepStar_trans h3
  have h4 := tail_2 n (e + 4 * n + 6)
  rw [show (e + 4 * n + 6) + 8 * n + 12 = e + 12 * n + 18 from by ring] at h4
  exact h4

-- D = 5n+9 (n >= 0)
theorem trans_big_r4 : ∀ n e,
    ⟨5 * n + 9, (0 : ℕ), 0, 0, e⟩ [fm]⊢⁺ ⟨8 * n + 15, 0, 0, 0, e + 12 * n + 21⟩ := by
  intro n e
  have hp := phase12_plus (5 * n + 8) e
  rw [show 5 * n + 8 + 1 = 5 * n + 9 from by ring,
      show e + (5 * n + 8) + 1 = e + 5 * n + 9 from by ring] at hp
  apply stepPlus_stepStar_stepPlus hp
  have h1 := drain_open_r2x4 (5 * n + 4) (e + 5 * n + 8)
  rw [show (5 * n + 4) + 5 = 5 * n + 9 from by ring,
      show (e + 5 * n + 8) + 1 = e + 5 * n + 9 from by ring] at h1
  apply stepStar_trans h1
  have h2 := drain_rounds n 0 4 (e + 4 * n + 8)
  rw [show 0 + 8 = 8 from by ring,
      show 4 + 5 * n = 5 * n + 4 from by ring,
      show (e + 4 * n + 8) + n = e + 5 * n + 8 from by ring,
      show 0 + 8 + 8 * n = 8 + 8 * n from by ring] at h2
  apply stepStar_trans h2
  have h3 := drain_round_open (8 * n + 6) 3 (e + 4 * n + 7)
  rw [show (8 * n + 6) + 2 = 8 + 8 * n from by ring,
      show 3 + 1 = 4 from by ring,
      show (e + 4 * n + 7) + 1 = e + 4 * n + 8 from by ring] at h3
  apply stepStar_trans h3
  have h4 := tail_3 n (e + 4 * n + 7)
  rw [show (e + 4 * n + 7) + 8 * n + 14 = e + 12 * n + 21 from by ring] at h4
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by finish)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩)
  · intro q ⟨a, e, hq⟩; subst hq
    rcases a with _ | _ | _ | _ | a'
    · exact ⟨_, ⟨3, e, rfl⟩, trans_D1 e⟩
    · exact ⟨_, ⟨4, e + 3, rfl⟩, trans_D2 e⟩
    · exact ⟨_, ⟨5, e + 6, rfl⟩, trans_D3 e⟩
    · exact ⟨_, ⟨6, e + 9, rfl⟩, trans_D4 e⟩
    · obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 5 ∧ a' = 5 * q + s := by
        exact ⟨a' / 5, a' % 5, Nat.mod_lt a' (by omega), by omega⟩
      rcases s with _ | _ | _ | _ | _ | s
      · exact ⟨⟨8 * q + 11, 0, 0, 0, e + 12 * q + 9⟩, ⟨8 * q + 10, e + 12 * q + 9, rfl⟩,
          by convert trans_big_r0 q e using 2⟩
      · exact ⟨⟨8 * q + 12, 0, 0, 0, e + 12 * q + 12⟩, ⟨8 * q + 11, e + 12 * q + 12, rfl⟩,
          by convert trans_big_r1 q e using 2⟩
      · exact ⟨⟨8 * q + 13, 0, 0, 0, e + 12 * q + 15⟩, ⟨8 * q + 12, e + 12 * q + 15, rfl⟩,
          by convert trans_big_r2 q e using 2⟩
      · exact ⟨⟨8 * q + 14, 0, 0, 0, e + 12 * q + 18⟩, ⟨8 * q + 13, e + 12 * q + 18, rfl⟩,
          by convert trans_big_r3 q e using 2⟩
      · exact ⟨⟨8 * q + 15, 0, 0, 0, e + 12 * q + 21⟩, ⟨8 * q + 14, e + 12 * q + 21, rfl⟩,
          by convert trans_big_r4 q e using 2⟩
      · omega
  · exact ⟨0, 0, rfl⟩

end Sz22_2003_unofficial_1012
