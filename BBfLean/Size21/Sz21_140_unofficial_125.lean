import BBfLean.FM
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# sz21_140_unofficial #125: [9/10, 22/21, 343/2, 5/11, 3/7]

Vector representation:
```
-1  2 -1  0  0
 1 -1  0 -1  1
-1  0  0  3  0
 0  0  1  0 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_125

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d+1, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+3, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 chain: e → c
theorem r4_chain : ∀ k, ∀ c d, ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k h <;> intro c d
  · exists 0
  rw [show (0 : ℕ) = 0 from rfl]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3 chain: a → d
theorem r3_chain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * k, e⟩ := by
  intro k; induction' k with k h <;> intro d e
  · exists 0
  rw [show k + 1 = k + 1 from rfl]
  step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R1+R2 interleave
theorem r1r2_chain : ∀ k, ∀ b c d e, ⟨1, b, c + k, d + k, e⟩ [fm]⊢* ⟨1, b + k, c, d, e + k⟩ := by
  intro k; induction' k with k h <;> intro b c d e
  · exists 0
  rw [show c + (k + 1) = (c + k) + 1 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  step fm
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R3+R2R2R2 drain rounds
theorem drain_rounds : ∀ k, ∀ a b e, ⟨a + 1, b + 3 * k, 0, 0, e⟩ [fm]⊢* ⟨a + 1 + 2 * k, b, 0, 0, e + 3 * k⟩ := by
  intro k; induction' k with k h <;> intro a b e
  · exists 0
  rw [show b + 3 * (k + 1) = b + 3 * k + 1 + 1 + 1 from by ring]
  step fm
  rw [show b + 3 * k + 1 + 1 + 1 = (b + 3 * k + 1 + 1) + 1 from by ring]
  step fm
  rw [show (b + 3 * k + 1 + 1) = (b + 3 * k + 1) + 1 from by ring]
  step fm
  rw [show (b + 3 * k + 1) = (b + 3 * k) + 1 from by ring]
  step fm
  rw [show a + 1 + 1 + 1 = (a + 2) + 1 from by ring]
  apply stepStar_trans (h (a + 2) b (e + 3))
  ring_nf; finish

-- Tail: drain with b mod 3 = 0
theorem tail_0 : ∀ a e, ⟨a, 0, 0, 0, e⟩ [fm]⊢* ⟨0, 0, e, 3 * a, 0⟩ := by
  intro a e
  have h1 := r3_chain a 0 e
  rw [show 0 + 3 * a = 3 * a from by ring] at h1
  have h2 := r4_chain e 0 (3 * a)
  rw [show 0 + e = e from by ring] at h2
  exact stepStar_trans h1 h2

-- Tail: drain with b mod 3 = 1
theorem tail_1 : ∀ a e, ⟨a + 1, 1, 0, 0, e⟩ [fm]⊢* ⟨0, 0, e + 1, 3 * a + 5, 0⟩ := by
  intro a e
  step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  have h1 := r3_chain (a + 1) 2 (e + 1)
  rw [show 2 + 3 * (a + 1) = 3 * a + 5 from by ring] at h1
  have h2 := r4_chain (e + 1) 0 (3 * a + 5)
  rw [show 0 + (e + 1) = e + 1 from by ring] at h2
  exact stepStar_trans h1 h2

-- Tail: drain with b mod 3 = 2
theorem tail_2 : ∀ a e, ⟨a + 1, 2, 0, 0, e⟩ [fm]⊢* ⟨0, 0, e + 2, 3 * a + 7, 0⟩ := by
  intro a e
  step fm
  rw [show (3 : ℕ) = 2 + 1 from by ring]
  step fm
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  step fm
  rw [show a + 1 + 1 = a + 2 from by ring]
  have h1 := r3_chain (a + 2) 1 (e + 2)
  rw [show 1 + 3 * (a + 2) = 3 * a + 7 from by ring] at h1
  have h2 := r4_chain (e + 2) 0 (3 * a + 7)
  rw [show 0 + (e + 2) = e + 2 from by ring] at h2
  exact stepStar_trans h1 h2

-- Drain + tail, case b mod 3 = 0
theorem drain_tail_0 : ∀ k E, ⟨(2 : ℕ), 3 * k, 0, 0, E⟩ [fm]⊢* ⟨0, 0, E + 3 * k, 6 * k + 6, 0⟩ := by
  intro k E
  rw [show (2 : ℕ) = 1 + 1 from by ring, show 3 * k = 0 + 3 * k from by ring]
  refine stepStar_trans (drain_rounds k 1 0 E) ?_
  refine stepStar_trans (tail_0 (1 + 1 + 2 * k) (E + 3 * k)) ?_
  rw [show 3 * (1 + 1 + 2 * k) = 6 * k + 6 from by ring,
      show E + (0 + 3 * k) = E + 3 * k from by ring]; finish

-- Drain + tail, case b mod 3 = 1
theorem drain_tail_1 : ∀ k E, ⟨(2 : ℕ), 3 * k + 1, 0, 0, E⟩ [fm]⊢* ⟨0, 0, E + 3 * k + 1, 6 * k + 8, 0⟩ := by
  intro k E
  rw [show (2 : ℕ) = 1 + 1 from by ring, show 3 * k + 1 = 1 + 3 * k from by ring]
  refine stepStar_trans (drain_rounds k 1 1 E) ?_
  rw [show 1 + 1 + 2 * k = (2 * k + 1) + 1 from by ring]
  refine stepStar_trans (tail_1 (2 * k + 1) (E + 3 * k)) ?_
  rw [show 3 * (2 * k + 1) + 5 = 6 * k + 8 from by ring]; finish

-- Drain + tail, case b mod 3 = 2
theorem drain_tail_2 : ∀ k E, ⟨(2 : ℕ), 3 * k + 2, 0, 0, E⟩ [fm]⊢* ⟨0, 0, E + 3 * k + 2, 6 * k + 10, 0⟩ := by
  intro k E
  rw [show (2 : ℕ) = 1 + 1 from by ring, show 3 * k + 2 = 2 + 3 * k from by ring]
  refine stepStar_trans (drain_rounds k 1 2 E) ?_
  rw [show 1 + 1 + 2 * k = (2 * k + 1) + 1 from by ring]
  refine stepStar_trans (tail_2 (2 * k + 1) (E + 3 * k)) ?_
  rw [show 3 * (2 * k + 1) + 7 = 6 * k + 10 from by ring]; finish

-- Base case
theorem main_trans_base : ⟨0, 0, 0, 3, 0⟩ [fm]⊢⁺ ⟨0, 0, 1, 4, 0⟩ := by
  execute fm 4

-- Main transition
theorem main_trans : ∀ c, ⟨(0 : ℕ), 0, c, c + 3, 0⟩ [fm]⊢⁺ ⟨0, 0, 2 * c + 1, 2 * c + 4, 0⟩ := by
  intro c
  rcases c with _ | c
  · exact main_trans_base
  · apply step_stepStar_stepPlus
      (show fm ⟨0, 0, c + 1, (c + 3) + 1, 0⟩ = some ⟨0, 1, c + 1, c + 3, 0⟩ by simp [fm])
    -- R2
    apply stepStar_trans (step_stepStar
      (show fm ⟨0, 0 + 1, c + 1, (c + 2) + 1, 0⟩ = some ⟨1, 0, c + 1, c + 2, 1⟩ by simp [fm]))
    -- R1R2 chain
    apply stepStar_trans (c₂ := ⟨1, c + 1, 0, 1, c + 2⟩)
    · have h := r1r2_chain (c + 1) 0 0 1 1
      simp only [Nat.zero_add] at h
      rw [show 1 + (c + 1) = c + 2 from by ring] at h
      exact h
    -- R2
    apply stepStar_trans (step_stepStar
      (show fm ⟨1, c + 1, 0, 0 + 1, c + 2⟩ = some ⟨2, c, 0, 0, c + 3⟩ by simp [fm]))
    -- Split on c mod 3
    have hmod : c % 3 < 3 := Nat.mod_lt _ (by omega)
    have hdiv : c = 3 * (c / 3) + c % 3 := (Nat.div_add_mod c 3).symm
    interval_cases (c % 3)
    · have hc : c = 3 * (c / 3) := by omega
      rw [hc]
      refine stepStar_trans (drain_tail_0 (c / 3) (3 * (c / 3) + 3)) ?_
      rw [hc]; ring_nf; finish
    · have hc : c = 3 * (c / 3) + 1 := by omega
      rw [hc]
      refine stepStar_trans (drain_tail_1 (c / 3) (3 * (c / 3) + 1 + 3)) ?_
      rw [hc]; ring_nf; finish
    · have hc : c = 3 * (c / 3) + 2 := by omega
      rw [hc]
      refine stepStar_trans (drain_tail_2 (c / 3) (3 * (c / 3) + 2 + 3)) ?_
      rw [hc]; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 3, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun c ↦ ⟨0, 0, c, c + 3, 0⟩) 0
  intro c; exact ⟨2 * c + 1, main_trans c⟩
