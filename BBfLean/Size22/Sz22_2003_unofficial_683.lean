import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #683: [35/6, 4/385, 605/2, 3/5, 2/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1 -1 -1
-1  0  1  0  2
 0  1 -1  0  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_683

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d+1, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R3 repeated: (a+k, 0, c, 0, e) →* (a, 0, c+k, 0, e+2*k)
theorem r3_chain : ∀ k, ∀ a c e, ⟨a + k, 0, c, 0, e⟩ [fm]⊢* ⟨a, 0, c + k, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) (e + 2))
    ring_nf; finish

-- R4 repeated: (0, b, c+k, 0, e) →* (0, b+k, c, 0, e)
theorem r4_chain : ∀ k, ∀ b c e, ⟨0, b, c + k, 0, e⟩ [fm]⊢* ⟨0, b + k, c, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) c e)
    ring_nf; finish

-- R2 repeated: (a, 0, k, k, e+k) →* (a+2*k, 0, 0, 0, e)
theorem r2_chain : ∀ k, ∀ a e, ⟨a, 0, k, k, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl, show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) e)
    ring_nf; finish

-- R3 then R4 combined: (k, 0, 0, 0, e) →* (0, k, 0, 0, e+2*k)
theorem r3r4_chain : ∀ k, ∀ e, ⟨k, 0, 0, 0, e⟩ [fm]⊢* ⟨0, k, 0, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans
    · show ⟨k, 0, 1, 0, e + 2⟩ [fm]⊢* ⟨0, 0, 1 + k, 0, e + 2 + 2 * k⟩
      have := r3_chain k 0 1 (e + 2)
      simp only [Nat.zero_add] at this
      exact this
    apply stepStar_trans
    · show ⟨0, 0, 1 + k, 0, e + 2 + 2 * k⟩ [fm]⊢* ⟨0, 1 + k, 0, 0, e + 2 + 2 * k⟩
      have := r4_chain (1 + k) 0 0 (e + 2 + 2 * k)
      simp only [Nat.zero_add] at this
      exact this
    ring_nf; finish

-- Inner drain: (2, b, c, c, e+2*b+c) →* (b+2+2*c, 0, 0, 0, e+b)
-- Strong induction on b. Each step of b reduces by 2, increasing c by 1.
theorem inner_drain : ∀ b, ∀ c e, ⟨2, b, c, c, e + 2 * b + c⟩ [fm]⊢* ⟨b + 2 + 2 * c, 0, 0, 0, e + b⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih
  intro c e
  rcases b with _ | _ | b
  · rw [show e + 2 * 0 + c = e + c from by ring,
        show (0 : ℕ) + 2 + 2 * c = 2 + 2 * c from by ring,
        show e + 0 = e from by ring]
    exact r2_chain c 2 e
  · rw [show e + 2 * 1 + c = (e + c + 1) + 1 from by ring]
    step fm
    rw [show (1 : ℕ) + 2 + 2 * c = 1 + 2 * (c + 1) from by ring,
        show e + 1 = e + 1 from rfl,
        show e + c + 1 = (e + 1) + c from by ring]
    exact r2_chain (c + 1) 1 (e + 1)
  · rw [show e + 2 * (b + 2) + c = (e + 2 * b + c + 3) + 1 from by ring]
    step fm; step fm; step fm
    rw [show e + 2 * b + c + 3 = (e + 2) + 2 * b + (c + 1) from by ring,
        show (b + 1 + 1) + 2 + 2 * c = b + 2 + 2 * (c + 1) from by ring,
        show e + (b + 1 + 1) = (e + 2) + b from by ring]
    exact ih b (by omega) (c + 1) (e + 2)

-- Main transition: (n+1, 0, 0, 0, e) →⁺ (n+2, 0, 0, 0, e+n)
-- Phases: R3 chain, R4 chain, R5, R1, R2, inner drain.
theorem main_trans : ∀ n e, ⟨n + 1, 0, 0, 0, e⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, e + n⟩ := by
  intro n e
  apply stepStar_stepPlus_stepPlus (r3r4_chain (n + 1) e)
  rw [show e + 2 * (n + 1) = (e + 2 * n + 1) + 1 from by ring]
  step fm; step fm
  rw [show e + 2 * n + 1 = (e + 2 * n) + 1 from by ring]
  step fm
  rw [show e + 2 * n = e + 2 * n + 0 from by ring,
      show n + 2 = n + 2 + 2 * 0 from by ring,
      show e + n = e + n from rfl]
  exact inner_drain n 0 e

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨n + 1, 0, 0, 0, e⟩) ⟨1, 0⟩
  intro ⟨n, e⟩; exact ⟨⟨n + 1, e + n⟩, main_trans n e⟩
