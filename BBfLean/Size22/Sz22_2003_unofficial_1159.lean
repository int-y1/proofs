import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1159: [5/6, 44/35, 77/2, 3/121, 15/11]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  1  1
 0  1  0  0 -2
 0  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1159

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

theorem a_drain : ∀ k d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (d + 1) (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k b d, ⟨0, b, 0, d, e + 2 * k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show e + 2 * (k + 1) = (e + 2 * k) + 1 + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

theorem interleave : ∀ k c e, ⟨0, 2 * k + 1, c + 1, k + 1, c + e⟩ [fm]⊢* ⟨1, 0, c + k + 1, 0, c + k + 1 + e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · step fm; step fm; ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 from by ring]
    step fm; step fm; step fm
    rw [show c + 1 + 1 = (c + 1) + 1 from by ring,
        show c + e + 1 = (c + 1) + e from by ring]
    apply stepStar_trans (ih (c + 1) e)
    ring_nf; finish

theorem r3r2_chain : ∀ k a c e, ⟨a + 1, 0, c + k, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) c (e + 2))
    ring_nf; finish

theorem main_trans (n : ℕ) : ⟨n + 1, 0, 0, 0, 3 * n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, 3 * (n + 1)⟩ := by
  -- Phase 1: drain a via R3
  have h1 : ⟨n + 1, 0, 0, 0, 3 * n⟩ [fm]⊢* ⟨0, 0, 0, n + 1, 4 * n + 1⟩ := by
    have := @a_drain 0 (n + 1) 0 (3 * n)
    simp only [Nat.zero_add] at this
    rw [show 3 * n + (n + 1) = 4 * n + 1 from by ring] at this
    exact this
  -- Phase 2: R4 chain
  have h2 : ⟨0, 0, 0, n + 1, 4 * n + 1⟩ [fm]⊢* ⟨0, 2 * n, 0, n + 1, 1⟩ := by
    have := @r4_chain 1 (2 * n) 0 (n + 1)
    simp only [Nat.zero_add] at this
    rw [show 1 + 2 * (2 * n) = 4 * n + 1 from by ring] at this
    exact this
  -- Phase 2b: R5
  have h3 : ⟨0, 2 * n, 0, n + 1, 1⟩ [fm]⊢* ⟨0, 2 * n + 1, 1, n + 1, 0⟩ := by
    rw [show (1 : ℕ) = 0 + 1 from by ring]; step fm; finish
  -- Phase 3: interleave
  have h4 : ⟨0, 2 * n + 1, 1, n + 1, 0⟩ [fm]⊢* ⟨1, 0, n + 1, 0, n + 1⟩ := by
    have := interleave n 0 0
    simp only [Nat.zero_add, Nat.add_zero] at this
    exact this
  -- Phase 4: R3,R2 chain
  have h5 : ⟨1, 0, n + 1, 0, n + 1⟩ [fm]⊢* ⟨n + 2, 0, 0, 0, 3 * n + 3⟩ := by
    have := r3r2_chain (n + 1) 0 0 (n + 1)
    simp only [Nat.zero_add] at this
    rw [show n + 1 + 1 = n + 2 from by ring,
        show n + 1 + 2 * (n + 1) = 3 * n + 3 from by ring] at this
    exact this
  -- Compose
  have h6 : ⟨n + 1, 0, 0, 0, 3 * n⟩ [fm]⊢* ⟨n + 2, 0, 0, 0, 3 * n + 3⟩ :=
    stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))
  rw [show 3 * n + 3 = 3 * (n + 1) from by ring] at h6
  exact stepStar_stepPlus h6 (by intro h; simp_all [Q])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, 3 * n⟩) 0
  intro n; exists n + 1; exact main_trans n
