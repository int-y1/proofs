import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1160: [5/6, 44/35, 91/2, 3/11, 15/13]

Vector representation:
```
-1 -1  1  0  0  0
 2  0 -1 -1  1  0
-1  0  0  1  0  1
 0  1  0  0 -1  0
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1160

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+2, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

-- R3 drains a to d and f (when b=0, c=0).
theorem r3_drain_a : ∀ k, ∀ a d f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · rw [Nat.add_succ a k]
    step fm
    apply stepStar_trans (ih a (d + 1) (f + 1))
    ring_nf; finish

-- R4 drains e to b (when a=0, c=0).
theorem r4_drain_e : ∀ k, ∀ b e, ⟨0, b, 0, d, e + k, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [Nat.add_succ e k]
    step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

-- R2/R1/R1 interleaved loop.
theorem r2r1r1_loop : ∀ k, ∀ c e,
    ⟨0, 2 * k + 1, c + 1, k + 1, e, f⟩ [fm]⊢* ⟨0, 1, c + k + 1, 1, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · exists 0
  · rw [show 2 * (k + 1) + 1 = ((2 * k + 1) + 1) + 1 from by ring,
        show (k + 1) + 1 = k + 1 + 1 from rfl]
    step fm; step fm; step fm
    show ⟨0, 2 * k + 1, (c + 1) + 1, k + 1, e + 1, f⟩ [fm]⊢* _
    apply stepStar_trans (ih (c + 1) (e + 1))
    ring_nf; finish

-- R3/R2 alternation chain.
theorem r3r2_chain : ∀ k, ∀ a c e f,
    ⟨a + 1, 0, c + k, 0, e, f⟩ [fm]⊢* ⟨a + 1 + k, 0, c, 0, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e f
  · exists 0
  · rw [Nat.add_succ c k]
    step fm; step fm
    show ⟨(a + 1) + 1, 0, c + k, 0, e + 1, f + 1⟩ [fm]⊢* _
    apply stepStar_trans (ih (a + 1) c (e + 1) (f + 1))
    ring_nf; finish

-- Main transition: (n+1, 0, 0, 0, 2n, n²) ⊢⁺ (n+2, 0, 0, 0, 2(n+1), (n+1)²)
theorem main_transition (n : ℕ) :
    ⟨n + 1, 0, 0, 0, 2 * n, n * n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, 2 * (n + 1), (n + 1) * (n + 1)⟩ := by
  -- Build all phase lemmas
  have h1 : ⟨n + 1, 0, 0, 0, 2 * n, n * n⟩ [fm]⊢*
      ⟨0, 0, 0, n + 1, 2 * n, n * n + n + 1⟩ := by
    have := r3_drain_a (n + 1) (e := 2 * n) 0 0 (n * n)
    rw [show (0 : ℕ) + (n + 1) = n + 1 from by omega,
        show n * n + (n + 1) = n * n + n + 1 from by ring] at this
    exact this
  have h2 : ⟨0, 0, 0, n + 1, 2 * n, n * n + n + 1⟩ [fm]⊢*
      ⟨0, 2 * n, 0, n + 1, 0, n * n + n + 1⟩ := by
    have := r4_drain_e (2 * n) (d := n + 1) (f := n * n + n + 1) 0 0
    rw [show (0 : ℕ) + 2 * n = 2 * n from by omega] at this
    exact this
  have h3 : ⟨0, 2 * n, 0, n + 1, 0, n * n + n + 1⟩ [fm]⊢
      ⟨0, 2 * n + 1, 1, n + 1, 0, n * n + n⟩ := by
    show (fm : FM) _ = some _; simp [fm]
  have h4 : ⟨0, 2 * n + 1, 1, n + 1, 0, n * n + n⟩ [fm]⊢*
      ⟨0, 1, n + 1, 1, n, n * n + n⟩ := by
    have := r2r1r1_loop (f := n * n + n) n 0 0
    rw [show (0 : ℕ) + n + 1 = n + 1 from by omega,
        show (0 : ℕ) + n = n from by omega,
        show (0 : ℕ) + 1 = 1 from by omega] at this
    exact this
  have h5 : ⟨0, 1, n + 1, 1, n, n * n + n⟩ [fm]⊢*
      ⟨1, 0, n + 1, 0, n + 1, n * n + n⟩ := by
    step fm; step fm; finish
  have h6 : ⟨1, 0, n + 1, 0, n + 1, n * n + n⟩ [fm]⊢*
      ⟨n + 2, 0, 0, 0, 2 * n + 2, n * n + 2 * n + 1⟩ := by
    step fm; step fm
    have := r3r2_chain n 1 0 (n + 2) (n * n + n + 1)
    rw [show (0 : ℕ) + n = n from by omega,
        show 1 + 1 + n = n + 2 from by omega,
        show (n + 2) + n = 2 * n + 2 from by ring,
        show n * n + n + 1 + n = n * n + 2 * n + 1 from by ring] at this
    exact this
  -- Compose: h1 (⊢*) + h2 (⊢*) + h3 (⊢) + h4 (⊢*) + h5 (⊢*) + h6 (⊢*) = ⊢⁺
  -- We need at least one step to get ⊢⁺. h3 is a single step.
  -- Strategy: compose h1, h2 into ⊢*, then h3 into ⊢⁺ via step, then h4,h5,h6 into ⊢*
  rw [show 2 * (n + 1) = 2 * n + 2 from by ring,
      show (n + 1) * (n + 1) = n * n + 2 * n + 1 from by ring]
  apply stepStar_stepPlus_stepPlus (stepStar_trans h1 h2)
  apply step_stepStar_stepPlus h3
  exact stepStar_trans h4 (stepStar_trans h5 h6)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 2, 1⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, 2 * n, n * n⟩) 1
  intro n; exists n + 1; exact main_transition n
