import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1155: [5/6, 44/35, 7/2, 3/11, 484/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  1  0
 0  1  0  0 -1
 2  0  0 -1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1155

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+2, b, c, d, e+2⟩
  | _ => none

-- R3 chain: (a+k, 0, 0, d, e) →* (a, 0, 0, d+k, e)
theorem a_to_d : ∀ k, ∀ a d, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro a d
  · exists 0
  · rw [show a + (k + 1) = a + k + 1 from by ring]; step fm
    apply stepStar_trans (ih a (d + 1)); ring_nf; finish

-- R4 chain: (0, b, 0, d, e+k) →* (0, b+k, 0, d, e)
theorem e_to_b : ∀ k, ∀ b e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · rw [show e + (k + 1) = e + k + 1 from by ring]; step fm
    show ⟨0, b + 1, 0, d, e + k⟩ [fm]⊢* ⟨0, b + (k + 1), 0, d, e⟩
    apply stepStar_trans (ih (b + 1) e); ring_nf; finish

-- R1+R1+R2 chain: after k rounds: (2, b+2k, c, d+k, e) →* (2, b, c+k, d, e+k)
theorem r1r1r2_chain : ∀ k, ∀ b c d e, ⟨2, b + 2 * k, c, d + k, e⟩ [fm]⊢* ⟨2, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = b + 2 * k + 1 + 1 from by ring,
        show d + (k + 1) = d + k + 1 from by ring]
    step fm; step fm; step fm
    show ⟨2, b + 2 * k, c + 1, d + k, e + 1⟩ [fm]⊢* ⟨2, b, c + (k + 1), d, e + (k + 1)⟩
    apply stepStar_trans (ih b (c + 1) d (e + 1)); ring_nf; finish

-- R3+R2 chain: (a+1, 0, k, 0, e) →* (a+k+1, 0, 0, 0, e+k)
theorem r3r2_chain : ∀ k, ∀ a e, ⟨a + 1, 0, k, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

-- R5 step lemma
theorem r5_step : ⟨0, b, 0, n + 1, 0⟩ [fm]⊢ ⟨2, b, 0, n, 2⟩ := by
  unfold fm; simp

-- Main transition: (n+1, 0, 0, 0, 2*n) →⁺ (n+2, 0, 0, 0, 2*n+2)
theorem main_trans : ⟨n + 1, 0, 0, 0, 2 * n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ := by
  -- Phase 1: R3 chain: (n+1, 0, 0, 0, 2n) →* (0, 0, 0, n+1, 2n)
  have h1 : ⟨n + 1, 0, 0, 0, 2 * n⟩ [fm]⊢* ⟨0, 0, 0, n + 1, 2 * n⟩ := by
    rw [show n + 1 = 0 + (n + 1) from by ring]
    exact a_to_d (n + 1) 0 0 (e := 2 * n)
  -- Phase 2: R4 chain: (0, 0, 0, n+1, 2n) →* (0, 2n, 0, n+1, 0)
  have h2 : ⟨0, 0, 0, n + 1, 2 * n⟩ [fm]⊢* ⟨0, 2 * n, 0, n + 1, 0⟩ := by
    rw [show (2 * n : ℕ) = 0 + 2 * n from by ring]
    exact e_to_b (2 * n) 0 0 (d := n + 1)
  -- Phase 3: R5 step: (0, 2n, 0, n+1, 0) → (2, 2n, 0, n, 2)
  have h3 : ⟨0, 2 * n, 0, n + 1, 0⟩ [fm]⊢ ⟨2, 2 * n, 0, n, 2⟩ :=
    r5_step
  -- Phase 4: R1+R1+R2 chain: (2, 2n, 0, n, 2) →* (2, 0, n, 0, n+2)
  have h4 : ⟨2, 2 * n, 0, n, 2⟩ [fm]⊢* ⟨2, 0, n, 0, n + 2⟩ := by
    have := r1r1r2_chain n 0 0 0 2
    simp only [Nat.zero_add] at this
    apply stepStar_trans this
    ring_nf; finish
  -- Phase 5: R3+R2 chain: (2, 0, n, 0, n+2) →* (n+2, 0, 0, 0, 2n+2)
  have h5 : ⟨2, 0, n, 0, n + 2⟩ [fm]⊢* ⟨n + 2, 0, 0, 0, 2 * n + 2⟩ := by
    rw [show (2 : ℕ) = 1 + 1 from by ring]
    apply stepStar_trans (r3r2_chain n 1 (n + 2))
    ring_nf; finish
  -- Compose all phases
  apply stepStar_stepPlus_stepPlus h1
  apply stepStar_stepPlus_stepPlus h2
  apply step_stepStar_stepPlus h3
  exact stepStar_trans h4 h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 4⟩)
  · execute fm 12
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, 2 * n⟩) 2
  intro n; exists n + 1; exact main_trans

end Sz22_2003_unofficial_1155
