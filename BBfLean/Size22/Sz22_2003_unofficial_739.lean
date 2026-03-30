import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #739: [35/6, 4/55, 143/2, 39/7, 15/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  1
 0  1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_739

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c+1, d, e, f⟩
  | _ => none

theorem r2_chain : ∀ k, ∀ a c d e f, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e f)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e (f + 1))
    ring_nf; finish

theorem r1r1r2_even : ∀ k, ∀ c d e f, ⟨2, 2 * k, c, d, e + k, f⟩ [fm]⊢* ⟨2, 0, c + k, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem r1r1r2_odd : ∀ k, ∀ c d e f, ⟨2, 2 * k + 1, c, d, e + k, f⟩ [fm]⊢* ⟨1, 0, c + k + 1, d + 2 * k + 1, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

-- Even interleave + R2 drain:
-- (2, 2*N, 0, 0, 2*N-1, f) ⊢* (2*N, 0, 1, 2*N, 0, f)
theorem interleave_even (m f : ℕ) :
    ⟨2, 2 * m + 2, 0, 0, 2 * m + 1, f⟩ [fm]⊢* ⟨2 * m + 2, 0, 1, 2 * m + 2, 0, f⟩ := by
  rw [show 2 * m + 2 = 2 * (m + 1) from by ring,
      show 2 * m + 1 = m + (m + 1) from by ring]
  apply stepStar_trans (r1r1r2_even (m + 1) 0 0 m f)
  have key := r2_chain m 2 1 (2 * (m + 1)) 0 f
  convert key using 2
  all_goals ring_nf

-- Odd interleave + R2 drain:
-- (2, 2*N+1, 0, 0, 2*N, f) ⊢* (2*N+1, 0, 1, 2*N+1, 0, f)
theorem interleave_odd (m f : ℕ) :
    ⟨2, 2 * m + 3, 0, 0, 2 * m + 2, f⟩ [fm]⊢* ⟨2 * m + 3, 0, 1, 2 * m + 3, 0, f⟩ := by
  rw [show 2 * m + 3 = 2 * (m + 1) + 1 from by ring,
      show 2 * m + 2 = (m + 1) + (m + 1) from by ring]
  apply stepStar_trans (r1r1r2_odd (m + 1) 0 0 (m + 1) f)
  have key := r2_chain (m + 1) 1 1 (2 * (m + 1) + 1) 0 f
  convert key using 2
  all_goals ring_nf

-- Tail: (N+1, 0, 1, N+1, 0, f) ⊢* (0, N+1, 0, 0, N+2, f+2*N+4)
-- = R3 + R2 + R3_chain(N+3) + R4_chain(N+1)
theorem tail_phase : ∀ N, ∀ f, ⟨N + 1, 0, 1, N + 1, 0, f⟩ [fm]⊢* ⟨0, N + 1, 0, 0, N + 2, f + 2 * N + 4⟩ := by
  intro N f
  -- R3: (N, 0, 1, N+1, 1, f+1)
  step fm
  -- R2: (N+2, 0, 0, N+1, 0, f+1)
  step fm
  -- Now state: (N+2, 0, 0, N+1, 0, f+1). R3 chain of N+2 steps.
  -- Need to write N+2 = 0 + (N+2)
  rw [show N + 2 = 0 + (N + 2) from by ring,
      show N + 1 = 0 + (N + 1) from by ring]
  apply stepStar_trans (r3_chain (N + 2) 0 (0 + (N + 1)) 0 (f + 1))
  -- After: (0, 0, 0, N+1, N+2, f+1+(N+2))
  apply stepStar_trans (r4_chain (N + 1) 0 0 (0 + (N + 2)) (f + 1 + (N + 2)))
  -- After: (0, N+1, 0, 0, N+2, f+1+(N+2)+(N+1))
  ring_nf; finish

-- Full even: (0, 2m+1, 0, 0, 2m+2, (2m+2)^2) ⊢⁺ (0, 2m+2, 0, 0, 2m+3, (2m+3)^2)
theorem main_even (m : ℕ) :
    ⟨0, 2 * m + 1, 0, 0, 2 * m + 2, (2 * m + 2) * (2 * m + 2)⟩ [fm]⊢⁺
    ⟨0, 2 * m + 2, 0, 0, 2 * m + 3, (2 * m + 3) * (2 * m + 3)⟩ := by
  -- Rewrite f to expose +1 for R5
  rw [show (2 * m + 2) * (2 * m + 2) = (2 * m + 1) * (2 * m + 3) + 1 from by ring]
  -- R5
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * m + 1, 0, 0, 2 * m + 2, (2 * m + 1) * (2 * m + 3) + 1⟩ =
      some ⟨0, 2 * m + 2, 1, 0, 2 * m + 2, (2 * m + 1) * (2 * m + 3)⟩
    simp [fm]
  -- R2: need e = (2*m+1)+1
  rw [show 2 * m + 2 = (2 * m + 1) + 1 from by ring]
  step fm
  -- After R2: (2, (2*m+1)+1, 0, 0, 2*m+1, f) = (2, 2*m+2, 0, 0, 2*m+1, f)
  rw [show (2 * m + 1) + 1 = 2 * m + 2 from by ring]
  -- Interleave
  apply stepStar_trans (interleave_even m ((2 * m + 1) * (2 * m + 3)))
  -- After: (2*m+2, 0, 1, 2*m+2, 0, f)
  -- Tail phase with N = 2*m+1, so N+1 = 2*m+2
  have key := tail_phase (2 * m + 1) ((2 * m + 1) * (2 * m + 3))
  convert key using 2
  all_goals ring_nf

-- Full odd: (0, 2m+2, 0, 0, 2m+3, (2m+3)^2) ⊢⁺ (0, 2m+3, 0, 0, 2m+4, (2m+4)^2)
theorem main_odd (m : ℕ) :
    ⟨0, 2 * m + 2, 0, 0, 2 * m + 3, (2 * m + 3) * (2 * m + 3)⟩ [fm]⊢⁺
    ⟨0, 2 * m + 3, 0, 0, 2 * m + 4, (2 * m + 4) * (2 * m + 4)⟩ := by
  rw [show (2 * m + 3) * (2 * m + 3) = (2 * m + 2) * (2 * m + 4) + 1 from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * m + 2, 0, 0, 2 * m + 3, (2 * m + 2) * (2 * m + 4) + 1⟩ =
      some ⟨0, 2 * m + 3, 1, 0, 2 * m + 3, (2 * m + 2) * (2 * m + 4)⟩
    simp [fm]
  rw [show 2 * m + 3 = (2 * m + 2) + 1 from by ring]
  step fm
  rw [show (2 * m + 2) + 1 = 2 * m + 3 from by ring]
  apply stepStar_trans (interleave_odd m ((2 * m + 2) * (2 * m + 4)))
  have key := tail_phase (2 * m + 2) ((2 * m + 2) * (2 * m + 4))
  convert key using 2
  all_goals ring_nf

theorem main_trans (n : ℕ) :
    ⟨0, n + 1, 0, 0, n + 2, (n + 2) * (n + 2)⟩ [fm]⊢⁺ ⟨0, n + 2, 0, 0, n + 3, (n + 3) * (n + 3)⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    exact main_even k
  · subst hk
    rw [show 2 * k + 1 + 1 = 2 * k + 2 from by ring,
        show 2 * k + 1 + 2 = 2 * k + 3 from by ring,
        show 2 * k + 1 + 3 = 2 * k + 4 from by ring]
    exact main_odd k

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 1, 0, 0, 2, 4⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, n + 1, 0, 0, n + 2, (n + 2) * (n + 2)⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_739
