import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1741: [8/15, 33/14, 65/2, 7/11, 21/13]

Vector representation:
```
 3 -1 -1  0  0  0
-1  1  0 -1  1  0
-1  0  1  0  0  1
 0  0  0  1 -1  0
 0  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1741

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e, f⟩ => some ⟨a+3, b, c, d, e, f⟩
  | ⟨a+1, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | _ => none

-- R2-R1 chain: k rounds of (R2, R1)
theorem r2r1_chain : ∀ k : ℕ, ∀ a c d e f : ℕ,
    ⟨a + 1, 0, c + k, d + k, e, f⟩ [fm]⊢* ⟨a + 2 * k + 1, 0, c, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm  -- R2
    step fm  -- R1
    show ⟨(a + 2) + 1, 0, c + k, d + k, e + 1, f⟩ [fm]⊢* ⟨a + 2 * (k + 1) + 1, 0, c, d, e + (k + 1), f⟩
    apply stepStar_trans (ih (a + 2) c d (e + 1) f)
    ring_nf; finish

-- R3 chain: drain a, incrementing c and f (b=0, d=0)
theorem r3_chain : ∀ k : ℕ, ∀ c e f : ℕ,
    ⟨k, 0, c, 0, e, f⟩ [fm]⊢* ⟨0, 0, c + k, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro c e f
  · exists 0
  · show ⟨k + 1, 0, c, 0, e, f⟩ [fm]⊢* _
    step fm  -- R3
    apply stepStar_trans (ih (c + 1) e (f + 1))
    ring_nf; finish

-- R4 chain: drain e, incrementing d (a=0, b=0)
theorem r4_chain : ∀ k : ℕ, ∀ c d f : ℕ,
    ⟨0, 0, c, d, k, f⟩ [fm]⊢* ⟨0, 0, c, d + k, 0, f⟩ := by
  intro k; induction' k with k ih <;> intro c d f
  · exists 0
  · show ⟨0, 0, c, d, k + 1, f⟩ [fm]⊢* _
    step fm  -- R4
    apply stepStar_trans (ih c (d + 1) f)
    ring_nf; finish

-- Main transition: (0, 0, C, N, 0, F) →⁺ (0, 0, C+N+3, N+1, 0, F+2N+4)
theorem main_trans (C N F : ℕ) (hC : C ≥ N + 2) (_ : N ≥ 1) (hF : F ≥ 1) :
    ⟨0, 0, C, N, 0, F⟩ [fm]⊢⁺ ⟨0, 0, C + N + 3, N + 1, 0, F + 2 * N + 4⟩ := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  obtain ⟨C', rfl⟩ : ∃ C', C = C' + N + 2 := ⟨C - N - 2, by omega⟩
  -- Phase 1: R5 step
  step fm
  -- Phase 2: R1 step
  show ⟨0, 1, C' + N + 2, N + 1, 0, F'⟩ [fm]⊢* _
  rw [show C' + N + 2 = (C' + N + 1) + 1 from by ring]
  step fm
  -- Phase 3: R2-R1 chain (N+1 rounds)
  have h3 : ⟨3, 0, C' + N + 1, N + 1, 0, F'⟩ [fm]⊢*
      ⟨2 * N + 5, 0, C', 0, N + 1, F'⟩ := by
    have := r2r1_chain (N + 1) 2 C' 0 0 F'
    convert this using 2; ring_nf
  apply stepStar_trans h3
  -- Phase 4: R3 chain
  have h4 : ⟨2 * N + 5, 0, C', 0, N + 1, F'⟩ [fm]⊢*
      ⟨0, 0, C' + 2 * N + 5, 0, N + 1, F' + 2 * N + 5⟩ :=
    r3_chain (2 * N + 5) C' (N + 1) F'
  apply stepStar_trans h4
  -- Phase 5: R4 chain
  have h5 : ⟨0, 0, C' + 2 * N + 5, 0, N + 1, F' + 2 * N + 5⟩ [fm]⊢*
      ⟨0, 0, C' + 2 * N + 5, N + 1, 0, F' + 2 * N + 5⟩ := by
    have := r4_chain (N + 1) (C' + 2 * N + 5) 0 (F' + 2 * N + 5)
    convert this using 2; ring_nf
  apply stepStar_trans h5
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 4, 1, 0, 5⟩)
  · execute fm 11
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ C N F, q = ⟨0, 0, C, N, 0, F⟩ ∧ C ≥ N + 2 ∧ N ≥ 1 ∧ F ≥ 1)
  · intro q ⟨C, N, F, hq, hC, hN, hF⟩; subst hq
    exact ⟨⟨0, 0, C + N + 3, N + 1, 0, F + 2 * N + 4⟩,
      ⟨C + N + 3, N + 1, F + 2 * N + 4, rfl, by omega, by omega, by omega⟩,
      main_trans C N F hC hN hF⟩
  · exact ⟨4, 1, 5, rfl, by omega, by omega, by omega⟩
