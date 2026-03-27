import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #158: [1/45, 385/2, 14/65, 39/7, 5/33]

Vector representation:
```
 0 -2 -1  0  0  0
-1  0  1  1  1  0
 1  0 -1  1  0 -1
 0  1  0 -1  0  1
 0 -1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_158

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e+1, f⟩
  | ⟨a, b, c+1, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f⟩
  | _ => none

-- R4 chain: d → b,f when a=0, c=0
theorem r4_chain : ∀ K b e f, ⟨0, b, 0, K, e, f⟩ [fm]⊢* ⟨0, b + K, 0, 0, e, f + K⟩ := by
  intro K; induction' K with K ih <;> intro b e f
  · simp; exists 0
  · rw [show (K + 1 : ℕ) = K + 1 from rfl]
    step fm
    apply stepStar_trans (ih (b + 1) e (f + 1))
    ring_nf; finish

-- R5/R1 drain: (0, 3K+1, 0, 0, e+K+1, f) →* (0, 0, 1, 0, e, f)
theorem r5r1_drain : ∀ K e f, ⟨0, 3 * K + 1, 0, 0, e + K + 1, f⟩ [fm]⊢* ⟨0, 0, 1, 0, e, f⟩ := by
  intro K; induction' K with K ih <;> intro e f
  · simp; step fm; finish
  · rw [show 3 * (K + 1) + 1 = (3 * K + 1) + 3 from by ring,
        show e + (K + 1) + 1 = (e + K + 1) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih e f)
    finish

-- R2/R3 chain: (1, 0, 0, d, e, K) →* (1, 0, 0, d+2K, e+K, 0)
theorem r2r3_chain : ∀ K d e, ⟨1, 0, 0, d, e, K⟩ [fm]⊢* ⟨1, 0, 0, d + 2 * K, e + K, 0⟩ := by
  intro K; induction' K with K ih <;> intro d e
  · simp; exists 0
  · rw [show (K + 1 : ℕ) = K + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

-- Main transition: (1, 0, 0, 3m, 2m, 0) ⊢⁺ (1, 0, 0, 3(2m+1), 2(2m+1), 0)
theorem main_trans (m : ℕ) :
    ⟨1, 0, 0, 3 * m, 2 * m, 0⟩ [fm]⊢⁺ ⟨1, 0, 0, 3 * (2 * m + 1), 2 * (2 * m + 1), 0⟩ := by
  -- Phase 1: Bootstrap (6 steps)
  -- (1, 0, 0, 3m, 2m, 0) → (0, 0, 0, 3m+1, 2m+2, 1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 0, 3 * m + 1, 2 * m + 2, 1⟩)
  · step fm -- R2: (0, 0, 1, 3m+1, 2m+1, 0)
    step fm -- R4: (0, 1, 1, 3m, 2m+1, 1)
    step fm -- R3: (1, 1, 0, 3m+1, 2m+1, 0)
    step fm -- R2: (0, 1, 1, 3m+2, 2m+2, 0)
    step fm -- R4: (0, 2, 1, 3m+1, 2m+2, 1)
    step fm -- R1: (0, 0, 0, 3m+1, 2m+2, 1)
    finish
  -- Phase 2: R4 chain (3m+1 steps)
  -- (0, 0, 0, 3m+1, 2m+2, 1) → (0, 3m+1, 0, 0, 2m+2, 3m+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 3 * m + 1, 0, 0, 2 * m + 2, 3 * m + 2⟩)
  · have h := r4_chain (3 * m + 1) 0 (2 * m + 2) 1
    simp only [Nat.zero_add] at h
    rw [show 1 + (3 * m + 1) = 3 * m + 2 from by ring] at h
    exact h
  -- Phase 3: R5/R1 drain
  -- (0, 3m+1, 0, 0, 2m+2, 3m+2) → (0, 0, 1, 0, m+1, 3m+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, 1, 0, m + 1, 3 * m + 2⟩)
  · have h := r5r1_drain m (m + 1) (3 * m + 2)
    rw [show m + 1 + m + 1 = 2 * m + 2 from by ring] at h
    exact h
  -- Phase 4: R3 (1 step)
  -- (0, 0, 1, 0, m+1, 3m+2) → (1, 0, 0, 1, m+1, 3m+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨1, 0, 0, 1, m + 1, 3 * m + 1⟩)
  · step fm
    finish
  -- Phase 5: R2/R3 chain
  -- (1, 0, 0, 1, m+1, 3m+1) → (1, 0, 0, 6m+3, 4m+2, 0)
  rw [show 3 * (2 * m + 1) = 6 * m + 3 from by ring,
      show 2 * (2 * m + 1) = 4 * m + 2 from by ring]
  have h := r2r3_chain (3 * m + 1) 1 (m + 1)
  rw [show 1 + 2 * (3 * m + 1) = 6 * m + 3 from by ring,
      show m + 1 + (3 * m + 1) = 4 * m + 2 from by ring] at h
  apply stepStar_stepPlus h
  intro heq
  have : (1 : ℕ) = 6 * m + 3 := by
    have := congr_arg (fun q : Q => q.2.2.2.1) heq
    simp at this
  omega

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun m ↦ ⟨1, 0, 0, 3 * m, 2 * m, 0⟩) 0
  intro m; exact ⟨2 * m + 1, main_trans m⟩

end Sz22_2003_unofficial_158
