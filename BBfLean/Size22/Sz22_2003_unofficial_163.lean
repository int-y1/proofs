import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #163: [1/45, 49/33, 4/3, 15/7, 99/2]

Vector representation:
```
 0 -2 -1  0  0
 0 -1  0  2 -1
 2 -1  0  0  0
 0  1  1 -1  0
-1  2  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_163

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

-- Phase 1: R5+R1 chain. Each pair consumes 1 from a and c, adds 1 to e.
-- (a+K, 0, c+K, 0, e) →* (a, 0, c, 0, e+K)
theorem r5r1_chain : ∀ K a c e,
    ⟨a + K, 0, c + K, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e + K⟩ := by
  intro K; induction' K with K ih <;> intro a c e
  · exists 0
  · rw [show a + (K + 1) = (a + K) + 1 from by ring,
        show c + (K + 1) = (c + K) + 1 from by ring]
    step fm
    step fm
    apply stepStar_trans (ih a c (e + 1))
    ring_nf; finish

-- Phase 2a: R5 then 2×R2.
-- (a+1, 0, 0, 0, e+2) →* (a, 0, 0, 4, e+1)
theorem r5_r2r2 : ∀ a e,
    ⟨a + 1, 0, 0, 0, e + 2⟩ [fm]⊢* ⟨a, 0, 0, 4, e + 1⟩ := by
  intro a e
  step fm
  step fm
  step fm
  ring_nf; finish

-- Phase 2b: R4+R2 chain (generalized).
-- (a, 0, j, j+4, e+K+1) →* (a, 0, j+K+1, j+K+5, e)
theorem r4r2_chain : ∀ K a j e,
    ⟨a, 0, j, j + 4, e + K + 1⟩ [fm]⊢* ⟨a, 0, j + K + 1, j + K + 5, e⟩ := by
  intro K; induction' K with K ih <;> intro a j e
  · step fm
    step fm
    ring_nf; finish
  · rw [show e + (K + 1) + 1 = (e + 1) + K + 1 from by ring]
    step fm
    step fm
    rw [show j + 1 + 4 = (j + 1) + 4 from by ring,
        show (e + 1) + K = e + K + 1 from by ring]
    apply stepStar_trans (ih a (j + 1) e)
    ring_nf; finish

-- Phase 3: R4+R3 chain. Each pair moves 1 from d to a (+2) and c (+1).
-- (a, 0, c, D, 0) →* (a+2*D, 0, c+D, 0, 0)
theorem r4r3_chain : ∀ D a c,
    ⟨a, 0, c, D, 0⟩ [fm]⊢* ⟨a + 2 * D, 0, c + D, 0, 0⟩ := by
  intro D; induction' D with D ih <;> intro a c
  · simp; exists 0
  · rw [show (D + 1 : ℕ) = D + 1 from rfl]
    step fm
    step fm
    apply stepStar_trans (ih (a + 2) (c + 1))
    ring_nf; finish

-- Main transition: (n+c+4, 0, c+2, 0, 0) ⊢⁺ (n+2c+11, 0, 2c+6, 0, 0)
theorem main_trans (n c : ℕ) :
    ⟨n + c + 4, 0, c + 2, 0, 0⟩ [fm]⊢⁺ ⟨n + 2 * c + 11, 0, 2 * c + 6, 0, 0⟩ := by
  -- Phase 1: R5+R1 chain (c+2 iterations)
  -- (n+c+4, 0, c+2, 0, 0) →* (n+2, 0, 0, 0, c+2)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + 2, 0, 0, 0, c + 2⟩)
  · have h := r5r1_chain (c + 2) (n + 2) 0 0
    rw [show n + 2 + (c + 2) = n + c + 4 from by ring] at h
    simpa using h
  -- Phase 2a: R5 + 2×R2
  -- (n+2, 0, 0, 0, c+2) →* (n+1, 0, 0, 4, c+1)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + 1, 0, 0, 4, c + 1⟩)
  · have h := r5_r2r2 (n + 1) c
    rw [show n + 1 + 1 = n + 2 from by ring] at h
    exact h
  -- Phase 2b: R4+R2 chain (c+1 iterations)
  -- (n+1, 0, 0, 4, c+1) →* (n+1, 0, c+1, c+5, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨n + 1, 0, c + 1, c + 5, 0⟩)
  · have h := r4r2_chain c (n + 1) 0 0
    rw [show 0 + c + 1 = c + 1 from by ring,
        show 0 + c + 5 = c + 5 from by ring] at h
    simpa using h
  -- Phase 3: R4+R3 chain (c+5 iterations)
  -- (n+1, 0, c+1, c+5, 0) →* (n+2c+11, 0, 2c+6, 0, 0)
  have h := r4r3_chain (c + 5) (n + 1) (c + 1)
  rw [show n + 1 + 2 * (c + 5) = n + 2 * c + 11 from by ring,
      show c + 1 + (c + 5) = 2 * c + 6 from by ring] at h
  apply stepStar_stepPlus h
  intro heq
  have := congr_arg (fun q : Q => q.2.2.2.1) heq
  simp at this

theorem nonhalt : ¬halts fm c₀ := by
  -- Bootstrap: c₀ = (1,0,0,0,0) →* (6,0,2,0,0) = (2+0+4, 0, 0+2, 0, 0)
  apply stepStar_not_halts_not_halts (c₂ := ⟨6, 0, 2, 0, 0⟩)
  · execute fm 7
  -- Use progress_nonhalt with P(q) := ∃ n c, q = (n+c+4, 0, c+2, 0, 0)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ n c, q = ⟨n + c + 4, 0, c + 2, 0, 0⟩)
  · intro q ⟨n, c, hq⟩
    refine ⟨⟨n + 2 * c + 11, 0, 2 * c + 6, 0, 0⟩, ⟨n + 3, 2 * c + 4, ?_⟩, hq ▸ main_trans n c⟩
    congr 1; omega
  · exact ⟨2, 0, by congr 1⟩

end Sz22_2003_unofficial_163
