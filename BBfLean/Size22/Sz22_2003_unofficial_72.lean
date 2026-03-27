import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #72: [1/18, 22/35, 715/2, 21/11, 2/39]

Vector representation:
```
-1 -2  0  0  0  0
 1  0 -1 -1  1  0
-1  0  1  0  1  1
 0  1  0  1 -1  0
 1 -1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_72

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e, f⟩ => some ⟨a, b, c, d, e, f⟩
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a+1, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d+1, e, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a+1, b, c, d, e, f⟩
  | _ => none

-- R4 chain: transfer e to b and d
theorem e_to_bd : ∀ k b d e f, ⟨0, b, 0, d, e+k, f⟩ [fm]⊢* ⟨0, b+k, 0, d+k, e, f⟩ := by
  intro k; induction' k with k h <;> intro b d e f
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _ _)
  ring_nf; finish

-- R5+R1 drain: each round b -= 3, f -= 1
theorem r5r1_drain : ∀ k b d f, ⟨0, b+3*k, 0, d, 0, f+k⟩ [fm]⊢* ⟨0, b, 0, d, 0, f⟩ := by
  intro k; induction' k with k h <;> intro b d f
  · exists 0
  rw [show b + 3 * (k + 1) = (b + 3 * k) + 3 from by ring,
      show f + (k + 1) = (f + k) + 1 from by ring]
  step fm -- R5
  rw [show b + 3 * k + 2 = (b + 3 * k) + 2 from by ring]
  step fm -- R1
  exact h _ _ _

-- R5 then R3: (0,2,0,d,0,g+1) → (1,1,0,d,0,g) → (0,1,1,d,1,g+1)
theorem r5_r3 : ∀ d g, ⟨0, 2, 0, d, 0, g+1⟩ [fm]⊢* ⟨0, 1, 1, d, 1, g+1⟩ := by
  intro d g
  step fm -- R5: (1, 1, 0, d, 0, g)
  step fm -- R3: (0, 1, 1, d, 1, g+1)
  finish

-- R2+R3 interleaved chain: each round d -= 1, e += 2, f += 1
theorem r2r3_chain : ∀ k d e f, ⟨0, 1, 1, d+k, e, f⟩ [fm]⊢* ⟨0, 1, 1, d, e+2*k, f+k⟩ := by
  intro k; induction' k with k h <;> intro d e f
  · exists 0
  rw [show d + (k + 1) = (d + k) + 1 from by ring]
  step fm -- R2
  step fm -- R3
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Main transition: (0,0,0,0,3n+2,f+n+1) →⁺ (0,0,0,0,6n+5,f+3n+3)
theorem main_trans (n f : ℕ) :
    ⟨0, 0, 0, 0, 3*n+2, f+n+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, 6*n+5, f+3*n+3⟩ := by
  -- Phase 1: (0,0,0,0,3n+2,f+n+1) →* (0,3n+2,0,3n+2,0,f+n+1)
  apply stepStar_stepPlus_stepPlus
  · have h1 := e_to_bd (3*n+2) 0 0 0 (f+n+1)
    simp only [Nat.zero_add] at h1; exact h1
  -- Phase 2: (0,3n+2,0,3n+2,0,f+n+1) →* (0,2,0,3n+2,0,f+1)
  apply stepStar_stepPlus_stepPlus
  · have h2 := r5r1_drain n 2 (3*n+2) (f+1)
    rw [show 2 + 3 * n = 3 * n + 2 from by ring,
        show f + 1 + n = f + n + 1 from by ring] at h2
    exact h2
  -- Phase 3: R5,R3: (0,2,0,3n+2,0,f+1) →* (0,1,1,3n+2,1,f+1)
  apply stepStar_stepPlus_stepPlus
  · exact r5_r3 (3*n+2) f
  -- Phase 4: R2+R3 chain: (0,1,1,3n+2,1,f+1) →* (0,1,1,0,6n+5,f+3n+3)
  apply stepStar_stepPlus_stepPlus
  · have h4 := r2r3_chain (3*n+2) 0 1 (f+1)
    simp only [Nat.zero_add] at h4
    rw [show 1 + 2 * (3 * n + 2) = 6 * n + 5 from by ring,
        show f + 1 + (3 * n + 2) = f + 3 * n + 3 from by ring] at h4
    exact h4
  -- Phase 5: R4, R2, R1: (0,1,1,0,6n+5,f+3n+3) →⁺ (0,0,0,0,6n+5,f+3n+3)
  rw [show 6 * n + 5 = (6 * n + 4) + 1 from by ring]
  step fm -- R4: (0, 2, 1, 1, 6n+4, f+3n+3)
  step fm -- R2: (1, 2, 0, 0, 6n+5, f+3n+3)
  step fm -- R1: (0, 0, 0, 0, 6n+5, f+3n+3)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, 0, 0, 3*n+2, f+n+1⟩) ⟨0, 1⟩
  intro ⟨n, f⟩
  exists ⟨2*n+1, f+n+1⟩
  show ⟨0, 0, 0, 0, 3*n+2, f+n+1⟩ [fm]⊢⁺ ⟨0, 0, 0, 0, 3*(2*n+1)+2, (f+n+1)+(2*n+1)+1⟩
  rw [show 3 * (2 * n + 1) + 2 = 6 * n + 5 from by ring,
      show (f + n + 1) + (2 * n + 1) + 1 = f + 3 * n + 3 from by ring]
  exact main_trans n f

end Sz22_2003_unofficial_72
