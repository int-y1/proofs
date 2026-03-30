import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1003: [4/15, 49/3, 33/2, 25/77, 3/35]

Vector representation:
```
 2 -1 -1  0  0
 0 -1  0  2  0
-1  1  0  0  1
 0  0  2 -1 -1
 0  1 -1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1003

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d+k, e+k) ->* (0, 0, c+2k, d, e)
theorem r4_chain : ∀ k, ∀ c d e, ⟨0, 0, c, d + k, e + k⟩ [fm]⊢* ⟨0, 0, c + 2 * k, d, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (c + 2) d e)
    ring_nf; finish

-- R3,R1 alternating: (a+1, 0, k, d, e) ->* (a+k+1, 0, 0, d, e+k)
theorem r3_r1_chain : ∀ k, ∀ a d e, ⟨a + 1, 0, k, d, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · step fm
    step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) d (e + 1))
    ring_nf; finish

-- Drain via R3,R2 alternating: (k, 0, 0, d, e) ->* (0, 0, 0, d+2k, e+k)
theorem drain : ∀ k, ∀ d e, ⟨k, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  · step fm
    step fm
    apply stepStar_trans (ih (d + 2) (e + 1))
    ring_nf; finish

-- Main transition: (0,0,0,n+e+2,e+1) ⊢⁺ (0,0,0,n+4e+4,4e+2)
-- Phases: R4(e+1) -> R5,R1 -> R3,R1(2e) -> drain(2e+2)
theorem main_trans (n e : ℕ) :
    ⟨0, 0, 0, n + e + 2, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 4 * e + 4, 4 * e + 2⟩ := by
  have h23 : ⟨0, 0, 2 * e + 2, n + 1, 0⟩ [fm]⊢* ⟨2, 0, 2 * e, n, 0⟩ := by
    step fm; step fm; finish
  have h4 : ⟨2, 0, 2 * e, n, 0⟩ [fm]⊢* ⟨2 * e + 2, 0, 0, n, 2 * e⟩ := by
    have := r3_r1_chain (2 * e) 1 n 0
    rw [show 1 + 2 * e + 1 = 2 * e + 2 from by ring,
        show 0 + 2 * e = 2 * e from by ring,
        show 1 + 1 = 2 from by ring] at this
    exact this
  have h5 : ⟨2 * e + 2, 0, 0, n, 2 * e⟩ [fm]⊢* ⟨0, 0, 0, n + 4 * e + 4, 4 * e + 2⟩ := by
    have := drain (2 * e + 2) n (2 * e)
    rw [show n + 2 * (2 * e + 2) = n + 4 * e + 4 from by ring,
        show 2 * e + (2 * e + 2) = 4 * e + 2 from by ring] at this
    exact this
  rw [show n + e + 2 = (n + e + 1) + 1 from by ring]
  step fm
  have h1' : ⟨0, 0, 2, n + e + 1, e⟩ [fm]⊢* ⟨0, 0, 2 * e + 2, n + 1, 0⟩ := by
    have := r4_chain e 2 (n + 1) 0
    rw [show (n + 1) + e = n + e + 1 from by ring,
        show 0 + e = e from by ring,
        show 2 + 2 * e = 2 * e + 2 from by ring] at this
    exact this
  apply stepStar_trans h1'
  apply stepStar_trans h23
  apply stepStar_trans h4
  exact h5

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨0, 0, 0, n + e + 2, e + 1⟩) ⟨0, 0⟩
  intro ⟨n, e⟩
  refine ⟨⟨n + 1, 4 * e + 1⟩, ?_⟩
  show ⟨0, 0, 0, n + e + 2, e + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, (n + 1) + (4 * e + 1) + 2, (4 * e + 1) + 1⟩
  rw [show (n + 1) + (4 * e + 1) + 2 = n + 4 * e + 4 from by ring,
      show (4 * e + 1) + 1 = 4 * e + 2 from by ring]
  exact main_trans n e

end Sz22_2003_unofficial_1003
