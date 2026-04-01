import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1217: [5/6, 539/2, 44/35, 3/11, 6/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  1
 2  0 -1 -1  1
 0  1  0  0 -1
 1  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1217

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e+1⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

-- R4 chain: (0, b, 0, d, k) →* (0, b+k, 0, d, 0)
theorem e_to_b : ∀ k b d, ⟨0, b, 0, d, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) d)
    ring_nf; finish

-- R1R1R3 chain: (2, b+2k, c, d+k, e) →* (2, b, c+k, d, e+k)
theorem r1r1r3_chain : ∀ k b c d e, ⟨2, b + 2 * k, c, d + k, e⟩ [fm]⊢* ⟨2, b, c + k, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2) + 2 * k from by ring,
        show d + (k + 1) = (d + 1) + k from by ring]
    apply stepStar_trans (ih (b + 2) c (d + 1) e)
    rw [show b + 2 = (b + 1) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show c + k + 1 = c + (k + 1) from by ring,
        show e + k + 1 = e + (k + 1) from by ring]
    finish

-- R3R2R2 chain: (0, 0, c+k, d+1, e) →* (0, 0, c, d+1+3k, e+3k)
theorem r3r2r2_chain : ∀ k c d e, ⟨0, 0, c + k, d + 1, e⟩ [fm]⊢* ⟨0, 0, c, d + 1 + 3 * k, e + 3 * k⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm
    step fm
    step fm
    rw [show d + 4 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih c (d + 3) (e + 3))
    ring_nf; finish

-- Full transition: (0, 0, 0, n+d+2, 2n+1) →⁺ (0, 0, 0, 3n+d+5, 4n+5)
theorem main_trans (n d : ℕ) :
    ⟨(0 : ℕ), 0, 0, n + d + 2, 2 * n + 1⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, 0, 3 * n + d + 5, 4 * n + 5⟩ := by
  -- R4 step to establish ⊢⁺: (0,0,0,n+d+2,2n+1) -> (0,1,0,n+d+2,2n)
  rw [show 2 * n + 1 = (2 * n) + 1 from by ring]
  step fm
  -- R4 chain (2n rounds): (0,1,0,n+d+2,2n) →* (0,2n+1,0,n+d+2,0)
  apply stepStar_trans (e_to_b (2 * n) 1 (n + d + 2))
  rw [show 1 + 2 * n = 2 * n + 1 from by ring]
  -- R5: (0,2n+1,0,n+d+2,0) -> (1,2n+2,0,n+d+1,0)
  rw [show n + d + 2 = (n + d + 1) + 1 from by ring]
  step fm
  -- R1: (1,2n+2,0,n+d+1,0) -> (0,2n+1,1,n+d+1,0)
  rw [show 2 * n + 2 = (2 * n + 1) + 1 from by ring]
  step fm
  -- R3: (0,2n+1,1,n+d+1,0) -> (2,2n+1,0,n+d,1)
  rw [show n + d + 1 = (n + d) + 1 from by ring]
  step fm
  -- R1R1R3 chain (n rounds): (2,2n+1,0,n+d,1) →* (2,1,n,d,n+1)
  rw [show 2 * n + 1 = 1 + 2 * n from by ring,
      show n + d = d + n from by ring]
  apply stepStar_trans (r1r1r3_chain n 1 0 d 1)
  rw [show 0 + n = n from by ring, show 1 + n = n + 1 from by ring]
  -- R1: (2,1,n,d,n+1) -> (1,0,n+1,d,n+1)
  step fm
  -- R2: (1,0,n+1,d,n+1) -> (0,0,n+1,d+2,n+2)
  step fm
  -- R3R2R2 chain (n+1 rounds): (0,0,n+1,d+2,n+2) →* (0,0,0,d+2+3(n+1),n+2+3(n+1))
  rw [show n + 1 = 0 + (n + 1) from by ring,
      show d + 2 = (d + 1) + 1 from by ring,
      show 0 + (n + 1) + 1 = n + 2 from by ring]
  apply stepStar_trans (r3r2r2_chain (n + 1) 0 (d + 1) (n + 2))
  have h1 : d + 1 + 1 + 3 * (n + 1) = 3 * n + d + 5 := by ring
  have h2 : n + 2 + 3 * (n + 1) = 4 * n + 5 := by ring
  rw [h1, h2]; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 5, 5⟩)
  · execute fm 10
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, d⟩ ↦ ⟨0, 0, 0, n + d + 2, 2 * n + 1⟩) ⟨2, 1⟩
  intro ⟨n, d⟩
  refine ⟨⟨2 * n + 2, n + d + 1⟩, ?_⟩
  show ⟨(0 : ℕ), 0, 0, n + d + 2, 2 * n + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, (2 * n + 2) + (n + d + 1) + 2, 2 * (2 * n + 2) + 1⟩
  rw [show (2 * n + 2) + (n + d + 1) + 2 = 3 * n + d + 5 from by ring,
      show 2 * (2 * n + 2) + 1 = 4 * n + 5 from by ring]
  exact main_trans n d

end Sz22_2003_unofficial_1217
