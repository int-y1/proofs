import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1390: [63/10, 847/2, 4/33, 5/7, 2/11]

Vector representation:
```
-1  2 -1  1  0
-1  0  0  1  2
 2 -1  0  0 -1
 0  0  1 -1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1390

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e⟩ => some ⟨a, b+2, c, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

-- R4: transfer d to c.
theorem d_to_c : ∀ k, ∀ c e, ⟨0, 0, c, k, e⟩ [fm]⊢* ⟨0, 0, c + k, 0, e⟩ := by
  intro k; induction' k with k ih
  · intro c e; exists 0
  · intro c e; step fm
    apply stepStar_trans (ih (c + 1) e); ring_nf; finish

-- R3,R1,R1 chain: C rounds.
-- (0, b+1, 2C, d, e+C) ⊢* (0, b+1+3C, 0, d+2C, e)
theorem r3r1r1_chain : ∀ C, ∀ b d e, ⟨0, b + 1, 2 * C, d, e + C⟩ [fm]⊢*
    ⟨0, b + 1 + 3 * C, 0, d + 2 * C, e⟩ := by
  intro C; induction' C with C ih
  · intro b d e; simp; exists 0
  · intro b d e
    rw [show 2 * (C + 1) = (2 * C) + 2 from by ring,
        show e + (C + 1) = (e + C) + 1 from by ring]
    step fm; step fm; step fm
    rw [show b + 1 + 2 + 1 = (b + 3) + 1 from by ring]
    apply stepStar_trans (ih (b + 3) (d + 2) e); ring_nf; finish

-- R3,R2,R2 chain: K rounds.
-- (0, K, 0, D, e+1) ⊢* (0, 0, 0, D+2K, e+1+3K)
theorem r3r2r2_chain : ∀ K, ∀ D e, ⟨0, K, 0, D, e + 1⟩ [fm]⊢*
    ⟨0, 0, 0, D + 2 * K, e + 1 + 3 * K⟩ := by
  intro K; induction' K with K ih
  · intro D e; simp; exists 0
  · intro D e
    rw [show (K + 1 : ℕ) = K + 1 from rfl]
    step fm; step fm; step fm
    rw [show e + 2 + 2 = (e + 3) + 1 from by ring]
    apply stepStar_trans (ih (D + 2) (e + 3)); ring_nf; finish

-- Main transition: (0, 0, 2C+1, 0, C+F+2) ⊢⁺ (0, 0, 8C+5, 0, 9C+F+7)
theorem main_trans (C F : ℕ) :
    ⟨0, 0, 2 * C + 1, 0, C + F + 2⟩ [fm]⊢⁺ ⟨0, 0, 8 * C + 5, 0, 9 * C + F + 7⟩ := by
  -- Opening: R5, R1
  rw [show C + F + 2 = (C + F + 1) + 1 from by ring,
      show 2 * C + 1 = (2 * C) + 1 from by ring]
  step fm; step fm
  -- After opening: (0, 2, 2*C, 1, C+F+1)
  -- Phase 1: R3R1R1 chain (C rounds)
  -- Need: (0, b+1, 2C, d, e+C) with b+1=2, d=1, e+C=C+F+1 => e=F+1
  rw [show (2 : ℕ) = 0 + 1 + 1 from by ring,
      show C + F + 1 = (F + 1) + C from by ring]
  apply stepStar_trans (r3r1r1_chain C (0 + 1) 1 (F + 1))
  -- After: (0, 0+1+1+3C, 0, 1+2C, F+1)
  -- Phase 2: R3R2R2 chain (2+3C rounds)
  -- Need: (0, K, 0, D, e+1) with K=2+3C, D=1+2C, e+1=F+1 => e=F
  rw [show 0 + 1 + 1 + 3 * C = 3 * C + 2 from by ring,
      show 1 + 2 * C = 2 * C + 1 from by ring]
  apply stepStar_trans (r3r2r2_chain (3 * C + 2) (2 * C + 1) F)
  -- After: (0, 0, 0, 2C+1+2(3C+2), F+1+3(3C+2))
  -- Phase 3: d_to_c
  rw [show 2 * C + 1 + 2 * (3 * C + 2) = 8 * C + 5 from by ring,
      show F + 1 + 3 * (3 * C + 2) = 9 * C + F + 7 from by ring]
  apply stepStar_trans (d_to_c (8 * C + 5) 0 (9 * C + F + 7))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 1, 0, 2⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨0, 0, 2 * p.1 + 1, 0, p.1 + p.2 + 2⟩) ⟨0, 0⟩
  intro ⟨C, F⟩
  exact ⟨⟨4 * C + 2, 5 * C + F + 3⟩, by
    show ⟨0, 0, 2 * C + 1, 0, C + F + 2⟩ [fm]⊢⁺
      ⟨0, 0, 2 * (4 * C + 2) + 1, 0, (4 * C + 2) + (5 * C + F + 3) + 2⟩
    rw [show 2 * (4 * C + 2) + 1 = 8 * C + 5 from by ring,
        show (4 * C + 2) + (5 * C + F + 3) + 2 = 9 * C + F + 7 from by ring]
    exact main_trans C F⟩

end Sz22_2003_unofficial_1390
