import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1836: [9/10, 77/2, 52/21, 5/13, 39/11]

Vector representation:
```
-1  2 -1  0  0  0
-1  0  0  1  1  0
 2 -1  0 -1  0  1
 0  0  1  0  0 -1
 0  1  0  0 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1836

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b, c+1, d, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d+1, e+1, f⟩
  | ⟨a, b+1, c, d+1, e, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c+1, d, e, f⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b+1, c, d, e, f+1⟩
  | _ => none

-- R4 chain: (0,0,c,d,e,k) →* (0,0,c+k,d,e,0)
theorem f_to_c : ∀ k c d e, ⟨(0 : ℕ), 0, c, d, e, k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + k, d, e, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · step fm
    apply stepStar_trans (ih (c + 1) d e)
    ring_nf; finish

-- R3+R1+R1 chain: (0,b+1,2(g+1),d+g+1,e,f) →* (0,b+3(g+1)+1,0,d,e,f+g+1)
theorem r3r1r1_chain : ∀ g b d e f,
    ⟨(0 : ℕ), b + 1, 2 * (g + 1), d + g + 1, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), b + 3 * (g + 1) + 1, 0, d, e, f + g + 1⟩ := by
  intro g; induction' g with g ih <;> intro b d e f
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (g + 1 + 1) = 2 * (g + 1) + 1 + 1 from by ring,
        show d + (g + 1) + 1 = d + (g + 1) + 1 from rfl]
    step fm; step fm; step fm
    rw [show b + 2 + 2 = (b + 3) + 1 from by ring,
        show d + (g + 1) = d + g + 1 from by ring]
    apply stepStar_trans (ih (b + 3) d e (f + 1))
    ring_nf; finish

-- R5 + r3r1r1_chain: (0,0,2(g+1),d+g+2,e+1,0) →* (0,3(g+1)+1,0,d+1,e,g+2)
theorem spiral (g d e : ℕ) :
    ⟨(0 : ℕ), 0, 2 * (g + 1), d + g + 2, e + 1, 0⟩ [fm]⊢*
    ⟨(0 : ℕ), 3 * (g + 1) + 1, 0, d + 1, e, g + 2⟩ := by
  step fm
  rw [show d + g + 2 = (d + 1) + g + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain g 0 (d + 1) e 1)
  ring_nf; finish

-- R3+R2+R2 drain: (0,k,0,d+1,e,f) →* (0,0,0,d+k+1,e+2k,f+k)
theorem drain : ∀ k d e f,
    ⟨(0 : ℕ), k, 0, d + 1, e, f⟩ [fm]⊢*
    ⟨(0 : ℕ), 0, 0, d + k + 1, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · step fm; step fm; step fm
    rw [show d + 1 + 1 = (d + 1) + 1 from by ring]
    apply stepStar_trans (ih (d + 1) (e + 2) (f + 1))
    ring_nf; finish

-- C(D,E,G) = (0,0,0,D+G+2,E+1,2(G+1)) ⊢⁺ C(D+G+1,E+6G+7,2G+2)
theorem main_trans (D E G : ℕ) :
    ⟨(0 : ℕ), 0, 0, D + G + 2, E + 1, 2 * (G + 1)⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, D + 3 * G + 5, E + 6 * G + 8, 4 * G + 6⟩ := by
  rw [show 2 * (G + 1) = (2 * G + 1) + 1 from by ring]
  step fm
  apply stepStar_trans (f_to_c (2 * G + 1) 1 (D + G + 2) (E + 1))
  rw [show 1 + (2 * G + 1) = 2 * (G + 1) from by ring,
      show D + G + 2 = D + (G + 1) + 1 from by ring]
  rw [show D + (G + 1) + 1 = D + G + 2 from by ring]
  apply stepStar_trans (spiral G D E)
  rw [show D + 1 = D + 0 + 1 from by ring]
  apply stepStar_trans (drain (3 * (G + 1) + 1) (D + 0) E (G + 2))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2, 2⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨D, E, G⟩ ↦ ⟨0, 0, 0, D + G + 2, E + 1, 2 * (G + 1)⟩) ⟨0, 1, 0⟩
  intro ⟨D, E, G⟩
  refine ⟨⟨D + G + 1, E + 6 * G + 7, 2 * G + 2⟩, ?_⟩
  show ⟨(0 : ℕ), 0, 0, D + G + 2, E + 1, 2 * (G + 1)⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, 0, (D + G + 1) + (2 * G + 2) + 2, (E + 6 * G + 7) + 1, 2 * ((2 * G + 2) + 1)⟩
  rw [show (D + G + 1) + (2 * G + 2) + 2 = D + 3 * G + 5 from by ring,
      show (E + 6 * G + 7) + 1 = E + 6 * G + 8 from by ring,
      show 2 * ((2 * G + 2) + 1) = 4 * G + 6 from by ring]
  exact main_trans D E G
