import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1184: [5/6, 49/2, 44/35, 9/11, 25/7]

Vector representation:
```
-1 -1  1  0  0
-1  0  0  2  0
 2  0 -1 -1  1
 0  2  0  0 -1
 0  0  2 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1184

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | _ => none

-- R4 repeated: (0, b, 0, d, e+k) →* (0, b+2*k, 0, d, e)
theorem e_to_b : ∀ k b d e, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + 2 * k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [Nat.add_succ e k]; step fm
    apply stepStar_trans (ih (b + 2) d e)
    ring_nf; finish

-- R3+R1+R1 interleaved
theorem interleaved : ∀ j c d e,
    ⟨0, 2 * j + 2, c + 1, d + j + 1, e⟩ [fm]⊢* ⟨0, 0, c + j + 2, d, e + j + 1⟩ := by
  intro j; induction' j with j ih <;> intro c d e
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show 2 * (j + 1) + 2 = (2 * j + 2) + 1 + 1 from by ring,
        show d + (j + 1) + 1 = (d + 1 + j) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 1 + j = d + j + 1 from by ring]
    apply stepStar_trans (ih (c + 1) d (e + 1))
    ring_nf; finish

-- R3+R2+R2 chain
theorem r3r2r2 : ∀ C d e, ⟨0, 0, C + 2, d + 1, e⟩ [fm]⊢* ⟨0, 0, 1, d + 3 * (C + 1) + 1, e + C + 1⟩ := by
  intro C; induction' C with C ih <;> intro d e
  · step fm; step fm; step fm; ring_nf; finish
  · rw [show (C + 1) + 2 = (C + 2) + 1 from by ring]
    step fm; step fm; step fm
    rw [show d + 2 + 2 = (d + 3) + 1 from by ring]
    apply stepStar_trans (ih (d + 3) (e + 1))
    ring_nf; finish

-- Final drain: (0, 0, 1, d+1, e) →⁺ (0, 0, 0, d+4, e+1)
theorem final_drain : ∀ d e, ⟨0, 0, 1, d + 1, e⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 4, e + 1⟩ := by
  intro d e; step fm; step fm; step fm; finish

-- E=0 case: (0, 0, 0, k+2, 0) →⁺ (0, 0, 0, k+7, 2)
theorem trans_E0 (k : ℕ) : ⟨0, 0, 0, k + 2, 0⟩ [fm]⊢⁺ ⟨0, 0, 0, k + 7, 2⟩ := by
  rw [show k + 2 = (k + 1) + 1 from by ring]
  step fm
  apply stepStar_trans
  · exact r3r2r2 0 k 0
  apply stepPlus_stepStar
  convert final_drain (k + 3) 1 using 2

-- E≥1 case
theorem trans_Esucc (k E : ℕ) : ⟨0, 0, 0, 2 * E + k + 4, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * E + k + 11, 2 * E + 4⟩ := by
  rw [show (E + 1 : ℕ) = 0 + (E + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (e_to_b (E + 1) 0 (2 * E + k + 4) 0)
  rw [show 0 + 2 * (E + 1) = 2 * E + 2 from by ring,
      show 2 * E + k + 4 = (2 * E + k + 3) + 1 from by ring]
  step fm
  -- Goal: (0, 2*E+2, 2, 2*E+k+3, 0) [fm]⊢* (0, 0, 0, 4*E+k+11, 2*E+4)
  apply stepStar_trans
  · rw [show (2 : ℕ) = 1 + 1 from by ring,
        show 2 * E + k + 3 = (E + k + 2) + E + 1 from by ring]
    exact interleaved E 1 (E + k + 2) 0
  -- Goal: (0, 0, 1+E+2, E+k+2, 0+E+1) [fm]⊢* target
  -- = (0, 0, 3+E, 2+E+k, 1+E) after ring_nf
  apply stepStar_trans
  · -- Need to convert (0, 0, 3+E, 2+E+k, 1+E) to (0, 0, (E+1)+2, (E+k+1)+1, E+1) for r3r2r2
    rw [show 1 + E + 2 = (E + 1) + 2 from by ring,
        show E + k + 2 = (E + k + 1) + 1 from by ring,
        show 0 + E + 1 = E + 1 from by ring]
    exact r3r2r2 (E + 1) (E + k + 1) (E + 1)
  -- Goal: (0, 0, 1, (E+k+1)+3*(E+2)+1, (E+1)+(E+1)+1) [fm]⊢* target
  apply stepPlus_stepStar
  convert final_drain (4 * E + k + 7) (2 * E + 3) using 2; ring_nf

-- Main transition
theorem main_trans (k E : ℕ) : ⟨0, 0, 0, 2 * E + k + 2, E⟩ [fm]⊢⁺ ⟨0, 0, 0, 4 * E + k + 7, 2 * E + 2⟩ := by
  rcases E with _ | E
  · convert trans_E0 k using 2; simp
  · convert trans_Esucc k E using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨k, E⟩ ↦ ⟨0, 0, 0, 2 * E + k + 2, E⟩) ⟨0, 0⟩
  intro ⟨k, E⟩
  exact ⟨⟨k + 1, 2 * E + 2⟩, by convert main_trans k E using 2; ring_nf⟩

end Sz22_2003_unofficial_1184
