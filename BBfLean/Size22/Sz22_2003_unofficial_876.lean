import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #876: [4/15, 1/3, 11319/2, 5/539, 3/7]

Vector representation:
```
 2 -1 -1  0  0
 0 -1  0  0  0
-1  1  0  3  1
 0  0  1 -2 -1
 0  1  0 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_876

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+3, e+1⟩
  | ⟨a, b, c, d+2, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | _ => none

-- R4 repeated: (0, 0, c, d+2k, k) →* (0, 0, c+k, d, 0)
theorem r4_drain : ∀ k c d, ⟨0, 0, c, d + 2 * k, k⟩ [fm]⊢* ⟨0, 0, c + k, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · exists 0
  · rw [show d + 2 * (k + 1) = (d + 2 * k) + 2 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    rw [show c + 1 = c + 1 from rfl]
    apply stepStar_trans (ih (c + 1) d)
    ring_nf; finish

-- R3+R1 chain: (a+1, 0, k, d, e) →* (a+1+k, 0, 0, d+3k, e+k)
theorem r3r1_chain : ∀ k a d e, ⟨a + 1, 0, k, d, e⟩ [fm]⊢* ⟨a + 1 + k, 0, 0, d + 3 * k, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a + 1) (d + 3) (e + 1))
    ring_nf; finish

-- R3+R2 drain: (a, 0, 0, d, e) →* (0, 0, 0, d+3a, e+a)
theorem r3r2_drain : ∀ a d e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 3 * a, e + a⟩ := by
  intro a; induction' a with a ih <;> intro d e
  · exists 0
  · rw [show (a : ℕ) + 1 = a + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (d + 3) (e + 1))
    ring_nf; finish

-- Main transition: (0, 0, 0, d+2E+3, E+1) →⁺ (0, 0, 0, d+6E+6, 2E+2)
theorem main_trans (E d : ℕ) :
    ⟨0, 0, 0, d + 2 * E + 3, E + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, d + 6 * E + 6, 2 * E + 2⟩ := by
  -- Phase A: R4 drain (E+1 steps)
  apply stepStar_stepPlus_stepPlus
  · rw [show d + 2 * E + 3 = (d + 1) + 2 * (E + 1) from by ring]
    exact r4_drain (E + 1) 0 (d + 1)
  -- At (0, 0, 0+(E+1), d+1, 0) = (0, 0, E+1, d+1, 0)
  rw [show 0 + (E + 1) = E + 1 from by ring]
  -- Phase B: R5. (0, 0, E+1, d+1, 0). R5 matches since d+1 ≥ 1.
  step fm
  -- At (0, 1, E+1, d, 0). R1 fires (b=1, c=E+1≥1).
  step fm
  -- At (2, 0, E, d, 0)
  show ⟨2, 0, E, d, 0⟩ [fm]⊢* ⟨0, 0, 0, d + 6 * E + 6, 2 * E + 2⟩
  rw [show (2 : ℕ) = 1 + 1 from by ring]
  apply stepStar_trans (r3r1_chain E 1 d 0)
  rw [show 1 + 1 + E = E + 2 from by ring, show 0 + E = E from by ring]
  apply stepStar_trans (r3r2_drain (E + 2) (d + 3 * E) E)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 6, 2⟩)
  · show c₀ [fm]⊢* (0, 0, 0, 6, 2)
    unfold c₀
    execute fm 9
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, E⟩ ↦ ⟨0, 0, 0, d + 2 * E + 3, E + 1⟩) ⟨1, 1⟩
  intro ⟨d, E⟩
  refine ⟨⟨d + 2 * E + 1, 2 * E + 1⟩, ?_⟩
  show ⟨0, 0, 0, d + 2 * E + 3, E + 1⟩ [fm]⊢⁺
    ⟨0, 0, 0, (d + 2 * E + 1) + 2 * (2 * E + 1) + 3, (2 * E + 1) + 1⟩
  rw [show (d + 2 * E + 1) + 2 * (2 * E + 1) + 3 = d + 6 * E + 6 from by ring,
      show (2 * E + 1) + 1 = 2 * E + 2 from by ring]
  exact main_trans E d

end Sz22_2003_unofficial_876
