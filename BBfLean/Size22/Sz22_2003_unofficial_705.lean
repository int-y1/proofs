import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #705: [35/6, 4/55, 121/2, 3/7, 30/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  1  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_705

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c+1, d, e⟩
  | _ => none

theorem r4_chain : ∀ k b e, ⟨0, b, 0, k, e⟩ [fm]⊢* ⟨0, b + k, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro b e
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e)
    ring_nf; finish

theorem r3_chain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2))
    ring_nf; finish

theorem r2_chain : ∀ k a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem zigzag_even : ∀ k c d e, ⟨0, 2 * k, c + 1, d, e + k⟩ [fm]⊢*
    ⟨0, 0, c + k + 1, d + 2 * k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem zigzag_odd : ∀ k c d e, ⟨0, 2 * k + 1, c + 1, d, e + k + 1⟩ [fm]⊢*
    ⟨1, 0, c + k + 1, d + 2 * k + 1, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e)
    ring_nf; finish

theorem phase_even (k e : ℕ) :
    ⟨0, 2 * k + 1, 0, 0, e + 2 * k + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 2, e + 4 * k + 10⟩ := by
  rw [show e + 2 * k + 4 = (e + k + 3) + (k + 1) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * k + 1, 0, 0, (e + k + 3) + (k + 1)⟩ = some ⟨1, 2 * k + 2, 1, 0, (e + k + 3) + k⟩
    simp [fm]
  rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
  step fm
  rw [show e + k + 3 + k = (e + k + 2) + (k + 1) from by ring]
  apply stepStar_trans (zigzag_odd k 1 1 (e + k + 2))
  rw [show 1 + k + 1 = k + 2 from by ring,
      show 1 + 2 * k + 1 = 2 * k + 2 from by ring,
      show e + k + 2 = e + (k + 2) from by ring]
  apply stepStar_trans (r2_chain (k + 2) 1 (2 * k + 2) e)
  rw [show 1 + 2 * (k + 2) = 2 * k + 5 from by ring,
      show 2 * k + 5 = 0 + (2 * k + 5) from by ring]
  apply stepStar_trans (r3_chain (2 * k + 5) 0 (2 * k + 2) e)
  ring_nf; finish

theorem phase_odd (k e : ℕ) :
    ⟨0, 2 * k + 2, 0, 0, e + 2 * k + 5⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 3, e + 4 * k + 12⟩ := by
  rw [show e + 2 * k + 5 = (e + k + 3) + (k + 2) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 2 * k + 2, 0, 0, (e + k + 3) + (k + 2)⟩ = some ⟨1, 2 * k + 3, 1, 0, (e + k + 3) + (k + 1)⟩
    simp [fm]
  rw [show 2 * k + 3 = (2 * k + 2) + 1 from by ring]
  step fm
  rw [show e + k + 3 + (k + 1) = (e + k + 3) + (k + 1) from by ring,
      show 2 * k + 2 = 2 * (k + 1) from by ring]
  apply stepStar_trans (zigzag_even (k + 1) 1 1 (e + k + 3))
  rw [show 1 + (k + 1) + 1 = k + 3 from by ring,
      show 1 + 2 * (k + 1) = 2 * k + 3 from by ring,
      show e + k + 3 = e + (k + 3) from by ring]
  apply stepStar_trans (r2_chain (k + 3) 0 (2 * k + 3) e)
  rw [show 0 + 2 * (k + 3) = 2 * k + 6 from by ring,
      show 2 * k + 6 = 0 + (2 * k + 6) from by ring]
  apply stepStar_trans (r3_chain (2 * k + 6) 0 (2 * k + 3) e)
  ring_nf; finish

theorem main_trans (n e : ℕ) :
    ⟨0, 0, 0, n + 1, e + n + 4⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 2, e + 2 * n + 10⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    apply stepStar_stepPlus_stepPlus (r4_chain (2 * k + 1) 0 (e + 2 * k + 4))
    convert phase_even k e using 2
    ring_nf
  · subst hk
    rw [show e + (2 * k + 1) + 4 = e + 2 * k + 5 from by ring,
        show e + 2 * (2 * k + 1) + 10 = e + 4 * k + 12 from by ring]
    apply stepStar_stepPlus_stepPlus (r4_chain (2 * k + 2) 0 (e + 2 * k + 5))
    convert phase_odd k e using 2
    ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 7⟩) (by execute fm 9)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨0, 0, 0, n + 1, e + n + 4⟩) ⟨0, 3⟩
  intro ⟨n, e⟩
  refine ⟨⟨n + 1, e + n + 5⟩, ?_⟩
  convert main_trans n e using 2
  ring_nf

end Sz22_2003_unofficial_705
