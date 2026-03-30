import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1067: [5/6, 1/35, 44/5, 7/2, 3/77, 5/7]

Vector representation:
```
-1 -1  1  0  0
 0  0 -1 -1  0
 2  0 -1  0  1
-1  0  0  1  0
 0  1  0 -1 -1
 0  0  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1067

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | _ => none

private theorem r4_drain : ∀ k, ∀ d e,
    ⟨k, (0 : ℕ), 0, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm; exact ih (d + 1) e

private theorem r5_drain : ∀ k, ∀ b d,
    ⟨(0 : ℕ), b, 0, d + k, k⟩ [fm]⊢* ⟨0, b + k, 0, d, 0⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · ring_nf; finish
  · rw [show d + (k + 1) = (d + k) + 1 from by ring,
        show b + (k + 1) = (b + 1) + k from by ring]
    step fm; exact ih (b + 1) d

private theorem r1r1r3_chain : ∀ k, ∀ B C E,
    ⟨(2 : ℕ), B + 2 * k, C, 0, E⟩ [fm]⊢* ⟨2, B, C + k, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro B C E
  · ring_nf; finish
  · rw [show B + 2 * (k + 1) = (B + 2 * k) + 2 from by ring,
        show C + (k + 1) = (C + 1) + k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    have h1 : ⟨(2 : ℕ), (B + 2 * k) + 2, C, 0, E⟩ [fm]⊢*
              ⟨2, B + 2 * k, C + 1, 0, E + 1⟩ := by
      step fm; step fm; step fm; ring_nf; finish
    exact stepStar_trans h1 (ih B (C + 1) (E + 1))

private theorem r3_drain : ∀ k, ∀ a E,
    ⟨a, (0 : ℕ), k, 0, E⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro a E
  · ring_nf; finish
  · rw [show a + 2 * (k + 1) = (a + 2) + 2 * k from by ring,
        show E + (k + 1) = (E + 1) + k from by ring]
    step fm; exact ih (a + 2) (E + 1)

private theorem main_trans (e : ℕ) :
    ⟨e + 1, (0 : ℕ), 0, 0, e⟩ [fm]⊢⁺ ⟨e + 2, 0, 0, 0, e + 1⟩ := by
  apply stepStar_stepPlus_stepPlus
  · exact r4_drain (e + 1) 0 e
  rw [show (0 : ℕ) + (e + 1) = 1 + e from by ring]
  apply stepStar_stepPlus_stepPlus
  · exact r5_drain e 0 1
  rw [show (0 : ℕ) + e = e from by ring]
  step fm; step fm
  rcases Nat.even_or_odd e with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- e = K + K (even)
    subst hK
    rw [show K + K = 0 + 2 * K from by ring]
    apply stepStar_trans (r1r1r3_chain K 0 0 1)
    rw [show (0 : ℕ) + K = K from by ring]
    apply stepStar_trans (r3_drain K 2 (1 + K))
    ring_nf; finish
  · -- e = 2 * K + 1 (odd)
    subst hK
    rw [show 2 * K + 1 = 1 + 2 * K from by ring]
    apply stepStar_trans (r1r1r3_chain K 1 0 1)
    rw [show (0 : ℕ) + K = K from by ring]
    step fm
    apply stepStar_trans (r3_drain (K + 1) 1 (1 + K))
    ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun e ↦ ⟨e + 1, 0, 0, 0, e⟩) 1
  intro e; exists e + 1; exact main_trans e

end Sz22_2003_unofficial_1067
