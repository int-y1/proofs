import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1897: [9/35, 65/33, 14/3, 11/13, 117/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  1  0  0
 0  0  0  0  1 -1
-1  2  0  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1897

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+2, c, d, e, f+1⟩
  | _ => none

-- R2/R1 interleaving: e rounds
theorem r2r1_chain : ∀ e, ∀ a b d f,
    ⟨a, b + 2, 0, d + e, e, f + 1⟩ [fm]⊢* ⟨a, b + e + 2, 0, d, 0, f + e + 1⟩ := by
  intro e; induction' e with e ih <;> intro a b d f
  · exists 0
  · rw [show d + (e + 1) = d + e + 1 from by ring]
    step fm -- R2
    step fm -- R1
    rw [show (a, b + 1 + 2, 0, d + e, e, f + 1 + 1) =
        (a, (b + 1) + 2, 0, d + e, e, (f + 1) + 1) from by ring_nf]
    apply stepStar_trans (ih a (b + 1) d (f + 1))
    ring_nf; finish

-- R3 chain: drain b into a and d
theorem r3_chain : ∀ b, ∀ a d f,
    ⟨a, b, 0, d, 0, f⟩ [fm]⊢* ⟨a + b, 0, 0, d + b, 0, f⟩ := by
  intro b; induction' b with b ih <;> intro a d f
  · exists 0
  · step fm -- R3
    apply stepStar_trans (ih (a + 1) (d + 1) f)
    ring_nf; finish

-- R4 chain: move f to e
theorem f_to_e : ∀ f, ∀ a d e,
    ⟨a, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + f, 0⟩ := by
  intro f; induction' f with f ih <;> intro a d e
  · exists 0
  · step fm -- R4
    apply stepStar_trans (ih a d (e + 1))
    ring_nf; finish

-- Main transition: (a+1, 0, 0, d+e, e, 0) →⁺ (a+e+2, 0, 0, d+e+2, e+1, 0)
theorem main_trans : ∀ a d e,
    ⟨a + 1, 0, 0, d + e, e, 0⟩ [fm]⊢⁺ ⟨a + e + 2, 0, 0, d + e + 2, e + 1, 0⟩ := by
  intro a d e
  step fm -- R5: (a, 2, 0, d+e, e, 1)
  apply stepStar_trans (r2r1_chain e a 0 d 0)
  rw [show 0 + e + 2 = e + 2 from by ring, show 0 + e + 1 = e + 1 from by ring]
  apply stepStar_trans (r3_chain (e + 2) a d (e + 1))
  apply stepStar_trans (f_to_e (e + 1) (a + (e + 2)) (d + (e + 2)) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d e, q = ⟨a + 1, 0, 0, d + e, e, 0⟩)
  · intro c ⟨a, d, e, hq⟩; subst hq
    exact ⟨⟨a + e + 2, 0, 0, d + e + 2, e + 1, 0⟩,
      ⟨a + e + 1, d + 1, e + 1, by ring_nf⟩,
      main_trans a d e⟩
  · exact ⟨0, 0, 0, by rfl⟩
