import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1896: [9/35, 65/33, 1274/3, 11/13, 3/2]

Vector representation:
```
 0  2 -1 -1  0  0
 0 -1  1  0 -1  1
 1 -1  0  2  0  1
 0  0  0  0  1 -1
-1  1  0  0  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1896

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e, f⟩
  | ⟨a, b+1, c, d, e+1, f⟩ => some ⟨a, b, c+1, d, e, f+1⟩
  | ⟨a, b+1, c, d, e, f⟩ => some ⟨a+1, b, c, d+2, e, f+1⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a, b, c, d, e+1, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | _ => none

theorem f_to_e : ∀ k, ∀ e, ⟨a, 0, 0, d, e, f + k⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f⟩ := by
  intro k; induction' k with k ih <;> intro e
  · exists 0
  · rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (ih (e + 1))
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ a d f, ⟨a, b + k, 0, d, 0, f⟩ [fm]⊢* ⟨a + k, b, 0, d + 2 * k, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · rw [← Nat.add_assoc]
    step fm
    apply stepStar_trans (ih (a + 1) (d + 2) (f + 1))
    ring_nf; finish

theorem r2r1_chain : ∀ e, ∀ b d f, ⟨a, b + 1, 0, d + e, e, f⟩ [fm]⊢* ⟨a, b + e + 1, 0, d, 0, f + e⟩ := by
  intro e; induction' e with e ih <;> intro b d f
  · exists 0
  · rw [show d + (e + 1) = (d + e) + 1 from by ring]
    step fm
    step fm
    rw [show b + 1 + 1 = (b + 1) + 1 from by ring]
    apply stepStar_trans (ih (b + 1) d (f + 1))
    ring_nf; finish

theorem main_trans : ⟨G + 1, 0, 0, G + 2 * n + 2, G + n + 1, 0⟩ [fm]⊢⁺
    ⟨2 * G + n + 2, 0, 0, 2 * G + 3 * n + 5, 2 * G + 2 * n + 3, 0⟩ := by
  step fm
  rw [show G + 2 * n + 2 = (n + 1) + (G + n + 1) from by ring]
  apply stepStar_trans (r2r1_chain (G + n + 1) (a := G) 0 (n + 1) 0)
  rw [show 0 + (G + n + 1) + 1 = G + n + 2 from by ring,
      show 0 + (G + n + 1) = G + n + 1 from by ring]
  rw [show G + n + 2 = 0 + (G + n + 2) from by ring]
  apply stepStar_trans (r3_drain (G + n + 2) (b := 0) G (n + 1) (G + n + 1))
  rw [show G + (G + n + 2) = 2 * G + n + 2 from by ring,
      show (n + 1) + 2 * (G + n + 2) = 2 * G + 3 * n + 5 from by ring,
      show (G + n + 1) + (G + n + 2) = 2 * G + 2 * n + 3 from by ring]
  rw [show (2 * G + 2 * n + 3) = 0 + (2 * G + 2 * n + 3) from by ring]
  apply stepStar_trans (f_to_e (2 * G + 2 * n + 3) (a := 2 * G + n + 2) (d := 2 * G + 3 * n + 5) 0)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 2, 1, 0⟩) (by execute fm 3)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, G⟩ ↦ ⟨G + 1, 0, 0, G + 2 * n + 2, G + n + 1, 0⟩) ⟨0, 0⟩
  intro ⟨n, G⟩
  refine ⟨⟨n + 1, 2 * G + n + 1⟩, ?_⟩
  show ⟨G + 1, 0, 0, G + 2 * n + 2, G + n + 1, 0⟩ [fm]⊢⁺
    ⟨(2 * G + n + 1) + 1, 0, 0, (2 * G + n + 1) + 2 * (n + 1) + 2,
     (2 * G + n + 1) + (n + 1) + 1, 0⟩
  rw [show (2 * G + n + 1) + 1 = 2 * G + n + 2 from by ring,
      show (2 * G + n + 1) + 2 * (n + 1) + 2 = 2 * G + 3 * n + 5 from by ring,
      show (2 * G + n + 1) + (n + 1) + 1 = 2 * G + 2 * n + 3 from by ring]
  exact main_trans
