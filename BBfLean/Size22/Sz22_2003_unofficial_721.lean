import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #721: [35/6, 4/55, 143/2, 3/7, 12/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 2  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_721

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+2, b+1, c, d, e, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 1))
    ring_nf; finish

theorem r2_chain_b0 : ∀ K, ∀ a c d e f, ⟨a, 0, c + K, d, e + K, f⟩ [fm]⊢* ⟨a + 2 * K, 0, c, d, e, f⟩ := by
  intro K; induction' K with K ih <;> intro a c d e f
  · exists 0
  · rw [show c + (K + 1) = (c + K) + 1 from by ring,
        show e + (K + 1) = (e + K) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e f)
    ring_nf; finish

theorem r2r1r1_cycle : ∀ k, ∀ c d e f, ⟨0, 2 * k, c + 1, d, e + k, f⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring,
        show c + 1 = (c) + 1 from by ring]
    step fm
    rw [show 2 * k + 1 = (2 * k) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem r2r1r1_cycle_odd : ∀ k, ∀ c d e f, ⟨0, 2 * k + 1, c + 1, d, e + k + 1, f⟩ [fm]⊢* ⟨1, 0, c + k + 1, d + 2 * k + 1, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · step fm; step fm; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring,
        show c + 1 = (c) + 1 from by ring]
    step fm
    rw [show 2 * k + 2 = (2 * k + 1) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem main_trans_odd (k f : ℕ) :
    ⟨0, 0, 0, 2 * k + 1, 4 * k + 3, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 2, 4 * k + 5, f + 2 * k + 4⟩ := by
  rw [show 2 * k + 1 = 0 + (2 * k + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * k + 1) 0 0 (4 * k + 3) (f + 1))
  rw [show 0 + (2 * k + 1) = (2 * k) + 1 from by ring,
      show f + 1 = f + 1 from rfl]
  apply step_stepStar_stepPlus
  · show fm ⟨0, (2 * k) + 1, 0, 0, 4 * k + 3, f + 1⟩ = some ⟨2, (2 * k) + 1 + 1, 0, 0, 4 * k + 3, f⟩
    simp [fm]
  rw [show (2 * k) + 1 + 1 = (2 * k + 1) + 1 from by ring]
  step fm; step fm
  rw [show 2 * k + 1 = (2 * k) + 1 from by ring,
      show 4 * k + 3 = (3 * k + 3) + k from by ring]
  apply stepStar_trans (r2r1r1_cycle k 1 2 (3 * k + 3) f)
  rw [show 1 + k + 1 = 0 + (k + 2) from by ring,
      show 3 * k + 3 = (2 * k + 1) + (k + 2) from by ring,
      show 2 + 2 * k = 2 * k + 2 from by ring]
  apply stepStar_trans (r2_chain_b0 (k + 2) 0 0 (2 * k + 2) (2 * k + 1) f)
  rw [show 0 + 2 * (k + 2) = 0 + (2 * k + 4) from by ring]
  apply stepStar_trans (r3_chain (2 * k + 4) 0 (2 * k + 2) (2 * k + 1) f)
  ring_nf; finish

theorem main_trans_even (k f : ℕ) :
    ⟨0, 0, 0, 2 * k + 2, 4 * k + 5, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * k + 3, 4 * k + 7, f + 2 * k + 5⟩ := by
  rw [show 2 * k + 2 = 0 + (2 * k + 2) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * k + 2) 0 0 (4 * k + 5) (f + 1))
  rw [show 0 + (2 * k + 2) = (2 * k + 1) + 1 from by ring,
      show f + 1 = f + 1 from rfl]
  apply step_stepStar_stepPlus
  · show fm ⟨0, (2 * k + 1) + 1, 0, 0, 4 * k + 5, f + 1⟩ = some ⟨2, (2 * k + 1) + 1 + 1, 0, 0, 4 * k + 5, f⟩
    simp [fm]
  rw [show (2 * k + 1) + 1 + 1 = (2 * k + 2) + 1 from by ring]
  step fm; step fm
  rw [show 2 * k + 2 = 2 * k + 1 + 1 from by ring,
      show 4 * k + 5 = (3 * k + 4) + (k + 1) from by ring]
  apply stepStar_trans (r2r1r1_cycle_odd k 1 2 (3 * k + 4) f)
  rw [show 1 + k + 1 = 0 + (k + 2) from by ring,
      show 3 * k + 4 = (2 * k + 2) + (k + 2) from by ring,
      show 2 + 2 * k + 1 = 2 * k + 3 from by ring]
  apply stepStar_trans (r2_chain_b0 (k + 2) 1 0 (2 * k + 3) (2 * k + 2) f)
  rw [show 1 + 2 * (k + 2) = 0 + (2 * k + 5) from by ring]
  apply stepStar_trans (r3_chain (2 * k + 5) 0 (2 * k + 3) (2 * k + 2) f)
  ring_nf; finish

theorem main_trans (n f : ℕ) :
    ⟨0, 0, 0, n + 1, 2 * n + 3, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 2, 2 * n + 5, f + n + 4⟩ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show k + k = 2 * k from by ring] at hk; subst hk
    convert main_trans_odd k f using 2; ring_nf
  · subst hk
    convert main_trans_even k f using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3, 3⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, f⟩ ↦ ⟨0, 0, 0, n + 1, 2 * n + 3, f + 1⟩) ⟨0, 2⟩
  intro ⟨n, f⟩; exact ⟨⟨n + 1, f + n + 3⟩, main_trans n f⟩

end Sz22_2003_unofficial_721
