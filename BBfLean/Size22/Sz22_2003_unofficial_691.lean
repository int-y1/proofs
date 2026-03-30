import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #691: [35/6, 4/55, 11/2, 3/7, 56/11]

Vector representation:
```
-1 -1  1  1  0
 2  0 -1  0 -1
-1  0  0  0  1
 0  1  0 -1  0
 3  0  0  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_691

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+3, b, c, d+1, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a d e, ⟨a, 0, k, d, e + k⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) d e)
    ring_nf; finish

theorem full_phase : ∀ b, ∀ c d E, ⟨0, b, c + 1, d, E + c + b + 1⟩ [fm]⊢* ⟨2 * c + b + 2, 0, 0, d + b, E⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih; intro c d E
  rcases b with _ | _ | b
  · -- b = 0: R2 chain drains c+1
    have key := r2_chain (c + 1) 0 d E
    convert key using 2; ring_nf
  · -- b = 1: R2, R1, then R2 chain
    rw [show E + c + 1 + 1 = (E + c + 1) + 1 from by ring]
    step fm; step fm
    have key := r2_chain (c + 1) 1 (d + 1) E
    have h1 : ⟨1, 0, c + 1, d + 1, E + c + 1⟩ [fm]⊢* ⟨1 + 2 * (c + 1), 0, 0, d + 1, E⟩ := by
      convert key using 2
    apply stepStar_trans h1
    ring_nf; finish
  · -- b = b + 2: R2, R1, R1 (one round), then IH with b
    rw [show E + c + (b + 2) + 1 = (E + c + b + 2) + 1 from by ring]
    step fm
    rw [show (b + 2 : ℕ) = (b + 1) + 1 from by ring]
    step fm; step fm
    have key := ih b (by omega) (c + 1) (d + 2) E
    have h1 : ⟨0, b, c + 1 + 1, d + 2, E + c + b + 2⟩ [fm]⊢* ⟨2 * (c + 1) + b + 2, 0, 0, d + 2 + b, E⟩ := by
      convert key using 2; ring_nf
    apply stepStar_trans h1
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n + 3, 0, 0, n + 1, n⟩ [fm]⊢⁺ ⟨n + 4, 0, 0, n + 2, n + 1⟩ := by
  rcases n with _ | _ | n
  · step fm; step fm; step fm; step fm; step fm; step fm; step fm; finish
  · step fm; step fm; step fm; step fm; step fm
    step fm; step fm; step fm; step fm; step fm; step fm; finish
  · have phase1 : ⟨n + 5, 0, 0, n + 3, n + 2⟩ [fm]⊢* ⟨0, 0, 0, n + 3, 2 * n + 7⟩ := by
      have := r3_chain (n + 5) 0 (n + 3) (n + 2)
      convert this using 2; ring_nf
    have phase2 : ⟨0, 0, 0, n + 3, 2 * n + 7⟩ [fm]⊢* ⟨0, n + 3, 0, 0, 2 * n + 7⟩ := by
      rw [show n + 3 = 0 + (n + 3) from by ring]
      exact r4_chain (n + 3) 0 0 (2 * n + 7)
    have phase3 : ⟨0, n + 3, 0, 0, 2 * n + 7⟩ [fm]⊢⁺ ⟨3, n + 3, 0, 1, 2 * n + 6⟩ := by
      rw [show 2 * n + 7 = (2 * n + 6) + 1 from by ring]
      step fm; finish
    have phase4 : ⟨3, n + 3, 0, 1, 2 * n + 6⟩ [fm]⊢* ⟨0, n, 3, 4, 2 * n + 6⟩ := by
      rw [show n + 3 = (n + 2) + 1 from by ring]
      step fm
      rw [show n + 2 = (n + 1) + 1 from by ring]
      step fm
      rw [show n + 1 = n + 1 from rfl]
      step fm; finish
    have phase5 : ⟨0, n, 3, 4, 2 * n + 6⟩ [fm]⊢* ⟨n + 6, 0, 0, n + 4, n + 3⟩ := by
      rw [show (3 : ℕ) = 2 + 1 from rfl,
          show 2 * n + 6 = (n + 3) + 2 + n + 1 from by ring]
      apply stepStar_trans (full_phase n 2 4 (n + 3))
      ring_nf; finish
    exact stepStar_stepPlus_stepPlus phase1
      (stepStar_stepPlus_stepPlus phase2
        (stepPlus_stepStar_stepPlus phase3
          (stepStar_trans phase4 phase5)))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, 0⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 3, 0, 0, n + 1, n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_691
