import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #733: [35/6, 4/55, 143/2, 3/7, 42/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_733

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d+1, e, f⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · step fm
    apply stepStar_trans (ih (b + 1) e f)
    ring_nf; finish

theorem r211_chain : ∀ k, ∀ c d e f,
    ⟨0, 2 * k, c + 1, d, e + k, f⟩ [fm]⊢* ⟨0, 0, c + k + 1, d + 2 * k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro c d e f
  · exists 0
  · rw [show 2 * (k + 1) = (2 * k) + 2 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c + 1) (d + 2) e f)
    ring_nf; finish

theorem r32_chain : ∀ k, ∀ a d f,
    ⟨a + 2, 0, k, d, 0, f⟩ [fm]⊢* ⟨a + k + 2, 0, 0, d, 0, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d f
  · exists 0
  · step fm; step fm
    apply stepStar_trans (ih (a + 1) d (f + 1))
    ring_nf; finish

theorem r3_drain : ∀ k, ∀ d e f, ⟨k, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · step fm
    apply stepStar_trans (ih d (e + 1) (f + 1))
    ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 2 * n, n + 1, n * n + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * n + 2, n + 2, n * n + 2 * n + 2⟩ := by
  -- Phase 1: R4 chain
  apply stepStar_stepPlus_stepPlus (r4_chain (2 * n) 0 (n + 1) (n * n + 1))
  -- goal: (0, 0+2n, 0, 0, n+1, n^2+1) ⊢⁺ target
  -- Phase 2: R5 step
  rw [show (0 : ℕ) + 2 * n = 2 * n from by ring,
      show n * n + 1 = (n * n) + 1 from by ring]
  apply step_stepStar_stepPlus
    (show fm ⟨0, 2 * n, 0, 0, n + 1, (n * n) + 1⟩ = some ⟨1, (2 * n) + 1, 0, 1, n + 1, n * n⟩
     from by simp [fm])
  -- goal: (1, 2n+1, 0, 1, n+1, n^2) ⊢* target
  -- Phase 3: R1 step
  apply stepStar_trans
    (step_stepStar (show fm ⟨1, (2 * n) + 1, 0, 1, n + 1, n * n⟩ =
      some ⟨0, 2 * n, 1, 2, n + 1, n * n⟩ from by simp [fm]))
  -- goal: (0, 2n, 1, 2, n+1, n^2) ⊢* target
  -- Phase 4: R2,R1,R1 chain (n rounds)
  rw [show n + 1 = 1 + n from by ring]
  apply stepStar_trans (r211_chain n 0 2 1 (n * n))
  -- goal: (0, 0, 0+n+1, 2+2n, 1, n^2) ⊢* target
  rw [show 0 + n + 1 = n + 1 from by ring,
      show 2 + 2 * n = 2 * n + 2 from by ring]
  -- Phase 5: R2 step
  apply stepStar_trans
    (step_stepStar (show fm ⟨0, 0, n + 1, 2 * n + 2, 1, n * n⟩ =
      some ⟨2, 0, n, 2 * n + 2, 0, n * n⟩ from by
      rw [show n + 1 = (n) + 1 from rfl, show (1 : ℕ) = 0 + 1 from rfl]; simp [fm]))
  -- Phase 6: R3,R2 alternating chain (n rounds)
  apply stepStar_trans (r32_chain n 0 (2 * n + 2) (n * n))
  -- goal: (0+n+2, 0, 0, 2n+2, 0, n^2+n) ⊢* target
  rw [show 0 + n + 2 = n + 2 from by ring]
  -- Phase 7: R3 drain (n+2 rounds)
  have h7 := r3_drain (n + 2) (2 * n + 2) 0 (n * n + n)
  convert h7 using 2
  all_goals ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 2, 2⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 2 * n + 2, n + 2, (n + 1) * (n + 1) + 1⟩) 0
  intro n; refine ⟨n + 1, ?_⟩
  have h := main_trans (n + 1)
  convert h using 2
  all_goals ring_nf

end Sz22_2003_unofficial_733
