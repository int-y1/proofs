import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #740: [35/6, 4/55, 1573/2, 3/7, 14/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  2  1
 0  1  0 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_740

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 2) (f + 1))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem r2_chain : ∀ k, ∀ a c d e f, ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e f)
    ring_nf; finish

theorem interleaved : ∀ n, ∀ c d e f,
    ⟨1, n + 1, c, d, e + c + n + 1, f⟩ [fm]⊢* ⟨n + 2 + 2 * c, 0, 0, d + n + 1, e, f⟩ := by
  intro n; induction' n using Nat.strongRecOn with n ih; intro c d e f
  rcases n with _ | n
  · rw [show e + c + 0 + 1 = e + (c + 1) from by ring]
    step fm
    have key := r2_chain (c + 1) 0 0 (d + 1) e f
    convert key using 2
    all_goals ring_nf
  · rw [show n + 1 + 1 = (n + 1) + 1 from by ring,
        show e + c + (n + 1) + 1 = (e + c + n + 1) + 1 from by ring]
    step fm; step fm; step fm
    rcases n with _ | n
    · rw [show e + c + 0 + 1 = e + (c + 1) from by ring]
      step fm
      have key := r2_chain c 3 0 (d + 1 + 1) e f
      rw [show e + c = Nat.add e c from rfl] at key
      convert key using 2
      all_goals ring_nf
    · have key := ih n (by omega) (c + 1) (d + 2) e f
      rw [show e + (c + 1) + n + 1 = e + c + (n + 1) + 1 from by ring,
          show d + 2 = d + 1 + 1 from by ring] at key
      convert key using 2
      all_goals ring_nf

theorem main_trans_succ (n e f : ℕ) :
    ⟨0, 0, 0, n + 1, e + n + 1, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 2, e + 2 * n + 4, f + n + 2⟩ := by
  -- Phase 1: R4 x (n+1): (0, 0, 0, n+1, e+n+1, f+1) -> (0, n+1, 0, 0, e+n+1, f+1)
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 0 + (n + 1), e + n + 1, f + 1⟩ = some ⟨0, 1, 0, n, e + n + 1, f + 1⟩
    simp [fm]
  have h1 := r4_chain n 1 0 (e + n + 1) (f + 1)
  rw [show (0 : ℕ) + n = n from by ring] at h1
  apply stepStar_trans h1
  -- Phase 2: R5: (0, n+1, 0, 0, e+n+1, f+1) -> (1, n+1, 0, 1, e+n+1, f)
  rw [show 1 + n = n + 1 from by ring]
  step fm
  -- Phase 3: Interleaved: (1, n+1, 0, 1, e+n+1, f) -> (n+2, 0, 0, n+2, e, f)
  rw [show e + n + 1 = e + 0 + n + 1 from by ring]
  apply stepStar_trans (interleaved n 0 1 e f)
  -- Phase 4: R3 x (n+2): (n+2, 0, 0, n+2, e, f) -> (0, 0, 0, n+2, e+2(n+2), f+(n+2))
  rw [show n + 2 + 2 * 0 = n + 2 from by ring,
      show 1 + n + 1 = n + 2 from by ring]
  have h2 := r3_chain (n + 2) 0 (n + 2) e f
  convert h2 using 2
  all_goals ring_nf

theorem main_trans (n e f : ℕ) :
    ⟨0, 0, 0, n, e + n, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 1, e + 2 * n + 2, f + n + 1⟩ := by
  rcases n with _ | n
  · apply step_stepStar_stepPlus
    · show fm ⟨0, 0, 0, 0, e, f + 1⟩ = some ⟨1, 0, 0, 1, e, f⟩; simp [fm]
    step fm
    ring_nf; finish
  · exact main_trans_succ n e f

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 0, 2, 1⟩) (by execute fm 1)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨n, e, f⟩ ↦ ⟨0, 0, 0, n, e + n, f + 1⟩) ⟨0, 2, 0⟩
  intro ⟨n, e, f⟩
  refine ⟨⟨n + 1, e + n + 1, f + n⟩, ?_⟩
  show ⟨0, 0, 0, n, e + n, f + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, n + 1, (e + n + 1) + (n + 1), (f + n) + 1⟩
  have key := main_trans n e f
  convert key using 2
  ring_nf

end Sz22_2003_unofficial_740
