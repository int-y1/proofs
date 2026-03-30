import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #770: [35/6, 52/55, 143/2, 3/7, 6/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  1
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_770

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e, f⟩
  | _ => none

theorem r3_chain : ∀ k d e f, ⟨k, 0, 0, d, e, f⟩ [fm]⊢* ⟨0, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro d e f
  · exists 0
  · rw [show e + (k + 1) = (e + 1) + k from by ring,
        show f + (k + 1) = (f + 1) + k from by ring]
    step fm
    exact ih d (e + 1) (f + 1)

theorem r4_chain : ∀ k b e f, ⟨0, b, 0, k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b e f
  · exists 0
  · rw [show b + (k + 1) = (b + 1) + k from by ring]
    step fm
    exact ih (b + 1) e f

private theorem gen_chain_aux : ∀ s a b c d e f, e + b ≤ s → b + c = e → a ≥ 1 →
    ⟨a, b, c, d, e, f⟩ [fm]⊢* ⟨a + b + 2 * c, 0, 0, d + b, 0, f + e⟩ := by
  intro s
  induction' s using Nat.strongRecOn with s IH
  intro a b c d e f hs hbc ha
  rcases b with _ | b
  · -- b = 0
    rcases e with _ | e
    · -- e = 0, c = 0
      have hc : c = 0 := by omega
      subst hc; exists 0
    · -- e + 1, c = e + 1
      have hc : c = e + 1 := by omega
      subst hc
      rw [show a + 0 + 2 * (e + 1) = (a + 2) + 0 + 2 * e from by ring,
          show d + 0 = d from by ring,
          show f + (e + 1) = (f + 1) + e from by ring]
      step fm
      exact IH (e + 0) (by omega) (a + 2) 0 e d e (f + 1) (by omega) (by omega) (by omega)
  · -- b + 1
    rcases e with _ | e
    · omega
    · -- e + 1
      rcases a with _ | _ | a
      · omega
      · -- a = 1
        rw [show 1 + (b + 1) + 2 * c = 2 + b + 2 * c from by ring,
            show d + (b + 1) = (d + 1) + b from by ring,
            show f + (e + 1) = (f + 1) + e from by ring]
        step fm; step fm
        exact IH (e + b) (by omega) 2 b c (d + 1) e (f + 1) (by omega) (by omega) (by omega)
      · -- a + 2
        rw [show (a + 2) + (b + 1) + 2 * c = (a + 1) + b + 2 * (c + 1) from by ring,
            show d + (b + 1) = (d + 1) + b from by ring,
            show f + (e + 1) = f + (e + 1) from rfl]
        step fm
        exact IH (e + 1 + b) (by omega) (a + 1) b (c + 1) (d + 1) (e + 1) f
          (by omega) (by omega) (by omega)

theorem gen_chain : ∀ a b c d e f, b + c = e → a ≥ 1 →
    ⟨a, b, c, d, e, f⟩ [fm]⊢* ⟨a + b + 2 * c, 0, 0, d + b, 0, f + e⟩ := by
  intro a b c d e f hbc ha
  exact gen_chain_aux (e + b) a b c d e f le_rfl hbc ha

theorem main_transition (n : ℕ) :
    ⟨n + 1, 0, 0, n, 0, n * n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 1, 0, (n + 1) * (n + 1)⟩ := by
  apply stepStar_stepPlus_stepPlus
  · show ⟨n + 1, 0, 0, n, 0, n * n⟩ [fm]⊢* ⟨0, 0, 0, n, 0 + (n + 1), n * n + (n + 1)⟩
    exact r3_chain (n + 1) n 0 (n * n)
  apply stepStar_stepPlus_stepPlus
  · show ⟨0, 0, 0, n, 0 + (n + 1), n * n + (n + 1)⟩ [fm]⊢*
        ⟨0, 0 + n, 0, 0, 0 + (n + 1), n * n + (n + 1)⟩
    exact r4_chain n 0 (0 + (n + 1)) (n * n + (n + 1))
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0 + n, 0, 0, 0 + (n + 1), n * n + (n + 1)⟩ =
        some ⟨1, 0 + n + 1, 0, 0, 0 + (n + 1), n * n + n⟩
    simp [fm]
  show ⟨1, 0 + n + 1, 0, 0, 0 + (n + 1), n * n + n⟩ [fm]⊢*
      ⟨n + 2, 0, 0, n + 1, 0, (n + 1) * (n + 1)⟩
  rw [show (0 : ℕ) + n + 1 = n + 1 from by omega,
      show (0 : ℕ) + (n + 1) = n + 1 from by omega]
  have h := gen_chain 1 (n + 1) 0 0 (n + 1) (n * n + n) (by omega) (by omega)
  rw [show 1 + (n + 1) + 2 * 0 = n + 2 from by ring,
      show (0 : ℕ) + (n + 1) = n + 1 from by ring,
      show n * n + n + (n + 1) = (n + 1) * (n + 1) from by ring] at h
  exact h

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, n, 0, n * n⟩) 0
  intro n; exact ⟨n + 1, main_transition n⟩
