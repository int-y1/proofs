import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #744: [35/6, 4/55, 1859/2, 3/7, 14/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  1  2
 0  1  0 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_744

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+2⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a d e f, ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 2))
    ring_nf; finish

theorem r4_chain : ∀ k, ∀ b d e f, ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem interleaved_aux : ∀ M, ∀ a b c d e f, 2 * b + c = M → a + c ≥ 1 →
    ⟨a, b, c, d, e + b + c, f⟩ [fm]⊢* ⟨a + b + 2 * c, 0, 0, d + b, e, f⟩ := by
  intro M; induction' M with M ih <;> intro a b c d e f hM hac
  · have hb : b = 0 := by omega
    have hc : c = 0 := by omega
    subst hb; subst hc; ring_nf; finish
  · rcases b with _ | b
    · rcases c with _ | c
      · omega
      · rw [show e + 0 + (c + 1) = (e + c) + 1 from by ring]
        step fm
        have := ih (a + 2) 0 c d e f (by omega) (by omega)
        rw [show e + 0 + c = e + c from by ring] at this
        apply stepStar_trans this
        ring_nf; finish
    · rcases a with _ | a
      · rcases c with _ | c
        · omega
        · rw [show e + (b + 1) + (c + 1) = (e + (b + 1) + c) + 1 from by ring]
          step fm
          have := ih 2 (b + 1) c d e f (by omega) (by omega)
          rw [show e + (b + 1) + c = e + (b + 1) + c from rfl] at this
          apply stepStar_trans this
          ring_nf; finish
      · rw [show e + (b + 1) + c = e + b + (c + 1) from by ring]
        step fm
        have := ih a b (c + 1) (d + 1) e f (by omega) (by omega)
        apply stepStar_trans this
        ring_nf; finish

theorem interleaved : ∀ b, ∀ a c d e f, a + c ≥ 1 →
    ⟨a, b, c, d, e + b + c, f⟩ [fm]⊢* ⟨a + b + 2 * c, 0, 0, d + b, e, f⟩ :=
  fun b a c d e f h => interleaved_aux (2 * b + c) a b c d e f rfl h

theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, n + 1, 1, n * n + 1⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 2, 1, (n + 1) * (n + 1) + 1⟩ := by
  -- Phase 1: R3 chain (n+1 steps)
  -- (n+1, 0, 0, n+1, 1, n²+1) → (0, 0, 0, n+1, n+2, n²+2n+3)
  have h1 : ⟨n + 1, 0, 0, n + 1, 1, n * n + 1⟩ [fm]⊢*
      ⟨0, 0, 0, n + 1, n + 2, n * n + 2 * n + 3⟩ := by
    have := r3_chain (n + 1) 0 (n + 1) 1 (n * n + 1)
    convert this using 2; ring_nf
  -- Phase 2: R4 chain (n+1 steps)
  -- (0, 0, 0, n+1, n+2, n²+2n+3) → (0, n+1, 0, 0, n+2, n²+2n+3)
  have h2 : ⟨0, 0, 0, n + 1, n + 2, n * n + 2 * n + 3⟩ [fm]⊢*
      ⟨0, n + 1, 0, 0, n + 2, n * n + 2 * n + 3⟩ := by
    have := r4_chain (n + 1) 0 0 (n + 2) (n * n + 2 * n + 3)
    convert this using 2; ring_nf
  -- Phase 3: R5 step
  -- (0, n+1, 0, 0, n+2, n²+2n+3) → (1, n+1, 0, 1, n+2, n²+2n+2)
  have h3 : ⟨0, n + 1, 0, 0, n + 2, n * n + 2 * n + 3⟩ [fm]⊢⁺
      ⟨1, n + 1, 0, 1, n + 2, n * n + 2 * n + 2⟩ := by
    rw [show n * n + 2 * n + 3 = (n * n + 2 * n + 2) + 1 from by ring]
    step fm; finish
  -- Phase 4: interleaved R1/R2 phase
  -- (1, n+1, 0, 1, n+2, (n+1)²+1) → (n+2, 0, 0, n+2, 1, (n+1)²+1)
  have h4 : ⟨1, n + 1, 0, 1, n + 2, (n + 1) * (n + 1) + 1⟩ [fm]⊢*
      ⟨n + 2, 0, 0, n + 2, 1, (n + 1) * (n + 1) + 1⟩ := by
    have := interleaved (n + 1) 1 0 1 1 ((n + 1) * (n + 1) + 1) (by omega)
    convert this using 2; ring_nf
  -- Compose
  apply stepStar_stepPlus_stepPlus h1
  apply stepStar_stepPlus_stepPlus h2
  apply stepPlus_stepStar_stepPlus h3
  rw [show n * n + 2 * n + 2 = (n + 1) * (n + 1) + 1 from by ring]
  exact h4

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 2, 1, 2⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, n + 1, 1, n * n + 1⟩) 1
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_744
