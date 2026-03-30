import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #831: [35/6, 8/55, 847/2, 3/7, 2/11]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  1  2
 0  1  0 -1  0
 1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_831

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c, d, e⟩
  | _ => none

theorem r4_chain : ∀ k, ∀ b d, ⟨(0 : ℕ), b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    rw [show b + (k + 1) = (b + 1) + k from by ring]
    exact ih (b + 1) d

theorem r3_drain : ∀ a, ∀ d e, ⟨a, 0, 0, d, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 0, d + a, e + 2 * a⟩ := by
  intro a; induction' a with a ih <;> intro d e
  · exists 0
  · step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

theorem r2_chain : ∀ c, ∀ a e, ⟨a, 0, c, d, e + c⟩ [fm]⊢* ⟨a + 3 * c, 0, 0, d, e⟩ := by
  intro c; induction' c with c ih <;> intro a e
  · exists 0
  · rw [show e + (c + 1) = e + c + 1 from by ring]
    step fm
    apply stepStar_trans (ih _ _)
    ring_nf; finish

theorem chain : ∀ b, ∀ a c d e, a + c ≥ 1 →
    ⟨a, b, c, d, e + b + c⟩ [fm]⊢* ⟨a + 3 * c + 2 * b, 0, 0, d + b, e⟩ := by
  intro b; induction' b with b ih <;> intro a c d e hac
  · rw [show e + 0 + c = e + c from by ring,
        show a + 3 * c + 2 * 0 = a + 3 * c from by ring,
        show d + 0 = d from by ring]
    exact r2_chain c a e
  · rcases a with _ | a
    · rcases c with _ | c
      · omega
      · rw [show e + (b + 1) + (c + 1) = e + b + c + 1 + 1 from by ring]
        step fm
        step fm
        rw [show 0 + 3 * (c + 1) + 2 * (b + 1) = 2 + 3 * (c + 1) + 2 * b from by ring,
            show d + (b + 1) = (d + 1) + b from by ring,
            show e + b + c + 1 = e + b + (c + 1) from by ring]
        exact ih 2 (c + 1) (d + 1) e (by omega)
    · rw [show e + (b + 1) + c = e + b + (c + 1) from by ring]
      step fm
      rw [show (a + 1) + 3 * c + 2 * (b + 1) = a + 3 * (c + 1) + 2 * b from by ring,
          show d + (b + 1) = (d + 1) + b from by ring]
      exact ih a (c + 1) (d + 1) e (by omega)

theorem main_transition (d e : ℕ) : ⟨(0 : ℕ), 0, 0, d + 1, e + d + 2⟩ [fm]⊢⁺
    ⟨0, 0, 0, 3 * d + 4, e + 4 * d + 6⟩ := by
  -- R4^(d+1): (0,0,0,d+1,e+d+2) →* (0,d+1,0,0,e+d+2)
  rw [show (d + 1 : ℕ) = 0 + (d + 1) from by ring]
  apply stepStar_stepPlus_stepPlus (r4_chain (d + 1) 0 0)
  -- Now goal: (0, d+1, 0, 0, e+d+2) ⊢⁺ target
  rw [show (0 + (d + 1) : ℕ) = d + 1 from by ring,
      show e + d + 2 = (e + d + 1) + 1 from by ring]
  -- R5
  step fm
  -- R1
  step fm
  -- R2
  rw [show e + d + 1 = (e + d) + 1 from by ring]
  step fm
  -- Chain: (3, d, 0, 1, e+d) →* (2d+3, 0, 0, d+1, e)
  apply stepStar_trans
  · rw [show (e + d : ℕ) = e + d + 0 from by ring]
    exact chain d 3 0 1 e (by omega)
  -- R3 drain: (2d+3, 0, 0, d+1, e) →* (0, 0, 0, 3d+4, e+4d+6)
  rw [show 3 + 3 * 0 + 2 * d = 2 * d + 3 from by ring,
      show 1 + d = d + 1 from by ring]
  apply stepStar_trans (r3_drain (2 * d + 3) (d + 1) e)
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 2⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨d, e⟩ ↦ ⟨0, 0, 0, d + 1, e + d + 2⟩) ⟨0, 0⟩
  intro ⟨d, e⟩
  refine ⟨⟨3 * d + 3, e + d + 1⟩, ?_⟩
  show ⟨0, 0, 0, d + 1, e + d + 2⟩ [fm]⊢⁺ ⟨0, 0, 0, (3 * d + 3) + 1, (e + d + 1) + (3 * d + 3) + 2⟩
  rw [show (3 * d + 3) + 1 = 3 * d + 4 from by ring,
      show (e + d + 1) + (3 * d + 3) + 2 = e + 4 * d + 6 from by ring]
  exact main_transition d e

end Sz22_2003_unofficial_831
