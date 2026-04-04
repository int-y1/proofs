import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1643: [77/15, 27/14, 4/3, 5/11, 33/2]

Vector representation:
```
 0 -1 -1  1  1
-1  3  0 -1  0
 2 -1  0  0  0
 0  0  1  0 -1
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1643

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem r4_chain : ∀ k a c,
    ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih a (c + 1)); ring_nf; finish

theorem r3_chain : ∀ k a e,
    ⟨a, k, 0, 0, e⟩ [fm]⊢* ⟨a + 2 * k, 0, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 2) e); ring_nf; finish

theorem interleave : ∀ M A B C D E,
    3 * C + D = M → B ≥ 1 → A ≥ C + D →
    ⟨A, B, C, D, E⟩ [fm]⊢* ⟨A + 2 * B + 3 * C + 5 * D, 0, 0, 0, E + C⟩ := by
  intro M; induction' M using Nat.strongRecOn with M ih; intro A B C D E hM hB hA
  rcases C with _ | C
  · rcases D with _ | D
    · simp only [Nat.mul_zero, Nat.add_zero]
      exact r3_chain B A E
    · rw [show A = (A - 1) + 1 from by omega,
          show D + 1 = D + 1 from rfl]
      step fm
      apply stepStar_trans (ih (3 * 0 + D) (by omega) (A - 1) (B + 3) 0 D E rfl (by omega) (by omega))
      ring_nf; finish
  · rcases B with _ | B
    · omega
    · rw [show B + 1 = B + 1 from rfl,
          show C + 1 = C + 1 from rfl]
      step fm
      rcases B with _ | B
      · rw [show A = (A - 1) + 1 from by omega,
            show D + 1 = D + 1 from rfl]
        step fm
        apply stepStar_trans (ih (3 * C + D) (by omega) (A - 1) 3 C D (E + 1) rfl (by omega) (by omega))
        ring_nf; finish
      · apply stepStar_trans (ih (3 * C + (D + 1)) (by omega) A (B + 1) C (D + 1) (E + 1) rfl (by omega) (by omega))
        ring_nf; finish

theorem main_trans (n e : ℕ) :
    ⟨n + e + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨n + 4 * e + 6, 0, 0, 0, e + 2⟩ := by
  have h1 : ⟨n + e + 2, 0, 0, 0, e + 1⟩ [fm]⊢* ⟨n + e + 2, 0, e + 1, 0, 0⟩ := by
    have := r4_chain (e + 1) (n + e + 2) 0
    rw [show 0 + (e + 1) = e + 1 from by ring] at this; exact this
  have h2 : ⟨n + e + 2, 0, e + 1, 0, 0⟩ [fm]⊢⁺ ⟨n + e + 1, 1, e + 1, 0, 1⟩ := by
    rw [show n + e + 2 = (n + e + 1) + 1 from by ring]
    step fm; finish
  have h3 : ⟨n + e + 1, 1, e + 1, 0, 1⟩ [fm]⊢* ⟨n + 4 * e + 6, 0, 0, 0, e + 2⟩ := by
    have := interleave (3 * (e + 1) + 0) (n + e + 1) 1 (e + 1) 0 1 (by ring) (by omega) (by omega)
    rw [show n + e + 1 + 2 * 1 + 3 * (e + 1) + 5 * 0 = n + 4 * e + 6 from by ring,
        show 1 + (e + 1) = e + 2 from by ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 0, 1⟩) (by execute fm 2)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨n, e⟩ ↦ ⟨n + e + 2, 0, 0, 0, e + 1⟩) ⟨0, 0⟩
  intro ⟨n, e⟩
  refine ⟨⟨n + 3 * e + 3, e + 1⟩, ?_⟩
  show ⟨n + e + 2, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨(n + 3 * e + 3) + (e + 1) + 2, 0, 0, 0, (e + 1) + 1⟩
  rw [show (n + 3 * e + 3) + (e + 1) + 2 = n + 4 * e + 6 from by ring,
      show (e + 1) + 1 = e + 2 from by ring]
  exact main_trans n e
