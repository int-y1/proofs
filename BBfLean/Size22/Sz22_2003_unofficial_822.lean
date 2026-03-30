import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #822: [35/6, 8/55, 121/2, 3/7, 6/11]

Vector representation:
```
-1 -1  1  1  0
 3  0 -1  0 -1
-1  0  0  0  2
 0  1  0 -1  0
 1  1  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_822

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+3, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b+1, c, d, e⟩
  | _ => none

theorem r3_drain : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d, e + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih a d (e + 2)); ring_nf; finish

theorem r4_drain : ∀ k b d e, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih <;> intro b d e
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (b + 1) d e); ring_nf; finish

theorem r2_chain : ∀ k a c d e, ⟨a, 0, c + k, d, e + k⟩ [fm]⊢* ⟨a + 3 * k, 0, c, d, e⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm; apply stepStar_trans (ih (a + 3) c d e); ring_nf; finish

theorem from_zero_a : ∀ B, ∀ c D e,
    ⟨0, B, c + 1, D, e + (c + 1) + B⟩ [fm]⊢* ⟨3 * (c + 1) + 2 * B, 0, 0, D + B, e⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih
  intro c D e
  rcases B with _ | _ | _ | B
  · convert r2_chain (c + 1) 0 0 D e using 2; ring_nf
  · rw [show e + (c + 1) + 1 = (e + c + 1) + 1 from by ring]
    step fm; step fm
    convert r2_chain (c + 1) 2 0 (D + 1) e using 2; ring_nf
  · rw [show e + (c + 1) + 2 = (e + c + 2) + 1 from by ring]
    step fm; step fm; step fm
    convert r2_chain (c + 2) 1 0 (D + 2) e using 2; ring_nf
  · rw [show e + (c + 1) + (B + 3) = (e + (c + 1) + B + 2) + 1 from by ring,
        show B + 3 = (B + 2) + 1 from by ring]
    step fm; step fm; step fm; step fm
    have := ih B (by omega) (c + 2) (D + 3) e
    convert this using 2; ring_nf

theorem interleaved (n e : ℕ) :
    ⟨1, n + 2, 0, 0, e + n + 2⟩ [fm]⊢* ⟨2 * n + 5, 0, 0, n + 2, e⟩ := by
  rw [show n + 2 = (n + 1) + 1 from by ring,
      show e + n + 2 = (e + n + 1) + 1 from by ring]
  step fm
  convert from_zero_a (n + 1) 0 1 e using 2; ring_nf

def E : ℕ → ℕ
  | 0 => 0
  | n + 1 => E n + 3 * (n + 1)

theorem main_trans (n : ℕ) :
    ⟨2 * n + 3, 0, 0, n + 1, E n⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, 0, n + 2, E n + 3 * (n + 1)⟩ := by
  -- First R3 step (gives ⊢⁺ → ⊢* conversion)
  rw [show 2 * n + 3 = (2 * n + 2) + 1 from by ring]
  step fm
  -- Goal: ⊢* from (2*n+2, 0, 0, n+1, E n+2) to target
  -- Remaining R3 drain
  rw [show 2 * n + 2 = 0 + (2 * n + 2) from by ring]
  apply stepStar_trans (r3_drain (2 * n + 2) 0 (n + 1) (E n + 2))
  -- At (0, 0, 0, n+1, E n + 2 + 2*(2*n+2))
  -- R4 drain
  rw [show n + 1 = 0 + (n + 1) from by ring]
  apply stepStar_trans (r4_drain (n + 1) 0 0 (E n + 2 + 2 * (2 * n + 2)))
  -- At (0, 0+(n+1), 0, 0, E n + 2 + 2*(2*n+2))
  -- R5 step
  rw [show 0 + (n + 1) = n + 1 from by ring,
      show E n + 2 + 2 * (2 * n + 2) = (E n + 4 * n + 5) + 1 from by ring]
  step fm
  -- At (1, n+2, 0, 0, E n + 4*n + 5)
  -- Interleaved chain
  rw [show E n + 4 * n + 5 = (E n + 3 * (n + 1)) + n + 2 from by ring]
  exact interleaved n (E n + 3 * (n + 1))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 1, E 0⟩)
  · show c₀ [fm]⊢* ⟨3, 0, 0, 1, 0⟩
    execute fm 4
  · apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun n ↦ ⟨2 * n + 3, 0, 0, n + 1, E n⟩) 0
    intro n; exists n + 1
    show ⟨2 * n + 3, 0, 0, n + 1, E n⟩ [fm]⊢⁺
         ⟨2 * (n + 1) + 3, 0, 0, (n + 1) + 1, E (n + 1)⟩
    rw [show 2 * (n + 1) + 3 = 2 * n + 5 from by ring,
        show (n + 1) + 1 = n + 2 from by ring,
        show E (n + 1) = E n + 3 * (n + 1) from rfl]
    exact main_trans n
