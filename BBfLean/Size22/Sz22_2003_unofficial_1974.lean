import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1974: [99/35, 25/39, 26/5, 7/11, 55/2]

Vector representation:
```
 0  2 -1 -1  1  0
 0 -1  2  0  0 -1
 1  0 -1  0  0  1
 0  0  0  1 -1  0
-1  0  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1974

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e, f⟩ => some ⟨a, b+2, c, d, e+1, f⟩
  | ⟨a, b+1, c, d, e, f+1⟩ => some ⟨a, b, c+2, d, e, f⟩
  | ⟨a, b, c+1, d, e, f⟩ => some ⟨a+1, b, c, d, e, f+1⟩
  | ⟨a, b, c, d, e+1, f⟩ => some ⟨a, b, c, d+1, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c+1, d, e+1, f⟩
  | _ => none

-- R4 repeated: move e to d. ⟨a, 0, 0, d, e+k, f⟩ →* ⟨a, 0, 0, d+k, e, f⟩
theorem e_to_d : ∀ k d, ⟨a, 0, 0, d, e + k, f⟩ [fm]⊢* ⟨a, 0, 0, d + k, e, f⟩ := by
  intro k; induction' k with k ih <;> intro d
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by omega]; step fm
    apply stepStar_trans (ih (d + 1)); ring_nf; finish

-- R3 repeated: ⟨a, 0, c+k, 0, e, f⟩ →* ⟨a+k, 0, c, 0, e, f+k⟩
theorem r3_chain : ∀ k a f, ⟨a, 0, c + k, 0, e, f⟩ [fm]⊢* ⟨a + k, 0, c, 0, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by omega]; step fm
    apply stepStar_trans (ih (a + 1) (f + 1)); ring_nf; finish

-- R2 repeated: ⟨a, b+k, c, 0, e, f+k⟩ →* ⟨a, b, c+2*k, 0, e, f⟩
theorem r2_chain : ∀ k b c f, ⟨a, b + k, c, 0, e, f + k⟩ [fm]⊢* ⟨a, b, c + 2 * k, 0, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b c f
  · exists 0
  · rw [show b + (k + 1) = (b + k) + 1 from by omega,
        show f + (k + 1) = (f + k) + 1 from by omega]; step fm
    apply stepStar_trans (ih b (c + 2) f); ring_nf; finish

-- Drain c=0: r2_chain then r3_chain
theorem drain_c0 :
    ⟨a, 0 + B, 0, 0, e, G + B⟩ [fm]⊢* ⟨a + 2 * B, 0, 0, 0, e, G + 2 * B⟩ := by
  apply stepStar_trans (r2_chain B 0 0 G (a := a) (e := e))
  show ⟨a, 0, 0 + 2 * B, 0, e, G⟩ [fm]⊢* _
  apply stepStar_trans (r3_chain (2 * B) a G (c := 0) (e := e)); ring_nf; finish

-- Drain c=1: r2_chain then r3_chain
theorem drain_c1 :
    ⟨a, 0 + B, 1, 0, e, G + B⟩ [fm]⊢* ⟨a + 1 + 2 * B, 0, 0, 0, e, G + 1 + 2 * B⟩ := by
  apply stepStar_trans (r2_chain B 0 1 G (a := a) (e := e))
  rw [show (1 : ℕ) + 2 * B = 0 + (1 + 2 * B) from by ring]
  apply stepStar_trans (r3_chain (1 + 2 * B) a G (c := 0) (e := e)); ring_nf; finish

-- Combined macro rounds + drain, by strong induction on D
theorem combined : ∀ D, ∀ a B E G,
    ⟨a, B + 2, 0, D, E, G + 2 * D + B + 2⟩ [fm]⊢*
    ⟨a + 3 * D + 2 * B + 4, 0, 0, 0, E + D, G + 3 * D + 2 * B + 4⟩ := by
  intro D; induction' D using Nat.strongRecOn with D ih
  intro a B E G
  rcases D with _ | _ | D'
  · -- D = 0
    rw [show G + 2 * 0 + B + 2 = G + (B + 2) from by ring,
        show (B : ℕ) + 2 = 0 + (B + 2) from by ring,
        show G + (0 + (B + 2)) = G + (B + 2) from by ring]
    apply stepStar_trans (drain_c0 (a := a) (B := B + 2) (e := E) (G := G))
    ring_nf; finish
  · -- D = 1
    rw [show G + 2 * 1 + B + 2 = (G + B + 3) + 1 from by ring]
    step fm; step fm
    rw [show B + 1 + 2 = 0 + (B + 3) from by ring,
        show G + B + 3 = G + (B + 3) from by ring]
    apply stepStar_trans (drain_c1 (a := a) (B := B + 3) (e := E + 1) (G := G))
    ring_nf; finish
  · -- D = D' + 2
    rw [show G + 2 * (D' + 2) + B + 2 = (G + 2 * D' + (B + 3) + 2) + 1 from by ring]
    step fm; step fm; step fm
    rw [show B + 1 + 2 + 2 = (B + 3) + 2 from by ring]
    apply stepStar_trans (ih D' (by omega) a (B + 3) (E + 2) G)
    ring_nf; finish

-- Main transition: canonical state →⁺ next canonical state
theorem main_trans : ∀ a n G,
    ⟨a + 1, 0, 0, n + 1, 0, G + 2 * n + 2⟩ [fm]⊢⁺
    ⟨a + 3 * n + 4, 0, 0, n + 2, 0, G + 3 * n + 4⟩ := by
  intro a n G
  apply step_stepStar_stepPlus (c₂ := ⟨a, 0, 1, n + 1, 1, G + 2 * n + 2⟩)
  · simp [fm]
  step fm
  rw [show (2 : ℕ) = 0 + 2 from by ring,
      show G + 2 * n + 2 = G + 2 * n + 0 + 2 from by ring]
  apply stepStar_trans (combined n a 0 2 G)
  rw [show a + 3 * n + 2 * 0 + 4 = a + 3 * n + 4 from by ring,
      show G + 3 * n + 2 * 0 + 4 = G + 3 * n + 4 from by ring,
      show 2 + n = 0 + (n + 2) from by ring]
  apply stepStar_trans (e_to_d (n + 2) 0 (a := a + 3 * n + 4) (e := 0) (f := G + 3 * n + 4))
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨10, 0, 0, 3, 0, 6⟩)
  · execute fm 30
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ × ℕ)
    (fun ⟨a, n, G⟩ ↦ ⟨a + 1, 0, 0, n + 1, 0, G + 2 * n + 2⟩) ⟨9, 2, 0⟩
  intro ⟨a, n, G⟩
  exact ⟨⟨a + 3 * n + 3, n + 1, G + n⟩, by
    show ⟨a + 1, 0, 0, n + 1, 0, G + 2 * n + 2⟩ [fm]⊢⁺
         ⟨a + 3 * n + 3 + 1, 0, 0, n + 1 + 1, 0, G + n + 2 * (n + 1) + 2⟩
    rw [show a + 3 * n + 3 + 1 = a + 3 * n + 4 from by ring,
        show G + n + 2 * (n + 1) + 2 = G + 3 * n + 4 from by ring]
    exact main_trans a n G⟩

end Sz22_2003_unofficial_1974
