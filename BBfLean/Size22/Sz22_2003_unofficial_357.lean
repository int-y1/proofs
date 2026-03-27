import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #357: [2/15, 297/14, 25/2, 7/11, 14/5]

Vector representation:
```
 1 -1 -1  0  0
-1  3  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_357

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d+1, e⟩
  | _ => none

-- Convert e to d via R4
theorem e_to_d : ∀ k c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨(0 : ℕ), 0, c, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    rw [show d + (k + 1) = (d + 1) + k from by ring]
    step fm; exact ih c (d + 1)

-- One R2 + 3 R1 cycle: 4 steps
theorem one_r2_3r1 : ∀ a c d e,
    ⟨a+1, 0, c+3, d+1, e⟩ [fm]⊢* ⟨a+3, (0 : ℕ), c, d, e+1⟩ := by
  intro a c d e; execute fm 4

-- Iterate R2+3R1 loop k times
theorem r2_3r1_loop : ∀ k, ∀ a c d e,
    ⟨a+1, 0, c + 3*k, d + k, e⟩ [fm]⊢* ⟨a + 2*k + 1, (0 : ℕ), c, d, e + k⟩ := by
  intro k; induction k with
  | zero => intro a c d e; ring_nf; exists 0
  | succ k ih =>
    intro a c d e
    rw [show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    apply stepStar_trans (one_r2_3r1 a (c + 3 * k) (d + k) e)
    rw [show a + 3 = (a + 2) + 1 from by ring]
    apply stepStar_trans (ih (a + 2) c d (e + 1))
    ring_nf; finish

-- R3 drain: convert a to c
theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 2*k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro c e; exists 0
  | succ k ih =>
    intro c e; step fm
    apply stepStar_trans (ih (c + 2) e)
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring]; finish

-- R1 drain: consume b via R1 steps
theorem r1_drain : ∀ k, ∀ a c e,
    ⟨a, k, c + k, 0, e⟩ [fm]⊢* ⟨a + k, (0 : ℕ), c, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm
    apply stepStar_trans (ih (a + 1) c e)
    rw [show a + 1 + k = a + (k + 1) from by ring]; finish

-- Cleanup c >= 3: 3 R1 + R3 drain
theorem cleanup_ge3 : ∀ a c e,
    ⟨a, 3, c + 3, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, c + 2*a + 6, 0, e⟩ := by
  intro a c e
  apply stepStar_trans (r1_drain 3 a c e)
  apply stepStar_trans (r3_drain (a + 3) c e)
  rw [show c + 2 * (a + 3) = c + 2 * a + 6 from by ring]; finish

-- Cleanup c = 2: 4 manual steps + R3 drain
theorem cleanup_eq2 : ∀ a e,
    ⟨a, 3, 2, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 2*a + 5, 0, e⟩ := by
  intro a e
  -- (a, 3, 2, 0, e) -> R1 -> (a+1, 2, 1, 0, e) -> R1 -> (a+2, 1, 0, 0, e)
  -- -> R3 -> (a+1, 1, 2, 0, e) -> R1 -> (a+2, 0, 1, 0, e) -> R3 drain
  apply stepStar_trans (c₂ := ⟨a + 2, 0, 1, 0, e⟩)
  · execute fm 4
  apply stepStar_trans (r3_drain (a + 2) 1 e)
  rw [show 1 + 2 * (a + 2) = 2 * a + 5 from by ring]; finish

-- Cleanup c = 1: 4 manual steps + R3 drain
theorem cleanup_eq1 : ∀ a e,
    ⟨a, 3, 1, 0, e⟩ [fm]⊢* ⟨(0 : ℕ), 0, 2*a + 4, 0, e⟩ := by
  intro a e
  -- (a, 3, 1, 0, e) -> R1 -> (a+1, 2, 0, 0, e) -> R3 -> (a, 2, 2, 0, e)
  -- -> R1 -> (a+1, 1, 1, 0, e) -> R1 -> (a+2, 0, 0, 0, e) -> R3 drain
  apply stepStar_trans (c₂ := ⟨a + 2, 0, 0, 0, e⟩)
  · execute fm 4
  apply stepStar_trans (r3_drain (a + 2) 0 e)
  rw [show 0 + 2 * (a + 2) = 2 * a + 4 from by ring]; finish

-- Inner phase: d rounds of R2+3R1, then final R2, then cleanup
theorem inner_phase : ∀ c d,
    ⟨1, 0, c + 3*d + 1, d + 1, 0⟩ [fm]⊢⁺ ⟨(0 : ℕ), 0, c + 4*d + 4, 0, d + 1⟩ := by
  intro c d
  -- d rounds of R2+3R1
  have h1 : ⟨1, 0, c + 3 * d + 1, d + 1, 0⟩ [fm]⊢*
      ⟨2 * d + 1, (0 : ℕ), c + 1, 1, d⟩ := by
    rw [show c + 3 * d + 1 = (c + 1) + 3 * d from by ring,
        show d + 1 = 1 + d from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    apply stepStar_trans (r2_3r1_loop d 0 (c + 1) 1 0)
    ring_nf; finish
  -- R2: (2d+1, 0, c+1, 1, d) -> (2d, 3, c+1, 0, d+1)
  have h2 : ⟨2 * d + 1, 0, c + 1, 1, d⟩ [fm]⊢⁺
      ⟨2 * d, (3 : ℕ), c + 1, 0, d + 1⟩ := by
    apply step_stepStar_stepPlus
    · show fm ⟨2 * d + 1, 0, c + 1, 1, d⟩ = some ⟨2 * d, 3, c + 1, 0, d + 1⟩
      rw [show 2 * d + 1 = (2 * d) + 1 from by ring,
          show (1 : ℕ) = 0 + 1 from by ring]
      simp [fm]
    finish
  -- Cleanup
  have h3 : ⟨2 * d, 3, c + 1, 0, d + 1⟩ [fm]⊢*
      ⟨(0 : ℕ), 0, c + 4 * d + 4, 0, d + 1⟩ := by
    match c with
    | 0 =>
      apply stepStar_trans (cleanup_eq1 (2 * d) (d + 1))
      ring_nf; finish
    | 1 =>
      apply stepStar_trans (cleanup_eq2 (2 * d) (d + 1))
      ring_nf; finish
    | c + 2 =>
      rw [show c + 2 + 1 = c + 3 from by ring]
      apply stepStar_trans (cleanup_ge3 (2 * d) c (d + 1))
      rw [show c + 2 * (2 * d) + 6 = c + 2 + 4 * d + 4 from by ring]; finish
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)

-- Auxiliary function for parameterizing the recurring state
def cp : ℕ → ℕ
  | 0 => 0
  | n + 1 => cp n + n + 2

theorem main_trans (n : ℕ) :
    ⟨0, 0, cp n + 3 * (n + 3) + 2, 0, n + 3⟩ [fm]⊢⁺
    ⟨(0 : ℕ), 0, cp (n + 1) + 3 * (n + 4) + 2, 0, n + 4⟩ := by
  -- e_to_d
  have h1 : ⟨0, 0, cp n + 3 * (n + 3) + 2, 0, n + 3⟩ [fm]⊢*
      ⟨(0 : ℕ), 0, cp n + 3 * (n + 3) + 2, n + 3, 0⟩ := by
    have := e_to_d (n + 3) (cp n + 3 * (n + 3) + 2) 0
    rwa [show 0 + (n + 3) = n + 3 from by ring] at this
  -- R5
  have h2 : ⟨0, 0, cp n + 3 * (n + 3) + 2, n + 3, 0⟩ [fm]⊢⁺
      ⟨1, (0 : ℕ), cp n + 3 * (n + 3) + 1, n + 4, 0⟩ := by
    apply step_stepStar_stepPlus
    · show fm ⟨0, 0, cp n + 3 * (n + 3) + 2, n + 3, 0⟩ =
          some ⟨1, 0, cp n + 3 * (n + 3) + 1, n + 4, 0⟩
      rw [show cp n + 3 * (n + 3) + 2 = (cp n + 3 * (n + 3) + 1) + 1 from by ring,
          show n + 4 = (n + 3) + 1 from by ring]
      simp [fm]
    finish
  -- inner_phase
  have h3 : ⟨1, 0, cp n + 3 * (n + 3) + 1, n + 4, 0⟩ [fm]⊢⁺
      ⟨(0 : ℕ), 0, cp (n + 1) + 3 * (n + 4) + 2, 0, n + 4⟩ := by
    rw [show n + 4 = (n + 3) + 1 from by ring]
    have := inner_phase (cp n) (n + 3)
    rw [show cp n + 4 * (n + 3) + 4 = cp (n + 1) + 3 * (n + 4) + 2 from by
      simp [cp]; ring] at this
    exact this
  exact stepStar_stepPlus_stepPlus h1 (stepPlus_trans h2 h3)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 11, 0, 3⟩) (by execute fm 46)
  have : (11 : ℕ) = cp 0 + 3 * (0 + 3) + 2 := by simp [cp]
  rw [this]
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, cp n + 3 * (n + 3) + 2, 0, n + 3⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_357
