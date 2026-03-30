import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #767: [35/6, 52/55, 143/2, 3/7, 14/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  1
-1  0  0  0  1  1
 0  1  0 -1  0  0
 1  0  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_767

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f+1⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+1, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b, c, d+1, e, f⟩
  | _ => none

theorem r3_drain : ∀ k, ∀ a d e f,
    ⟨a + k, 0, 0, d, e, f⟩ [fm]⊢* ⟨a, 0, 0, d, e + k, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a d e f
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih a d (e + 1) (f + 1))
    ring_nf; finish

theorem r4_drain : ∀ k, ∀ b d e f,
    ⟨0, b, 0, d + k, e, f⟩ [fm]⊢* ⟨0, b + k, 0, d, e, f⟩ := by
  intro k; induction' k with k ih <;> intro b d e f
  · exists 0
  · rw [show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b + 1) d e f)
    ring_nf; finish

theorem r2_drain : ∀ k, ∀ a c d e f,
    ⟨a, 0, c + k, d, e + k, f⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e, f + k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e f
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a + 2) c d e (f + 1))
    ring_nf; finish

-- Inner loop: (0, B, c+1, 2*c+2, E+B+c+1, F) →* (B+2*c+2, 0, 0, B+2*c+2, E, F+B+c+1)
theorem inner_loop : ∀ B, ∀ c E F,
    ⟨0, B, c + 1, 2 * c + 2, E + B + c + 1, F⟩ [fm]⊢*
    ⟨B + 2 * c + 2, 0, 0, B + 2 * c + 2, E, F + B + c + 1⟩ := by
  intro B; induction' B using Nat.strongRecOn with B ih
  intro c E F
  rcases B with _ | _ | B
  · -- B = 0: R2 drain (c+1) times
    have h := r2_drain (c + 1) 0 0 (2 * c + 2) E F
    simp only [Nat.zero_add] at h ⊢
    simp only [Nat.add_zero] at h ⊢
    apply stepStar_trans h
    ring_nf; finish
  · -- B = 1: R2, R1, then R2 drain
    rw [show E + 1 + c + 1 = (E + c + 1) + 1 from by ring,
        show c + 1 = 0 + (c + 1) from by ring]
    step fm  -- R2
    rw [show (Nat.add 0 c : ℕ) = c from Nat.zero_add c,
        show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm  -- R1
    have h := r2_drain (c + 1) 1 0 (2 * c + 3) E (F + 1)
    simp only [Nat.zero_add] at h ⊢
    apply stepStar_trans h
    ring_nf; finish
  · -- B + 2: R2, R1, R1, then IH(B, c+1)
    rw [show E + (B + 2) + c + 1 = (E + B + c + 2) + 1 from by ring,
        show c + 1 = 0 + (c + 1) from by ring]
    step fm  -- R2
    rw [show (Nat.add 0 c : ℕ) = c from Nat.zero_add c,
        show (2 : ℕ) = 1 + 1 from by ring,
        show B + 2 = (B + 1) + 1 from by ring]
    step fm  -- R1
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm  -- R1
    have h := ih B (by omega) (c + 1) E (F + 1)
    ring_nf at h ⊢
    apply stepStar_trans h
    finish

-- Main transition.
theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, n + 1, 1, n * n⟩ [fm]⊢⁺
    ⟨n + 2, 0, 0, n + 2, 1, (n + 1) * (n + 1)⟩ := by
  have h1 := r3_drain (n + 1) 0 (n + 1) 1 (n * n)
  simp only [Nat.zero_add] at h1
  have h2 := r4_drain (n + 1) 0 0 (n + 2) (n * n + n + 1)
  simp only [Nat.zero_add] at h2
  have h3 : ⟨0, n + 1, 0, 0, n + 2, n * n + n + 1⟩ [fm]⊢*
      ⟨n + 2, 0, 0, n + 2, 1, (n + 1) * (n + 1)⟩ := by
    rw [show n * n + n + 1 = (n * n + n) + 1 from by ring]
    step fm  -- R5
    rw [show (1 : ℕ) = 0 + 1 from by ring]
    step fm  -- R1
    have h := inner_loop n 0 1 (n * n + n)
    ring_nf at h ⊢
    apply stepStar_trans h
    finish
  have hall : ⟨n + 1, 0, 0, n + 1, 1, n * n⟩ [fm]⊢*
      ⟨n + 2, 0, 0, n + 2, 1, (n + 1) * (n + 1)⟩ := by
    apply stepStar_trans h1
    apply stepStar_trans _ (stepStar_trans h2 h3)
    ring_nf; finish
  exact stepStar_stepPlus hall (by simp [Q, Prod.mk.injEq])

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 1, 1, 0⟩)
  · execute fm 2
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, n + 1, 1, n * n⟩) 0
  intro n; exists n + 1; exact main_trans n
