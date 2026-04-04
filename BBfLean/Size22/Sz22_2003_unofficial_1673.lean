import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1673: [77/15, 9/14, 2/3, 5/11, 231/2]

Vector representation:
```
 0 -1 -1  1  1
-1  2  0 -1  0
 1 -1  0  0  0
 0  0  1  0 -1
-1  1  0  1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1673

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ A C,
    ⟨A, 0, C, 0, k⟩ [fm]⊢* ⟨A, 0, C + k, (0 : ℕ), 0⟩ := by
  intro k; induction k with
  | zero => intro A C; simp; exists 0
  | succ k ih =>
    intro A C; step fm
    rw [show C + (k + 1) = (C + 1) + k from by ring]
    exact ih A (C + 1)

theorem b_to_a : ∀ k, ∀ A E,
    ⟨A, k, 0, 0, E⟩ [fm]⊢* ⟨A + k, 0, 0, (0 : ℕ), E⟩ := by
  intro k; induction k with
  | zero => intro A E; simp; exists 0
  | succ k ih =>
    intro A E; step fm
    apply stepStar_trans (ih (A + 1) E); ring_nf; finish

theorem r1r1r2_round : ∀ A C D E,
    ⟨A + 1, 2, C + 2, D, E⟩ [fm]⊢* ⟨A, 2, C, D + 1, E + 2⟩ := by
  intro A C D E
  rw [show (2 : ℕ) = 1 + 1 from by ring, show C + 2 = (C + 1) + 1 from by ring]
  step fm
  rw [show (C + 1 : ℕ) = C + 1 from rfl]
  step fm
  rw [show (A + 1 : ℕ) = A + 1 from rfl, show D + 2 = (D + 1) + 1 from by ring]
  step fm; ring_nf; finish

theorem r2_chain : ∀ A, ∀ B D E,
    ⟨A, B, 0, D + A, E⟩ [fm]⊢* ⟨0, B + 2 * A, 0, D, E⟩ := by
  intro A; induction A with
  | zero => intro B D E; simp; exists 0
  | succ A ih =>
    intro B D E
    rw [show D + (A + 1) = (D + A) + 1 from by ring,
        show (A + 1 : ℕ) = A + 1 from rfl]
    step fm
    apply stepStar_trans (ih (B + 2) D E); ring_nf; finish

theorem interleaved_drain : ∀ C, ∀ F G E,
    ⟨C + F, 2, C, F + G + 1, E⟩ [fm]⊢* ⟨0, C + 2 * F + 2, 0, G + 1, E + C⟩ := by
  intro C
  induction' C using Nat.strongRecOn with C ih
  intro F G E
  rcases C with _ | _ | C
  · have h := r2_chain F 2 (G + 1) E
    rw [show G + 1 + F = F + G + 1 from by ring,
        show 2 + 2 * F = 2 * F + 2 from by ring] at h
    rw [show 0 + F = F from by ring,
        show 0 + 2 * F + 2 = 2 * F + 2 from by ring,
        show E + 0 = E from by ring]; exact h
  · rw [show 1 + F = F + 1 from by ring]
    rw [show (2 : ℕ) = 1 + 1 from by ring,
        show (1 : ℕ) = 0 + 1 from by ring]
    step fm
    have h := r2_chain (F + 1) 1 (G + 1) (E + 1)
    rw [show G + 1 + (F + 1) = F + G + 2 from by ring,
        show 1 + 2 * (F + 1) = 2 * F + 3 from by ring] at h
    apply stepStar_trans h
    rw [show 1 + 2 * F + 2 = 2 * F + 3 from by ring,
        show E + 1 = E + 1 from by ring]; finish
  · rw [show C + 2 + F = (C + F + 1) + 1 from by ring,
        show C + 2 = C + 2 from by ring]
    apply stepStar_trans (r1r1r2_round (C + F + 1) C (F + G + 1) E)
    have h := ih C (by omega) (F + 1) G (E + 2)
    rw [show C + (F + 1) = C + F + 1 from by ring,
        show F + 1 + G + 1 = F + G + 2 from by ring] at h
    apply stepStar_trans h
    rw [show C + 2 + 2 * F + 2 = C + 2 * (F + 1) + 2 from by ring,
        show E + (C + 2) = E + 2 + C from by ring]; finish

theorem r3r2_step : ∀ B E,
    ⟨0, B + 1, 0, (1 : ℕ), E⟩ [fm]⊢* ⟨0, B + 2, 0, (0 : ℕ), E⟩ := by
  intro B E; step fm
  rw [show (1 : ℕ) = 0 + 1 from by ring]
  step fm; ring_nf; finish

theorem main_trans (n : ℕ) :
    ⟨n + 1, 0, 0, 0, n⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, (0 : ℕ), n + 1⟩ := by
  rcases n with _ | n
  · execute fm 5
  · have p1 : ⟨n + 2, 0, 0, 0, n + 1⟩ [fm]⊢* ⟨n + 2, 0, n + 1, (0 : ℕ), 0⟩ := by
      have h := e_to_c (n + 1) (n + 2) 0
      rw [show 0 + (n + 1) = n + 1 from by ring] at h; exact h
    have p2 : ⟨n + 2, 0, n + 1, 0, 0⟩ [fm]⊢⁺ ⟨n + 1, 1, n + 1, 1, 1⟩ := by
      rw [show n + 2 = (n + 1) + 1 from by ring]
      step fm; finish
    have p3 : ⟨n + 1, 1, n + 1, 1, 1⟩ [fm]⊢* ⟨n + 1, 0, n, 2, 2⟩ := by
      rw [show (1 : ℕ) = 0 + 1 from by ring, show n + 1 = n + 1 from rfl]
      step fm; ring_nf; finish
    have p4 : ⟨n + 1, 0, n, 2, 2⟩ [fm]⊢* ⟨n, 2, n, 1, 2⟩ := by
      rw [show n + 1 = n + 1 from rfl, show (2 : ℕ) = 1 + 1 from by ring]
      step fm; ring_nf; finish
    have p5 : ⟨n, 2, n, 1, 2⟩ [fm]⊢* ⟨0, n + 2, 0, (1 : ℕ), n + 2⟩ := by
      have h := interleaved_drain n 0 0 2
      simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero] at h
      rw [show 2 + n = n + 2 from by ring] at h; exact h
    have p6 : ⟨0, n + 2, 0, 1, n + 2⟩ [fm]⊢* ⟨0, n + 3, 0, (0 : ℕ), n + 2⟩ := by
      have h := r3r2_step (n + 1) (n + 2)
      rw [show n + 1 + 1 = n + 2 from by ring,
          show n + 1 + 2 = n + 3 from by ring] at h; exact h
    have p7 : ⟨0, n + 3, 0, 0, n + 2⟩ [fm]⊢* ⟨n + 3, 0, 0, (0 : ℕ), n + 2⟩ := by
      have h := b_to_a (n + 3) 0 (n + 2)
      rw [show 0 + (n + 3) = n + 3 from by ring] at h; exact h
    exact stepStar_stepPlus_stepPlus p1
      (stepPlus_stepStar_stepPlus p2
        (stepStar_trans p3 (stepStar_trans p4 (stepStar_trans p5 (stepStar_trans p6 p7)))))

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 1, 0, 0, 0, n⟩) 0
  intro n; exists n + 1
  exact main_trans n

end Sz22_2003_unofficial_1673
