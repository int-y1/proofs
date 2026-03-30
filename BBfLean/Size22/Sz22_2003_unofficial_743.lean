import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #743: [35/6, 4/55, 1573/2, 3/7, 6/13]

Vector representation:
```
-1 -1  1  1  0  0
 2  0 -1  0 -1  0
-1  0  0  0  2  1
 0  1  0 -1  0  0
 1  1  0  0  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_743

def Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e, f⟩ => some ⟨a, b, c+1, d+1, e, f⟩
  | ⟨a, b, c+1, d, e+1, f⟩ => some ⟨a+2, b, c, d, e, f⟩
  | ⟨a+1, b, c, d, e, f⟩ => some ⟨a, b, c, d, e+2, f+1⟩
  | ⟨a, b, c, d+1, e, f⟩ => some ⟨a, b+1, c, d, e, f⟩
  | ⟨a, b, c, d, e, f+1⟩ => some ⟨a+1, b+1, c, d, e, f⟩
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

theorem interleave : ∀ b, ∀ c d e f, ⟨1, b + 1, c, d, e + c + b + 1, f⟩ [fm]⊢* ⟨2 * c + b + 2, 0, 0, d + b + 1, e, f⟩ := by
  intro b; induction' b using Nat.strongRecOn with b ih
  rcases b with _ | _ | b
  · -- b = 0
    intro c d e f
    rw [show e + c + 0 + 1 = (e + (c + 1)) from by ring]
    step fm
    have h := r2_chain (c + 1) 0 0 (d + 1) e f
    simp only [Nat.zero_add] at h
    rw [show 2 * c + 0 + 2 = 0 + 2 * (c + 1) from by ring,
        show d + 0 + 1 = d + 1 from by ring]
    apply stepStar_trans h
    ring_nf; finish
  · -- b = 1
    intro c d e f
    rw [show e + c + 1 + 1 = (e + (c + 1)) + 1 from by ring,
        show (1 : ℕ) + 1 = 2 from rfl]
    step fm; step fm; step fm
    have h := r2_chain (c + 1) 1 0 (d + 2) e f
    simp only [Nat.zero_add] at h
    rw [show 2 * c + 1 + 2 = 1 + 2 * (c + 1) from by ring,
        show d + 1 + 1 = d + 2 from by ring]
    apply stepStar_trans h
    ring_nf; finish
  · -- b + 2
    intro c d e f
    rw [show e + c + (b + 2) + 1 = (e + c + b + 1) + 2 from by ring,
        show (b + 2 : ℕ) + 1 = (b + 1) + 1 + 1 from by ring]
    step fm
    rw [show (b + 1 : ℕ) + 1 = (b + 1) + 1 from rfl]
    step fm; step fm
    rw [show 2 * c + (b + 1 + 1) + 2 = 2 * (c + 1) + b + 2 from by ring,
        show d + (b + 1 + 1) + 1 = (d + 2) + b + 1 from by ring,
        show d + 1 + 1 = d + 2 from by ring,
        show (e + c + b + 1) + 1 = e + (c + 1) + b + 1 from by ring]
    exact ih b (by omega) (c + 1) (d + 2) e f

theorem main_trans (n t : ℕ) :
    ⟨n + 1, 0, 0, n, t + n, t⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 1, t + 2 * n + 1, t + n⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨n + 1, 0, 0, n, t + n, t⟩ = some ⟨n, 0, 0, n, t + n + 2, t + 1⟩
    simp [fm]
  have h1 := r3_chain n 0 n (t + n + 2) (t + 1)
  simp only [Nat.zero_add] at h1
  apply stepStar_trans h1
  rw [show t + n + 2 + 2 * n = t + 3 * n + 2 from by ring,
      show t + 1 + n = t + n + 1 from by ring]
  have h2 := r4_chain n 0 0 (t + 3 * n + 2) (t + n + 1)
  simp only [Nat.zero_add] at h2
  apply stepStar_trans h2
  rw [show t + n + 1 = (t + n) + 1 from by ring]
  step fm
  have h3 := interleave n 0 0 (t + 2 * n + 1) (t + n)
  rw [show t + 2 * n + 1 + 0 + n + 1 = t + 3 * n + 2 from by ring,
      show 2 * 0 + n + 2 = n + 2 from by ring,
      show 0 + n + 1 = n + 1 from by ring] at h3
  apply stepStar_trans h3
  ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun p ↦ ⟨p.1 + 1, 0, 0, p.1, p.2 + p.1, p.2⟩) ⟨0, 0⟩
  intro ⟨n, t⟩
  refine ⟨⟨n + 1, t + n⟩, ?_⟩
  show ⟨n + 1, 0, 0, n, t + n, t⟩ [fm]⊢⁺ ⟨n + 2, 0, 0, n + 1, t + n + (n + 1), t + n⟩
  rw [show t + n + (n + 1) = t + 2 * n + 1 from by ring]
  exact main_trans n t

end Sz22_2003_unofficial_743
