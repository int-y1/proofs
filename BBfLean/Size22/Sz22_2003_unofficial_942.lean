import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #942: [4/15, 33/14, 25/2, 7/11, 99/5]

Vector representation:
```
 2 -1 -1  0  0
-1  1  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 0  2 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_942

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | _ => none

theorem r4_drain : ∀ k, ∀ c d,
    ⟨0, 0, c, d, k⟩ [fm]⊢* ⟨0, 0, c, d + k, 0⟩ := by
  intro k; induction' k with k ih <;> intro c d
  · ring_nf; finish
  · rw [show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; apply stepStar_trans (ih c (d + 1)); ring_nf; finish

theorem r3_drain : ∀ k, ∀ c e,
    ⟨k, 0, c, 0, e⟩ [fm]⊢* ⟨0, 0, c + 2 * k, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro c e
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih (c + 2) e); ring_nf; finish

theorem r2r1_chain : ∀ k, ∀ a c e,
    ⟨a + 1, 0, c + k, k, e + 1⟩ [fm]⊢* ⟨a + k + 1, 0, c, 0, e + k + 1⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · ring_nf; finish
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show (k : ℕ) + 1 = k + 1 from rfl]
    step fm; step fm
    apply stepStar_trans (ih (a + 1) c (e + 1)); ring_nf; finish

theorem main_trans (c n : ℕ) (hc : c ≥ n + 4) :
    ⟨0, 0, c, 0, n + 1⟩ [fm]⊢⁺ ⟨0, 0, c + n + 6, 0, n + 2⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, c, 0, (n : ℕ) + 1⟩ = some ⟨0, 0, c, 1, n⟩
    unfold fm; simp only
  have h1 : ⟨0, 0, c, 1, n⟩ [fm]⊢* ⟨0, 0, c, n + 1, 0⟩ := by
    have h := r4_drain n c 1
    rw [show 1 + n = n + 1 from by ring] at h; exact h
  have h2 : ⟨0, 0, c, n + 1, 0⟩ [fm]⊢* ⟨0, 2, c - 1, n + 1, 1⟩ := by
    rw [show c = (c - 1) + 1 from by omega]
    step fm; finish
  have h3 : ⟨0, 2, c - 1, n + 1, 1⟩ [fm]⊢* ⟨4, 0, c - 3, n + 1, 1⟩ := by
    rw [show c - 1 = (c - 3) + 1 + 1 from by omega,
        show (2 : ℕ) = 1 + 1 from rfl]
    step fm; step fm; finish
  have h4 : ⟨4, 0, c - 3, n + 1, 1⟩ [fm]⊢* ⟨n + 5, 0, c - n - 4, 0, n + 2⟩ := by
    have h := r2r1_chain (n + 1) 3 (c - n - 4) 0
    rw [show (c - n - 4) + (n + 1) = c - 3 from by omega,
        show 3 + (n + 1) + 1 = n + 5 from by ring,
        show 0 + (n + 1) + 1 = n + 2 from by ring,
        show (n : ℕ) + 1 = n + 1 from rfl] at h
    exact h
  have h5 : ⟨n + 5, 0, c - n - 4, 0, n + 2⟩ [fm]⊢* ⟨0, 0, c + n + 6, 0, n + 2⟩ := by
    have h := r3_drain (n + 5) (c - n - 4) (n + 2)
    rw [show c - n - 4 + 2 * (n + 5) = c + n + 6 from by omega] at h
    exact h
  exact stepStar_trans h1 (stepStar_trans h2 (stepStar_trans h3 (stepStar_trans h4 h5)))

def cv : ℕ → ℕ
  | 0 => 7
  | n + 1 => cv n + n + 6

theorem cv_ge (n : ℕ) : cv n ≥ n + 4 := by
  induction n with
  | zero => simp [cv]
  | succ n ih => simp [cv]; omega

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 7, 0, 1⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, cv n, 0, n + 1⟩) 0
  intro n
  refine ⟨n + 1, ?_⟩
  show ⟨0, 0, cv n, 0, n + 1⟩ [fm]⊢⁺ ⟨0, 0, cv (n + 1), 0, n + 2⟩
  simp only [cv]
  exact main_trans (cv n) n (cv_ge n)

end Sz22_2003_unofficial_942
