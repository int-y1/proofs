import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1718: [77/45, 25/14, 22/5, 3/11, 35/2]

Vector representation:
```
 0 -2 -1  1  1
-1  0  2 -1  0
 1  0 -1  0  1
 0  1  0  0 -1
-1  0  1  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6 (1M context)
-/

namespace Sz22_2003_unofficial_1718

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | _ => none

theorem r3_chain_b0 : ∀ k, ∀ A C E,
    ⟨A, 0, C + k, 0, E⟩ [fm]⊢* ⟨A + k, 0, C, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A C E
  · exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih (A + 1) C (E + 1))
  rw [show A + 1 + k = A + (k + 1) from by ring, show E + 1 + k = E + (k + 1) from by ring]; finish

theorem r3_chain_b1 : ∀ k, ∀ A C E,
    ⟨A, 1, C + k, 0, E⟩ [fm]⊢* ⟨A + k, 1, C, 0, E + k⟩ := by
  intro k; induction' k with k ih <;> intro A C E
  · exists 0
  rw [show C + (k + 1) = (C + k) + 1 from by ring]; step fm
  apply stepStar_trans (ih (A + 1) C (E + 1))
  rw [show A + 1 + k = A + (k + 1) from by ring, show E + 1 + k = E + (k + 1) from by ring]; finish

theorem r4_chain : ∀ k, ∀ A B, ⟨A, B, 0, 0, k⟩ [fm]⊢* ⟨A, B + k, 0, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro A B
  · exists 0
  step fm; apply stepStar_trans (ih A (B + 1))
  rw [show B + 1 + k = B + (k + 1) from by ring]; finish

theorem r1r1r2_chain : ∀ k, ∀ A B D E,
    ⟨A + k, B + 4 * k, 2, D, E⟩ [fm]⊢* ⟨A, B, 2, D + k, E + 2 * k⟩ := by
  intro k; induction' k with k ih <;> intro A B D E
  · simp; exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show B + 4 * (k + 1) = (B + 4 * k) + 4 from by ring]
  apply stepStar_trans
    (stepStar_trans (step_stepStar (show fm ⟨(A+k)+1, (B+4*k)+4, 2, D, E⟩ = some ⟨(A+k)+1, (B+4*k)+2, 1, D+1, E+1⟩ from by simp [fm]))
    (stepStar_trans (step_stepStar (show fm ⟨(A+k)+1, (B+4*k)+2, 1, D+1, E+1⟩ = some ⟨(A+k)+1, B+4*k, 0, D+2, E+2⟩ from by simp [fm]))
      (step_stepStar (show fm ⟨(A+k)+1, B+4*k, 0, D+2, E+2⟩ = some ⟨A+k, B+4*k, 2, D+1, E+2⟩ from by simp [fm]))))
  apply stepStar_trans (ih A B (D + 1) (E + 2))
  rw [show D + 1 + k = D + (k + 1) from by ring, show E + 2 + 2 * k = E + 2 * (k + 1) from by ring]; finish

theorem r3r2_alt_b0 : ∀ k, ∀ C D E,
    ⟨0, 0, C + 1, D + k, E⟩ [fm]⊢* ⟨0, 0, C + k + 1, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · ring_nf; finish
  rw [show D + (k + 1) = (D + k) + 1 from by ring]
  apply stepStar_trans
    (stepStar_trans (step_stepStar (show fm ⟨0, 0, C+1, (D+k)+1, E⟩ = some ⟨1, 0, C, (D+k)+1, E+1⟩ from by simp [fm]))
      (step_stepStar (show fm ⟨1, 0, C, (D+k)+1, E+1⟩ = some ⟨0, 0, C+2, D+k, E+1⟩ from by simp [fm])))
  rw [show C + 2 = (C + 1) + 1 from by ring]
  apply stepStar_trans (ih (C + 1) D (E + 1))
  rw [show C + 1 + k + 1 = C + (k + 1) + 1 from by ring, show E + 1 + k = E + (k + 1) from by ring]; finish

theorem r3r2_alt_b1 : ∀ k, ∀ C D E,
    ⟨0, 1, C + 1, D + k, E⟩ [fm]⊢* ⟨0, 1, C + k + 1, D, E + k⟩ := by
  intro k; induction' k with k ih <;> intro C D E
  · ring_nf; finish
  rw [show D + (k + 1) = (D + k) + 1 from by ring]
  apply stepStar_trans
    (stepStar_trans (step_stepStar (show fm ⟨0, 1, C+1, (D+k)+1, E⟩ = some ⟨1, 1, C, (D+k)+1, E+1⟩ from by simp [fm]))
      (step_stepStar (show fm ⟨1, 1, C, (D+k)+1, E+1⟩ = some ⟨0, 1, C+2, D+k, E+1⟩ from by simp [fm])))
  rw [show C + 2 = (C + 1) + 1 from by ring]
  apply stepStar_trans (ih (C + 1) D (E + 1))
  rw [show C + 1 + k + 1 = C + (k + 1) + 1 from by ring, show E + 1 + k = E + (k + 1) from by ring]; finish

theorem r2_chain_b0 : ∀ k, ∀ A C D E,
    ⟨A + k, 0, C, D + k, E⟩ [fm]⊢* ⟨A, 0, C + 2 * k, D, E⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring, show D + (k + 1) = (D + k) + 1 from by ring]
  apply stepStar_trans (step_stepStar (show fm ⟨(A+k)+1, 0, C, (D+k)+1, E⟩ = some ⟨A+k, 0, C+2, D+k, E⟩ from by simp [fm]))
  apply stepStar_trans (ih A (C + 2) D E)
  rw [show C + 2 + 2 * k = C + 2 * (k + 1) from by ring]; finish

theorem r2_chain_b1 : ∀ k, ∀ A C D E,
    ⟨A + k, 1, C, D + k, E⟩ [fm]⊢* ⟨A, 1, C + 2 * k, D, E⟩ := by
  intro k; induction' k with k ih <;> intro A C D E
  · simp; exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring, show D + (k + 1) = (D + k) + 1 from by ring]
  apply stepStar_trans (step_stepStar (show fm ⟨(A+k)+1, 1, C, (D+k)+1, E⟩ = some ⟨A+k, 1, C+2, D+k, E⟩ from by simp [fm]))
  apply stepStar_trans (ih A (C + 2) D E)
  rw [show C + 2 + 2 * k = C + 2 * (k + 1) from by ring]; finish

theorem tail_b0 (C D E : ℕ) (hC : C ≥ 1) :
    ⟨0, 0, C, D, E⟩ [fm]⊢* ⟨C + D, E + C + 2 * D, 0, 0, 0⟩ := by
  have h1 : ⟨0, 0, C, D, E⟩ [fm]⊢* ⟨0, 0, C + D, 0, E + D⟩ := by
    rcases D with _ | D; · simp; exists 0
    have h := r3r2_alt_b0 (D + 1) (C - 1) 0 E
    rw [show (C - 1) + 1 = C from by omega, show C - 1 + (D + 1) + 1 = C + (D + 1) from by omega,
        show 0 + (D + 1) = D + 1 from by ring] at h; exact h
  have h2 := r3_chain_b0 (C + D) 0 0 (E + D)
  rw [show 0 + (C + D) = C + D from by ring, show E + D + (C + D) = E + C + 2 * D from by ring] at h2
  have h3 := r4_chain (E + C + 2 * D) (C + D) 0
  rw [show 0 + (E + C + 2 * D) = E + C + 2 * D from by ring] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem tail_b1 (C D E : ℕ) (hC : C ≥ 1) :
    ⟨0, 1, C, D, E⟩ [fm]⊢* ⟨C + D, 1 + E + C + 2 * D, 0, 0, 0⟩ := by
  have h1 : ⟨0, 1, C, D, E⟩ [fm]⊢* ⟨0, 1, C + D, 0, E + D⟩ := by
    rcases D with _ | D; · simp; exists 0
    have h := r3r2_alt_b1 (D + 1) (C - 1) 0 E
    rw [show (C - 1) + 1 = C from by omega, show C - 1 + (D + 1) + 1 = C + (D + 1) from by omega,
        show 0 + (D + 1) = D + 1 from by ring] at h; exact h
  have h2 := r3_chain_b1 (C + D) 0 0 (E + D)
  rw [show 0 + (C + D) = C + D from by ring, show E + D + (C + D) = E + C + 2 * D from by ring] at h2
  have h3 := r4_chain (E + C + 2 * D) (C + D) 1
  rw [show 1 + (E + C + 2 * D) = 1 + E + C + 2 * D from by ring] at h3
  exact stepStar_trans h1 (stepStar_trans h2 h3)

theorem main_trans (n : ℕ) :
    ⟨n + 2, 3 * (n + 1), 0, 0, 0⟩ [fm]⊢⁺ ⟨n + 3, 3 * (n + 2), 0, 0, 0⟩ := by
  rw [show n + 2 = (n + 1) + 1 from by ring, show 3 * (n + 1) = (3 * n + 1) + 2 from by ring]
  apply step_stepStar_stepPlus (show fm ⟨(n+1)+1, (3*n+1)+2, 0, 0, 0⟩ = some ⟨n+1, (3*n+1)+2, 1, 1, 0⟩ from by simp [fm])
  apply stepStar_trans (step_stepStar (show fm ⟨n+1, (3*n+1)+2, 1, 1, 0⟩ = some ⟨n+1, 3*n+1, 0, 2, 1⟩ from by simp [fm]))
  apply stepStar_trans (step_stepStar (show fm ⟨n+1, 3*n+1, 0, 2, 1⟩ = some ⟨n, 3*n+1, 2, 1, 1⟩ from by simp [fm]))
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rcases Nat.even_or_odd m with ⟨p, hp⟩ | ⟨p, hp⟩
    · -- n = 4p
      have hn : n = 4 * p := by omega
      subst hn; rw [show 3 * (4 * p) + 1 = 12*p+1 from by ring, show 4*p+3 = 4*p+3 from rfl, show 3*(4*p+1+1) = 12*p+6 from by ring]
      have h1 := r1r1r2_chain (3*p) p 1 1 1
      rw [show p+3*p = 4*p from by ring, show 1+4*(3*p) = 12*p+1 from by ring, show 1+3*p = 3*p+1 from by ring, show 1+2*(3*p) = 6*p+1 from by ring] at h1
      apply stepStar_trans h1
      have h2 := r2_chain_b1 p 0 2 (2*p+1) (6*p+1)
      rw [show 0+p = p from by ring, show (2*p+1)+p = 3*p+1 from by ring, show 2+2*p = 2*p+2 from by ring] at h2
      apply stepStar_trans h2
      have h3 := tail_b1 (2*p+2) (2*p+1) (6*p+1) (by omega)
      rw [show 2*p+2+(2*p+1) = 4*p+3 from by ring, show 1+(6*p+1)+(2*p+2)+2*(2*p+1) = 12*p+6 from by ring] at h3
      exact h3
    · -- n = 4p+2
      have hn : n = 4 * p + 2 := by omega
      subst hn; rw [show 3*(4*p+2)+1 = 12*p+7 from by ring, show 4*p+2+3 = 4*p+5 from by ring, show 3*(4*p+2+1+1) = 12*p+12 from by ring]
      have h1 := r1r1r2_chain (3*p+1) (p+1) 3 1 1
      rw [show (p+1)+(3*p+1) = 4*p+2 from by ring, show 3+4*(3*p+1) = 12*p+7 from by ring, show 1+(3*p+1) = 3*p+2 from by ring, show 1+2*(3*p+1) = 6*p+3 from by ring] at h1
      apply stepStar_trans h1
      apply stepStar_trans (step_stepStar (show fm ⟨p+1, 3, 2, 3*p+2, 6*p+3⟩ = some ⟨p+1, 1, 1, 3*p+3, 6*p+4⟩ from by simp [fm]))
      have h2 := r2_chain_b1 (p+1) 0 1 (2*p+2) (6*p+4)
      rw [show 0+(p+1) = p+1 from by ring, show (2*p+2)+(p+1) = 3*p+3 from by ring, show 1+2*(p+1) = 2*p+3 from by ring] at h2
      apply stepStar_trans h2
      have h3 := tail_b1 (2*p+3) (2*p+2) (6*p+4) (by omega)
      rw [show 2*p+3+(2*p+2) = 4*p+5 from by ring, show 1+(6*p+4)+(2*p+3)+2*(2*p+2) = 12*p+12 from by ring] at h3
      exact h3
  · rcases Nat.even_or_odd m with ⟨p, hp⟩ | ⟨p, hp⟩
    · -- n = 4p+1
      have hn : n = 4 * p + 1 := by omega
      subst hn; rw [show 3*(4*p+1)+1 = 12*p+4 from by ring, show 4*p+1+3 = 4*p+4 from by ring, show 3*(4*p+1+1+1) = 12*p+9 from by ring]
      have h1 := r1r1r2_chain (3*p+1) p 0 1 1
      rw [show p+(3*p+1) = 4*p+1 from by ring, show 0+4*(3*p+1) = 12*p+4 from by ring, show 1+(3*p+1) = 3*p+2 from by ring, show 1+2*(3*p+1) = 6*p+3 from by ring] at h1
      apply stepStar_trans h1
      have h2 := r2_chain_b0 p 0 2 (2*p+2) (6*p+3)
      rw [show 0+p = p from by ring, show (2*p+2)+p = 3*p+2 from by ring, show 2+2*p = 2*p+2 from by ring] at h2
      apply stepStar_trans h2
      have h3 := tail_b0 (2*p+2) (2*p+2) (6*p+3) (by omega)
      rw [show 2*p+2+(2*p+2) = 4*p+4 from by ring, show (6*p+3)+(2*p+2)+2*(2*p+2) = 12*p+9 from by ring] at h3
      exact h3
    · -- n = 4p+3
      have hn : n = 4 * p + 3 := by omega
      subst hn; rw [show 3*(4*p+3)+1 = 12*p+10 from by ring, show 4*p+3+3 = 4*p+6 from by ring, show 3*(4*p+3+1+1) = 12*p+15 from by ring]
      have h1 := r1r1r2_chain (3*p+2) (p+1) 2 1 1
      rw [show (p+1)+(3*p+2) = 4*p+3 from by ring, show 2+4*(3*p+2) = 12*p+10 from by ring, show 1+(3*p+2) = 3*p+3 from by ring, show 1+2*(3*p+2) = 6*p+5 from by ring] at h1
      apply stepStar_trans h1
      apply stepStar_trans (step_stepStar (show fm ⟨p+1, 2, 2, 3*p+3, 6*p+5⟩ = some ⟨p+1, 0, 1, 3*p+4, 6*p+6⟩ from by simp [fm]))
      have h2 := r2_chain_b0 (p+1) 0 1 (2*p+3) (6*p+6)
      rw [show 0+(p+1) = p+1 from by ring, show (2*p+3)+(p+1) = 3*p+4 from by ring, show 1+2*(p+1) = 2*p+3 from by ring] at h2
      apply stepStar_trans h2
      have h3 := tail_b0 (2*p+3) (2*p+3) (6*p+6) (by omega)
      rw [show 2*p+3+(2*p+3) = 4*p+6 from by ring, show (6*p+6)+(2*p+3)+2*(2*p+3) = 12*p+15 from by ring] at h3
      exact h3

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 3, 0, 0, 0⟩) (by execute fm 8)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨n + 2, 3 * (n + 1), 0, 0, 0⟩) 0
  intro n; exists n + 1
  show ⟨n + 2, 3 * (n + 1), 0, 0, 0⟩ [fm]⊢⁺ ⟨(n + 1) + 2, 3 * ((n + 1) + 1), 0, 0, 0⟩
  rw [show (n + 1) + 2 = n + 3 from by ring, show 3 * ((n + 1) + 1) = 3 * (n + 2) from by ring]
  exact main_trans n

end Sz22_2003_unofficial_1718
