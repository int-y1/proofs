import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #565: [35/18, 4/55, 77/2, 3/7, 10/11]

Vector representation:
```
-1 -2  1  1  0
 2  0 -1  0 -1
-1  0  0  1  1
 0  1  0 -1  0
 1  0  1  0 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_565

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+2, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+1, d, e⟩
  | _ => none

-- R4 chain: d to b
theorem d_to_b : ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  have h : ∀ k b, ⟨0, b, 0, d + k, e⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
    intro k; induction' k with k ih <;> intro b
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _); ring_nf; finish
  exact h k b

-- R3 drain with b=0
theorem r3_drain_b0 : ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
  have h : ∀ k a d e, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e + k⟩ := by
    intro k; induction' k with k ih <;> intro a d e
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish
  exact h k a d e

-- R3 drain with b=1
theorem r3_drain_b1 : ⟨a + k, 1, 0, d, e⟩ [fm]⊢* ⟨a, 1, 0, d + k, e + k⟩ := by
  have h : ∀ k a d e, ⟨a + k, 1, 0, d, e⟩ [fm]⊢* ⟨a, 1, 0, d + k, e + k⟩ := by
    intro k; induction' k with k ih <;> intro a d e
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish
  exact h k a d e

-- General lower phase with b=0: by induction on c
-- (a+1, 0, c, d, e) ->* (0, 0, 0, d+2c+a+1, c+e+a+1)
theorem gen_lower_b0 :
    ∀ c, ∀ a d e, ⟨a+1, 0, c, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2*c + a + 1, c + e + a + 1⟩ := by
  intro c; induction' c with c ih <;> intro a d e
  · rw [show a + 1 = 0 + (a + 1) from by ring]
    apply stepStar_trans r3_drain_b0; ring_nf; finish
  · rcases e with _ | e
    · -- e=0, c+1: R3 fires (a+1 >= 1), then R2 fires (c+1 >= 1, e=1)
      step fm; step fm
      apply stepStar_trans (ih _ _ _); ring_nf; finish
    · -- e>=1, c+1: R2 fires (c+1 >= 1, e+1 >= 1)
      step fm
      apply stepStar_trans (ih _ _ _); ring_nf; finish

-- General lower phase with b=1
theorem gen_lower_b1 :
    ∀ c, ∀ a d e, ⟨a+1, 1, c, d, e⟩ [fm]⊢* ⟨0, 1, 0, d + 2*c + a + 1, c + e + a + 1⟩ := by
  intro c; induction' c with c ih <;> intro a d e
  · rw [show a + 1 = 0 + (a + 1) from by ring]
    apply stepStar_trans r3_drain_b1; ring_nf; finish
  · rcases e with _ | e
    · step fm; step fm
      apply stepStar_trans (ih _ _ _); ring_nf; finish
    · step fm
      apply stepStar_trans (ih _ _ _); ring_nf; finish

-- Upper R1,R1,R2 rounds
theorem upper_rounds :
    ⟨2, b + 4 * k, c, d, k + e⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e⟩ := by
  have h : ∀ k b c d, ⟨2, b + 4 * k, c, d, k + e⟩ [fm]⊢* ⟨2, b, c + k, d + 2 * k, e⟩ := by
    intro k; induction' k with k ih <;> intro b c d
    · ring_nf; finish
    rw [Nat.mul_succ, ← Nat.add_assoc, show (k + 1) + e = k + e + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish
  exact h k b c d

-- Tail b=3: R1 then gen_lower_b1
theorem tail_b3_lower :
    ⟨2, 3, c, d, e⟩ [fm]⊢* ⟨0, 1, 0, d + 2 * c + 4, c + e + 2⟩ := by
  -- R1: (1, 1, c+1, d+1, e). gen_lower_b1 with a+1 = 1.
  step fm
  apply stepStar_trans (gen_lower_b1 (c+1) 0 (d+1) e)
  ring_nf; finish

-- Tail b=2: R1 then gen_lower_b0
theorem tail_b2_lower :
    ⟨2, 2, c, d, e⟩ [fm]⊢* ⟨0, 0, 0, d + 2 * c + 4, c + e + 2⟩ := by
  step fm
  apply stepStar_trans (gen_lower_b0 (c+1) 0 (d+1) e)
  ring_nf; finish

-- Interleaving for E odd
theorem interleave_odd :
    ∀ k, ⟨0, 6 * k + 1, 0, 0, 2 * k + 1⟩ [fm]⊢* ⟨0, 1, 0, 6 * k + 3, 2 * k + 2⟩ := by
  intro k; rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm; rcases m with _ | m
    · execute fm 5
    · step fm; step fm; step fm
      suffices h : ⟨2, 3 + 4*(3*m+2), 1, 1, (3*m+2)+(m+1)⟩ [fm]⊢*
          ⟨0, 1, 0, 6*(2*(m+1))+3, 2*(2*(m+1))+2⟩ by convert h using 2; all_goals (simp [Nat.mul_comm, Nat.add_comm]; try ring_nf)
      apply stepStar_trans upper_rounds
      apply stepStar_trans tail_b3_lower
      ring_nf; finish
  · subst hm; rcases m with _ | m
    · execute fm 14
    · step fm; step fm; step fm
      suffices h : ⟨2, 1 + 4*(3*m+4), 1, 1, (3*m+4)+(m+1)⟩ [fm]⊢*
          ⟨0, 1, 0, 6*(2*(m+1)+1)+3, 2*(2*(m+1)+1)+2⟩ by convert h using 2; all_goals (simp [Nat.mul_comm, Nat.add_comm]; try ring_nf)
      apply stepStar_trans upper_rounds
      apply stepStar_trans (gen_lower_b1 _ 1 _ _)
      ring_nf; finish

-- Interleaving for E even
theorem interleave_even :
    ∀ k, ⟨0, 6 * k + 4, 0, 0, 2 * k + 2⟩ [fm]⊢* ⟨0, 0, 0, 6 * k + 7, 2 * k + 3⟩ := by
  intro k; rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm; rcases m with _ | m
    · execute fm 11
    · step fm; step fm; step fm
      suffices h : ⟨2, 2 + 4*(3*m+3), 1, 1, (3*m+3)+(m+1)⟩ [fm]⊢*
          ⟨0, 0, 0, 6*(2*(m+1))+7, 2*(2*(m+1))+3⟩ by convert h using 2; all_goals (simp [Nat.mul_comm, Nat.add_comm]; try ring_nf)
      apply stepStar_trans upper_rounds
      apply stepStar_trans tail_b2_lower
      ring_nf; finish
  · subst hm; rcases m with _ | m
    · execute fm 20
    · step fm; step fm; step fm
      suffices h : ⟨2, 0 + 4*(3*m+5), 1, 1, (3*m+5)+(m+1)⟩ [fm]⊢*
          ⟨0, 0, 0, 6*(2*(m+1)+1)+7, 2*(2*(m+1)+1)+3⟩ by convert h using 2; all_goals (simp [Nat.mul_comm, Nat.add_comm]; try ring_nf)
      apply stepStar_trans upper_rounds
      apply stepStar_trans (gen_lower_b0 _ 1 _ _)
      ring_nf; finish

-- Main transition
theorem main_trans (n : ℕ) :
    ⟨0, 0, 0, 6 * n + 1, 2 * n + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 6 * n + 7, 2 * n + 3⟩ := by
  rw [show (6 * n + 1 : ℕ) = 0 + (6 * n + 0 + 1) from by omega]
  apply step_stepStar_stepPlus
  · show fm ⟨0, 0, 0, 0 + (6 * n + 0 + 1), 2 * n + 1⟩ =
         some ⟨0, 0 + 1, 0, 6 * n + 0, 2 * n + 1⟩
    simp [fm]
  rw [show 6 * n + 0 = 0 + (6 * n) from by omega]
  apply stepStar_trans d_to_b
  suffices hs : ⟨0, 6*n+1, 0, 0, 2*n+1⟩ [fm]⊢* ⟨0, 0, 0, 6*n+7, 2*n+3⟩ by
    convert hs using 2; simp [Nat.mul_comm, Nat.add_comm]
  apply stepStar_trans (interleave_odd n)
  rw [show (6*n+3 : ℕ) = 0 + (6*n+3) from by omega]
  apply stepStar_trans d_to_b
  suffices hs2 : ⟨0, 6*n+4, 0, 0, 2*n+2⟩ [fm]⊢* ⟨0, 0, 0, 6*n+7, 2*n+3⟩ by
    convert hs2 using 2; simp [Nat.mul_comm, Nat.add_comm]; ring_nf
  exact interleave_even n

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 1⟩)
  · execute fm 1
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, 6 * n + 1, 2 * n + 1⟩) 0
  intro n; exists (n + 1)
  rw [show 6 * (n + 1) + 1 = 6 * n + 7 from by omega,
      show 2 * (n + 1) + 1 = 2 * n + 3 from by omega]
  exact main_trans n
