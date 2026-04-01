import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1448: [7/15, 242/3, 9/77, 5/121, 33/2]

Vector representation:
```
 0 -1 -1  1  0
 1 -1  0  0  2
 0  2  0 -1 -1
 0  0  1  0 -2
-1  1  0  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1448

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e+2⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b, c, d, e+2⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d, e+1⟩
  | _ => none

theorem e_to_c : ∀ k, ∀ a c e, (⟨a, 0, c, 0, e + 2 * k⟩ : Q) [fm]⊢*
    ⟨a, 0, c + k, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a c e; ring_nf; finish
  | succ k ih =>
    intro a c e
    rw [show e + 2 * (k + 1) = e + 2 * k + 2 from by ring]
    step fm
    apply stepStar_trans (ih a (c + 1) e); ring_nf; finish

theorem eat3 : ∀ k, ∀ a c d, (⟨a + k, 0, c + 3 * k, d + 1, 0⟩ : Q) [fm]⊢*
    ⟨a, 0, c, d + 2 * k + 1, 0⟩ := by
  intro k; induction k with
  | zero => intro a c d; ring_nf; finish
  | succ k ih =>
    intro a c d
    rw [show a + (k + 1) = (a + k) + 1 from by ring,
        show c + 3 * (k + 1) = (c + 3 * k) + 3 from by ring]
    step fm; step fm; step fm; step fm; step fm
    apply stepStar_trans (ih a c (d + 2)); ring_nf; finish

-- c_drain with E ∈ {0, 1} and invariant tracking
theorem c_drain : ∀ C, ∀ A D E, 3 * A ≥ C + 4 → E ≤ 1 →
    ∃ A' D' E', (⟨A, 0, C + 1, D + 1, E + 1⟩ : Q) [fm]⊢*
      ⟨A', 0, 0, D' + 1, E' + 1⟩ ∧ E' ≤ 2 := by
  intro C; induction C using Nat.strongRecOn with
  | _ C ih =>
  intro A D E hA hE
  rcases C with _ | _ | _ | C
  · -- C = 0: R3+R1+R2 -> (A+1, 0, 0, D+1, E+2)
    exact ⟨A + 1, D, E + 1, by step fm; step fm; step fm; ring_nf; finish, by omega⟩
  · -- C = 1
    rcases E with _ | E
    · -- E = 0: (A, 0, 2, D+1, 1). R3+R1+R1+R5+R2 -> (A, 0, 0, D+2, 3)
      obtain ⟨A0, rfl⟩ : ∃ A0, A = A0 + 2 := ⟨A - 2, by omega⟩
      exact ⟨A0 + 2, D + 1, 2, by
        show (⟨A0 + 2, 0, 0 + 1 + 1, D + 1, 0 + 1⟩ : Q) [fm]⊢*
          ⟨A0 + 2, 0, 0, (D + 1) + 1, 2 + 1⟩
        step fm; step fm; step fm; step fm; step fm; ring_nf; finish, by omega⟩
    · -- E = 1: (A, 0, 2, D+1, 2). R3+R1+R1 -> (A, 0, 0, D+2, 1)
      rcases E with _ | E
      · exact ⟨A, D + 1, 0, by
          show (⟨A, 0, 0 + 1 + 1, D + 1, (0 + 1) + 1⟩ : Q) [fm]⊢*
            ⟨A, 0, 0, (D + 1) + 1, 0 + 1⟩
          step fm; step fm; step fm; ring_nf; finish, by omega⟩
      · omega
  · -- C = 2
    rcases E with _ | E
    · -- E = 0: (A, 0, 3, D+1, 1). R3+R1+R1+R5+R1 -> (A-1, 0, 0, D+3, 1)
      obtain ⟨A0, rfl⟩ : ∃ A0, A = A0 + 2 := ⟨A - 2, by omega⟩
      exact ⟨A0 + 1, D + 2, 0, by
        show (⟨A0 + 2, 0, 0 + 1 + 1 + 1, D + 1, 0 + 1⟩ : Q) [fm]⊢*
          ⟨A0 + 1, 0, 0, (D + 2) + 1, 0 + 1⟩
        step fm; step fm; step fm; step fm; step fm; ring_nf; finish, by omega⟩
    · -- E >= 1
      rcases E with _ | E
      · -- E = 1: (A, 0, 3, D+1, 2). R3+R1+R1+R3+R1+R2 -> (A+1, 0, 0, D+2, 2)
        exact ⟨A + 1, D + 1, 1, by
          show (⟨A, 0, 0 + 1 + 1 + 1, D + 1, (0 + 1) + 1⟩ : Q) [fm]⊢*
            ⟨A + 1, 0, 0, (D + 1) + 1, 1 + 1⟩
          step fm; step fm; step fm; step fm; step fm; step fm; ring_nf; finish, by omega⟩
      · omega
  · -- C >= 3
    rcases E with _ | E
    · -- E = 0: (A, 0, C+4, D+1, 1). R3+R1+R1+R5+R1 -> (A-1, 0, C+1, D+3, 1).
      -- Recurse with C' = C, A' = A-1, E' = 0
      obtain ⟨A0, rfl⟩ : ∃ A0, A = A0 + 2 := ⟨A - 2, by omega⟩
      obtain ⟨A', D', E', hstep, hE'⟩ := ih C (by omega) (A0 + 1) (D + 2) 0 (by omega) (by omega)
      exact ⟨A', D', E', by
        show (⟨A0 + 2, 0, C + 1 + 1 + 1 + 1, D + 1, 0 + 1⟩ : Q) [fm]⊢* _
        step fm; step fm; step fm; step fm; step fm
        apply stepStar_trans _ hstep; ring_nf; finish, hE'⟩
    · rcases E with _ | E
      · -- E = 1: (A, 0, C+4, D+1, 2). R3+R1+R1 -> (A, 0, C+2, D+2, 1).
        -- But C+2 is still c+1 form with c = C+1. So recurse with C'=C+1, E=0.
        obtain ⟨A', D', E', hstep, hE'⟩ := ih (C + 1) (by omega) A (D + 1) 0 (by omega) (by omega)
        exact ⟨A', D', E', by
          show (⟨A, 0, C + 1 + 1 + 1 + 1, D + 1, (0 + 1) + 1⟩ : Q) [fm]⊢* _
          step fm; step fm; step fm
          apply stepStar_trans _ hstep; ring_nf; finish, hE'⟩
      · omega

-- Refill for even e: via (a+1, 0, k+1, 1, 1) with E_param = 0
theorem refill_even (a k : ℕ) (hinv : 3 * a + 3 ≥ 2 * k + 1) :
    ∃ A' D' E', (⟨a + 1, 0, k + 1, 1, 1⟩ : Q) [fm]⊢* ⟨A', 0, 0, D' + 1, E' + 1⟩ ∧
    3 * A' + 3 ≥ E' + 1 := by
  rcases k with _ | _ | _ | k
  · refine ⟨a + 2, 0, 1, ?_, by omega⟩
    step fm; step fm; step fm; ring_nf; finish
  · refine ⟨a + 1, 1, 2, ?_, by omega⟩
    show (⟨a + 1, 0, 0 + 1 + 1, 1, 1⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, 1 + 1, 2 + 1⟩
    step fm; step fm; step fm; step fm; step fm; ring_nf; finish
  · refine ⟨a, 2, 0, ?_, by omega⟩
    show (⟨a + 1, 0, 0 + 1 + 1 + 1, 1, 1⟩ : Q) [fm]⊢* ⟨a, 0, 0, 2 + 1, 0 + 1⟩
    step fm; step fm; step fm; step fm; step fm; ring_nf; finish
  · have : k + 3 + 1 = k + 1 + 1 + 1 + 1 := by ring
    rw [show k + 1 + 1 + 1 + 1 = k + 3 + 1 from by ring] at *
    obtain ⟨A', D', E', hstep, hE'⟩ := c_drain (k + 3) (a + 1) 0 0 (by omega) (by omega)
    exact ⟨A', D', E', hstep, by omega⟩

-- Refill for odd e: via (a+1, 0, k+1, 1, 2) with E_param = 1
theorem refill_odd (a k : ℕ) (hinv : 3 * a + 3 ≥ 2 * k + 2) :
    ∃ A' D' E', (⟨a + 1, 0, k + 1, 1, 2⟩ : Q) [fm]⊢* ⟨A', 0, 0, D' + 1, E' + 1⟩ ∧
    3 * A' + 3 ≥ E' + 1 := by
  rcases k with _ | _ | k
  · refine ⟨a + 2, 0, 2, ?_, by omega⟩
    step fm; step fm; step fm; ring_nf; finish
  · refine ⟨a + 1, 1, 0, ?_, by omega⟩
    show (⟨a + 1, 0, 0 + 1 + 1, 1, 2⟩ : Q) [fm]⊢* ⟨a + 1, 0, 0, 1 + 1, 0 + 1⟩
    step fm; step fm; step fm; ring_nf; finish
  · rw [show k + 1 + 1 + 1 = k + 2 + 1 from by ring] at *
    obtain ⟨A', D', E', hstep, hE'⟩ := c_drain (k + 2) (a + 1) 0 1 (by omega) (by omega)
    exact ⟨A', D', E', hstep, by omega⟩

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 0, 1, 3⟩) (by execute fm 15)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d e, q = ⟨a, 0, 0, d + 1, e + 1⟩ ∧ 3 * a + 3 ≥ e + 1)
  · intro q ⟨a, d, e, hq, hinv⟩; subst hq
    rcases d with _ | d
    · -- d = 0: refill
      rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [show k + k = 2 * k from by ring] at hk; subst hk
        have h_e2c : (⟨a + 2, 0, 0, 0, 2 * k + 4⟩ : Q) [fm]⊢* ⟨a + 2, 0, k + 2, 0, 0⟩ := by
          rw [show 2 * k + 4 = 0 + 2 * (k + 2) from by ring]
          have := e_to_c (k + 2) (a + 2) 0 0; convert this using 2; ring_nf
        have h_r5r1 : (⟨a + 2, 0, k + 2, 0, 0⟩ : Q) [fm]⊢* ⟨a + 1, 0, k + 1, 1, 1⟩ := by
          rw [show k + 2 = (k + 1) + 1 from by ring, show a + 2 = (a + 1) + 1 from by ring]
          step fm; step fm; finish
        obtain ⟨A', D', E', hcd, hinv'⟩ := refill_even a k hinv
        exact ⟨⟨A', 0, 0, D' + 1, E' + 1⟩, ⟨A', D', E', rfl, hinv'⟩,
          by apply step_stepStar_stepPlus
             · show fm ⟨a, 0, 0, 0 + 1, 2 * k + 1⟩ = some ⟨a, 2, 0, 0, 2 * k⟩; rfl
             step fm; step fm
             rw [show a + 1 + 1 = a + 2 from by ring, show 2 * k + 2 + 2 = 2 * k + 4 from by ring]
             exact stepStar_trans h_e2c (stepStar_trans h_r5r1 hcd)⟩
      · subst hk
        have h_e2c : (⟨a + 2, 0, 0, 0, 2 * k + 5⟩ : Q) [fm]⊢* ⟨a + 2, 0, k + 2, 0, 1⟩ := by
          rw [show 2 * k + 5 = 1 + 2 * (k + 2) from by ring]
          have := e_to_c (k + 2) (a + 2) 0 1; convert this using 2; ring_nf
        have h_r5r1 : (⟨a + 2, 0, k + 2, 0, 1⟩ : Q) [fm]⊢* ⟨a + 1, 0, k + 1, 1, 2⟩ := by
          rw [show k + 2 = (k + 1) + 1 from by ring, show a + 2 = (a + 1) + 1 from by ring]
          step fm; step fm; finish
        obtain ⟨A', D', E', hcd, hinv'⟩ := refill_odd a k (by omega)
        exact ⟨⟨A', 0, 0, D' + 1, E' + 1⟩, ⟨A', D', E', rfl, hinv'⟩,
          by apply step_stepStar_stepPlus
             · show fm ⟨a, 0, 0, 0 + 1, 2 * k + 1 + 1⟩ = some ⟨a, 2, 0, 0, 2 * k + 1⟩; rfl
             step fm; step fm
             rw [show a + 1 + 1 = a + 2 from by ring,
                 show 2 * k + 1 + 2 + 2 = 2 * k + 5 from by ring]
             exact stepStar_trans h_e2c (stepStar_trans h_r5r1 hcd)⟩
    · -- d >= 1: one step of d-drain
      exact ⟨⟨a + 2, 0, 0, d + 1, e + 4⟩, ⟨a + 2, d, e + 3, rfl, by omega⟩,
        by rw [show d + 2 = (d + 1) + 1 from by ring]
           step fm; step fm; step fm; ring_nf; finish⟩
  · exact ⟨2, 0, 2, rfl, by omega⟩

end Sz22_2003_unofficial_1448
