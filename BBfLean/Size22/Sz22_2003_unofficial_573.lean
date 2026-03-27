import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #573: [35/6, 11/2, 4/55, 3/7, 140/11]

Vector representation:
```
-1 -1  1  1  0
-1  0  0  0  1
 2  0 -1  0 -1
 0  1  0 -1  0
 2  0  1  1 -1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_573

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c+1, d, e+1⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+2, b, c+1, d+1, e⟩
  | _ => none

-- R4 repeated: convert d to b
theorem d_to_b : ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
  have h : ∀ k b, ⟨0, b, 0, d+k, e⟩ [fm]⊢* ⟨0, b+k, 0, d, e⟩ := by
    intro k; induction' k with k ih <;> intro b
    · exists 0
    rw [← Nat.add_assoc]; step fm
    apply stepStar_trans (ih _); ring_nf; finish
  exact h k b

-- R5+R1+R1 opening (3 steps, ⊢⁺)
theorem opening : ⟨0, b+2, 0, 0, e+1⟩ [fm]⊢⁺ ⟨0, b, 3, 3, e⟩ := by
  step fm; step fm; step fm; finish

-- R3+R1+R1 chain with arbitrary remaining b
theorem r3r1r1_chain :
    ⟨0, b+2*k, c+1, d, e+k+1⟩ [fm]⊢* ⟨0, b, c+k+1, d+2*k, e+1⟩ := by
  have h : ∀ k c d e,
      ⟨0, b+2*k, c+1, d, e+k+1⟩ [fm]⊢* ⟨0, b, c+k+1, d+2*k, e+1⟩ := by
    intro k; induction' k with k ih <;> intro c d e
    · exists 0
    rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring,
        show e + (k + 1) + 1 = (e + k + 1) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _ _); ring_nf; finish
  exact h k c d e

-- R3+R1+R2: handle leftover b=1
theorem r3r1r2 :
    ⟨0, 1, c+1, d, e+1⟩ [fm]⊢* ⟨0, 0, c+1, d+1, e+1⟩ := by
  step fm; step fm; step fm; finish

-- R3+R2+R2 drain
theorem drain :
    ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1⟩ := by
  have h : ∀ k c e,
      ⟨0, 0, c+k, d, e+1⟩ [fm]⊢* ⟨0, 0, c, d, e+k+1⟩ := by
    intro k; induction' k with k ih <;> intro c e
    · exists 0
    rw [show c + (k + 1) = (c + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih _ _); ring_nf; finish
  exact h k c e

-- Odd n=2m+1: (0, 0, 0, 2m+2, 4m+5) →⁺ (0, 0, 0, 2m+3, 4m+7)
theorem odd_trans :
    ⟨0, 0, 0, 2*m+2, 4*m+5⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+3, 4*m+7⟩ := by
  -- R4: → (0, 2m+2, 0, 0, 4m+5)
  rw [show (2*m+2 : ℕ) = 0 + (2*m+2) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0) (k := 2*m+2) (e := 4*m+5))
  simp only [Nat.zero_add]
  -- opening: → (0, 2m, 3, 3, 4m+4)
  rw [show (2*m+2 : ℕ) = 2*m + 2 from by ring,
      show (4*m+5 : ℕ) = (4*m+4) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (b := 2*m) (e := 4*m+4))
  -- R3+R1+R1 (m rounds, b goes from 2m to 0): → (0, 0, m+3, 2m+3, 3m+4+1)
  rw [show (2*m : ℕ) = 0 + 2*m from by ring,
      show (3 : ℕ) = 2 + 1 from by ring,
      show (4*m+4 : ℕ) = (3*m+3) + m + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain (b := 0) (k := m) (c := 2) (d := 3) (e := 3*m+3))
  -- drain (m+3 rounds): → (0, 0, 0, 2m+3, 4m+7)
  rw [show (2+m+1 : ℕ) = m + 3 from by ring,
      show (3+2*m : ℕ) = 2*m+3 from by ring,
      show (3*m+3+1 : ℕ) = (3*m+3) + 1 from by ring,
      show (m+3 : ℕ) = 0 + (m+3) from by ring]
  apply stepStar_trans (drain (k := m+3) (c := 0) (d := 2*m+3) (e := 3*m+3))
  ring_nf; finish

-- Even n=2(m+1): (0, 0, 0, 2m+3, 4m+7) →⁺ (0, 0, 0, 2m+4, 4m+9)
theorem even_trans :
    ⟨0, 0, 0, 2*m+3, 4*m+7⟩ [fm]⊢⁺ ⟨0, 0, 0, 2*m+4, 4*m+9⟩ := by
  -- R4: → (0, 2m+3, 0, 0, 4m+7)
  rw [show (2*m+3 : ℕ) = 0 + (2*m+3) from by ring]
  apply stepStar_stepPlus_stepPlus (d_to_b (b := 0) (d := 0) (k := 2*m+3) (e := 4*m+7))
  simp only [Nat.zero_add]
  -- opening: → (0, 2m+1, 3, 3, 4m+6)
  rw [show (2*m+3 : ℕ) = (2*m+1) + 2 from by ring,
      show (4*m+7 : ℕ) = (4*m+6) + 1 from by ring]
  apply stepPlus_stepStar_stepPlus (opening (b := 2*m+1) (e := 4*m+6))
  -- R3+R1+R1 (m rounds, b goes from 2m+1 to 1): → (0, 1, m+3, 2m+3, 3m+6+1)
  rw [show (2*m+1 : ℕ) = 1 + 2*m from by ring,
      show (3 : ℕ) = 2 + 1 from by ring,
      show (4*m+6 : ℕ) = (3*m+5) + m + 1 from by ring]
  apply stepStar_trans (r3r1r1_chain (b := 1) (k := m) (c := 2) (d := 3) (e := 3*m+5))
  -- R3+R1+R2 (leftover b=1): → (0, 0, m+3, 2m+4, 3m+6+1)
  rw [show (2+m+1 : ℕ) = (m+2) + 1 from by ring,
      show (3+2*m : ℕ) = 2*m+3 from by ring,
      show (3*m+5+1 : ℕ) = (3*m+5) + 1 from by ring]
  apply stepStar_trans (r3r1r2 (c := m+2) (d := 2*m+3) (e := 3*m+5))
  -- drain (m+3 rounds): → (0, 0, 0, 2m+4, 4m+9)
  rw [show (m+2+1 : ℕ) = m + 3 from by ring,
      show (2*m+3+1 : ℕ) = 2*m+4 from by ring,
      show (3*m+5+1 : ℕ) = (3*m+5) + 1 from by ring,
      show (m+3 : ℕ) = 0 + (m+3) from by ring]
  apply stepStar_trans (drain (k := m+3) (c := 0) (d := 2*m+4) (e := 3*m+5))
  ring_nf; finish

-- Main transition: (0, 0, 0, n+1, 2n+3) →⁺ (0, 0, 0, n+2, 2n+5)
theorem main_trans :
    ⟨0, 0, 0, n+1, 2*n+3⟩ [fm]⊢⁺ ⟨0, 0, 0, n+2, 2*n+5⟩ := by
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- n = K + K (even)
    rw [show K + K = 2 * K from by ring] at hK; subst hK
    rcases K with _ | m
    · -- K=0, n=0
      execute fm 10
    · -- K=m+1, n=2(m+1)
      rw [show 2 * (m + 1) + 1 = 2*m + 3 from by ring,
          show 2 * (2 * (m + 1)) + 3 = 4*m + 7 from by ring,
          show 2 * (m + 1) + 2 = 2*m + 4 from by ring,
          show 2 * (2 * (m + 1)) + 5 = 4*m + 9 from by ring]
      exact even_trans
  · -- n = 2K+1 (odd)
    subst hK
    rw [show 2*K+1 + 1 = 2*K + 2 from by ring,
        show 2*(2*K+1) + 3 = 4*K + 5 from by ring,
        show 2*K+1 + 2 = 2*K + 3 from by ring,
        show 2*(2*K+1) + 5 = 4*K + 7 from by ring]
    exact odd_trans

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 1, 3⟩) (by execute fm 7)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨0, 0, 0, n+1, 2*n+3⟩) 0
  intro n; exact ⟨n+1, main_trans⟩
