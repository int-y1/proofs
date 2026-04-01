import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #1156: [5/6, 44/35, 7/2, 3/11, 550/7]

Vector representation:
```
-1 -1  1  0  0
 2  0 -1 -1  1
-1  0  0  1  0
 0  1  0  0 -1
 1  0  2 -1  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_1156

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a+1, b+1, c, d, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a+1, b, c+2, d, e+1⟩
  | _ => none

variable {a b c d e : ℕ}

-- R3 chain: drain a to d (b=0, c=0)
theorem a_to_d : ∀ k, ⟨a + k, 0, 0, d, e⟩ [fm]⊢* ⟨a, 0, 0, d + k, e⟩ := by
  intro k; induction' k with k ih generalizing a d e
  · exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a) (d := d + 1))
    ring_nf; finish

-- R4 chain: drain e to b (a=0, c=0)
theorem e_to_b : ∀ k, ⟨0, b, 0, d, e + k⟩ [fm]⊢* ⟨0, b + k, 0, d, e⟩ := by
  intro k; induction' k with k ih generalizing b d e
  · exists 0
  · rw [show e + (k + 1) = (e + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (b := b + 1))
    ring_nf; finish

-- R2 chain (b=0): (a, 0, c+k, d+k, e) →* (a+2k, 0, c, d, e+k)
theorem r2_chain : ∀ k, ⟨a, 0, c + k, d + k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing a c d e
  · exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm
    apply stepStar_trans (ih (a := a + 2) (e := e + 1))
    ring_nf; finish

-- R2 chain specialized for d=0: (a, 0, c+k, k, e) →* (a+2k, 0, c, 0, e+k)
theorem r2_drain : ∀ k, ⟨a, 0, c + k, k, e⟩ [fm]⊢* ⟨a + 2 * k, 0, c, 0, e + k⟩ := by
  intro k
  have h := @r2_chain a c 0 e k
  simp only [Nat.zero_add] at h; exact h

-- R2-R1-R1 three-step cycle
theorem r2r1r1_chain : ∀ k, ⟨0, b + 2 * k, c + 1, d + k, e⟩ [fm]⊢* ⟨0, b, c + k + 1, d, e + k⟩ := by
  intro k; induction' k with k ih generalizing b c d e
  · exists 0
  · rw [show b + 2 * (k + 1) = (b + 2 * k) + 1 + 1 from by ring,
        show d + (k + 1) = (d + k) + 1 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih (c := c + 1) (e := e + 1))
    ring_nf; finish

-- R3-R2 alternating chain
theorem r3r2_chain : ∀ k, ⟨a + 1, 0, k, 0, e⟩ [fm]⊢* ⟨a + k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih generalizing a e
  · exists 0
  · step fm; step fm
    rw [show a + 2 = (a + 1) + 1 from by ring]
    apply stepStar_trans (ih (a := a + 1) (e := e + 1))
    ring_nf; finish

-- Full transition for odd index: C(2m+1) ⊢⁺ C(2m+2)
-- (4m+3, 0, 0, 0, 6m+3) ⊢⁺ (4m+5, 0, 0, 0, 6m+6)
theorem trans_odd (m : ℕ) :
    ⟨4 * m + 3, 0, 0, 0, 6 * m + 3⟩ [fm]⊢⁺ ⟨4 * m + 5, 0, 0, 0, 6 * m + 6⟩ := by
  -- R3 drain
  apply stepStar_stepPlus_stepPlus
  · have h1 := @a_to_d 0 0 (6 * m + 3) (4 * m + 3)
    simp only [Nat.zero_add] at h1; exact h1
  -- R4 drain
  apply stepStar_stepPlus_stepPlus
  · have h2 := @e_to_b 0 (4 * m + 3) 0 (6 * m + 3)
    simp only [Nat.zero_add] at h2; exact h2
  -- R5
  rw [show (4 * m + 3 : ℕ) = (4 * m + 2) + 1 from by ring]
  step fm
  -- R1
  rw [show (6 * m + 3 : ℕ) = (6 * m + 2) + 1 from by ring]
  step fm
  -- R2-R1-R1 chain: k=3m+1, b=0
  apply stepStar_trans
  · rw [show (6 * m + 2 : ℕ) = 0 + 2 * (3 * m + 1) from by ring,
        show (4 * m + 2 : ℕ) = (m + 1) + (3 * m + 1) from by ring]
    exact @r2r1r1_chain 0 2 (m + 1) 1 (3 * m + 1)
  -- At (0, 0, 3m+4, m+1, 3m+2)
  -- R2 drain: k=m+1
  apply stepStar_trans
  · rw [show 2 + (3 * m + 1) + 1 = (2 * m + 3) + (m + 1) from by ring,
        show 1 + (3 * m + 1) = 3 * m + 2 from by ring]
    exact @r2_drain 0 (2 * m + 3) (3 * m + 2) (m + 1)
  -- At (2m+2, 0, 2m+3, 0, 4m+3)
  -- R3-R2 chain: k=2m+3
  apply stepStar_trans
  · rw [show 0 + 2 * (m + 1) = (2 * m + 1) + 1 from by ring,
        show 3 * m + 2 + (m + 1) = 4 * m + 3 from by ring]
    exact @r3r2_chain (2 * m + 1) (4 * m + 3) (2 * m + 3)
  ring_nf; finish

-- Full transition for even index (m >= 1): C(2(m+1)) ⊢⁺ C(2(m+1)+1)
-- (4m+5, 0, 0, 0, 6m+6) ⊢⁺ (4m+7, 0, 0, 0, 6m+9)
theorem trans_even_succ (m : ℕ) :
    ⟨4 * m + 5, 0, 0, 0, 6 * m + 6⟩ [fm]⊢⁺ ⟨4 * m + 7, 0, 0, 0, 6 * m + 9⟩ := by
  -- R3 drain
  apply stepStar_stepPlus_stepPlus
  · have h1 := @a_to_d 0 0 (6 * m + 6) (4 * m + 5)
    simp only [Nat.zero_add] at h1; exact h1
  -- R4 drain
  apply stepStar_stepPlus_stepPlus
  · have h2 := @e_to_b 0 (4 * m + 5) 0 (6 * m + 6)
    simp only [Nat.zero_add] at h2; exact h2
  -- R5
  rw [show (4 * m + 5 : ℕ) = (4 * m + 4) + 1 from by ring]
  step fm
  -- R1
  rw [show (6 * m + 6 : ℕ) = (6 * m + 5) + 1 from by ring]
  step fm
  -- R2-R1-R1 chain: k=3m+2, b=1
  apply stepStar_trans
  · rw [show (6 * m + 5 : ℕ) = 1 + 2 * (3 * m + 2) from by ring,
        show (4 * m + 4 : ℕ) = (m + 2) + (3 * m + 2) from by ring]
    exact @r2r1r1_chain 1 2 (m + 2) 1 (3 * m + 2)
  -- At (0, 1, 3m+5, m+2, 3m+3)
  -- R2
  rw [show 2 + (3 * m + 2) + 1 = (3 * m + 4) + 1 from by ring,
      show (m + 2 : ℕ) = (m + 1) + 1 from by ring,
      show 1 + (3 * m + 2) = 3 * m + 3 from by ring]
  step fm
  -- R1
  step fm
  -- R2 drain: k=m+1
  apply stepStar_trans
  · rw [show (3 * m + 4 + 1 : ℕ) = (2 * m + 4) + (m + 1) from by ring,
        show (3 * m + 3 + 1 : ℕ) = 3 * m + 4 from by ring]
    exact @r2_drain 1 (2 * m + 4) (3 * m + 4) (m + 1)
  -- At (2m+3, 0, 2m+4, 0, 4m+5)
  -- R3-R2 chain: k=2m+4
  apply stepStar_trans
  · rw [show 1 + 2 * (m + 1) = (2 * m + 2) + 1 from by ring,
        show 3 * m + 4 + (m + 1) = 4 * m + 5 from by ring]
    exact @r3r2_chain (2 * m + 2) (4 * m + 5) (2 * m + 4)
  ring_nf; finish

-- Main transition: C(n) ⊢⁺ C(n+1) for all n
theorem main_trans (n : ℕ) :
    ⟨2 * n + 1, 0, 0, 0, 3 * n⟩ [fm]⊢⁺ ⟨2 * (n + 1) + 1, 0, 0, 0, 3 * (n + 1)⟩ := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = m + m
    subst hm
    rcases m with _ | m
    · -- n = 0
      execute fm 6
    · -- n = 2(m+1)
      rw [show (m + 1) + (m + 1) = 2 * (m + 1) from by ring,
          show 2 * (2 * (m + 1)) + 1 = 4 * m + 5 from by ring,
          show 3 * (2 * (m + 1)) = 6 * m + 6 from by ring,
          show 2 * (2 * (m + 1) + 1) + 1 = 4 * m + 7 from by ring,
          show 3 * (2 * (m + 1) + 1) = 6 * m + 9 from by ring]
      exact trans_even_succ m
  · -- n = 2m + 1
    subst hm
    rw [show 2 * (2 * m + 1) + 1 = 4 * m + 3 from by ring,
        show 3 * (2 * m + 1) = 6 * m + 3 from by ring,
        show 2 * (2 * m + 1 + 1) + 1 = 4 * m + 5 from by ring,
        show 3 * (2 * m + 1 + 1) = 6 * m + 6 from by ring]
    exact trans_odd m

theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 1, 0, 0, 0, 3 * n⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_1156
