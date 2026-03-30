import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #845: [36/35, 5/22, 49/2, 11/3, 15/7]

Vector representation:
```
 2  2 -1 -1  0
-1  0  1  0 -1
-1  0  0  2  0
 0 -1  0  0  1
 0  1  1 -1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_845

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a+2, b+2, c, d, e⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+2, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c+1, d, e⟩
  | _ => none

-- R4 chain: (0, b+K, 0, d, e) ⊢* (0, b, 0, d, e+K)
theorem b_to_e : ∀ K b d e, ⟨0, b + K, 0, d, e⟩ [fm]⊢* ⟨0, b, 0, d, e + K⟩ := by
  intro K; induction' K with K ih <;> intro b d e
  · exists 0
  · rw [show b + (K + 1) = (b + K) + 1 from by ring]
    step fm; apply stepStar_trans (ih b d (e + 1)); ring_nf; finish

-- R3 chain: (K, b, 0, d, 0) ⊢* (0, b, 0, d+2K, 0)
theorem a_to_d : ∀ K b d, ⟨K, b, 0, d, 0⟩ [fm]⊢* ⟨0, b, 0, d + 2 * K, 0⟩ := by
  intro K; induction' K with K ih <;> intro b d
  · exists 0
  · step fm; apply stepStar_trans (ih b (d + 2)); ring_nf; finish

-- R5+R1R2 chain: (0,0,0,d+K+1,e+K) ⊢⁺ (K, 2K+1, 1, d, e)
theorem phase1 : ∀ K d e, ⟨0, 0, 0, d + K + 1, e + K⟩ [fm]⊢⁺ ⟨K, 2 * K + 1, 1, d, e⟩ := by
  intro K; induction' K with K ih <;> intro d e
  · rw [show d + 0 + 1 = d + 1 from by ring, show e + 0 = e from by ring,
        show 2 * 0 + 1 = 1 from by ring, show (0 : ℕ) = 0 from rfl]
    step fm; finish
  · rw [show d + (K + 1) + 1 = (d + 1) + K + 1 from by ring,
        show e + (K + 1) = (e + 1) + K from by ring]
    apply stepPlus_stepStar_stepPlus (ih (d + 1) (e + 1))
    step fm; step fm
    rw [show 2 * (K + 1) + 1 = 2 * K + 3 from by ring]
    finish

-- R2 drain: (a+K, b, c, 0, e+K) →* (a, b, c+K, 0, e)
theorem r2_drain : ∀ K a b c e, ⟨a + K, b, c, 0, e + K⟩ [fm]⊢* ⟨a, b, c + K, 0, e⟩ := by
  intro K; induction' K with K ih <;> intro a b c e
  · exists 0
  · rw [show a + (K + 1) = (a + K) + 1 from by ring,
        show e + (K + 1) = (e + K) + 1 from by ring]
    step fm; apply stepStar_trans (ih a b (c + 1) e); ring_nf; finish

-- Cleanup: (a+1, b, c, 0, 0) →* (0, b+2c, 0, 2a+3c+2, 0)
theorem cleanup : ∀ c a b, ⟨a + 1, b, c, 0, 0⟩ [fm]⊢* ⟨0, b + 2 * c, 0, 2 * a + 3 * c + 2, 0⟩ := by
  intro c; induction' c using Nat.strongRecOn with c ih; intro a b
  rcases c with _ | _ | c
  · rw [show b + 2 * 0 = b from by ring, show 2 * a + 3 * 0 + 2 = 0 + 2 * (a + 1) from by ring]
    exact a_to_d (a + 1) b 0
  · step fm; step fm; step fm
    rw [show b + 2 * 1 = b + 2 from by ring, show 2 * a + 3 * 1 + 2 = 3 + 2 * (a + 1) from by ring]
    exact a_to_d (a + 1) (b + 2) 3
  · step fm; step fm; step fm
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih c (by omega) (a + 3) (b + 4))
    rw [show b + 4 + 2 * c = b + 2 * (c + 2) from by ring,
        show 2 * (a + 3) + 3 * c + 2 = 2 * a + 3 * (c + 2) + 2 from by ring]
    finish

-- Case 1: e ≤ d-2. After phase1, d_param ≥ 1, so R1 fires.
-- d = e + D + 2 where D ≥ 0.
theorem transition_case1 (e D : ℕ) :
    ⟨0, 0, 0, e + D + 2, e⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * e + D + 4, 2 * e + 3⟩ := by
  have h1 := phase1 e (D + 1) 0
  simp only [Nat.zero_add] at h1
  rw [show e + D + 2 = D + 1 + e + 1 from by ring]
  apply stepPlus_stepStar_stepPlus h1
  step fm
  apply stepStar_trans (a_to_d (e + 2) (2 * e + 3) D)
  rw [show D + 2 * (e + 2) = 2 * e + D + 4 from by ring,
      show 2 * e + 3 = 0 + (2 * e + 3) from by ring]
  apply stepStar_trans (b_to_e (2 * e + 3) 0 (2 * e + D + 4) 0)
  ring_nf; finish

-- Combined case 2+3 with explicit A, R parameters.
-- d = A+R+2, e = A+2R+1. K = A+R+1.
-- After phase1: (A+R+1, 2(A+R+1)+1, 1, 0, R)
-- After R2 drain R: (A+1, 2(A+R+1)+1, R+1, 0, 0)
-- After cleanup: (0, 2A+4R+5, 0, 2A+3R+5, 0)
-- After b_to_e: (0, 0, 0, 2A+3R+5, 2A+4R+5)
theorem transition_case23 (A R : ℕ) :
    ⟨0, 0, 0, A + R + 2, A + 2 * R + 1⟩ [fm]⊢⁺ ⟨0, 0, 0, 2 * A + 3 * R + 5, 2 * A + 4 * R + 5⟩ := by
  -- Phase 1
  have h1 := phase1 (A + R + 1) 0 R
  simp only [Nat.zero_add] at h1
  rw [show A + R + 2 = (A + R + 1) + 1 from by ring,
      show A + 2 * R + 1 = R + (A + R + 1) from by ring]
  apply stepPlus_stepStar_stepPlus h1
  -- State: (A+R+1, 2*(A+R+1)+1, 1, 0, R)
  -- R2 drain R: need to match a-position without corrupting b-position.
  -- Use have to specialize r2_drain, then simp, then show goal matches.
  have h2 := r2_drain R (A + 1) (2 * (A + R + 1) + 1) 1 0
  simp only [Nat.zero_add] at h2
  -- h2: (A+1+R, 2*(A+R+1)+1, 1, 0, R) ⊢* (A+1, 2*(A+R+1)+1, 1+R, 0, 0)
  -- Goal LHS: (A+R+1, 2*(A+R+1)+1, 1, 0, R)
  -- A+1+R = A+R+1 definitionally? No: A+1+R ≠ A+R+1 in general.
  -- But ring_nf would normalize both to the same form. However we can't ring_nf the goal.
  -- Rewrite h2 to match the goal.
  rw [show A + 1 + R = A + R + 1 from by ring] at h2
  apply stepStar_trans h2
  -- State: (A+1, 2*(A+R+1)+1, 1+R, 0, 0)
  rw [show 1 + R = R + 1 from by ring]
  apply stepStar_trans (cleanup (R + 1) A (2 * (A + R + 1) + 1))
  rw [show 2 * (A + R + 1) + 1 + 2 * (R + 1) = 0 + (2 * A + 4 * R + 5) from by ring,
      show 2 * A + 3 * (R + 1) + 2 = 2 * A + 3 * R + 5 from by ring]
  apply stepStar_trans (b_to_e (2 * A + 4 * R + 5) 0 (2 * A + 3 * R + 5) 0)
  ring_nf; finish

-- Main transition
theorem main_transition (d e : ℕ) (_ : d ≥ 2) (hde : 2 * d ≥ e + 3) :
    ⟨0, 0, 0, d, e⟩ [fm]⊢⁺ ⟨0, 0, 0, d + e + 2, 2 * e + 3⟩ := by
  by_cases h : e + 2 ≤ d
  · -- Case 1: d ≥ e+2
    have h1 := transition_case1 e (d - e - 2)
    have p1 : e + (d - e - 2) + 2 = d := by omega
    have p2 : 2 * e + (d - e - 2) + 4 = d + e + 2 := by omega
    rw [p1, p2] at h1; exact h1
  · -- Case 2+3: e ≥ d-1
    -- A = 2d-e-3, R = e-d+1.
    -- Use obtain to avoid Nat subtraction issues.
    obtain ⟨A, hA⟩ : ∃ A, e + 3 + A = 2 * d := ⟨2 * d - e - 3, by omega⟩
    obtain ⟨R, hR⟩ : ∃ R, d + R = e + 1 := ⟨e + 1 - d, by omega⟩
    have h1 := transition_case23 A R
    have p1 : A + R + 2 = d := by omega
    have p2 : A + 2 * R + 1 = e := by omega
    have p3 : 2 * A + 3 * R + 5 = d + e + 2 := by omega
    have p4 : 2 * A + 4 * R + 5 = 2 * e + 3 := by omega
    rw [p1, p2, p3, p4] at h1; exact h1

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 0, 2, 0⟩) (by execute fm 1)
  apply progress_nonhalt
    (P := fun q ↦ ∃ d e, q = ⟨0, 0, 0, d, e⟩ ∧ d ≥ 2 ∧ 2 * d ≥ e + 3)
  · intro q ⟨d, e, hq, hd, hde⟩
    refine ⟨⟨0, 0, 0, d + e + 2, 2 * e + 3⟩, ⟨d + e + 2, 2 * e + 3, rfl, ?_, ?_⟩, ?_⟩
    · omega
    · omega
    · rw [hq]; exact main_transition d e hd hde
  · exact ⟨2, 0, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_845
