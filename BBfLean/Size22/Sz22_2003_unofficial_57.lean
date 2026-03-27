import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #57: [1/15, 9/77, 98/3, 5/7, 847/2]

Vector representation:
```
 0 -1 -1  0  0
 0  2  0 -1 -1
 1 -1  0  2  0
 0  0  1 -1  0
-1  0  0  1  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_57

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d+2, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c, d+1, e+2⟩
  | _ => none

-- R4 chain: (a, 0, c, k, 0) -> (a, 0, c+k, 0, 0)
theorem r4_chain : ∀ k, ∀ a c, ⟨a, 0, c, k, 0⟩ [fm]⊢* ⟨a, 0, c+k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · simp; exists 0
  step fm
  apply stepStar_trans (ih a (c + 1))
  ring_nf; finish

-- Drain chain: (a+k, 0, c+2k, 0, e) -> (a, 0, c, 0, e+k)
theorem drain : ∀ k, ∀ a c e, ⟨a+k, 0, c+2*k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring,
      show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring]
  step fm; step fm; step fm; step fm
  apply stepStar_trans (ih a c (e + 1))
  ring_nf; finish

-- R3 chain (e=0): (a, b+k, 0, d, 0) -> (a+k, b, 0, d+2k, 0)
theorem r3_chain : ∀ k, ∀ a b d, ⟨a, b+k, 0, d, 0⟩ [fm]⊢* ⟨a+k, b, 0, d+2*k, 0⟩ := by
  intro k; induction' k with k ih <;> intro a b d
  · exists 0
  rw [show b + (k + 1) = b + k + 1 from rfl]
  step fm
  apply stepStar_trans (ih (a + 1) b (d + 2))
  ring_nf; finish

-- R2R2R3 chain: (A, b, 0, 2, E+2j) -> (A+j, b+3j, 0, 2, E)
theorem r2r2r3 : ∀ j, ∀ A b E,
    ⟨A, b, 0, 2, E+2*j⟩ [fm]⊢* ⟨A+j, b+3*j, 0, 2, E⟩ := by
  intro j; induction' j with j ih <;> intro A b E
  · simp; exists 0
  rw [show E + 2 * (j + 1) = (E + 2 * j) + 2 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (ih (A + 1) (b + 3) E)
  ring_nf; finish

-- Rebuild from (A+1, 0, 0, 0, 2m+1) -> (A+4m+6, 0, 0, 6m+10, 0)
theorem rebuild_0_odd (A m : ℕ) :
    ⟨A+1, 0, 0, 0, 2*m+1⟩ [fm]⊢⁺ ⟨A+4*m+6, 0, 0, 6*m+10, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨A+1, 0, 0, 0, 2*m+1⟩ = some ⟨A, 0, 0, 1, 2*m+3⟩; simp [fm]
  step fm; step fm
  -- Now at (A+1, 1, 0, 2, 2m+2)
  apply stepStar_trans (c₂ := ⟨A+m+2, 3*m+4, 0, 2, 0⟩)
  · have h := r2r2r3 (m+1) (A+1) 1 0
    rw [show 0 + 2 * (m + 1) = 2 * m + 2 from by ring] at h
    refine stepStar_trans h ?_; ring_nf; finish
  have h := r3_chain (3*m+4) (A+m+2) 0 2
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_; ring_nf; finish

-- Rebuild from (A+1, 0, 0, 0, 2m) -> (A+4m+4, 0, 0, 6m+7, 0)
theorem rebuild_0_even (A m : ℕ) :
    ⟨A+1, 0, 0, 0, 2*m⟩ [fm]⊢⁺ ⟨A+4*m+4, 0, 0, 6*m+7, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨A+1, 0, 0, 0, 2*m⟩ = some ⟨A, 0, 0, 1, 2*m+2⟩; simp [fm]
  step fm; step fm
  -- Now at (A+1, 1, 0, 2, 2m+1)
  apply stepStar_trans (c₂ := ⟨A+m+1, 3*m+1, 0, 2, 1⟩)
  · have h := r2r2r3 m (A+1) 1 1
    rw [show 1 + 2 * m = 2 * m + 1 from by ring] at h
    refine stepStar_trans h ?_; ring_nf; finish
  step fm; step fm
  have h := r3_chain (3*m+2) (A+m+2) 0 3
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_; ring_nf; finish

-- Rebuild from (B, 0, 0, 2, 2p+1) -> (B+4p+2, 0, 0, 6p+5, 0)
theorem rebuild_2_odd (B p : ℕ) :
    ⟨B, 0, 0, 2, 2*p+1⟩ [fm]⊢⁺ ⟨B+4*p+2, 0, 0, 6*p+5, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨B+p, 3*p, 0, 2, 1⟩)
  · have h := r2r2r3 p B 0 1
    rw [show 1 + 2 * p = 2 * p + 1 from by ring] at h
    refine stepStar_trans h ?_; ring_nf; finish
  apply step_stepStar_stepPlus
  · show fm ⟨B+p, 3*p, 0, 2, 1⟩ = some ⟨B+p, 3*p+2, 0, 1, 0⟩; simp [fm]
  step fm
  have h := r3_chain (3*p+1) (B+p+1) 0 3
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_; ring_nf; finish

-- Rebuild from (B, 0, 0, 2, 2p+2) -> (B+4p+4, 0, 0, 6p+8, 0)
theorem rebuild_2_even (B p : ℕ) :
    ⟨B, 0, 0, 2, 2*p+2⟩ [fm]⊢⁺ ⟨B+4*p+4, 0, 0, 6*p+8, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨B+p+1, 3*p+3, 0, 2, 0⟩)
  · have h := r2r2r3 (p+1) B 0 0
    rw [show 0 + 2 * (p + 1) = 2 * p + 2 from by ring] at h
    refine stepStar_trans h ?_; ring_nf; finish
  apply step_stepStar_stepPlus
  · show fm ⟨B+p+1, 3*p+3, 0, 2, 0⟩ = some ⟨B+p+2, 3*p+2, 0, 4, 0⟩; simp [fm]
  have h := r3_chain (3*p+2) (B+p+2) 0 4
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_; ring_nf; finish

-- Main even: (a+k+1, 0, 0, 2k, 0) ⊢⁺ (a+2k+4, 0, 0, 3k+7, 0)
theorem main_even (a k : ℕ) :
    ⟨a+k+1, 0, 0, 2*k, 0⟩ [fm]⊢⁺ ⟨a+2*k+4, 0, 0, 3*k+7, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 0, 0, k⟩)
  · apply stepStar_trans (c₂ := ⟨a+k+1, 0, 2*k, 0, 0⟩)
    · have h := r4_chain (2*k) (a+k+1) 0
      simp only [Nat.zero_add] at h; exact h
    have h := drain k (a+1) 0 0
    simp only [Nat.zero_add] at h
    rw [show a + 1 + k = a + k + 1 from by ring] at h; exact h
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm; convert rebuild_0_even a m using 2; ring_nf
  · subst hm; convert rebuild_0_odd a m using 2; ring_nf

-- Main odd: (a+k+1, 0, 0, 2k+1, 0) ⊢⁺ (a+2k+3, 0, 0, 3k+5, 0)
theorem main_odd (a k : ℕ) :
    ⟨a+k+1, 0, 0, 2*k+1, 0⟩ [fm]⊢⁺ ⟨a+2*k+3, 0, 0, 3*k+5, 0⟩ := by
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 0, 0, 2, k+1⟩)
  · apply stepStar_trans (c₂ := ⟨a+k+1, 0, 2*k+1, 0, 0⟩)
    · have h := r4_chain (2*k+1) (a+k+1) 0
      simp only [Nat.zero_add] at h; exact h
    apply stepStar_trans (c₂ := ⟨a+1, 0, 1, 0, k⟩)
    · have h := drain k (a+1) 1 0
      simp only [Nat.zero_add] at h
      rw [show a + 1 + k = a + k + 1 from by ring,
          show 1 + 2 * k = 2 * k + 1 from by ring] at h; exact h
    step fm; step fm; step fm; step fm
    ring_nf; finish
  rcases Nat.even_or_odd k with ⟨p, hp⟩ | ⟨p, hp⟩
  · subst hp; convert rebuild_2_odd (a+1) p using 2; ring_nf
  · subst hp; convert rebuild_2_even (a+1) p using 2; ring_nf

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨4, 0, 0, 7, 0⟩) (by execute fm 7)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a d, q = ⟨a, 0, 0, d, 0⟩ ∧ 2 * a ≥ d + 1 ∧ d ≥ 1)
  · intro c ⟨a, d, hq, ha, hd⟩; subst hq
    rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- d = 2k (Nat.even_or_odd gives d = k + k)
      subst hk
      have hk1 : k ≥ 1 := by omega
      have hak : a ≥ k + 1 := by omega
      set a' := a - k - 1
      refine ⟨⟨a' + 2*k + 4, 0, 0, 3*k+7, 0⟩,
              ⟨a' + 2*k + 4, 3*k+7, rfl, by omega, by omega⟩, ?_⟩
      have ha_eq : a = a' + k + 1 := by omega
      rw [ha_eq, show k + k = 2 * k from by ring]
      exact main_even a' k
    · -- d = 2k+1 (Nat.even_or_odd gives d = 2*k + 1)
      subst hk
      have hak : a ≥ k + 1 := by omega
      set a' := a - k - 1
      refine ⟨⟨a' + 2*k + 3, 0, 0, 3*k+5, 0⟩,
              ⟨a' + 2*k + 3, 3*k+5, rfl, by omega, by omega⟩, ?_⟩
      have ha_eq : a = a' + k + 1 := by omega
      rw [ha_eq]
      exact main_odd a' k
  · exact ⟨4, 7, rfl, by omega, by omega⟩

end Sz22_2003_unofficial_57
