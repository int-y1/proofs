import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #10: [1/45, 50/77, 7/5, 3/7, 605/2]

Vector representation:
```
 0 -2 -1  0  0
 1  0  2 -1 -1
 0  0 -1  1  0
 0  1  0 -1  0
-1  0  1  0  2
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_10

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+2, c+1, d, e⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b, c, d+1, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d, e+2⟩
  | _ => none

-- R3 chain: c → d when b ≤ 1 and e = 0
theorem c_to_d : ∀ k, ∀ a b d, b ≤ 1 → ⟨a, b, k, d, 0⟩ [fm]⊢* ⟨a, b, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a b d hb
  · simp; exists 0
  have hstep : fm ⟨a, b, k + 1, d, 0⟩ = some ⟨a, b, k, d + 1, 0⟩ := by
    rcases b with _ | _ | b <;> simp [fm]; omega
  apply stepStar_trans (step_stepStar hstep)
  have := h a b (d + 1) hb
  rw [show d + 1 + k = d + (k + 1) from by ring] at this
  exact this

-- R4 chain: d → b when c = 0 and e = 0
theorem d_to_b : ∀ k, ∀ a b, ⟨a, b, 0, k, 0⟩ [fm]⊢* ⟨a, b+k, 0, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b
  · simp; exists 0
  rw [show (k + 1 : ℕ) = k + 1 from rfl]
  step fm
  apply stepStar_trans (h a _)
  ring_nf; finish

-- R5,R1 drain (even b): (A+K, 2K, 0, 0, E) →* (A, 0, 0, 0, E+2K)
theorem r5r1_even : ∀ K, ∀ A E, ⟨A+K, 2*K, 0, 0, E⟩ [fm]⊢* ⟨A, 0, 0, 0, E+2*K⟩ := by
  intro K; induction' K with K h <;> intro A E
  · simp; exists 0
  rw [show A + (K + 1) = (A + K) + 1 from by ring,
      show 2 * (K + 1) = 2 * K + 2 from by ring]
  step fm
  step fm
  apply stepStar_trans (h A (E + 2))
  ring_nf; finish

-- R5,R1 drain (odd b): (A+K, 2K+1, 0, 0, E) →* (A, 1, 0, 0, E+2K)
theorem r5r1_odd : ∀ K, ∀ A E, ⟨A+K, 2*K+1, 0, 0, E⟩ [fm]⊢* ⟨A, 1, 0, 0, E+2*K⟩ := by
  intro K; induction' K with K h <;> intro A E
  · simp; exists 0
  rw [show A + (K + 1) = (A + K) + 1 from by ring,
      show 2 * (K + 1) + 1 = (2 * K + 1) + 2 from by ring]
  step fm
  step fm
  apply stepStar_trans (h A (E + 2))
  ring_nf; finish

-- R5,R3: (A+1, B, 0, 0, E) →* (A, B, 0, 1, E+2) when B ≤ 1
theorem r5r3 (a b e : ℕ) (hb : b ≤ 1) : ⟨a+1, b, 0, 0, e⟩ [fm]⊢* ⟨a, b, 0, 1, e+2⟩ := by
  have hstep1 : fm ⟨a + 1, b, 0, 0, e⟩ = some ⟨a, b, 1, 0, e + 2⟩ := by
    rcases b with _ | _ | b <;> simp [fm]
  apply stepStar_trans (step_stepStar hstep1)
  have hstep2 : fm ⟨a, b, 1, 0, e + 2⟩ = some ⟨a, b, 0, 1, e + 2⟩ := by
    rcases b with _ | _ | b <;> simp [fm]; omega
  exact step_stepStar hstep2

-- R2,R3 chain: (A, B, C, 1, k+1) →* (A+k+1, B, C+k+2, 0, 0) when B ≤ 1
theorem r2r3_chain : ∀ k, ∀ a b c, b ≤ 1 → ⟨a, b, c, 1, k+1⟩ [fm]⊢* ⟨a+k+1, b, c+k+2, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b c hb
  · -- k = 0: one R2 step
    have hstep : fm ⟨a, b, c, 1, 1⟩ = some ⟨a + 1, b, c + 2, 0, 0⟩ := by
      rcases b with _ | _ | b <;> simp [fm]; omega
    exact step_stepStar hstep
  · -- R2: (a, b, c, 1, k+2) → (a+1, b, c+2, 0, k+1)
    have hstep1 : fm ⟨a, b, c, 1, k + 2⟩ = some ⟨a + 1, b, c + 2, 0, k + 1⟩ := by
      rcases b with _ | _ | b <;> simp [fm]; omega
    apply stepStar_trans (step_stepStar hstep1)
    -- R3: (a+1, b, c+2, 0, k+1) → (a+1, b, c+1, 1, k+1)
    have hstep2 : fm ⟨a + 1, b, c + 2, 0, k + 1⟩ = some ⟨a + 1, b, c + 1, 1, k + 1⟩ := by
      rcases b with _ | _ | b <;> simp [fm]; omega
    apply stepStar_trans (step_stepStar hstep2)
    have ih := h (a + 1) b (c + 1) hb
    apply stepStar_trans ih
    ring_nf; finish

-- Main transition: (a+m+2, 0, 2m+3, 0, 0) ⊢⁺ (a+3m+8, 0, 2m+9, 0, 0)
theorem main_trans (a m : ℕ) :
    ⟨a+m+2, 0, 2*m+3, 0, 0⟩ [fm]⊢⁺ ⟨a+3*m+8, 0, 2*m+9, 0, 0⟩ := by
  -- Phase A: c → d
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+m+2, 0, 0, 2*m+3, 0⟩)
  · have h := c_to_d (2*m+3) (a+m+2) 0 0 (by omega)
    simp only [Nat.zero_add] at h; exact h
  -- Phase B: d → b
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+m+2, 2*m+3, 0, 0, 0⟩)
  · have h := d_to_b (2*m+3) (a+m+2) 0
    simp only [Nat.zero_add] at h; exact h
  -- Phase C: R5,R1 odd drain: b=2m+3=2(m+1)+1, K=m+1
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+1, 1, 0, 0, 2*m+2⟩)
  · have h := r5r1_odd (m+1) (a+1) 0
    rw [show a + 1 + (m + 1) = a + m + 2 from by ring,
        show 2 * (m + 1) + 1 = 2 * m + 3 from by ring] at h
    simp only [Nat.zero_add] at h
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring] at h
    exact h
  -- Phase D: R5,R3: (a+1, 1, 0, 0, 2m+2) →* (a, 1, 0, 1, 2m+4)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a, 1, 0, 1, 2*m+4⟩)
  · have h := r5r3 a 1 (2*m+2) (by omega)
    rw [show 2 * m + 2 + 2 = 2 * m + 4 from by ring] at h
    exact h
  -- Phase E: R2,R3 chain: (a, 1, 0, 1, 2m+4) →* (a+2m+4, 1, 2m+5, 0, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+2*m+4, 1, 2*m+5, 0, 0⟩)
  · have h := r2r3_chain (2*m+3) a 1 0 (by omega)
    rw [show a + (2 * m + 3) + 1 = a + 2 * m + 4 from by ring,
        show 0 + (2 * m + 3) + 2 = 2 * m + 5 from by ring,
        show (2 * m + 3) + 1 = 2 * m + 4 from by ring] at h
    exact h
  -- Phase F: c → d
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+2*m+4, 1, 0, 2*m+5, 0⟩)
  · have h := c_to_d (2*m+5) (a+2*m+4) 1 0 (by omega)
    simp only [Nat.zero_add] at h; exact h
  -- Phase G: d → b
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+2*m+4, 2*m+6, 0, 0, 0⟩)
  · have h := d_to_b (2*m+5) (a+2*m+4) 1
    rw [show 1 + (2 * m + 5) = 2 * m + 6 from by ring] at h
    exact h
  -- Phase H: R5,R1 even drain: b=2m+6=2(m+3), K=m+3
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+m+1, 0, 0, 0, 2*m+6⟩)
  · have h := r5r1_even (m+3) (a+m+1) 0
    rw [show a + m + 1 + (m + 3) = a + 2 * m + 4 from by ring,
        show 2 * (m + 3) = 2 * m + 6 from by ring] at h
    simp only [Nat.zero_add] at h; exact h
  -- Phase I: R5,R3: (a+m+1, 0, 0, 0, 2m+6) →* (a+m, 0, 0, 1, 2m+8)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨a+m, 0, 0, 1, 2*m+8⟩)
  · have h := r5r3 (a+m) 0 (2*m+6) (by omega)
    rw [show a + m + 1 = a + m + 1 from rfl,
        show 2 * m + 6 + 2 = 2 * m + 8 from by ring] at h
    exact h
  -- Phase J: R2,R3 chain: (a+m, 0, 0, 1, 2m+8) →⁺ (a+3m+8, 0, 2m+9, 0, 0)
  -- k+1 = 2m+8, k = 2m+7
  have h := r2r3_chain (2*m+7) (a+m) 0 0 (by omega)
  rw [show a + m + (2 * m + 7) + 1 = a + 3 * m + 8 from by ring,
      show 0 + (2 * m + 7) + 2 = 2 * m + 9 from by ring,
      show (2 * m + 7) + 1 = 2 * m + 8 from by ring] at h
  exact stepStar_stepPlus h (by
    intro heq
    have : a + m = a + 3 * m + 8 := by
      have := congr_arg (fun q : Q => q.1) heq
      simp at this; exact this
    omega)

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨2, 0, 3, 0, 0⟩) (by execute fm 5)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, m⟩ ↦ ⟨a+m+2, 0, 2*m+3, 0, 0⟩) ⟨0, 0⟩
  intro ⟨a, m⟩; exact ⟨⟨a+2*m+3, m+3⟩, by
    show ⟨a+m+2, 0, 2*m+3, 0, 0⟩ [fm]⊢⁺ ⟨(a+2*m+3)+(m+3)+2, 0, 2*(m+3)+3, 0, 0⟩
    rw [show (a + 2 * m + 3) + (m + 3) + 2 = a + 3 * m + 8 from by ring,
        show 2 * (m + 3) + 3 = 2 * m + 9 from by ring]
    exact main_trans a m⟩

end Sz21_140_unofficial_10
