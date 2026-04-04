import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_1638

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a, b, c, d+1, e+1⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e+1⟩
  | _ => none

-- R4 chain: transfer e to c
theorem e_to_c : ∀ k c, ⟨a, 0, c, 0, k⟩ [fm]⊢* ⟨a, 0, c + k, 0, 0⟩ := by
  intro k; induction' k with k ih <;> intro c
  · exists 0
  step fm; apply stepStar_trans (ih (c + 1)); ring_nf; finish

-- R3 chain: drain b into a
theorem r3_chain : ∀ k, ∀ A E, ⟨A, k, 0, 0, E⟩ [fm]⊢* ⟨A + k, 0, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A E
  · exists 0
  step fm
  rw [show A + (k + 1) = (A + 1) + k from by ring]
  exact ih (A + 1) E

-- R2 drain: drain d into b (works with any initial b)
theorem r2_drain : ∀ k, ∀ A B E, ⟨A + k, B, 0, k, E⟩ [fm]⊢* ⟨A, B + 3 * k, 0, 0, E⟩ := by
  intro k; induction' k with k ih <;> intro A B E
  · exists 0
  rw [show A + (k + 1) = (A + k) + 1 from by ring,
      show (k : ℕ) + 1 = k + 1 from rfl]
  step fm
  rw [show B + 3 * (k + 1) = (B + 3) + 3 * k from by ring]
  exact ih A (B + 3) E

-- Combined drain: (A, 3, C, D, F) ⊢* (A + 2D + C + 3, 0, 0, 0, F + C)
-- Uses A = X + D + C as fuel for R2 steps
theorem full_drain : ∀ C, ∀ X D F,
    ⟨X + D + C, 3, C, D, F⟩ [fm]⊢* ⟨X + 3 * D + 2 * C + 3, 0, 0, 0, F + C⟩ := by
  intro C; induction' C using Nat.strongRecOn with C ih; intro X D F
  rcases C with _ | _ | _ | C
  · -- C = 0
    simp
    apply stepStar_trans (r2_drain D X 3 F)
    rw [show X + 3 * D + 2 * 0 + 3 = X + (3 + 3 * D) from by ring]
    exact r3_chain (3 + 3 * D) X F
  · -- C = 1
    rw [show X + D + 1 = X + D + 1 from rfl,
        show (3 : ℕ) = 2 + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm
    rw [show X + 3 * D + 2 * 1 + 3 = X + (2 + 3 * (D + 1)) from by ring,
        show F + 1 = F + 1 from rfl]
    apply stepStar_trans (r2_drain (D + 1) X 2 (F + 1))
    exact r3_chain (2 + 3 * (D + 1)) X (F + 1)
  · -- C = 2
    rw [show X + D + 2 = X + D + 2 from rfl,
        show (3 : ℕ) = 1 + 1 + 1 from rfl,
        show (2 : ℕ) = 0 + 1 + 1 from rfl]
    step fm; step fm
    rw [show X + 3 * D + 2 * 2 + 3 = X + (1 + 3 * (D + 2)) from by ring,
        show F + 2 = F + 2 from rfl]
    apply stepStar_trans (r2_drain (D + 2) X 1 (F + 2))
    exact r3_chain (1 + 3 * (D + 2)) X (F + 2)
  · -- C = C' + 3: one round of 3 R1s + 1 R2, then recurse
    rw [show X + D + (C + 3) = X + D + C + 3 from by ring,
        show (3 : ℕ) = 2 + 1 from rfl,
        show C + 3 = (C + 2) + 1 from by ring]
    step fm -- R1: b=3→2, c→c+2
    rw [show (2 : ℕ) = 1 + 1 from rfl,
        show C + 2 = (C + 1) + 1 from by ring]
    step fm -- R1: b=2→1, c→c+1
    rw [show (1 : ℕ) = 0 + 1 from rfl,
        show C + 1 = C + 1 from rfl]
    step fm -- R1: b=1→0, c→c
    -- Now at (X + D + C + 3, 0, C, D + 3, F + 3)
    -- R2: a >= 1, d >= 1
    rw [show X + D + C + 3 = (X + D + C + 2) + 1 from by ring,
        show D + 3 = (D + 2) + 1 from by ring]
    step fm -- R2
    -- Now at (X + D + C + 2, 3, C, D + 2, F + 3)
    -- = (X + (D + 2) + C, 3, C, D + 2, F + 3)
    rw [show X + D + C + 2 = X + (D + 2) + C from by ring,
        show X + 3 * D + 2 * (C + 3) + 3 = X + 3 * (D + 2) + 2 * C + 3 from by ring,
        show F + (C + 3) = (F + 3) + C from by ring]
    exact ih C (by omega) X (D + 2) (F + 3)

-- Main transition: (a + e + 3, 0, 0, 0, e + 1) ⊢⁺ (a + 2*e + 6, 0, 0, 0, e + 2)
theorem main_trans (a e : ℕ) :
    ⟨a + e + 3, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨a + 2 * e + 6, 0, 0, 0, e + 2⟩ := by
  -- Phase 1: R4 x (e+1): (a+e+3, 0, e+1, 0, 0)
  have p1 : ⟨a + e + 3, 0, 0, 0, e + 1⟩ [fm]⊢* ⟨a + e + 3, 0, e + 1, 0, 0⟩ := by
    have := e_to_c (a := a + e + 3) (e + 1) 0; simpa using this
  -- Phase 2: R5 + R1: (a+e+2, 0, e, 2, 2)
  have p2 : ⟨a + e + 3, 0, e + 1, 0, 0⟩ [fm]⊢* ⟨a + e + 2, 0, e, 2, 2⟩ := by
    rw [show a + e + 3 = (a + e + 2) + 1 from by ring,
        show e + 1 = e + 1 from rfl]
    step fm -- R5: (a+e+2, 1, e+1, 1, 1)
    rw [show e + 1 = e + 1 from rfl,
        show (1 : ℕ) = 0 + 1 from rfl]
    step fm -- R1: (a+e+2, 0, e, 2, 2)
    ring_nf; finish
  -- Phase 3: R2: (a+e+1, 3, e, 1, 2)
  have p3 : ⟨a + e + 2, 0, e, 2, 2⟩ [fm]⊢* ⟨a + e + 1, 3, e, 1, 2⟩ := by
    rw [show a + e + 2 = (a + e + 1) + 1 from by ring,
        show (2 : ℕ) = 1 + 1 from by ring]
    step fm; ring_nf; finish
  -- Phase 4: full_drain: (a+e+1, 3, e, 1, 2) ⊢* (a+2e+6, 0, 0, 0, e+2)
  have p4 : ⟨a + e + 1, 3, e, 1, 2⟩ [fm]⊢* ⟨a + 2 * e + 6, 0, 0, 0, e + 2⟩ := by
    rw [show a + e + 1 = a + 1 + e from by ring,
        show a + 2 * e + 6 = a + 3 * 1 + 2 * e + 3 from by ring,
        show e + 2 = 2 + e from by ring]
    exact full_drain e a 1 2
  exact stepStar_stepPlus_stepPlus p1
    (stepPlus_stepStar_stepPlus
      (stepStar_stepPlus p2 (by unfold Q; simp))
      (stepStar_trans p3 p4))

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 0, 0, 1⟩)
  · unfold c₀; execute fm 6
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ)
    (fun ⟨a, e⟩ ↦ ⟨a + e + 3, 0, 0, 0, e + 1⟩) ⟨0, 0⟩
  intro ⟨a, e⟩
  refine ⟨⟨a + e + 2, e + 1⟩, ?_⟩
  show ⟨a + e + 3, 0, 0, 0, e + 1⟩ [fm]⊢⁺ ⟨a + e + 2 + (e + 1) + 3, 0, 0, 0, e + 1 + 1⟩
  rw [show a + e + 2 + (e + 1) + 3 = a + 2 * e + 6 from by ring,
      show e + 1 + 1 = e + 2 from by ring]
  exact main_trans a e

end Sz22_2003_unofficial_1638
