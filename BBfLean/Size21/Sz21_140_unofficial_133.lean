import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #133: [9/35, 1/33, 50/3, 11/25, 21/2]

Vector representation:
```
 0  2 -1 -1  0
 0 -1  0  0 -1
 1 -1  2  0  0
 0  0 -2  0  1
-1  1  0  1  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_133

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+2, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+1, b, c+2, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

-- R3 chain: b → a,c
theorem r3_chain : ∀ k, ∀ a b c, ⟨a, b+k, c, 0, 0⟩ [fm]⊢* ⟨a+k, b, c+2*k, 0, 0⟩ := by
  intro k; induction' k with k h <;> intro a b c
  · exists 0
  rw [show b + (k + 1) = (b + k) + 1 from by ring]
  step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- R4 chain: c → e
theorem r4_chain : ∀ k, ∀ a c e, ⟨a, 0, c+2*k, 0, e⟩ [fm]⊢* ⟨a, 0, c, 0, e+k⟩ := by
  intro k; induction k with
  | zero => intro a c e; exists 0
  | succ k ih =>
    intro a c e
    have step1 : fm ⟨a, 0, (c + 2 * k) + 1 + 1, 0, e⟩ = some ⟨a, 0, c + 2 * k, 0, e + 1⟩ := by simp [fm]
    rw [show c + 2 * (k + 1) = (c + 2 * k) + 1 + 1 from by ring]
    exact stepStar_trans (step_stepStar step1)
      (by have := ih a c (e + 1); rw [show e + 1 + k = e + (k + 1) from by ring] at this; exact this)

-- R2 chain: cancel b and e
theorem r2_chain_00 : ∀ k, ∀ a b e, ⟨a, b+k, 0, 0, e+k⟩ [fm]⊢* ⟨a, b, 0, 0, e⟩ := by
  intro k; induction k with
  | zero => intro a b e; exists 0
  | succ k ih =>
    intro a b e
    have step1 : fm ⟨a, (b + k) + 1, 0, 0, (e + k) + 1⟩ = some ⟨a, b + k, 0, 0, e + k⟩ := by simp [fm]
    rw [show b + (k + 1) = (b + k) + 1 from by ring, show e + (k + 1) = (e + k) + 1 from by ring]
    exact stepStar_trans (step_stepStar step1) (ih a b e)

-- R5/R2 alternation: a → d
theorem r5r2_alt : ∀ k, ∀ a d, ⟨a+k, 0, 0, d, k⟩ [fm]⊢* ⟨a, 0, 0, d+k, 0⟩ := by
  intro k; induction' k with k h <;> intro a d
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm; step fm
  apply stepStar_trans (h _ _)
  ring_nf; finish

-- R3/R1/R1 rounds: drain d by 2, grow b by 3
theorem r3r1r1_rounds : ∀ K, ∀ a b d, ⟨a, b+1, 0, d+2*K, 0⟩ [fm]⊢* ⟨a+K, b+1+3*K, 0, d, 0⟩ := by
  intro K; induction' K with K h <;> intro a b d
  · exists 0
  rw [show d + 2 * (K + 1) = (d + 2 * K) + 1 + 1 from by ring]
  step fm; step fm; step fm
  apply stepStar_trans (h _ _ _)
  ring_nf; finish

-- Common prefix
theorem prefix_steps (a D : ℕ) : ⟨a+1, 0, 0, D+1, 0⟩ [fm]⊢* ⟨a+1, 4, 0, D, 0⟩ := by
  step fm; step fm; step fm; step fm; ring_nf; finish

-- D=0 transition
theorem trans_d0 (a : ℕ) : ⟨a+1, 0, 0, 0, 0⟩ [fm]⊢⁺ ⟨a+2, 0, 0, 1, 0⟩ := by
  execute fm 15

-- D=2K+1 (odd) internal
theorem odd_star (a K : ℕ) : ⟨a, 1, 0, 2*K+2, 0⟩ [fm]⊢* ⟨a+K+1, 0, 0, 3*K+4, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨a+1, 4, 0, 2*K, 0⟩)
  · step fm; step fm; step fm; ring_nf; finish
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨a+1+K, 3+1+3*K, 0, 0, 0⟩)
  · have h := r3r1r1_rounds K (a+1) 3 0
    rw [show 0 + 2 * K = 2 * K from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨a+4*K+5, 0, 8+6*K, 0, 0⟩)
  · have h := r3_chain (4+3*K) (a+1+K) 0 0
    rw [show 0 + (4 + 3 * K) = 4 + 3 * K from by ring] at h
    refine stepStar_trans h ?_; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨a+4*K+5, 0, 0, 0, 4+3*K⟩)
  · have h := r4_chain (4+3*K) (a+4*K+5) 0 0
    rw [show 0 + 2 * (4 + 3 * K) = 8 + 6 * K from by ring,
        show 0 + (4 + 3 * K) = 4 + 3 * K from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨a+4*K+4, 1, 0, 1, 4+3*K⟩)
  · have : fm ⟨(a+4*K+4) + 1, 0, 0, 0, 4+3*K⟩ = some ⟨a+4*K+4, 1, 0, 1, 4+3*K⟩ := by simp [fm]
    rw [show a + 4 * K + 5 = (a + 4 * K + 4) + 1 from by ring]; exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨a+4*K+4, 0, 0, 1, 3+3*K⟩)
  · have : fm ⟨a+4*K+4, 0+1, 0, 1, (3+3*K)+1⟩ = some ⟨a+4*K+4, 0, 0, 1, 3+3*K⟩ := by simp [fm]
    rw [show 4 + 3 * K = (3 + 3 * K) + 1 from by ring]; exact step_stepStar this
  have h := r5r2_alt (3+3*K) (a+K+1) 1
  rw [show (a + K + 1) + (3 + 3 * K) = a + 4 * K + 4 from by ring] at h
  refine stepStar_trans h ?_; ring_nf; finish

-- D=2K+1 transition
theorem trans_odd (a K : ℕ) : ⟨a+1, 0, 0, 2*K+1, 0⟩ [fm]⊢⁺ ⟨a+K+1, 0, 0, 3*K+4, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a+1, 0, 0, 2*K+1, 0⟩ = some ⟨a, 1, 0, 2*K+2, 0⟩
    rw [show 2 * K + 1 = (2 * K + 1) from rfl, show 2 * K + 2 = (2 * K + 1) + 1 from by ring]
    simp [fm]
  exact odd_star a K

-- D=2K+2 (even) internal
theorem even_star (a K : ℕ) : ⟨a, 1, 0, 2*K+3, 0⟩ [fm]⊢* ⟨a+K+4, 0, 0, 3*K+2, 0⟩ := by
  apply stepStar_trans (c₂ := ⟨a+1, 4, 0, 2*K+1, 0⟩)
  · step fm; step fm; step fm; ring_nf; finish
  rw [show (4 : ℕ) = 3 + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨a+1+K, 3+1+3*K, 0, 1, 0⟩)
  · have h := r3r1r1_rounds K (a+1) 3 1
    rw [show 1 + 2 * K = 2 * K + 1 from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨a+K+3, 4+3*K, 3, 0, 0⟩)
  · rw [show 3 + 1 + 3 * K = (3 + 3 * K) + 1 from by ring]
    step fm; step fm; step fm; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨a+4*K+7, 0, 11+6*K, 0, 0⟩)
  · have h := r3_chain (4+3*K) (a+K+3) 0 3
    rw [show 0 + (4 + 3 * K) = 4 + 3 * K from by ring] at h
    refine stepStar_trans h ?_; ring_nf; finish
  apply stepStar_trans (c₂ := ⟨a+4*K+7, 0, 1, 0, 5+3*K⟩)
  · have h := r4_chain (5+3*K) (a+4*K+7) 1 0
    rw [show 1 + 2 * (5 + 3 * K) = 11 + 6 * K from by ring,
        show 0 + (5 + 3 * K) = 5 + 3 * K from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨a+4*K+6, 3, 0, 0, 5+3*K⟩)
  · rw [show a + 4 * K + 7 = (a + 4 * K + 6) + 1 from by ring]
    step fm; step fm; finish
  apply stepStar_trans (c₂ := ⟨a+4*K+6, 0, 0, 0, 2+3*K⟩)
  · have h := r2_chain_00 3 (a+4*K+6) 0 (2+3*K)
    rw [show (2 + 3 * K) + 3 = 5 + 3 * K from by ring] at h; exact h
  apply stepStar_trans (c₂ := ⟨a+4*K+5, 1, 0, 1, 2+3*K⟩)
  · have : fm ⟨(a+4*K+5)+1, 0, 0, 0, 2+3*K⟩ = some ⟨a+4*K+5, 1, 0, 1, 2+3*K⟩ := by simp [fm]
    rw [show a + 4 * K + 6 = (a + 4 * K + 5) + 1 from by ring]; exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨a+4*K+5, 0, 0, 1, 1+3*K⟩)
  · have : fm ⟨a+4*K+5, 0+1, 0, 1, (1+3*K)+1⟩ = some ⟨a+4*K+5, 0, 0, 1, 1+3*K⟩ := by simp [fm]
    rw [show 2 + 3 * K = (1 + 3 * K) + 1 from by ring]; exact step_stepStar this
  have h := r5r2_alt (1+3*K) (a+K+4) 1
  rw [show (a + K + 4) + (1 + 3 * K) = a + 4 * K + 5 from by ring] at h
  refine stepStar_trans h ?_; ring_nf; finish

-- D=2K+2 transition
theorem trans_even (a K : ℕ) : ⟨a+1, 0, 0, 2*K+2, 0⟩ [fm]⊢⁺ ⟨a+K+4, 0, 0, 3*K+2, 0⟩ := by
  apply step_stepStar_stepPlus
  · show fm ⟨a+1, 0, 0, 2*K+2, 0⟩ = some ⟨a, 1, 0, 2*K+3, 0⟩
    rw [show 2 * K + 2 = (2 * K + 2) from rfl, show 2 * K + 3 = (2 * K + 2) + 1 from by ring]
    simp [fm]
  exact even_star a K

-- Main theorem
theorem nonhalt : ¬halts fm c₀ := by
  apply progress_nonhalt_simple (fm := fm) (A := ℕ × ℕ) (fun ⟨a, d⟩ ↦ ⟨a+1, 0, 0, d, 0⟩) ⟨0, 0⟩
  intro ⟨a, d⟩
  rcases d with _ | d
  · exact ⟨⟨a+1, 1⟩, trans_d0 a⟩
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · subst hK
    rw [show K + K + 1 = 2 * K + 1 from by ring]
    exact ⟨⟨a+K, 3*K+4⟩, trans_odd a K⟩
  · subst hK
    rw [show 2 * K + 1 + 1 = 2 * K + 2 from by ring]
    exact ⟨⟨a+K+3, 3*K+2⟩, trans_even a K⟩

end Sz21_140_unofficial_133
