import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz21_140_unofficial #18: [2/15, 99/14, 25/2, 7/11, 22/5]

Vector representation:
```
 1 -1 -1  0  0
-1  2  0 -1  1
-1  0  2  0  0
 0  0  0  1 -1
 1  0 -1  0  1
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz21_140_unofficial_18

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+1, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+2, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | _ => none

-- R4 repeated: e → d
theorem e_to_d : ∀ k, ∀ d e, ⟨(0:ℕ), (0:ℕ), c, d, e+k⟩ [fm]⊢* ⟨(0:ℕ), (0:ℕ), c, d+k, e⟩ := by
  intro k; induction' k with k ih <;> intro d e
  · exists 0
  rw [show e + (k + 1) = (e + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R3 repeated: a → c
theorem a_to_c : ∀ k, ∀ a c, ⟨a+k, (0:ℕ), c, (0:ℕ), e⟩ [fm]⊢* ⟨a, (0:ℕ), c+2*k, (0:ℕ), e⟩ := by
  intro k; induction' k with k ih <;> intro a c
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  step fm
  apply stepStar_trans (ih _ _)
  ring_nf; finish

-- R2,R1,R1 round: 3 explicit steps
theorem r2r1r1_one (a c d e : ℕ) : ⟨a+1, 0, c+2, d+1, e⟩ [fm]⊢* ⟨a+2, 0, c, d, e+1⟩ := by
  apply stepStar_trans (c₂ := ⟨a, 2, c+2, d, e+1⟩)
  · have : fm ⟨a+1, 0, c+2, d+1, e⟩ = some ⟨a, 0+2, c+2, d, e+1⟩ := by simp [fm]
    exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨a+1, 1, c+1, d, e+1⟩)
  · have : fm ⟨a, 1+1, (c+1)+1, d, e+1⟩ = some ⟨a+1, 1, c+1, d, e+1⟩ := by simp [fm]
    rw [show 1 + 1 = 2 from rfl, show (c + 1) + 1 = c + 2 from by ring] at this
    exact step_stepStar this
  have : fm ⟨a+1, 0+1, c+1, d, e+1⟩ = some ⟨(a+1)+1, 0, c, d, e+1⟩ := by simp [fm]
  rw [show (a + 1) + 1 = a + 2 from by ring] at this
  exact step_stepStar this

-- R2,R1,R1 rounds by induction
theorem r2r1r1_rounds : ∀ k, ∀ a c d e, ⟨a+1, 0, c+2*k, d+k, e⟩ [fm]⊢* ⟨a+1+k, 0, c, d, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a c d e
  · exists 0
  rw [show c + 2 * (k + 1) = (c + 2 * k) + 2 from by ring,
      show d + (k + 1) = (d + k) + 1 from by ring]
  apply stepStar_trans (r2r1r1_one a (c + 2 * k) (d + k) e)
  have h := ih (a+1) c d (e+1)
  rw [show a + 1 + 1 = a + 2 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- R2 chain: consuming a and d, building b and e
theorem r2_chain : ∀ k, ∀ a b e, ⟨a+k, b, 0, k, e⟩ [fm]⊢* ⟨a, b+2*k, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show a + (k + 1) = (a + k) + 1 from by ring]
  apply stepStar_trans (c₂ := ⟨a + k, b + 2, 0, k, e + 1⟩)
  · have : fm ⟨(a+k)+1, b, 0, k+1, e⟩ = some ⟨a+k, b+2, 0, k, e+1⟩ := by simp [fm]
    exact step_stepStar this
  refine stepStar_trans (ih a (b+2) (e+1)) ?_
  ring_nf; finish

-- R3,R1,R1 round: consuming b by 2, incrementing a
theorem r3r1r1_one (a b e : ℕ) : ⟨a+1, b+2, 0, 0, e⟩ [fm]⊢* ⟨a+2, b, 0, 0, e⟩ := by
  apply stepStar_trans (c₂ := ⟨a, b+2, 2, 0, e⟩)
  · have : fm ⟨a+1, b+2, 0, 0, e⟩ = some ⟨a, b+2, 0+2, 0, e⟩ := by simp [fm]
    exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨a+1, b+1, 1, 0, e⟩)
  · have : fm ⟨a, (b+1)+1, 1+1, 0, e⟩ = some ⟨a+1, b+1, 1, 0, e⟩ := by simp [fm]
    rw [show (b + 1) + 1 = b + 2 from by ring, show 1 + 1 = 2 from rfl] at this
    exact step_stepStar this
  have : fm ⟨a+1, (b)+1, 0+1, 0, e⟩ = some ⟨(a+1)+1, b, 0, 0, e⟩ := by simp [fm]
  rw [show (a + 1) + 1 = a + 2 from by ring] at this
  exact step_stepStar this

-- R3,R1,R1 rounds
theorem r3r1r1_rounds : ∀ k, ∀ a b e, ⟨a+1, b+2*k, 0, 0, e⟩ [fm]⊢* ⟨a+1+k, b, 0, 0, e⟩ := by
  intro k; induction' k with k ih <;> intro a b e
  · exists 0
  rw [show b + 2 * (k + 1) = (b + 2 * k) + 2 from by ring]
  apply stepStar_trans (r3r1r1_one a (b + 2 * k) e)
  have h := ih (a+1) b e
  rw [show a + 1 + 1 = a + 2 from by ring] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- b_consume for even b: (2, 2K, 0, 0, e) →* (0, 0, 2K+4, 0, e)
theorem b_consume_even (K : ℕ) : ∀ e, ⟨2, 2*K, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2*K+4, 0, e⟩ := by
  intro e
  apply stepStar_trans (c₂ := ⟨K + 2, 0, 0, 0, e⟩)
  · have h := r3r1r1_rounds K 1 0 e
    rw [show 1 + 1 + K = K + 2 from by ring, show 1 + 1 = 2 from rfl] at h
    simp only [Nat.zero_add] at h; exact h
  have h := @a_to_c e (K + 2) 0 0
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- b_consume for odd b: (2, 2K+1, 0, 0, e) →* (0, 0, 2K+5, 0, e)
theorem b_consume_odd (K : ℕ) : ∀ e, ⟨2, 2*K+1, 0, 0, e⟩ [fm]⊢* ⟨0, 0, 2*K+5, 0, e⟩ := by
  intro e
  apply stepStar_trans (c₂ := ⟨K + 2, 1, 0, 0, e⟩)
  · have h := r3r1r1_rounds K 1 1 e
    rw [show 1 + 1 + K = K + 2 from by ring, show 1 + 1 = 2 from rfl,
        show 1 + 2 * K = 2 * K + 1 from by ring] at h
    exact h
  apply stepStar_trans (c₂ := ⟨K+1, 1, 2, 0, e⟩)
  · have : fm ⟨(K+1)+1, 1, 0, 0, e⟩ = some ⟨K+1, 1, 0+2, 0, e⟩ := by simp [fm]
    rw [show (K + 1) + 1 = K + 2 from by ring] at this
    exact step_stepStar this
  apply stepStar_trans (c₂ := ⟨K+2, 0, 1, 0, e⟩)
  · have : fm ⟨K+1, 0+1, 1+1, 0, e⟩ = some ⟨(K+1)+1, 0, 1, 0, e⟩ := by simp [fm]
    rw [show 1 + 1 = 2 from rfl, show (K + 1) + 1 = K + 2 from by ring] at this
    exact step_stepStar this
  have h := @a_to_c e (K + 2) 0 1
  simp only [Nat.zero_add] at h
  refine stepStar_trans h ?_
  ring_nf; finish

-- Main transition: (0, 0, d+3, d+1, 0) ⊢⁺ (0, 0, d+4, d+2, 0)
theorem main_trans (d : ℕ) :
    ⟨0, 0, d+3, d+1, 0⟩ [fm]⊢⁺ ⟨0, 0, d+4, d+2, 0⟩ := by
  -- R5 step (gives stepPlus)
  apply step_stepStar_stepPlus (c₂ := ⟨1, 0, d+2, d+1, 1⟩)
  · show fm ⟨0, 0, (d+2)+1, d+1, 0⟩ = some ⟨0+1, 0, d+2, d+1, 0+1⟩; simp [fm]
  -- R2
  apply stepStar_trans (c₂ := ⟨0, 2, d+2, d, 2⟩)
  · have : fm ⟨0+1, 0, d+2, d+1, 1⟩ = some ⟨0, 0+2, d+2, d, 1+1⟩ := by simp [fm]
    rw [show 1 + 1 = 2 from rfl] at this; exact step_stepStar this
  -- R1
  apply stepStar_trans (c₂ := ⟨1, 1, d+1, d, 2⟩)
  · have : fm ⟨0, 1+1, (d+1)+1, d, 2⟩ = some ⟨0+1, 1, d+1, d, 2⟩ := by simp [fm]
    rw [show 1 + 1 = 2 from rfl, show (d + 1) + 1 = d + 2 from by ring] at this
    exact step_stepStar this
  -- R1
  apply stepStar_trans (c₂ := ⟨2, 0, d, d, 2⟩)
  · have : fm ⟨1, 0+1, d+1, d, 2⟩ = some ⟨1+1, 0, d, d, 2⟩ := by simp [fm]
    rw [show 1 + 1 = 2 from rfl] at this; exact step_stepStar this
  -- Split by parity of d
  rcases Nat.even_or_odd d with ⟨K, hK⟩ | ⟨K, hK⟩
  · -- d even: d = 2K
    rw [show K + K = 2 * K from by ring] at hK; subst hK
    -- r2r1r1_rounds: K rounds
    apply stepStar_trans (c₂ := ⟨K + 2, 0, 0, K, K + 2⟩)
    · have h := r2r1r1_rounds K 1 0 K 2
      rw [show 1 + 1 + K = K + 2 from by ring, show 1 + 1 = 2 from rfl,
          show 0 + 2 * K = 2 * K from by ring, show K + K = 2 * K from by ring] at h
      exact h
    -- R2 chain
    apply stepStar_trans (c₂ := ⟨2, 2*K, 0, 0, 2*K+2⟩)
    · have h := r2_chain K 2 0 (K + 2)
      rw [show 2 + K = K + 2 from by ring] at h
      simp only [Nat.zero_add] at h
      refine stepStar_trans h ?_; ring_nf; finish
    -- b_consume even
    apply stepStar_trans (b_consume_even K (2*K+2))
    -- e_to_d
    have h := e_to_d (c := 2*K+4) (2*K+2) 0 0
    simp only [Nat.zero_add] at h; exact h
  · -- d odd: d = 2K+1
    subst hK
    -- r2r1r1_rounds: K rounds
    apply stepStar_trans (c₂ := ⟨K + 2, 0, 1, K + 1, K + 2⟩)
    · have h := r2r1r1_rounds K 1 1 (K + 1) 2
      rw [show 1 + 1 + K = K + 2 from by ring, show 1 + 1 = 2 from rfl,
          show 1 + 2 * K = 2 * K + 1 from by ring,
          show K + 1 + K = 2 * K + 1 from by ring] at h
      exact h
    -- R2
    apply stepStar_trans (c₂ := ⟨K + 1, 2, 1, K, K + 3⟩)
    · have : fm ⟨(K+1)+1, 0, 1, K+1, K+2⟩ = some ⟨K+1, 0+2, 1, K, (K+2)+1⟩ := by simp [fm]
      rw [show (K + 1) + 1 = K + 2 from by ring, show (K + 2) + 1 = K + 3 from by ring] at this
      exact step_stepStar this
    -- R1
    apply stepStar_trans (c₂ := ⟨K + 2, 1, 0, K, K + 3⟩)
    · have : fm ⟨K+1, 1+1, 0+1, K, K+3⟩ = some ⟨(K+1)+1, 1, 0, K, K+3⟩ := by simp [fm]
      rw [show 1 + 1 = 2 from rfl, show (K + 1) + 1 = K + 2 from by ring] at this
      exact step_stepStar this
    -- R2 chain
    apply stepStar_trans (c₂ := ⟨2, 2*K+1, 0, 0, 2*K+3⟩)
    · have h := r2_chain K 2 1 (K + 3)
      rw [show 2 + K = K + 2 from by ring] at h
      refine stepStar_trans h ?_; ring_nf; finish
    -- b_consume odd
    apply stepStar_trans (b_consume_odd K (2*K+3))
    -- e_to_d
    have h := e_to_d (c := 2*K+5) (2*K+3) 0 0
    simp only [Nat.zero_add] at h
    refine stepStar_trans h ?_; ring_nf; finish

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨0, 0, 3, 1, 0⟩) (by execute fm 4)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ) (fun d ↦ ⟨0, 0, d+3, d+1, 0⟩) 0
  intro d; exact ⟨d+1, main_trans d⟩

end Sz21_140_unofficial_18
