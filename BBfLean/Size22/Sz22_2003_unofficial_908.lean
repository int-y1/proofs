import BBfLean.FM
import Mathlib.Tactic.Ring

namespace Sz22_2003_unofficial_908

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d, e⟩ => some ⟨a+2, b, c, d, e⟩
  | ⟨a+1, b, c, d+1, e⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+2, d, e+1⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b, c, d+1, e⟩
  | ⟨a, b, c, d, e+1⟩ => some ⟨a+1, b, c+2, d, e⟩
  | _ => none

theorem r3_chain : ∀ k, ∀ a c e, ⟨a + k, (0 : ℕ), c, (0 : ℕ), e⟩ [fm]⊢* ⟨a, 0, c + 2 * k, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a c e
  · simp; exists 0
  · rw [show a + (k + 1) = (a + k) + 1 from by ring]
    have h : ⟨(a + k) + 1, (0 : ℕ), c, (0 : ℕ), e⟩ [fm]⊢ ⟨a + k, 0, c + 2, 0, e + 1⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h)
    apply stepStar_trans (ih a (c + 2) (e + 1))
    rw [show c + 2 + 2 * k = c + 2 * (k + 1) from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; exists 0

theorem r4_chain : ∀ k, ∀ c d e, ⟨(0 : ℕ), (0 : ℕ), c + k, d, e⟩ [fm]⊢* ⟨0, 0, c, d + k, e⟩ := by
  intro k; induction' k with k ih <;> intro c d e
  · simp; exists 0
  · rw [show c + (k + 1) = (c + k) + 1 from by ring]
    have h : ⟨(0 : ℕ), (0 : ℕ), (c + k) + 1, d, e⟩ [fm]⊢ ⟨0, 0, c + k, d + 1, e⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h)
    apply stepStar_trans (ih c (d + 1) e)
    rw [show d + 1 + k = d + (k + 1) from by ring]; exists 0

theorem phases12_from2 (A e : ℕ) : ⟨A, (0 : ℕ), (2 : ℕ), (0 : ℕ), e⟩ [fm]⊢* ⟨0, 0, 0, 2 + 2 * A, e + A⟩ := by
  have h1 := r3_chain A 0 2 e; simp at h1
  apply stepStar_trans h1
  have h2 := r4_chain (2 + 2 * A) 0 0 (e + A); simp at h2; exact h2

theorem round_bge1 : ⟨(0 : ℕ), b + 1, (0 : ℕ), d + 5, e + 1⟩ [fm]⊢* ⟨0, b + 4, 0, d, e⟩ := by
  have h1 : ⟨(0 : ℕ), b + 1, (0 : ℕ), d + 5, e + 1⟩ [fm]⊢ ⟨1, b + 1, 2, d + 5, e⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar h1)
  have h2 : ⟨(1 : ℕ), b + 1, (2 : ℕ), d + 5, e⟩ [fm]⊢ ⟨3, b, 1, d + 5, e⟩ := by
    show ⟨1, b + 1, 1 + 1, d + 5, e⟩ [fm]⊢ ⟨1 + 2, b, 1, d + 5, e⟩; simp [fm]
  apply stepStar_trans (step_stepStar h2)
  rcases b with _ | b'
  · have : ⟨(3 : ℕ), (0 : ℕ), (1 : ℕ), d + 5, e⟩ [fm]⊢ ⟨2, 1, 1, d + 4, e⟩ := by
      show ⟨2 + 1, 0, 1, (d + 4) + 1, e⟩ [fm]⊢ ⟨2, 0 + 1, 1, d + 4, e⟩; simp [fm]
    apply stepStar_trans (step_stepStar this)
    have : ⟨(2 : ℕ), (1 : ℕ), (1 : ℕ), d + 4, e⟩ [fm]⊢ ⟨4, 0, 0, d + 4, e⟩ := by
      show ⟨2, 0 + 1, 0 + 1, d + 4, e⟩ [fm]⊢ ⟨2 + 2, 0, 0, d + 4, e⟩; simp [fm]
    apply stepStar_trans (step_stepStar this)
    execute fm 4
  · have : ⟨(3 : ℕ), b' + 1, (1 : ℕ), d + 5, e⟩ [fm]⊢ ⟨5, b', 0, d + 5, e⟩ := by
      show ⟨3, b' + 1, 0 + 1, d + 5, e⟩ [fm]⊢ ⟨3 + 2, b', 0, d + 5, e⟩; simp [fm]
    apply stepStar_trans (step_stepStar this)
    have : ⟨(5 : ℕ), b', (0 : ℕ), d + 5, e⟩ [fm]⊢* ⟨0, b' + 5, 0, d, e⟩ := by execute fm 5
    apply stepStar_trans this
    rw [show b' + 5 = (b' + 1) + 4 from by ring]; exists 0

theorem combined_rounds : ∀ K, ∀ r f,
    ⟨(0 : ℕ), (0 : ℕ), (0 : ℕ), r + 5 * (K + 1), f + (K + 1)⟩ [fm]⊢* ⟨0, 3 * (K + 1), 0, r, f⟩ := by
  intro K; induction' K with K ih <;> intro r f
  · rw [show r + 5 * 1 = r + 5 from by ring, show f + 1 = f + 1 from rfl,
        show (3 : ℕ) * 1 = 3 from by ring]
    execute fm 8
  · rw [show r + 5 * (K + 1 + 1) = (r + 5) + 5 * (K + 1) from by ring,
        show f + (K + 1 + 1) = (f + 1) + (K + 1) from by ring]
    apply stepStar_trans (ih (r + 5) (f + 1))
    show ⟨0, 3 * (K + 1), 0, r + 5, f + 1⟩ [fm]⊢* ⟨0, 3 * (K + 1 + 1), 0, r, f⟩
    rw [show (3 : ℕ) * (K + 1) = (3 * K + 3 - 1) + 1 from by omega]
    apply stepStar_trans (round_bge1 (b := 3 * K + 3 - 1) (d := r) (e := f))
    rw [show 3 * K + 3 - 1 + 4 = 3 * (K + 1 + 1) from by omega]; exists 0

theorem endgame_r0 : ∀ b e, ⟨(0 : ℕ), b + 2, (0 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢* ⟨5, b, 0, 0, e⟩ := by
  intro b e; rcases b with _ | b'
  · execute fm 3
  · have h1 : ⟨(0 : ℕ), b' + 1 + 2, (0 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢ ⟨1, b' + 3, 2, 0, e⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h1)
    have h2 : ⟨(1 : ℕ), b' + 3, (2 : ℕ), (0 : ℕ), e⟩ [fm]⊢ ⟨3, b' + 2, 1, 0, e⟩ := by
      show ⟨1, (b' + 2) + 1, 1 + 1, 0, e⟩ [fm]⊢ ⟨1 + 2, b' + 2, 1, 0, e⟩; simp [fm]
    apply stepStar_trans (step_stepStar h2)
    have h3 : ⟨(3 : ℕ), b' + 2, (1 : ℕ), (0 : ℕ), e⟩ [fm]⊢ ⟨5, b' + 1, 0, 0, e⟩ := by
      show ⟨3, (b' + 1) + 1, 0 + 1, 0, e⟩ [fm]⊢ ⟨3 + 2, b' + 1, 0, 0, e⟩; simp [fm]
    exact step_stepStar h3

theorem endgame_r1 : ∀ b e, ⟨(0 : ℕ), b + 1, (0 : ℕ), (1 : ℕ), e + 1⟩ [fm]⊢* ⟨4, b, 0, 0, e⟩ := by
  intro b e; rcases b with _ | b'
  · execute fm 4
  · have h1 : ⟨(0 : ℕ), b' + 1 + 1, (0 : ℕ), (1 : ℕ), e + 1⟩ [fm]⊢ ⟨1, b' + 2, 2, 1, e⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h1)
    have h2 : ⟨(1 : ℕ), b' + 2, (2 : ℕ), (1 : ℕ), e⟩ [fm]⊢ ⟨3, b' + 1, 1, 1, e⟩ := by
      show ⟨1, (b' + 1) + 1, 1 + 1, 1, e⟩ [fm]⊢ ⟨1 + 2, b' + 1, 1, 1, e⟩; simp [fm]
    apply stepStar_trans (step_stepStar h2)
    have h3 : ⟨(3 : ℕ), b' + 1, (1 : ℕ), (1 : ℕ), e⟩ [fm]⊢ ⟨5, b', 0, 1, e⟩ := by
      show ⟨3, b' + 1, 0 + 1, 1, e⟩ [fm]⊢ ⟨3 + 2, b', 0, 1, e⟩; simp [fm]
    apply stepStar_trans (step_stepStar h3)
    have : ⟨(5 : ℕ), b', (0 : ℕ), (1 : ℕ), e⟩ [fm]⊢* ⟨4, b' + 1, 0, 0, e⟩ := by execute fm 1
    apply stepStar_trans this; exists 0

theorem endgame_r2 : ∀ b e, ⟨(0 : ℕ), b, (0 : ℕ), (2 : ℕ), e + 1⟩ [fm]⊢* ⟨3, b, 0, 0, e⟩ := by
  intro b e; rcases b with _ | b
  · execute fm 5
  · have h1 : ⟨(0 : ℕ), b + 1, (0 : ℕ), (2 : ℕ), e + 1⟩ [fm]⊢ ⟨1, b + 1, 2, 2, e⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h1)
    have h2 : ⟨(1 : ℕ), b + 1, (2 : ℕ), (2 : ℕ), e⟩ [fm]⊢ ⟨3, b, 1, 2, e⟩ := by
      show ⟨1, b + 1, 1 + 1, 2, e⟩ [fm]⊢ ⟨1 + 2, b, 1, 2, e⟩; simp [fm]
    apply stepStar_trans (step_stepStar h2)
    rcases b with _ | b'
    · execute fm 3
    · have : ⟨(3 : ℕ), b' + 1, (1 : ℕ), (2 : ℕ), e⟩ [fm]⊢ ⟨5, b', 0, 2, e⟩ := by
        show ⟨3, b' + 1, 0 + 1, 2, e⟩ [fm]⊢ ⟨3 + 2, b', 0, 2, e⟩; simp [fm]
      apply stepStar_trans (step_stepStar this)
      have : ⟨(5 : ℕ), b', (0 : ℕ), (2 : ℕ), e⟩ [fm]⊢* ⟨3, b' + 2, 0, 0, e⟩ := by execute fm 2
      apply stepStar_trans this
      rw [show b' + 2 = b' + 1 + 1 from by ring]; exists 0

theorem endgame_r3 : ∀ b e, ⟨(0 : ℕ), b, (0 : ℕ), (3 : ℕ), e + 1⟩ [fm]⊢* ⟨2, b + 1, 0, 0, e⟩ := by
  intro b e; rcases b with _ | b
  · execute fm 6
  · have h1 : ⟨(0 : ℕ), b + 1, (0 : ℕ), (3 : ℕ), e + 1⟩ [fm]⊢ ⟨1, b + 1, 2, 3, e⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h1)
    have h2 : ⟨(1 : ℕ), b + 1, (2 : ℕ), (3 : ℕ), e⟩ [fm]⊢ ⟨3, b, 1, 3, e⟩ := by
      show ⟨1, b + 1, 1 + 1, 3, e⟩ [fm]⊢ ⟨1 + 2, b, 1, 3, e⟩; simp [fm]
    apply stepStar_trans (step_stepStar h2)
    rcases b with _ | b'
    · execute fm 4
    · have : ⟨(3 : ℕ), b' + 1, (1 : ℕ), (3 : ℕ), e⟩ [fm]⊢ ⟨5, b', 0, 3, e⟩ := by
        show ⟨3, b' + 1, 0 + 1, 3, e⟩ [fm]⊢ ⟨3 + 2, b', 0, 3, e⟩; simp [fm]
      apply stepStar_trans (step_stepStar this)
      have : ⟨(5 : ℕ), b', (0 : ℕ), (3 : ℕ), e⟩ [fm]⊢* ⟨2, b' + 3, 0, 0, e⟩ := by execute fm 3
      apply stepStar_trans this
      rw [show b' + 3 = (b' + 1) + 1 + 1 from by ring]; exists 0

theorem endgame_r4 : ∀ b e, ⟨(0 : ℕ), b, (0 : ℕ), (4 : ℕ), e + 1⟩ [fm]⊢* ⟨1, b + 2, 0, 0, e⟩ := by
  intro b e; rcases b with _ | b
  · execute fm 7
  · have h1 : ⟨(0 : ℕ), b + 1, (0 : ℕ), (4 : ℕ), e + 1⟩ [fm]⊢ ⟨1, b + 1, 2, 4, e⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h1)
    have h2 : ⟨(1 : ℕ), b + 1, (2 : ℕ), (4 : ℕ), e⟩ [fm]⊢ ⟨3, b, 1, 4, e⟩ := by
      show ⟨1, b + 1, 1 + 1, 4, e⟩ [fm]⊢ ⟨1 + 2, b, 1, 4, e⟩; simp [fm]
    apply stepStar_trans (step_stepStar h2)
    rcases b with _ | b'
    · execute fm 5
    · have : ⟨(3 : ℕ), b' + 1, (1 : ℕ), (4 : ℕ), e⟩ [fm]⊢ ⟨5, b', 0, 4, e⟩ := by
        show ⟨3, b' + 1, 0 + 1, 4, e⟩ [fm]⊢ ⟨3 + 2, b', 0, 4, e⟩; simp [fm]
      apply stepStar_trans (step_stepStar this)
      have : ⟨(5 : ℕ), b', (0 : ℕ), (4 : ℕ), e⟩ [fm]⊢* ⟨1, b' + 4, 0, 0, e⟩ := by execute fm 4
      apply stepStar_trans this
      rw [show b' + 4 = (b' + 1) + 1 + 2 from by ring]; exists 0

theorem buildup : ⟨a + 1, b + 2, (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢* ⟨a + 4, b, 0, 0, e + 1⟩ := by
  rcases b with _ | b'
  · execute fm 3
  · have h1 : ⟨a + 1, b' + 1 + 2, (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢ ⟨a, b' + 3, 2, 0, e + 1⟩ := by
      show ⟨a + 1, b' + 1 + 2, 0, 0, e⟩ [fm]⊢ ⟨a, b' + 1 + 2, 0 + 2, 0, e + 1⟩; simp [fm]
    apply stepStar_trans (step_stepStar h1)
    have h2 : ⟨a, b' + 3, (2 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢ ⟨a + 2, b' + 2, 1, 0, e + 1⟩ := by
      show ⟨a, (b' + 2) + 1, 1 + 1, 0, e + 1⟩ [fm]⊢ ⟨a + 2, b' + 2, 1, 0, e + 1⟩; simp [fm]
    apply stepStar_trans (step_stepStar h2)
    have h3 : ⟨a + 2, b' + 2, (1 : ℕ), (0 : ℕ), e + 1⟩ [fm]⊢ ⟨a + 4, b' + 1, 0, 0, e + 1⟩ := by
      show ⟨a + 2, (b' + 1) + 1, 0 + 1, 0, e + 1⟩ [fm]⊢ ⟨a + 2 + 2, b' + 1, 0, 0, e + 1⟩; simp [fm]
    exact step_stepStar h3

theorem buildup_chain : ∀ k, ∀ a e, ⟨a + 1, 2 * k, (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢* ⟨a + 3 * k + 1, 0, 0, 0, e + k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · simp; exists 0
  · show ⟨a + 1, 2 * k + 2, 0, 0, e⟩ [fm]⊢* _
    apply stepStar_trans (buildup (a := a) (b := 2 * k) (e := e))
    rw [show a + 4 = (a + 3) + 1 from by ring]
    apply stepStar_trans (ih (a + 3) (e + 1))
    rw [show a + 3 + 3 * k + 1 = a + 3 * (k + 1) + 1 from by ring,
        show e + 1 + k = e + (k + 1) from by ring]; exists 0

-- All trans_mod use: first R3 step, then phases12_from2, then (optionally) combined_rounds,
-- then endgame, then buildup_chain.

-- mod 0: (5*(k+1), 0, 0, 0, e) ⊢⁺ (9*k+11, 0, 0, 0, e+6*k+4)
theorem trans_mod0 (k e : ℕ) :
    ⟨5 * (k + 1), (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢⁺ ⟨9 * k + 11, 0, 0, 0, e + 6 * k + 4⟩ := by
  have h1 : ⟨5 * (k + 1), (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢ ⟨5 * k + 4, 0, 2, 0, e + 1⟩ := by
    rw [show 5 * (k + 1) = (5 * k + 4) + 1 from by ring]; simp [fm]
  apply step_stepStar_stepPlus h1
  apply stepStar_trans (phases12_from2 (5 * k + 4) (e + 1))
  rw [show 2 + 2 * (5 * k + 4) = 0 + 5 * ((2 * k + 1) + 1) from by ring,
      show e + 1 + (5 * k + 4) = (e + 3 * k + 3) + ((2 * k + 1) + 1) from by ring]
  apply stepStar_trans (combined_rounds (2 * k + 1) 0 (e + 3 * k + 3))
  rw [show 3 * ((2 * k + 1) + 1) = (6 * k + 4) + 2 from by ring,
      show e + 3 * k + 3 = (e + 3 * k + 2) + 1 from by ring]
  apply stepStar_trans (endgame_r0 (6 * k + 4) (e + 3 * k + 2))
  rw [show (5 : ℕ) = 4 + 1 from by ring,
      show 6 * k + 4 = 2 * (3 * k + 2) from by ring]
  apply stepStar_trans (buildup_chain (3 * k + 2) 4 (e + 3 * k + 2))
  rw [show 4 + 3 * (3 * k + 2) + 1 = 9 * k + 11 from by ring,
      show e + 3 * k + 2 + (3 * k + 2) = e + 6 * k + 4 from by ring]; exists 0

-- mod 1: (5*k+1, 0, 0, 0, e) ⊢⁺ (9*k+3, 0, 0, 0, e+6*k)
-- After first step: (5*k, 0, 2, 0, e+1)
-- phases12_from2(5*k, e+1): (0, 0, 0, 2+10*k, e+1+5*k)
-- k=0: D=2, r=2, no rounds, endgame_r2(0, e) -> (3, 0, 0, 0, e)
-- k>=1: D=2+10*k = 2 + 5*2k, r=2, K+1=2k rounds
theorem trans_mod1 (k e : ℕ) :
    ⟨5 * k + 1, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢⁺ ⟨9 * k + 3, 0, 0, 0, e + 6 * k⟩ := by
  have h1 : ⟨5 * k + 1, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢ ⟨5 * k, 0, 2, 0, e + 1⟩ := by
    rw [show 5 * k + 1 = (5 * k) + 1 from by ring]; simp [fm]
  apply step_stepStar_stepPlus h1
  apply stepStar_trans (phases12_from2 (5 * k) (e + 1))
  rcases k with _ | k
  · -- k=0: D=2, endgame_r2(0, e)
    show ⟨0, 0, 0, 2, e + 1⟩ [fm]⊢* ⟨3, 0, 0, 0, e⟩
    exact endgame_r2 0 e
  · -- k>=1: D=2+10*(k+1) = 2 + 5*((2*k+1)+1)
    rw [show 2 + 2 * (5 * (k + 1)) = 2 + 5 * ((2 * k + 1) + 1) from by ring,
        show e + 1 + 5 * (k + 1) = (e + 3 * k + 4) + ((2 * k + 1) + 1) from by ring]
    apply stepStar_trans (combined_rounds (2 * k + 1) 2 (e + 3 * k + 4))
    rw [show 3 * ((2 * k + 1) + 1) = 6 * k + 6 from by ring,
        show e + 3 * k + 4 = (e + 3 * k + 3) + 1 from by ring]
    apply stepStar_trans (endgame_r2 (6 * k + 6) (e + 3 * k + 3))
    rw [show (3 : ℕ) = 2 + 1 from by ring,
        show 6 * k + 6 = 2 * (3 * k + 3) from by ring]
    apply stepStar_trans (buildup_chain (3 * k + 3) 2 (e + 3 * k + 3))
    rw [show 2 + 3 * (3 * k + 3) + 1 = 9 * (k + 1) + 3 from by ring,
        show e + 3 * k + 3 + (3 * k + 3) = e + 6 * (k + 1) from by ring]; exists 0

-- mod 2: (5*k+2, 0, 0, 0, e) ⊢⁺ (9*k+4, 0, 0, 0, e+6*k+2)
-- After first step: (5*k+1, 0, 2, 0, e+1)
-- phases12_from2(5*k+1, e+1): (0, 0, 0, 2+2*(5*k+1), e+1+5*k+1) = (0, 0, 0, 10*k+4, e+5*k+2)
-- k=0: D=4, r=4, no rounds, endgame_r4(0, e+1) then buildup_chain(1)
-- k>=1: D=10*k+4 = 4+5*2k, r=4, K+1=2k rounds
theorem trans_mod2 (k e : ℕ) :
    ⟨5 * k + 2, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢⁺ ⟨9 * k + 4, 0, 0, 0, e + 6 * k + 2⟩ := by
  have h1 : ⟨5 * k + 2, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢ ⟨5 * k + 1, 0, 2, 0, e + 1⟩ := by
    rw [show 5 * k + 2 = (5 * k + 1) + 1 from by ring]; simp [fm]
  apply step_stepStar_stepPlus h1
  apply stepStar_trans (phases12_from2 (5 * k + 1) (e + 1))
  rcases k with _ | k
  · -- k=0: D=4, endgame_r4(0, e+1) then buildup(1)
    show ⟨0, 0, 0, 4, e + 2⟩ [fm]⊢* ⟨4, 0, 0, 0, e + 2⟩
    rw [show e + 2 = (e + 1) + 1 from by ring]
    apply stepStar_trans (endgame_r4 0 (e + 1))
    rw [show (1 : ℕ) = 0 + 1 from by ring, show (2 : ℕ) = 2 * 1 from by ring]
    apply stepStar_trans (buildup_chain 1 0 (e + 1))
    rw [show 0 + 3 * 1 + 1 = 4 from by ring, show e + 1 + 1 = e + 2 from by ring]; exists 0
  · -- k>=1: D=2+2*(5*(k+1)+1) = 4+5*((2*k+1)+1)
    rw [show 2 + 2 * (5 * (k + 1) + 1) = 4 + 5 * ((2 * k + 1) + 1) from by ring,
        show e + 1 + (5 * (k + 1) + 1) = (e + 3 * k + 5) + ((2 * k + 1) + 1) from by ring]
    apply stepStar_trans (combined_rounds (2 * k + 1) 4 (e + 3 * k + 5))
    rw [show 3 * ((2 * k + 1) + 1) = 6 * k + 6 from by ring,
        show e + 3 * k + 5 = (e + 3 * k + 4) + 1 from by ring]
    apply stepStar_trans (endgame_r4 (6 * k + 6) (e + 3 * k + 4))
    rw [show (1 : ℕ) = 0 + 1 from by ring,
        show 6 * k + 6 + 2 = 2 * (3 * k + 4) from by ring]
    apply stepStar_trans (buildup_chain (3 * k + 4) 0 (e + 3 * k + 4))
    rw [show 0 + 3 * (3 * k + 4) + 1 = 9 * (k + 1) + 4 from by ring,
        show e + 3 * k + 4 + (3 * k + 4) = e + 6 * (k + 1) + 2 from by ring]; exists 0

-- mod 3: (5*k+3, 0, 0, 0, e) ⊢⁺ (9*k+7, 0, 0, 0, e+6*k+2)
-- After first step: (5*k+2, 0, 2, 0, e+1)
-- phases12_from2(5*k+2, e+1): (0, 0, 0, 2+10*k+4, e+1+5*k+2) = (0, 0, 0, 10*k+6, e+5*k+3)
-- D=10*k+6 = 1+5*(2*k+1), r=1, K+1=2*k+1, K=2*k
theorem trans_mod3 (k e : ℕ) :
    ⟨5 * k + 3, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢⁺ ⟨9 * k + 7, 0, 0, 0, e + 6 * k + 2⟩ := by
  have h1 : ⟨5 * k + 3, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢ ⟨5 * k + 2, 0, 2, 0, e + 1⟩ := by
    rw [show 5 * k + 3 = (5 * k + 2) + 1 from by ring]; simp [fm]
  apply step_stepStar_stepPlus h1
  apply stepStar_trans (phases12_from2 (5 * k + 2) (e + 1))
  rw [show 2 + 2 * (5 * k + 2) = 1 + 5 * ((2 * k) + 1) from by ring,
      show e + 1 + (5 * k + 2) = (e + 3 * k + 2) + ((2 * k) + 1) from by ring]
  apply stepStar_trans (combined_rounds (2 * k) 1 (e + 3 * k + 2))
  rw [show 3 * ((2 * k) + 1) = (6 * k + 2) + 1 from by ring,
      show e + 3 * k + 2 = (e + 3 * k + 1) + 1 from by ring]
  apply stepStar_trans (endgame_r1 (6 * k + 2) (e + 3 * k + 1))
  rw [show (4 : ℕ) = 3 + 1 from by ring,
      show 6 * k + 2 = 2 * (3 * k + 1) from by ring]
  apply stepStar_trans (buildup_chain (3 * k + 1) 3 (e + 3 * k + 1))
  rw [show 3 + 3 * (3 * k + 1) + 1 = 9 * k + 7 from by ring,
      show e + 3 * k + 1 + (3 * k + 1) = e + 6 * k + 2 from by ring]; exists 0

-- mod 4: (5*k+4, 0, 0, 0, e) ⊢⁺ (9*k+8, 0, 0, 0, e+6*k+4)
-- After first step: (5*k+3, 0, 2, 0, e+1)
-- phases12_from2(5*k+3, e+1): (0, 0, 0, 2+10*k+6, e+1+5*k+3) = (0, 0, 0, 10*k+8, e+5*k+4)
-- D=10*k+8 = 3+5*(2*k+1), r=3, K+1=2*k+1, K=2*k
theorem trans_mod4 (k e : ℕ) :
    ⟨5 * k + 4, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢⁺ ⟨9 * k + 8, 0, 0, 0, e + 6 * k + 4⟩ := by
  have h1 : ⟨5 * k + 4, (0 : ℕ), (0 : ℕ), (0 : ℕ), e⟩ [fm]⊢ ⟨5 * k + 3, 0, 2, 0, e + 1⟩ := by
    rw [show 5 * k + 4 = (5 * k + 3) + 1 from by ring]; simp [fm]
  apply step_stepStar_stepPlus h1
  apply stepStar_trans (phases12_from2 (5 * k + 3) (e + 1))
  rw [show 2 + 2 * (5 * k + 3) = 3 + 5 * ((2 * k) + 1) from by ring,
      show e + 1 + (5 * k + 3) = (e + 3 * k + 3) + ((2 * k) + 1) from by ring]
  apply stepStar_trans (combined_rounds (2 * k) 3 (e + 3 * k + 3))
  rw [show 3 * ((2 * k) + 1) = 6 * k + 3 from by ring,
      show e + 3 * k + 3 = (e + 3 * k + 2) + 1 from by ring]
  apply stepStar_trans (endgame_r3 (6 * k + 3) (e + 3 * k + 2))
  rw [show (2 : ℕ) = 1 + 1 from by ring,
      show 6 * k + 3 + 1 = 2 * (3 * k + 2) from by ring]
  apply stepStar_trans (buildup_chain (3 * k + 2) 1 (e + 3 * k + 2))
  rw [show 1 + 3 * (3 * k + 2) + 1 = 9 * k + 8 from by ring,
      show e + 3 * k + 2 + (3 * k + 2) = e + 6 * k + 4 from by ring]; exists 0

theorem nonhalt : ¬halts fm c₀ := by
  apply stepStar_not_halts_not_halts (c₂ := ⟨1, 0, 0, 0, 0⟩) (by exists 0)
  apply progress_nonhalt (fm := fm)
    (P := fun q ↦ ∃ a e, q = ⟨a + 1, 0, 0, 0, e⟩)
  · intro c ⟨a, e, hq⟩; subst hq
    rcases (show (a + 1) % 5 = 0 ∨ (a + 1) % 5 = 1 ∨ (a + 1) % 5 = 2 ∨
            (a + 1) % 5 = 3 ∨ (a + 1) % 5 = 4 from by omega) with h | h | h | h | h
    · obtain ⟨k, hk⟩ : ∃ k, a + 1 = 5 * (k + 1) := ⟨(a + 1) / 5 - 1, by omega⟩
      rw [hk]
      exact ⟨⟨9 * k + 11, 0, 0, 0, e + 6 * k + 4⟩,
        ⟨9 * k + 10, e + 6 * k + 4, by ring_nf⟩, trans_mod0 k e⟩
    · obtain ⟨k, hk⟩ : ∃ k, a + 1 = 5 * k + 1 := ⟨(a + 1) / 5, by omega⟩
      rw [hk]
      exact ⟨⟨9 * k + 3, 0, 0, 0, e + 6 * k⟩,
        ⟨9 * k + 2, e + 6 * k, by ring_nf⟩, trans_mod1 k e⟩
    · obtain ⟨k, hk⟩ : ∃ k, a + 1 = 5 * k + 2 := ⟨(a + 1) / 5, by omega⟩
      rw [hk]
      exact ⟨⟨9 * k + 4, 0, 0, 0, e + 6 * k + 2⟩,
        ⟨9 * k + 3, e + 6 * k + 2, by ring_nf⟩, trans_mod2 k e⟩
    · obtain ⟨k, hk⟩ : ∃ k, a + 1 = 5 * k + 3 := ⟨(a + 1) / 5, by omega⟩
      rw [hk]
      exact ⟨⟨9 * k + 7, 0, 0, 0, e + 6 * k + 2⟩,
        ⟨9 * k + 6, e + 6 * k + 2, by ring_nf⟩, trans_mod3 k e⟩
    · obtain ⟨k, hk⟩ : ∃ k, a + 1 = 5 * k + 4 := ⟨(a + 1) / 5, by omega⟩
      rw [hk]
      exact ⟨⟨9 * k + 8, 0, 0, 0, e + 6 * k + 4⟩,
        ⟨9 * k + 7, e + 6 * k + 4, by ring_nf⟩, trans_mod4 k e⟩
  · exact ⟨0, 0, rfl⟩
