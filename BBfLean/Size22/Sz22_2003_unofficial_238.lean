import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #238: [11/105, 3/22, 20/3, 35/2, 9/5]

Vector representation:
```
 0 -1 -1 -1  1
-1  1  0  0 -1
 2 -1  1  0  0
-1  0  1  1  0
 0  2 -1  0  0
```

This Fractran program doesn't halt.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_238

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b+1, c+1, d+1, e⟩ => some ⟨a, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e+1⟩ => some ⟨a, b+1, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a+2, b, c+1, d, e⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b, c+1, d+1, e⟩
  | ⟨a, b, c+1, d, e⟩ => some ⟨a, b+2, c, d, e⟩
  | _ => none

def tri : ℕ → ℕ
  | 0 => 0
  | n + 1 => tri n + n + 1

-- R4 chain: (k, 0, c, d, 0) →* (0, 0, c+k, d+k, 0)
theorem r4_chain : ∀ k c d, ⟨k, 0, c, d, 0⟩ [fm]⊢* ⟨0, 0, c + k, d + k, 0⟩ := by
  intro k; induction k with
  | zero => intro c d; exists 0
  | succ k ih =>
    intro c d
    have hstep : fm ⟨k + 1, 0, c, d, 0⟩ = some ⟨k, 0, c + 1, d + 1, 0⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar hstep)
    have := ih (c + 1) (d + 1)
    rw [show c + 1 + k = c + (k + 1) from by ring,
        show d + 1 + k = d + (k + 1) from by ring] at this
    exact this

-- Drain base case c=0: (0, 0, 1, 1, e) →* (2, 0, 0, 0, e+1)
theorem drain_base_zero (e : ℕ) : ⟨0, 0, 1, 1, e⟩ [fm]⊢* ⟨2, 0, 0, 0, e + 1⟩ := by
  apply stepStar_trans (step_stepStar (show fm ⟨0, 0, 1, 1, e⟩ = some ⟨0, 2, 0, 1, e⟩ from by simp [fm]))
  apply stepStar_trans (step_stepStar (show fm ⟨0, 2, 0, 1, e⟩ = some ⟨2, 1, 1, 1, e⟩ from by simp [fm]))
  exact step_stepStar (show fm ⟨2, 1, 1, 1, e⟩ = some ⟨2, 0, 0, 0, e + 1⟩ from by simp [fm])

-- Drain base case c≥1: (0, 0, c+2, 1, e) →* (2, 0, c+1, 0, e+1)
theorem drain_base_succ (c e : ℕ) : ⟨0, 0, c + 2, 1, e⟩ [fm]⊢* ⟨2, 0, c + 1, 0, e + 1⟩ := by
  apply stepStar_trans (step_stepStar (show fm ⟨0, 0, c + 2, 1, e⟩ = some ⟨0, 2, c + 1, 1, e⟩ from by simp [fm]))
  apply stepStar_trans (step_stepStar (show fm ⟨0, 2, c + 1, 1, e⟩ = some ⟨0, 1, c, 0, e + 1⟩ from by simp [fm]))
  exact step_stepStar (show fm ⟨0, 1, c, 0, e + 1⟩ = some ⟨2, 0, c + 1, 0, e + 1⟩ from by simp [fm])

-- Unified drain base: (0, 0, c+1, 1, e) →* (2, 0, c, 0, e+1)
theorem drain_base (c e : ℕ) : ⟨0, 0, c + 1, 1, e⟩ [fm]⊢* ⟨2, 0, c, 0, e + 1⟩ := by
  rcases c with _ | c
  · exact drain_base_zero e
  · exact drain_base_succ c e

-- Drain: (0, 0, 3k+c+1, 2k+1, e) →* (2, 0, c, 0, e+2k+1)
theorem drain : ∀ k c e, ⟨0, 0, 3 * k + c + 1, 2 * k + 1, e⟩ [fm]⊢* ⟨2, 0, c, 0, e + 2 * k + 1⟩ := by
  intro k; induction k with
  | zero => intro c e; simp; exact drain_base c e
  | succ k ih =>
    intro c e
    have h1 : fm ⟨0, 0, 3 * (k + 1) + c + 1, 2 * (k + 1) + 1, e⟩ =
              some ⟨0, 2, 3 * k + c + 3, 2 * k + 3, e⟩ := by
      simp [fm]; ring_nf
    apply stepStar_trans (step_stepStar h1)
    have h2 : fm ⟨0, 2, 3 * k + c + 3, 2 * k + 3, e⟩ =
              some ⟨0, 1, 3 * k + c + 2, 2 * k + 2, e + 1⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h2)
    have h3 : fm ⟨0, 1, 3 * k + c + 2, 2 * k + 2, e + 1⟩ =
              some ⟨0, 0, 3 * k + c + 1, 2 * k + 1, e + 2⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h3)
    have := ih c (e + 2)
    rw [show e + 2 + 2 * k + 1 = e + 2 * (k + 1) + 1 from by ring] at this
    exact this

-- R3 chain: (a, k, c, 0, 0) →* (a+2k, 0, c+k, 0, 0)
theorem r3_chain : ∀ k a c, ⟨a, k, c, 0, 0⟩ [fm]⊢* ⟨a + 2 * k, 0, c + k, 0, 0⟩ := by
  intro k; induction k with
  | zero => intro a c; simp; exists 0
  | succ k ih =>
    intro a c
    have hstep : fm ⟨a, k + 1, c, 0, 0⟩ = some ⟨a + 2, k, c + 1, 0, 0⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar hstep)
    have := ih (a + 2) (c + 1)
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) from by ring,
        show c + 1 + k = c + (k + 1) from by ring] at this
    exact this

-- Build loop: (2, b, c, 0, 2j+1) →* (2, b+j, c+j, 0, 1)
theorem build_loop : ∀ j b c, ⟨2, b, c, 0, 2 * j + 1⟩ [fm]⊢* ⟨2, b + j, c + j, 0, 1⟩ := by
  intro j; induction j with
  | zero => intro b c; simp; exists 0
  | succ j ih =>
    intro b c
    have h1 : fm ⟨2, b, c, 0, 2 * (j + 1) + 1⟩ = some ⟨1, b + 1, c, 0, 2 * j + 2⟩ := by
      simp [fm]; ring_nf
    apply stepStar_trans (step_stepStar h1)
    have h2 : fm ⟨1, b + 1, c, 0, 2 * j + 2⟩ = some ⟨0, b + 2, c, 0, 2 * j + 1⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h2)
    have h3 : fm ⟨0, b + 2, c, 0, 2 * j + 1⟩ = some ⟨2, b + 1, c + 1, 0, 2 * j + 1⟩ := by simp [fm]
    apply stepStar_trans (step_stepStar h3)
    have := ih (b + 1) (c + 1)
    rw [show b + 1 + j = b + (j + 1) from by ring,
        show c + 1 + j = c + (j + 1) from by ring] at this
    exact this

-- Build finish: (2, b, c, 0, 1) →* (2b+3, 0, c+b+1, 0, 0)
theorem build_finish (b c : ℕ) : ⟨2, b, c, 0, 1⟩ [fm]⊢* ⟨2 * b + 3, 0, c + b + 1, 0, 0⟩ := by
  have h1 : fm ⟨2, b, c, 0, 1⟩ = some ⟨1, b + 1, c, 0, 0⟩ := by simp [fm]
  apply stepStar_trans (step_stepStar h1)
  have := r3_chain (b + 1) 1 c
  rw [show 1 + 2 * (b + 1) = 2 * b + 3 from by ring,
      show c + (b + 1) = c + b + 1 from by ring] at this
  exact this

-- Full build: (2, 0, c, 0, 2k+1) →* (2k+3, 0, c+2k+1, 0, 0)
theorem build (k c : ℕ) : ⟨2, 0, c, 0, 2 * k + 1⟩ [fm]⊢* ⟨2 * k + 3, 0, c + 2 * k + 1, 0, 0⟩ := by
  apply stepStar_trans (build_loop k 0 c)
  simp only [Nat.zero_add]
  have := build_finish k (c + k)
  rw [show c + k + k + 1 = c + 2 * k + 1 from by ring] at this
  exact this

-- Main transition using tri:
-- (2n+3, 0, tri(n+1), 0, 0) ⊢⁺ (2n+5, 0, tri(n+2), 0, 0)
theorem main_trans (n : ℕ) :
    ⟨2 * n + 3, 0, tri (n + 1), 0, 0⟩ [fm]⊢⁺ ⟨2 * n + 5, 0, tri (n + 2), 0, 0⟩ := by
  -- tri(n+1) = tri(n) + n + 1, tri(n+2) = tri(n+1) + n + 2
  -- a = 2n+3 = 2(n+1)+1
  -- Phase 1: R4 chain with k = 2n+3
  -- (2n+3, 0, tri(n+1), 0, 0) →* (0, 0, tri(n+1)+2n+3, 2n+3, 0)
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨0, 0, tri (n + 1) + (2 * n + 3), 2 * n + 3, 0⟩)
  · have := r4_chain (2 * n + 3) (tri (n + 1)) 0
    simp only [Nat.zero_add] at this; exact this
  -- Phase 2: Drain with k = n+1, c_drain = tri(n+1) - (n+1)
  -- Need: 3*(n+1) + c_drain + 1 = tri(n+1) + 2n+3
  -- c_drain = tri(n+1) + 2n+3 - 3n - 3 - 1 = tri(n+1) - n - 1 = tri(n)
  -- Since tri(n+1) = tri(n) + n + 1, we have tri(n+1) - n - 1 = tri(n). ✓
  -- drain(n+1, tri(n), 0): (0, 0, 3(n+1)+tri(n)+1, 2(n+1)+1, 0) →* (2, 0, tri(n), 0, 2(n+1)+1)
  -- 3(n+1)+tri(n)+1 = 3n+3+tri(n)+1 = tri(n)+3n+4
  -- And tri(n+1)+2n+3 = tri(n)+n+1+2n+3 = tri(n)+3n+4. ✓
  apply stepStar_stepPlus_stepPlus (c₂ := ⟨2, 0, tri n, 0, 2 * (n + 1) + 1⟩)
  · have hdrain := drain (n + 1) (tri n) 0
    simp only [Nat.zero_add] at hdrain
    rw [show 3 * (n + 1) + tri n + 1 = tri (n + 1) + (2 * n + 3) from by
      simp [tri]; ring] at hdrain
    exact hdrain
  -- Phase 3: Build with k = n+1
  -- (2, 0, tri(n), 0, 2(n+1)+1) →* (2(n+1)+3, 0, tri(n)+2(n+1)+1, 0, 0)
  -- = (2n+5, 0, tri(n)+2n+3, 0, 0)
  -- tri(n)+2n+3 = tri(n)+(n+1)+(n+2) = tri(n+1)+(n+2) = tri(n+2). ✓
  have hbuild := build (n + 1) (tri n)
  rw [show tri n + 2 * (n + 1) + 1 = tri (n + 2) from by simp [tri]; ring,
      show 2 * (n + 1) + 3 = 2 * n + 5 from by ring] at hbuild
  exact stepStar_stepPlus hbuild (by
    intro heq
    have : (2 : ℕ) = 2 * n + 5 := congr_arg (fun q : Q => q.1) heq
    omega)

theorem nonhalt : ¬halts fm c₀ := by
  -- c₀ = (1, 0, 0, 0, 0) →* (3, 0, 1, 0, 0) = (2*0+3, 0, tri 1, 0, 0) in 6 steps
  apply stepStar_not_halts_not_halts (c₂ := ⟨3, 0, 1, 0, 0⟩) (by execute fm 6)
  apply progress_nonhalt_simple (fm := fm) (A := ℕ)
    (fun n ↦ ⟨2 * n + 3, 0, tri (n + 1), 0, 0⟩) 0
  intro n; exact ⟨n + 1, main_trans n⟩

end Sz22_2003_unofficial_238
