import BBfLean.FM
import Mathlib.Tactic.Ring

/-!
# sz22_2003_unofficial #430: [27/35, 1/33, 25/3, 22/25, 21/2]

Vector representation:
```
 0  3 -1 -1  0
 0 -1  0  0 -1
 0 -1  2  0  0
 1  0 -2  0  1
-1  1  0  1  0
```

Canonical states are (hydra_a(n) + hydra_b(n), 0, 0, 0, hydra_a(n) - 1).
The FM halts when hydra_b = -1 via the R5+R2 loop exhausting the a-register.

Author: Claude Opus 4.6
-/

namespace Sz22_2003_unofficial_430

def Q := ℕ × ℕ × ℕ × ℕ × ℕ
def c₀ : Q := ⟨1, 0, 0, 0, 0⟩
def fm : Q → Option Q := fun q ↦ match q with
  | ⟨a, b, c+1, d+1, e⟩ => some ⟨a, b+3, c, d, e⟩
  | ⟨a, b+1, c, d, e+1⟩ => some ⟨a, b, c, d, e⟩
  | ⟨a, b+1, c, d, e⟩ => some ⟨a, b, c+2, d, e⟩
  | ⟨a, b, c+2, d, e⟩ => some ⟨a+1, b, c, d, e+1⟩
  | ⟨a+1, b, c, d, e⟩ => some ⟨a, b+1, c, d+1, e⟩
  | _ => none

def prop_hydra :=
  ∀ (a : ℕ → ℕ) (b : ℕ → ℤ)
  (_a_ini : a 0 = 1)
  (_a_rec : ∀ n, a (n + 1) = if a n % 2 = 0 then 5 * (a n / 2) + 2 else 5 * (a n / 2))
  (_b_ini : b 0 = 0)
  (_b_rec : ∀ n, b (n + 1) = if a n % 2 = 0 then b n - 1 else b n + 2),
  ∀ n, b n ≥ 0

def hydra_a : ℕ → ℕ
  | 0 => 1
  | n+1 => if hydra_a n % 2 = 0 then 5 * (hydra_a n / 2) + 2 else 5 * (hydra_a n / 2)

def hydra_b : ℕ → ℤ
  | 0 => 0
  | n+1 => if hydra_a n % 2 = 0 then hydra_b n - 1 else hydra_b n + 2

-- ============================================================
-- Phase lemmas
-- ============================================================

-- R5+R2 loop: each step does a--, d++, e--
theorem r5r2_loop : ∀ c, ∀ a d, ⟨a+c, 0, 0, d, c⟩ [fm]⊢* ⟨a, 0, 0, d+c, 0⟩ := by
  intro c; induction' c with c ih <;> intro a d
  · ring_nf; finish
  · rw [show a + (c + 1) = (a + c) + 1 from by ring]
    step fm; step fm
    apply stepStar_trans (ih a (d + 1))
    ring_nf; finish

-- R1R1R3 even interleaving: (a, b, 2, 2*(K+1), 0) →* (a, b+5*(K+1)+1, 0, 0, 0)
theorem r1r1r3_even : ∀ K, ∀ a b, ⟨a, b, 2, 2*(K+1), 0⟩ [fm]⊢* ⟨a, b+5*(K+1)+1, 0, 0, 0⟩ := by
  intro K; induction' K with K ih <;> intro a b
  · step fm; step fm; ring_nf; finish
  · rw [show 2 * (K + 1 + 1) = 2 * (K + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a (b + 5))
    ring_nf; finish

-- R1R1R3 odd interleaving: (a, b, 2, 2*K+1, 0) →* (a, b+5*K+3, 1, 0, 0)
theorem r1r1r3_odd : ∀ K, ∀ a b, ⟨a, b, 2, 2*K+1, 0⟩ [fm]⊢* ⟨a, b+5*K+3, 1, 0, 0⟩ := by
  intro K; induction' K with K ih <;> intro a b
  · step fm; ring_nf; finish
  · rw [show 2 * (K + 1) + 1 = (2 * K + 1) + 2 from by ring]
    step fm; step fm; step fm
    apply stepStar_trans (ih a (b + 5))
    ring_nf; finish

-- R3 drain: b → c
theorem r3_drain : ∀ b, ∀ a c, ⟨a, b, c, 0, 0⟩ [fm]⊢* ⟨a, 0, c+2*b, 0, 0⟩ := by
  intro b; induction' b with b ih <;> intro a c
  · ring_nf; finish
  · step fm; apply stepStar_trans (ih a (c + 2)); ring_nf; finish

-- R4 drain even: c → a, e
theorem r4_drain : ∀ k, ∀ a e, ⟨a, 0, 2*k, 0, e⟩ [fm]⊢* ⟨a+k, 0, 0, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · ring_nf; finish
  · rw [show 2 * (k + 1) = 2 * k + 2 from by ring]
    step fm; apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

-- R4 drain odd: c → a, e (leaving c=1)
theorem r4_drain_odd : ∀ k, ∀ a e, ⟨a, 0, 2*k+1, 0, e⟩ [fm]⊢* ⟨a+k, 0, 1, 0, e+k⟩ := by
  intro k; induction' k with k ih <;> intro a e
  · ring_nf; finish
  · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring]
    step fm; apply stepStar_trans (ih (a + 1) (e + 1)); ring_nf; finish

-- Odd cleanup: R5, R1, R2×4
theorem odd_cleanup : ∀ a e, ⟨a+1, 0, 1, 0, e+4⟩ [fm]⊢* ⟨a, 0, 0, 0, e⟩ := by
  intro a e; step fm; step fm; step fm; step fm; step fm; step fm; finish

-- ============================================================
-- Clean wrappers
-- ============================================================

theorem r1r1r3_even0 : ∀ K a, ⟨a, 0, 2, 2*(K+1), 0⟩ [fm]⊢* ⟨a, 5*(K+1)+1, 0, 0, 0⟩ := by
  intro K a; have h := r1r1r3_even K a 0; simp only [Nat.zero_add] at h; exact h

theorem r1r1r3_odd0 : ∀ K a, ⟨a, 0, 2, 2*K+1, 0⟩ [fm]⊢* ⟨a, 5*K+3, 1, 0, 0⟩ := by
  intro K a; have h := r1r1r3_odd K a 0; simp only [Nat.zero_add] at h; exact h

theorem r3_drain0 : ∀ b a, ⟨a, b, 0, 0, 0⟩ [fm]⊢* ⟨a, 0, 2*b, 0, 0⟩ := by
  intro b a; have h := r3_drain b a 0; simp only [Nat.zero_add] at h; exact h

theorem r4_drain0 : ∀ k a, ⟨a, 0, 2*k, 0, 0⟩ [fm]⊢* ⟨a+k, 0, 0, 0, k⟩ := by
  intro k a; have h := r4_drain k a 0; simp only [Nat.zero_add] at h; exact h

theorem r4_drain_odd0 : ∀ k a, ⟨a, 0, 2*k+1, 0, 0⟩ [fm]⊢* ⟨a+k, 0, 1, 0, k⟩ := by
  intro k a; have h := r4_drain_odd k a 0; simp only [Nat.zero_add] at h; exact h

theorem r5r2_loop0 : ∀ c, ⟨c, 0, 0, 0, c⟩ [fm]⊢* ⟨0, 0, 0, c, 0⟩ := by
  intro c; have h := r5r2_loop c 0 0; simp only [Nat.zero_add] at h; exact h

-- ============================================================
-- Round lemmas
-- ============================================================

-- Even round: hydra_a = 2(K+1), e = 2K+1, a-register = B + 2K + 2
theorem round_even : ∀ K B, ⟨B+2*K+2, 0, 0, 0, 2*K+1⟩ [fm]⊢* ⟨B+5*K+6, 0, 0, 0, 5*K+6⟩ := by
  intro K B
  -- Phase 1: R5+R2 loop (2K+1 steps)
  rw [show B + 2 * K + 2 = (B + 1) + (2 * K + 1) from by ring]
  apply stepStar_trans (r5r2_loop (2*K+1) (B+1) 0)
  -- State: (B+1, 0, 0, 2K+1, 0)
  -- Phase 2: R5+R3
  simp only [Nat.zero_add]
  step fm; step fm
  -- State: (B, 0, 2, 2K+2, 0)
  rw [show 2 * K + 2 = 2 * (K + 1) from by ring]
  -- Phase 3: R1R1R3 even interleaving
  apply stepStar_trans (r1r1r3_even0 K B)
  -- Phase 4: R3 drain
  apply stepStar_trans (r3_drain0 (5*(K+1)+1) B)
  -- Phase 5: R4 drain even
  rw [show 2 * (5 * (K + 1) + 1) = 2 * (5 * K + 6) from by ring]
  apply stepStar_trans (r4_drain0 (5*K+6) B)
  ring_nf; finish

-- Odd round: hydra_a = 2K+1, e = 2K, a-register = B + 2K + 1, K ≥ 1
theorem round_odd : ∀ K, K ≥ 1 → ∀ B, ⟨B+2*K+1, 0, 0, 0, 2*K⟩ [fm]⊢* ⟨B+5*K+2, 0, 0, 0, 5*K-1⟩ := by
  intro K hK B
  -- Phase 1: R5+R2 loop (2K steps)
  rw [show B + 2 * K + 1 = (B + 1) + 2 * K from by ring]
  apply stepStar_trans (r5r2_loop (2*K) (B+1) 0)
  -- Phase 2: R5+R3
  simp only [Nat.zero_add]
  step fm; step fm
  -- Phase 3: R1R1R3 odd interleaving
  apply stepStar_trans (r1r1r3_odd0 K B)
  -- Phase 4: R3 drain (from (B, 5K+3, 1, 0, 0))
  apply stepStar_trans (r3_drain (5*K+3) B 1)
  -- Phase 5: R4 drain odd
  rw [show 1 + 2 * (5 * K + 3) = 2 * (5 * K + 3) + 1 from by ring]
  apply stepStar_trans (r4_drain_odd0 (5*K+3) B)
  -- Phase 6: Odd cleanup
  rw [show B + (5 * K + 3) = (B + 5 * K + 2) + 1 from by omega,
      show (5 * K + 3 : ℕ) = (5 * K - 1) + 4 from by omega]
  exact odd_cleanup (B + 5 * K + 2) (5 * K - 1)

-- ============================================================
-- Connecting FM to hydra sequences
-- ============================================================

theorem bootstrap : c₀ [fm]⊢* ⟨3, 0, 0, 0, 1⟩ := by execute fm 16

theorem halted_state : ∀ d, halted fm ⟨0, 0, 0, d, 0⟩ := by intro d; rfl

-- ============================================================
-- Helpers for the main theorem
-- ============================================================

private theorem unique_a (a : ℕ → ℕ) (ha0 : a 0 = 1)
    (ha : ∀ n, a (n + 1) = if a n % 2 = 0 then 5 * (a n / 2) + 2 else 5 * (a n / 2)) :
    ∀ n, a n = hydra_a n := by
  intro n; induction n with
  | zero => simp [hydra_a, ha0]
  | succ n ih => simp [ha, hydra_a, ih]

private theorem unique_b (a : ℕ → ℕ) (b : ℕ → ℤ) (ha0 : a 0 = 1)
    (ha : ∀ n, a (n + 1) = if a n % 2 = 0 then 5 * (a n / 2) + 2 else 5 * (a n / 2))
    (hb0 : b 0 = 0)
    (hb : ∀ n, b (n + 1) = if a n % 2 = 0 then b n - 1 else b n + 2) :
    ∀ n, b n = hydra_b n := by
  intro n; induction n with
  | zero => simp [hydra_b, hb0]
  | succ n ih => simp [hb, hydra_b, unique_a a ha0 ha n, ih]

private theorem prop_hydra_iff : prop_hydra ↔ ∀ n, hydra_b n ≥ 0 := by
  constructor
  · intro h n
    exact h hydra_a hydra_b rfl (fun n => by simp [hydra_a]) rfl (fun n => by simp [hydra_b]) n
  · intro h a b ha0 ha hb0 hb n
    rw [unique_b a b ha0 ha hb0 hb n]; exact h n

private theorem hydra_a_ge_2 (n : ℕ) (hn : n ≥ 2) : hydra_a n ≥ 2 := by
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [hydra_a]
    split
    · omega
    · cases m with
      | zero => omega
      | succ k =>
        cases k with
        | zero => simp [hydra_a] at *
        | succ k => have := ih (by omega); omega

private theorem hydra_b_step (n : ℕ) :
    hydra_b (n + 1) = if hydra_a n % 2 = 0 then hydra_b n - 1 else hydra_b n + 2 := by rfl

private theorem hydra_a_step (n : ℕ) :
    hydra_a (n + 1) = if hydra_a n % 2 = 0 then 5 * (hydra_a n / 2) + 2 else 5 * (hydra_a n / 2) := by rfl

private theorem canonical_round (n : ℕ) (hbn : hydra_b (n + 2) ≥ 0)
    (hbn1 : hydra_b (n + 3) ≥ 0) :
    (⟨hydra_a (n + 2) + (hydra_b (n + 2)).toNat, 0, 0, 0, hydra_a (n + 2) - 1⟩ : Q)
    [fm]⊢* ⟨hydra_a (n + 3) + (hydra_b (n + 3)).toNat, 0, 0, 0, hydra_a (n + 3) - 1⟩ := by
  have ha2 := hydra_a_ge_2 (n + 2) (by omega)
  by_cases hpar : hydra_a (n + 2) % 2 = 0
  · -- Even case: hydra_a(n+2) = 2K, K = hydra_a(n+2)/2
    have hKpos : hydra_a (n + 2) / 2 ≥ 1 := by omega
    have he : hydra_a (n + 2) - 1 = 2 * (hydra_a (n + 2) / 2 - 1) + 1 := by omega
    have ha3 : hydra_a (n + 3) = 5 * (hydra_a (n + 2) / 2) + 2 := by
      rw [hydra_a_step]; rw [if_pos hpar]
    have hb3 : hydra_b (n + 3) = hydra_b (n + 2) - 1 := by
      rw [hydra_b_step]; rw [if_pos hpar]
    have hb3nat : (hydra_b (n + 3)).toNat = (hydra_b (n + 2)).toNat - 1 := by
      rw [hb3]; omega
    rw [he, ha3, hb3nat]
    -- LHS a-reg: hydra_a(n+2) + hydra_b(n+2).toNat = 2K + B
    -- round_even needs B + 2K + 2 form, where K' = K - 1
    -- a-reg = hydra_a(n+2) + B = 2K + B = B + 2*(K-1) + 2
    -- RHS a-reg: (5K+2) + (B-1) = B + 5K + 1 = B + 5*(K-1) + 6
    rw [show hydra_a (n + 2) + (hydra_b (n + 2)).toNat =
        (hydra_b (n + 2)).toNat + 2 * (hydra_a (n + 2) / 2 - 1) + 2 from by omega]
    rw [show 5 * (hydra_a (n + 2) / 2) + 2 + ((hydra_b (n + 2)).toNat - 1) =
        (hydra_b (n + 2)).toNat + 5 * (hydra_a (n + 2) / 2 - 1) + 6 from by omega]
    rw [show 5 * (hydra_a (n + 2) / 2) + 2 - 1 =
        5 * (hydra_a (n + 2) / 2 - 1) + 6 from by omega]
    exact round_even (hydra_a (n + 2) / 2 - 1) ((hydra_b (n + 2)).toNat)
  · -- Odd case: hydra_a(n+2) = 2K+1, K = hydra_a(n+2)/2
    have hKpos : hydra_a (n + 2) / 2 ≥ 1 := by omega
    have he : hydra_a (n + 2) - 1 = 2 * (hydra_a (n + 2) / 2) := by omega
    have ha3 : hydra_a (n + 3) = 5 * (hydra_a (n + 2) / 2) := by
      rw [hydra_a_step]; rw [if_neg hpar]
    have hb3 : hydra_b (n + 3) = hydra_b (n + 2) + 2 := by
      rw [hydra_b_step]; rw [if_neg hpar]
    have hb3nat : (hydra_b (n + 3)).toNat = (hydra_b (n + 2)).toNat + 2 := by
      rw [hb3]; omega
    rw [he, ha3, hb3nat]
    rw [show hydra_a (n + 2) + (hydra_b (n + 2)).toNat =
        (hydra_b (n + 2)).toNat + 2 * (hydra_a (n + 2) / 2) + 1 from by omega]
    rw [show 5 * (hydra_a (n + 2) / 2) + ((hydra_b (n + 2)).toNat + 2) =
        (hydra_b (n + 2)).toNat + 5 * (hydra_a (n + 2) / 2) + 2 from by omega]
    rw [show 5 * (hydra_a (n + 2) / 2) - 1 = 5 * (hydra_a (n + 2) / 2) - 1 from rfl]
    exact round_odd (hydra_a (n + 2) / 2) (by omega) ((hydra_b (n + 2)).toNat)

private theorem canonical_ne (n : ℕ) :
    (⟨hydra_a (n + 2) + (hydra_b (n + 2)).toNat, 0, 0, 0, hydra_a (n + 2) - 1⟩ : Q) ≠
    ⟨hydra_a (n + 3) + (hydra_b (n + 3)).toNat, 0, 0, 0, hydra_a (n + 3) - 1⟩ := by
  have ha2 := hydra_a_ge_2 (n + 2) (by omega)
  by_cases hpar : hydra_a (n + 2) % 2 = 0
  · have ha3 : hydra_a (n + 3) = 5 * (hydra_a (n + 2) / 2) + 2 := by
      rw [hydra_a_step]; rw [if_pos hpar]
    intro h; simp only [Prod.mk.injEq] at h; omega
  · have ha3 : hydra_a (n + 3) = 5 * (hydra_a (n + 2) / 2) := by
      rw [hydra_a_step]; rw [if_neg hpar]
    intro h; simp only [Prod.mk.injEq] at h; omega

private theorem reach_canonical (n : ℕ) (hb : ∀ k, k ≤ n + 2 → hydra_b k ≥ 0) :
    (⟨3, 0, 0, 0, 1⟩ : Q) [fm]⊢*
    ⟨hydra_a (n + 2) + (hydra_b (n + 2)).toNat, 0, 0, 0, hydra_a (n + 2) - 1⟩ := by
  induction n with
  | zero =>
    have hb2 : hydra_b 2 = 1 := by decide
    have ha2 : hydra_a 2 = 2 := by decide
    rw [ha2, hb2]; finish
  | succ n ih =>
    have hb' : ∀ k, k ≤ n + 2 → hydra_b k ≥ 0 := fun k hk => hb k (by omega)
    apply stepStar_trans (ih hb')
    exact canonical_round n (hb (n + 2) (by omega)) (hb (n + 3) (by omega))

private theorem first_neg_is_even (n : ℕ)
    (hbprev : hydra_b n ≥ 0)
    (hbneg : hydra_b (n + 1) < 0) :
    hydra_a n % 2 = 0 ∧ hydra_b n = 0 := by
  rw [hydra_b_step] at hbneg
  split_ifs at hbneg with h
  · exact ⟨h, by omega⟩
  · omega

-- When hydra_b = 0 and even step, the FM halts after reaching the next canonical state
private theorem even_halts (K : ℕ) :
    halts fm (⟨2 * (K + 1), 0, 0, 0, 2 * K + 1⟩ : Q) := by
  rw [show 2 * (K + 1) = 0 + 2 * K + 2 from by ring]
  apply stepStar_halts (round_even K 0)
  simp only [Nat.zero_add]
  exact stepStar_halts (r5r2_loop0 (5 * K + 6)) (halted_halts (halted_state _))

-- ============================================================
-- Main theorem
-- ============================================================

theorem nonhalt_iff_hydra : ¬halts fm c₀ ↔ prop_hydra := by
  rw [prop_hydra_iff]
  constructor
  · -- Forward: ¬halts → ∀ n, hydra_b n ≥ 0
    intro hnh n
    by_contra hlt
    push_neg at hlt
    apply hnh
    have hexists : ∃ m, hydra_b m < 0 := ⟨n, hlt⟩
    set m := Nat.find hexists with hm_def
    have hmneg : hydra_b m < 0 := Nat.find_spec hexists
    have hmin : ∀ k, k < m → ¬(hydra_b k < 0) := fun k hk => Nat.find_min hexists hk
    have hball : ∀ k, k < m → hydra_b k ≥ 0 := by
      intro k hk; exact Int.not_lt.mp (hmin k hk)
    have hm2 : m ≥ 2 := by
      rcases m with _ | _ | m
      · simp [hydra_b] at hmneg
      · simp [hydra_b, hydra_a] at hmneg
      · omega
    have hbm1 : hydra_b (m - 1) ≥ 0 := hball (m - 1) (by omega)
    have hm_eq : (m - 1) + 1 = m := by omega
    have ⟨heven, hb0⟩ := first_neg_is_even (m - 1) hbm1 (by rw [hm_eq]; exact hmneg)
    have hm4 : m ≥ 4 := by
      rcases m with _ | _ | _ | _ | m
      · omega
      · omega
      · simp [hydra_b, hydra_a] at hb0
      · simp [hydra_b, hydra_a] at hb0
      · omega
    have ha_ge2 : hydra_a (m - 1) ≥ 2 := hydra_a_ge_2 (m - 1) (by omega)
    have hK : hydra_a (m - 1) - 1 = 2 * (hydra_a (m - 1) / 2 - 1) + 1 := by omega
    have hreach := reach_canonical (m - 3) (fun k hk => hball k (by omega))
    rw [show m - 3 + 2 = m - 1 from by omega] at hreach
    rw [show (hydra_b (m - 1)).toNat = 0 from by omega] at hreach
    rw [show hydra_a (m - 1) + 0 = 2 * (hydra_a (m - 1) / 2) from by omega] at hreach
    rw [show 2 * (hydra_a (m - 1) / 2) = 2 * (hydra_a (m - 1) / 2 - 1 + 1) from by omega] at hreach
    rw [hK] at hreach
    exact stepStar_halts (stepStar_trans bootstrap hreach)
      (even_halts (hydra_a (m - 1) / 2 - 1))
  · -- Backward: ∀ n, hydra_b n ≥ 0 → ¬halts
    intro hb
    apply stepStar_not_halts_not_halts bootstrap
    apply progress_nonhalt_simple (fm := fm) (A := ℕ)
      (fun n => (⟨hydra_a (n + 2) + (hydra_b (n + 2)).toNat, 0, 0, 0, hydra_a (n + 2) - 1⟩ : Q)) 0
    intro n
    exact ⟨n + 1, stepStar_stepPlus (canonical_round n (hb (n + 2)) (hb (n + 3))) (canonical_ne n)⟩

end Sz22_2003_unofficial_430
