import YM.QCD.Plum.Belly
import YM.QCD.RP.Yard
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Plum
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f : Side}{F:ℕ}{β:ℝ} {R:Cells.Cut c} {K:KernelChoices}
open Tide Flume YM.Next.Free Kites Acre Rails Rain Loom Fleet
variable {X:Pixel c F}{J:Patch}{w z:ℝ} {A:Set (Site c)}
variable (hp:Healing J X)(he:Continuous X)(hv:Cvol X=1)(h: Even c.val)(hN:4≤c.val)
include he
lemma sheerT (ŝ:ℝ)(hZ:∀ U,‖X U‖ ≤ ŝ)(x:Stud c F)(H:Stays x)(hx:WithinP w x): ‖Tide.fresh X x‖ ≤ ŝ*w:=by
    unfold Tide.fresh; refine (norm_integral_le_of_norm_le_const (μ:=prior su c) (C:=ŝ*w) ?_).trans (le_of_eq ?_)
    · refine ae_of_all _ fun i=>?_ ; exact (Grass.price _).trans ((norm_mul_le ..).trans (mul_le_mul (hZ i) (hx i) (norm_nonneg _) ((norm_nonneg _).trans (hZ i))))
    simp
local notation "d"=> longM J
variable {t r:ℕ}
include hp hv hN h
lemma quadrant (hY: 2^t*(r+2*d)≤c.val)(p:Site c)(x:Stud c F)(H:Fence (RP.square p fun _=>r) x)(hx:WithinP w x):∃ y:Stud c F, Stays y∧WithinP (w^((2^t)^4:ℕ)) y ∧ ‖Tide.fresh X x‖^((2^t)^4:ℕ) ≤ ‖Tide.fresh X y‖:=by
    let g (s : Finset Axis) (i : Axis) := if i∈s then 2^t*(r+2*d)-2*d else r
    have Hq (s : Finset Axis) : ∃ (q : Site c) (y : Stud c F), Fence (RP.square q (g s)) y ∧ WithinP (w^((2^t)^s.card:ℕ)) y ∧ ‖Tide.fresh X x‖^((2^t)^s.card:ℕ) ≤ ‖Tide.fresh X y‖ := by
        induction s using Finset.induction_on with
        | empty => exact ⟨p,x,by simpa [g] using H,by simpa using hx,by simp⟩
        | @insert a s h₁ ih=>
           obtain ⟨q,y,Y,hy,hQ⟩:= ih; have hi: g s a=r:=by simp [g,h₁]
           obtain ⟨u,z,Z,hz',hg⟩:= grows hp he hv h hN t q a (g s) (by simpa only [hi] using hY) y Y hy -- hY?
           rw [hi,show Function.update (g s) a (2^t*(r+2*d)-2*d)=g (insert a s) from funext fun i=> by rcases eq_or_ne i a with h|h <;> simp [g,h]] at Z; rw [card_insert_of_notMem h₁,pow_succ,pow_mul,pow_mul]; exact ⟨u,z,Z,hz', (pow_le_pow_left₀ (by positivity) hQ _).trans hg⟩
    obtain ⟨u,y,Y,hy,hh⟩:=Hq univ; exact ⟨y,Y.hp,by simpa [Axis] using hy,by simpa [Axis] using hh⟩
noncomputable def quota (P:Patch)(r:ℕ)(A:ℝ):ℝ:= Real.exp (|A| *(↑(2*(r+2*longM P)):ℝ)^4)
lemma planetary (p:Site c)(he':r+2*d ≤ c.val) (x:Stud c F)(H:Fence (RP.square p fun _=>r) x)(hx:WithinP w x)(A:ℝ)(hU:∀ U, ‖X U‖ ≤ Globe.expo A c) : ‖Tide.fresh X x‖ ≤ quota J r A * w:=by
    let Q:= r+2*d; have hQ:0<Q:=by unfold Q; change 0<r+2*(40*(J.J+3)); omega
    obtain ⟨m,hM,hk⟩:∃ m:ℕ,2^m*Q ≤ c.val ∧ c.val< 2^(m+1)*Q:=by
        let m:= Nat.log 2 (c.val / Q)
        have hp:2^m ≤ c.val / Q:=Nat.pow_log_le_self 2 (by have hv:c.val / Q ≥ 1:= (Nat.le_div_iff_mul_le hQ).2 (by simpa using he'); omega)
        refine ⟨m,(Nat.le_div_iff_mul_le hQ).1 hp,?_⟩; by_contra! he; exact Nat.not_lt_of_ge ((Nat.le_div_iff_mul_le hQ).2 he) (Nat.lt_pow_succ_log_self (by norm_num) _)
    obtain ⟨y,Y,hw,hY⟩:= quadrant hp he hv h hN hM p x H hx
    have hx':0≤ w:= hx.nonneg; apply le_of_pow_le_pow_left₀ (show ((2^m)^4:ℕ) ≠ 0 by positivity) (mul_nonneg (Real.exp_pos _).le hx'); apply (hY.trans (sheerT he _ hU y Y hw)).trans; rw [mul_pow]; apply mul_le_mul_of_nonneg_right _ (by positivity); unfold Globe.expo; rw [← Real.exp_nat_mul,Real.exp_le_exp,site_card];
    have he : (c.val:ℝ) ≤ (2:ℝ)^m * ↑(2*Q) := by rw [pow_succ, mul_assoc] at hk; exact_mod_cast hk.le
    change -(↑(c.val^4):ℝ)*A ≤ ↑((2^m)^4:ℕ)*(|A| * (↑(2*Q):ℝ)^4); have hp:= pow_le_pow_left₀ (Nat.cast_nonneg _) he 4; rw [mul_pow] at hp; push_cast at *; nlinarith only [mul_le_mul_of_nonneg_left (neg_le_abs A) (show 0≤ (c.val:ℝ)^4 by positivity),mul_le_mul_of_nonneg_right hp (abs_nonneg A)]
end YM.QCD.Plum
