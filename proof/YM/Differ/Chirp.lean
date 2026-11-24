import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
/-! Two-ended matching. Keep absolute sizes before marker amplitude, scaled weights handed out elsewhere. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bounce
-- maybe namespace used.CN.
variable (d:ℕ)
-- absolute cost above plus normalized obligations at output. finite
structure Ticket (a a' u:ℝ) : Prop where
    starts: 1 ≤ a
    leads : 1 ≤ a'
    moves : 0 < u
    bounded : u ≤ 1
    shrinks : (a^2+a) * (Real.sqrt u) ≤ 1/32
    carried : a* (Real.sqrt u) * (a'^2) ≤1/32
abbrev ε (a:ℝ) := (8*a^2)⁻¹
abbrev decayU (u:ℝ) := u^(d+1)
abbrev planU (u:ℝ) := u^d*Real.sqrt u
variable {a b p t y x d' R' u:ℝ}
local notation "εA"=> ε a
local notation "εB"=> ε b
local notation "s"=>Real.sqrt u
local notation "Q"=> decayU d u
local notation "Λ"=> planU d u
variable (he:Ticket a b u) -- notation local
include he
lemma margin :0 < ε a ∧ (1+a^2) * ε a ≤1/4 ∧ ε a ≤ 1:=by
    have h:0<a:=zero_lt_one.trans_le he.starts; have hε:0<ε a:=by unfold ε; positivity
    have h1 : (1+a^2) * ε a ≤1/4:=by unfold ε; rw [← div_eq_mul_inv]; field_simp; nlinarith only [one_le_pow₀ he.starts (n:=2)] -- names
    exact ⟨hε,h1, (le_mul_of_one_le_left hε.le (le_add_of_nonneg_right (sq_nonneg _))|>.trans (h1.trans (by norm_num)))⟩
lemma gain : Q= Λ*s:=by unfold decayU planU; rw [mul_assoc,Real.mul_self_sqrt he.moves.le,pow_succ]
-- use also across.Pre.Events.Match two ended recurrence
variable (hy:0≤ y)(hP:0≤ t) (hp:p ≤ a*(x+decayU d u*t))(hq:u^d*y ≤ p) (hM : R'= a*(p+decayU d u*t) + x)(hN:0 ≤ R')(hX:x ≤ ε a*R')
include hp hP hM hX hN
lemma release_fee {v:ℝ}(hv:t ≤ v) : a*(p+Q*v)+x ≤ (1/2:ℝ)*Λ*v:=by
    have ha:0<a:=zero_lt_one.trans_le he.starts; have h0:0<u:=he.moves; have h :0<Λ:=mul_pos (pow_pos h0 d) (Real.sqrt_pos.mpr h0); have hp0:= he.shrinks; have hε:=(margin he).2.1
    have hγ(v:ℝ)(hp:0 ≤ v):(a^2+a)*(Q*v) ≤ 1/32*(Λ*v):=by rw [gain d he]; linarith only [mul_le_mul_of_nonneg_right hp0 (mul_nonneg h.le hp)]
    have hL(v:ℝ)(hx:t≤v) : a*(p+Q*v)+x ≤ (1+a^2)*x+(a^2+a)*(Q*v):=by nlinarith only [mul_le_mul_of_nonneg_left (hp.trans (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hx (pow_nonneg h0.le _)) _) ha.le)) ha.le] -- rw priority
    have hY:(1+a^2)*x ≤ 1/4*R':= (mul_le_mul_of_nonneg_left hX (by positivity : 0≤1+a^2)).trans ((mul_assoc ..).ge.trans (mul_le_mul_of_nonneg_right hε hN)) -- actually (1+a)* eps*R' assoc, check
    have hF:R' ≤ 1/4*Λ*t:= by nlinarith only [hγ t hP,hY,hL t le_rfl,hM,mul_nonneg h.le hP]
    have hV:=mul_le_mul_of_nonneg_left hv h.le; nlinarith only [hγ v (hP.trans hv),hY,hV,hL v hv,hF,mul_nonneg h.le hP]
include hq
lemma ascends : R' ≤ Λ*t ∧ y ≤ ε b*t:=by
    have ha:0<a:= zero_lt_one.trans_le he.starts; have hb:0<b:= zero_lt_one.trans_le he.leads; have h0:0<u:= he.moves
    have hγ:0<Λ:= mul_pos (pow_pos h0 d) (Real.sqrt_pos.mpr h0); have hΘ:R' ≤ Λ*t:= by have hx:= release_fee d he hP hp hM hN hX (le_refl t); rw [hM]; exact hx.trans (show 1/2*Λ*t ≤ Λ*t from by nlinarith only [mul_nonneg hγ.le hP]) -- sig
    refine ⟨hΘ,?_⟩; have hh:x ≤ Λ*t:= hX.trans ((mul_le_of_le_one_left hN (margin he).2.2).trans hΘ)
    have hk:Q≤ Λ:=by rw [gain d he]; exact mul_le_of_le_one_right hγ.le (Real.sqrt_le_one.mpr he.bounded)
    have hV: p ≤ a*(Λ*t+Λ*t):=hp.trans (mul_le_mul_of_nonneg_left (add_le_add hh (mul_le_mul_of_nonneg_right hk hP)) ha.le)
    have ht:y ≤ 2*a*s*t:=by apply le_of_mul_le_mul_left _ (pow_pos h0 d); exact (hq.trans hV).trans_eq (by unfold planU; ring)
    apply ht.trans; refine mul_le_mul_of_nonneg_right ?_ hP; unfold ε; rw [← one_div]; apply (le_div_iff₀ (by positivity)).2
    nlinarith only [he.carried]
omit he hp hP hN hM hq hX
variable {n l k:ℕ} (a u p R y:ℕ→ℝ)
local notation "Rt"=> R
noncomputable abbrev wages (a u:ℕ→ℝ)(d k:ℕ)(p T:ℝ):= a k*(p+decayU d (u k)*T)
structure Tracer (m N:ℕ) :Prop where
  up (i:ℕ):m ≤ i→ i < N→ Ticket (a i) (a (i+1)) (u i)
  tall(i):m ≤ i→i ≤ N→ 0 ≤ R i
  base : y m=0
  reads(i):m ≤ i→ i < N→ (u i)^d*y (i+1) ≤ p i
  learns(i):m ≤ i→ i < N→ p i ≤ a i*(y i+decayU d (u i)*R (i+1))
  promises(i):m ≤ i→ i < N→ R i= wages a u d i (p i) (R (i+1))+y i
variable (A:Tracer d a u p R y l n)
include A
lemma lowR (h:l ≤ k)(hv:k≤ n)(ht:1≤ a l): y k ≤ ε (a k)*R k :=by
    induction k,h using Nat.le_induction with
    | base=> rw [A.base]; exact mul_nonneg (by have hp:0<a l:=zero_lt_one.trans_le ht; unfold ε; positivity) (A.tall _ le_rfl hv)
    | succ i hi ih=>
       exact (ascends d (A.up i hi hv) (A.tall (i+1) (Nat.le_step hi) hv) (A.learns i hi hv) (A.reads i hi hv) (A.promises i hi hv) (A.tall i hi (by omega)) (ih (by omega))).2
lemma budgetR (T:ℕ→ℝ)(hP: R n≤ T n)(hk:∀ i,l ≤ i→ i < n→ T i=planU d (u i)*T (i+1))(h:l ≤ k)(he:k ≤ n)(ht:1≤ a l):R k≤ T k:=by
     induction he using Nat.decreasingInduction with|self=>exact hP|of_succ i hv ih=>
       exact (ascends d (A.up i h hv) (A.tall (i+1) (Nat.le_step h) hv) (A.learns i h hv) (A.reads i h hv) (A.promises i h hv) (A.tall i h hv.le) (lowR d a u p R y A h hv.le ht)).1.trans ((mul_le_mul_of_nonneg_left (ih (Nat.le_step h)) (mul_nonneg (pow_nonneg (A.up i h hv).moves.le _) (Real.sqrt_nonneg _))).trans_eq (hk i h hv).symm)
end YM.Bounce
#print axioms YM.Bounce.budgetR
