import YM.QCD.High.Prima
/-!
# Deterministic wrapping expansions at a fixed budget point
Uses finite equal distribution of minimum-cost pollen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.High
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar
variable {ι β:Type}
-- Scale/add proof. Weaken conditional for E heads. exact HASpanic.
variable {ι' μ:Type}
open Finch Calm Stem Push.BetaTransport Ring0 Jets.Touch Collection WilsonStartup
variable (b:Flavor N){G:Gem c N ι} {Y:Ruby.Hue c N β}{K:PathData su}{O:Clip}{W: St c}
namespace PrismT
local notation "S0"=>EvenA c N
open Stew.Project
noncomputable abbrev flash (B:ℕ)(c:Side):= Φ B (-7/4) c
lemma flash_top (B:ℕ): Tendsto (flash B) atTop (𝓝 0):=by
    have h:=Lunar.shine B (show 0< (7/4:ℝ) from (by norm_num)) 0 1 zero_le_one; simp only [pow_zero,mul_one] at h; convert! h using 1; funext i; unfold flash Φ; ring_nf
lemma coatP (p:BudgetPoint)(w:ℝ):∀ᶠ c:Side in atTop, flash p.B c*w ≤ shrugs p.B c:=by
    let g c':=Φ p.B (-(1/8:ℝ)) c'; have hp:Tendsto g atTop (𝓝 0):=by simpa only [pow_zero,mul_one] using Lunar.shine p.B (show 0<(1/8:ℝ) from by norm_num) 0 1 zero_le_one
    have ht := hp.mul_const w; rw [zero_mul] at ht; filter_upwards [ht.eventually_le_const (by norm_num : (0:ℝ)<1)] with c hx; rw [show flash p.B c=shrugs p.B c*g c from ?_,mul_assoc]; swap; · unfold flash Φ shrugs g; rw [←Real.exp_add]; congr 1; ring
    exact mul_le_of_le_one_right (Real.exp_pos _).le hx
lemma dime (c:Side)(N:ℕ): (Fintype.card (Keys c N):ℝ)= (c.val:ℝ)^4*(24*N):=by unfold Keys Pairs Modes Lat.Row Lat.Fiber; simp [Pinor,Hue,Flavor,site_card]; ring -- test
lemma crownT (B N:ℕ):∀ᶠ c:Side in atTop,∀ v:ℝ,0 ≤ v→ |v^2-1| ≤ flash B c*8→ Steep c N v:=by
    have hh:= Lunar.shine B (show 0 < (7/4:ℝ) from by norm_num) 4 ((8:ℝ)*(24*N)) (by positivity)
    filter_upwards [hh.eventually_le_const (by norm_num : 0 < (1/8:ℝ))] with c hx v hv hP
    let z:= flash B c; have hp:v≤ 1+ z*8:= by
        by_cases h:v≤1; · exact h.trans (by have hZ:0< z:=Real.exp_pos _; linarith only [hZ])
        have he:1 ≤ v:=le_of_not_ge h|>.trans (le_refl _); linarith only [le_self_pow₀ he (show 2 ≠0 by omega), (abs_le.mp hP).2]
    -- note graph notation problems
    let x:=Fintype.card (Keys c N);
    apply le_trans (show _≤ (Real.exp (z*8))^x from pow_le_pow_left₀ (hv.trans (le_max_right ..)) (max_le (Real.one_le_exp (mul_nonneg (Real.exp_pos _).le (by positivity))) (hp.trans ((add_comm ..).trans_le (Real.add_one_le_exp _)))) x); rw [← Real.exp_nat_mul]; apply Real.exp_monotone; rw [show (x:ℝ)= (c.val:ℝ)^4*(24*N) from dime ..]; rw [show Φ B (-(7 / 4:ℝ)) c=z from by unfold z flash Φ; ring_nf] at hx; linarith only [hx]
variable {α P₀ U v s L' q₀ M t' :ℝ}
lemma tuneH (hV:1/4 ≤ P₀)(he:|U|≤ w)(hv:|s|≤a)(hh:|v|≤a)(ha:a ≤1/64)(hU:|q₀|≤2):∃ (r f:ℝ), 0<r∧r≤2∧r^2*(P₀+s)= P₀ ∧r^2*(U+q₀+v)=U+f∧ |r^2-1|≤a*8 ∧ |r^2*q₀-f|≤ a*(8*w+4) ∧|q₀-f|≤a*(20+8*w):=by
    let n:= P₀+s; have hx':1/8 ≤ n:=by unfold n; linarith only [hV,(abs_le.mp hv).1,ha]
    have hK:0<P₀:=(by linarith); have ht:0<n:=(by linarith); let r:= Real.sqrt (P₀/n); let f:=r^2*(U+q₀+v)- U; have hr:0<r:=Real.sqrt_pos.mpr (div_pos hK ht); have hR :r^2*n=P₀:=by unfold r; rw [Real.sq_sqrt (div_pos hK ht).le, div_mul_cancel₀ _ ht.ne']
    have hp: |r^2-1| ≤ a*8:=by
        have hg: |r^2-1| *n≤a:=by rw [← abs_of_pos ht, ←abs_mul, sub_mul,hR,one_mul, show P₀-n= -s from (by unfold n; ring),abs_neg]; exact hv
        linarith only [hg,mul_le_mul_of_nonneg_left hx' (abs_nonneg (r^2-1))]
    have hw:r ≤ 2:=by nlinarith only [hr,(abs_le.mp hp).2,ha]
    have hQ: |r^2*q₀-f|≤ a*(8*w+4):=by
          rw [show r^2*q₀-f= - ((r^2-1)*U+r^2*v) from (by unfold f;ring),abs_neg]; refine (abs_add_le ..).trans ?_; rw [abs_mul,abs_mul, abs_sq]; have hA:0 ≤ a:= (abs_nonneg _).trans hv; linarith only [mul_le_mul hp he (abs_nonneg _) (mul_nonneg hA (by positivity)),mul_le_mul (pow_le_pow_left₀ hr.le hw 2) hh (abs_nonneg _) (by positivity)] -- last linarith only
    refine ⟨r,f,hr,hw,hR,(by unfold f; abel),hp,hQ,?_⟩; nth_rw 1 [show q₀-f=(r^2*q₀-f)-(r^2-1)*q₀ from (by ring)]; apply (abs_sub ..).trans; rw [abs_mul]; linarith only [mul_le_mul hp hU (abs_nonneg _) (show 0≤ a*8 from (abs_nonneg _).trans hp),hQ]
lemma forceζ (h:ForceMass U t v (2*a))(hp:0<a)(hz:|v-s|<a):ForceMass U t s a:=by
    obtain ⟨h1,h2⟩:= abs_lt.mp hz; exact ⟨fun hx=>by linarith [h.1 hx],fun hx=>by linarith [h.2 hx]⟩
end PrismT
end YM.QCD.High
