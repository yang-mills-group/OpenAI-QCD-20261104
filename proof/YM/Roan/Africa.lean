import YM.Roan.Ode
import YM.Roan.Croft
import YM.Roan.Wire
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.TableT Tawny.Pane Tawny.BendR
open Oriole Counting Counting.Click PCAC Patria.Gall.Seals Patria.Gall
-- incomes cost norm.S
local notation "Z"=> RawVec 10
variable (u a α ε L Q A₂ M B C D θ e:ℝ)
variable {n:ℕ}(p:ℕ→Z)(Pt:ℕ→BudgetPoint)(A V:ℕ→ℝ)(W:Axis→ℕ→ℝ)
variable (hP : Pan n p Pt W A V u α a ε)
local notation "Hℓ" z:arg => (L*z)
local notation "F₀"=> (Fintype.card (Rings 10):ℝ)
-- supersed stage.V Costs. Hype L = d^4 or d^5. β budgets polynomial choose later.
local notation "Y" x:arg=> (L*a)
local notation "φ" L:arg=> ((L*F₀)*(α*u^8))
local notation "δ" L:arg=> (L*F₀*(2*ε))
local notation "τ" L:arg=> (B+2*(L*a+1)*M)
local notation "∆e" L:arg=> (δ L * τ L + θ*M)
local notation "ΦL" L:arg n:arg=> (B+n*(∆e L)) -- n real
local notation "ψω" L:arg n:arg=> (φ L*(ΦL L n)+δ L*(τ L))
local notation "Φ" L:arg => δ L * τ L
local notation "Ω" L:arg=> φ L * (Φ L)+ δ L * τ L+ θ*M
structure FundX (n:ℕ):Prop where
       m_ng: 0 < M
       e_ng: 0 ≤ θ
       money : 0 ≤B
       north: ΦL L (n:ℝ) + B+ 3*((n:ℝ)*ψω L (n:ℝ)) < M
       desire : n* (∆e L) ≤ e
       south: (Φ Q)+3*n*(Ω Q)+B< M
       fare : n*(Ω Q)≤e
#print FundX
set_option quotPrecheck false
local notation "p★" i:arg=> (Pt i).threshold
local notation "co" Lp:arg S:arg j:arg=> compass (cashR Lp S n j) (A j)
local notation "tX" Lp:arg S:arg j:arg=> torque (cashR Lp S n j) (A j)
local notation "po" Lp:arg S:arg j:arg=> point (p★ j) (cashR Lp S n j) (A j)
variable {S t s:ℝ}(l:ℝ) (hX:Signature C D)
local notation "costA"=> D*(C*e)
local notation "costT"=> D*(C*M)
-- define gross endpoint decoded errors
structure GlowZ (n:ℕ)(S:ℝ)(p:ℕ→Z):Prop where
       Δ : ‖(compass (cashR L S n 0) (A 0)) (p 0)-(compass (cashR L S n n) (A n)) (p n)‖≤ D*(C*e)
       h : ‖ (torque (cashR L S n 0) (A 0)) (p 0) -(torque (cashR L S n n) (A n)) (p n)‖≤D*(C*e)
       h0: ‖(torque (cashR L S n 0) (A 0)) (p 0)‖≤ D*(C*M)
       yields(j:ℕ): j≤ n → ‖point (Pt j).threshold (cashR L S n j) (A j) (p j)‖ ≤2*(D*(C*M))
#print GlowZ
-- corrected call parameters
variable (hF:FundX u a α ε (l^4) (l^5) M B θ e n)(hh:3 ≤ l)(hw:l*u^2=1)(hα:4*a*u≤1/2)(hT:Stair.Twist n Pt A V l u θ) (hQ:0 < S)(hZ:∀ j,W j n≤ B*S)
include hF hh hw hα hT hX hQ hZ hP
lemma lusterX : GlowZ (l^4) M C D e Pt A n S p :=by
       let L:=l^4; have hl:0<l:=lt_of_lt_of_le (by norm_num) hh; have hL:0<L:=pow_pos hl _; let u':=cashR L S n
       let T:= trunks p Pt A u'; let K(k:Fin 4):=nuP k Pt A V u L
       obtain ⟨he,hx,hz⟩:= cash_κ L S hL hQ n
       have hup:= hP.step; have hd:= motionV a u l hw hP.prim hup hh hα
       have hBB(a:ℝ)(h:a≤B*S):u' n*a ≤B:=by unfold u'; rw[hz,mul_comm,one_div,←div_eq_mul_inv]; exact (div_le_iff₀ hQ).mpr h
       have h (j:Axis) : (∀ i:ℕ,i≤ n → blip T j i≤ M) ∧ wages j (T 0 0 -T n 0) ≤ e:=by
             let Z1:=fun i=>u' i*W j i; have hh₁:= shinesG α a ε L u j hP hL.le he hx hd.1; have hg:Z1 n ≤B:= hBB _ (hZ _); have ht:wages j (T n 0)≤B:= (paso ..).trans ((hh₁.funds n le_rfl).trans hg)
             have hε:=hP.toxin; have ha:=hP.script; have hD:=hF.north; let g:= ΦL L (n:ℝ); let H:=(wages j (T n 0)+n*(∆e L)); have hh:H≤ g:= add_le_add_left ht _; have heA:0 ≤ φ L:= by positivity
             have hp: H+B+3*(n*(φ L*H+δ L*(τ L)))< M:=by
                   refine lt_of_le_of_lt ?_ hD; refine add_le_add (add_le_add_left hh B) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left hh heA) _) (Nat.cast_nonneg _)) (by norm_num))
             have hΨ:= strongY j T K Z1 (L*a) (φ L) (δ L) θ B M (mul_nonneg hL.le hP.prim) heA (by positivity) hF.e_ng hh₁ hg hT.x hT.eT hF.m_ng hp
             have heΩ:= hΨ.2 0 (Nat.zero_le n); rw [Nat.sub_zero] at heΩ; exact ⟨hΨ.1, heΩ.trans hF.desire⟩
       have hc:= zero_le_one.trans hX.pos; have ht:= zero_le_one.trans hX.ng; have hD':‖T 0 0-T n 0‖≤ C*e:= hX.qual _ e fun i=>(h i).2
       have hc'(i:ℕ)(hi:i ≤ n)(k:Fin 4): ‖T i k‖ ≤C*M:= (hX.qual _ _ (fun j=> (paso j T i k).trans ((h j).1 i hi)))
       have hi(i:ℕ): (co L S i) (p i)= prismA (T i 0) ∧ (tX L S i) (p i)=(axM 0) (T i 0):= bank_p _ 0
       refine ⟨?_ ,?_ ,?_ ,fun i hi=>?_⟩
       · rw [ (hi 0).1,(hi n).1, ←map_sub]; exact (hX.read1 _).trans (mul_le_mul_of_nonneg_left hD' ht)
       · rw [(hi 0).2,(hi n).2, ←map_sub]; exact (hX.read0 _).trans (mul_le_mul_of_nonneg_left hD' ht)
       · rw [(hi 0).2]; exact (hX.read0 _).trans (mul_le_mul_of_nonneg_left (hc' _ (Nat.zero_le _) _) ht)
       rw [point_p]; let t:= p★ i; have hm:0≤costT:= by positivity [hF.m_ng]
       have he(k:Fin 4): ‖prismB (T i k)‖≤costT:=(hX.read2 _).trans (mul_le_mul_of_nonneg_left (hc' _ hi k) ht); apply (norm_add_le ..).trans; rw[norm_smul,Complex.norm_real,Real.norm_of_nonneg ((Pt i).threshold_pos.le)]; exact (add_le_add (mul_le_mul_of_nonneg_left (he 1) ((Pt i).threshold_pos.le)) (he 2)).trans (le_trans (add_le_add_left (mul_le_of_le_one_left hm (Pt i).threshold_le) _) (by rw[two_mul]))
-- inequality high endpoint.S.Ph local weights.
lemma lumenQ (hs:bet 0 (p 0)=0)(hq: p★ 0 ≤ s)(hv: p★ n ≤ s): ‖point (p★ 0) (cashR (l^5) S n 0) (A 0) (p 0) - point (p★ n) (cashR (l^5) S n n) (A n) (p n)‖ ≤ 2*s*costT+costA:=by
       let L:=l^5; have hl:0 < l:=lt_of_lt_of_le (by norm_num) hh; have hL:0<L:=pow_pos hl _; let u':=cashR L S n; let T:=trunks p Pt A u'; let K(k:Fin 4):=nuP k Pt A V u L
       obtain ⟨he,hx,hz⟩:=cash_κ L S hL hQ n; have hup:= hP.step; have hd:=motionV a u l hw hP.prim hup hh hα
       have hb(j:Axis):(∀ i:ℕ,i ≤n → blip T j i≤ M)∧ wages j (T 0 2-T n 2) ≤ e:=by
            let Z1:=fun i=>u' i* W j i; have hε:=hP.toxin; have ha:=hP.script; have hhB:= shinesG α a ε L u j hP hL.le he hx hd.2
            have hS:Z1 n ≤ B:=by unfold Z1 u'; rw [hz,mul_comm,one_div,←div_eq_mul_inv]; exact (div_le_iff₀ hQ).mpr (hZ _)
            have hE : wages j (T 0 0) ≤0:=by unfold T trunks stack; rw [hs,smul_zero,smul_zero,wageT]
            have hΨ:= strongX j T K Z1 (L*a) (φ L) (δ L) θ B 0 M (mul_nonneg hL.le hP.prim) (by positivity) (by positivity) hF.e_ng hhB hS hT.g hT.t hE hF.m_ng (by simpa only [zero_add] using hF.south)
            have hz':= hΨ.2 0 2 (Nat.zero_le _) (by decide); rw [Nat.sub_zero,zero_add] at hz'; exact ⟨hΨ.1,hz'.trans hF.fare⟩
       have ht:= zero_le_one.trans hX.ng; have hμ:‖T 0 2 -T n 2‖≤ C*e:= hX.qual _ e (fun j=> (hb j).2)
       have hV:‖prismB (T 0 2)-prismB (T n 2)‖≤ costA:=by rw [← map_sub]; exact (hX.read2 _).trans (mul_le_mul_of_nonneg_left hμ ht)
       have hz' (i:ℕ)(hi:i≤ n)(he:p★ i≤ s): ‖(↑(p★ i):ℂ) • prismB (T i 1)‖ ≤ s*costT:=by
            rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg ((Pt i).threshold_pos.le)]
            apply (_: _ ≤ s*‖prismB (T i 1)‖) |>.trans; · refine mul_le_mul_of_nonneg_left ((hX.read2 _).trans (mul_le_mul_of_nonneg_left (hX.qual _ _ (fun j=> (paso j T i 1).trans ((hb j).1 i hi))) ht)) (le_trans (Pt i).threshold_pos.le he)
            exact mul_le_mul_of_nonneg_right he (norm_nonneg _)
       rw [point_p,point_p]; let r(i:ℕ):=(↑(p★ i):ℂ); let e0(i:ℕ):=r i • prismB (T i 1); let e1(i:ℕ):=prismB (T i 2)
       change ‖e0 0+ e1 0-(e0 n+e1 n)‖ ≤ _; rw [show e0 0+e1 0 -(e0 n+e1 n)=(e0 0-e0 n)+(e1 0-e1 n) from by abel]; refine (norm_add_le ..).trans (add_le_add ?_ hV); exact (norm_sub_le ..).trans ((add_le_add (hz' 0 (Nat.zero_le _) hq) (hz' n le_rfl hv)).trans_eq (by ring))
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.lusterX
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.lumenQ
