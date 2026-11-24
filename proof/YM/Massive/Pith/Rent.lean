import YM.Massive.Pith.Cover
import YM.QCD.Finch.Dad
/-! lantern shelf aggregated at a *single* power via CrossP. Used for the first power. Winding components included already (cost with own anchor). -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false -- parallel unfold cases
noncomputable section
namespace YM.QCD.Pith
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open Revolve Stew Reggae Brick Port Entr
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
variable (b:Flavor N)
local notation "J"=> Modes c N
variable {t r q:ℝ}{p:BudgetPoint}{ι α β:Type}
variable (o:Site c) (M:Spike)

variable (E:Gem c N ι)
variable (m:Flavor N→ℝ)
def unitL (b:Flavor N)(m:ℝ)(o:Site c):EvenA c N:= lightP1 b o ((m:ℂ) • 1)
lemma loyalty (P: Spike)(x:ℝ): (x:ℂ) • P = x • P := Complex.coe_smul x P
lemma Lscale (x:ℝ): unitL b x o=x • lightP1 b o 1:=by unfold unitL lightP1; rw [loyalty]; exact map_smul ((loanP b o).restrictScalars ℝ) x _
lemma approved (x:ℝ)(_p:BudgetPoint)(ht:0<t) : Sen o t (unitL b x o) ≤priceP N*(t^2*‖x‖):=by
    apply (priceLoan b o ((x:ℂ) • 1) ht).trans_eq; rw [norm_smul,Complex.norm_real,norm_one,mul_one]
lemma moneyL (x:ℝ)(B:BudgetPoint)(ht:0<t): Woven o {o} B t (fun _=>unitL b x o) (priceP N*(t^2*‖x‖)) := by
    apply (constWoven _ _ _ _ (approved b o x B ht)); exact GateLoan b o _ _ (mem_singleton_self _)
lemma cashL (x:ℝ)(U:Site c): Regal c N (unitL b x U)=unitL b x U:=by apply Regal_loan; unfold Stew.tale; simp only [star_smul,Matrix.mul_smul, Matrix.smul_mul,star_one,mul_one,g5_sq]; congr! 1; simp
abbrev rentGem : Gem c N (Site c × Flavor N):=⟨fun i=> ⟨i.1,{i.1},mem_singleton_self _⟩,fun z _=> unitL z.2 (m z.2) z.1⟩
set_option quotPrecheck false
variable (c)
lemma rentCross : CrossP (rentGem (c:=c) m):=by
    refine ⟨fun i=>shadeLoan i.2 i.1 _, fun i _=>phaseLoan i.2 i.1 _,fun i _=>cashL _ _ _,fun s k g hp=>?_⟩
    refine ⟨Equiv.prodCongr (act s) (Equiv.refl _),?_⟩; rintro ⟨p,i⟩
    refine ⟨?_,fun _=>?_⟩
    · dsimp only [rentGem]; congr!
    change Diode _ _ _ _ (lightP1 _ _ _) =unitL i (m i) _; rw [turnLoan _ _ _ hp,Matrix.mul_smul,Matrix.smul_mul,mul_one, hp.2.unit.2]; rfl
abbrev priceL (t:ℝ)(x:Flavor N):= priceP N*(t^2*‖m x‖)
lemma singleton_cover (x:Site c): coverNumber p.B {x}=1:= by
        obtain ⟨D,hD,h'⟩:=coverNumber_realized p.B ({x}:Support c); apply le_antisymm _ _
        · have ht:=Corona.tile x 0 p.B p.B_pos; exact (Corona.cover_mono (halo_subset _ _) _).trans ht |>.trans (by omega)
        rw [← h']; have hh:= hD.1 (Finset.mem_singleton_self x); obtain ⟨j,hj,-⟩:=halo_spec.mp hh; exact card_pos.mpr ⟨j,hj⟩ -- explicit c binder order
open Shells.Warmlet
lemma rentPaid (m: Flavor N→ℝ) : Valued (rentGem (c:=c) m).addr q (priceL m t ∘ Prod.snd) p.B (Real.exp q*∑ b, priceL m t b):=by
    intro i; apply budget_finite ?_ ?_
    · intro j; split; · dsimp only [Function.comp_apply]; unfold priceL; have ht:= priceP_nonneg (N:=N); positivity
      exact le_rfl
    rw [Fintype.sum_prod_type,Finset.mul_sum, sum_comm]; refine le_of_eq (sum_congr rfl fun b _=> ?_)
    rw [sum_eq_single i]; rotate_left
    · intro j _ hj; exact if_neg hj
    · simp
    rw [if_pos (show ((rentGem (c:=c) m).addr (i,b)).site=i from rfl)]; change priceL m t b *Real.exp (q*coverNumber p.B {i}) = _; rw [singleton_cover,Nat.cast_one,mul_one,mul_comm]
variable {c}
def gaugeMass (E:Gem c N ι):Flavor N→ℝ:=fun b=> qMass (till E b 0)
variable (X:Grid c) {w:ι→ℝ} (h:Valued E.addr r w p.B q)(hw:∀ i,Woven (E.addr i).site (E.addr i).support p t (E.view i) (w i)) (hr:0≤r) (hz:0<t)
local notation "Y"=> rentGem (c:=c) (gaugeMass E)
include hw h hr hz
lemma scaleMass : t^2 * ‖gaugeMass E b‖ ≤ widthB*q:= by
    unfold gaugeMass; exact (mul_le_mul_of_nonneg_left (crops (till E b 0)).1 (sq_nonneg _)).trans (Stew.diligent E b h hw hz hr widthB_le (Classical.choose_spec preMoment).2 none 0)
lemma refunded : Valued (Y).addr r (priceL (gaugeMass E) t ∘ Prod.snd) p.B (Real.exp r*(jointFee N*q)):=by
    intro x; let m:=gaugeMass E; have hh(i): priceL m t i ≤ priceP N*(widthB*q):=mul_le_mul_of_nonneg_left (scaleMass i E h hw hr hz) priceP_nonneg
    refine budget_loosen (rentPaid c (gaugeMass E) x) (mul_le_mul_of_nonneg_left ((sum_le_sum fun i _=> hh i).trans_eq ?_) (Real.exp_pos _).le)
    unfold jointFee; simp only [sum_const, Fintype.card_fin, card_univ,nsmul_eq_mul,Flavor];ring
variable (he:CrossP E)
include he
lemma rentRecept : HasSum (fun i=> Tall.breeze (t:=p.threshold) E i X) (Patron.total (Y) p.threshold X):=by
    let m:= gaugeMass E; have hT := Licence_g (show Licence p r q t E from ⟨w,h,hw⟩); have hf: Summable w:= Loom.sumRide _ _ _ h (fun i=>(hw i).travel) hr; let S:= rentGem (c:=c) m
    have hp(x:Flavor N)(j):=costsE E x hf hz (fun i=>(hw i).sizeU 1 (AnalyticBridge.VerifiedReset.flat_ok ..)) j
    have hl (z: Site c×Flavor N): HasSum (fun i:ι=> if Healthy p.threshold ({z.1}:Support c) X then loanP z.2 z.1 (unitM E z.2 z.1 none i) else (0:EvenA c N)) (Patron.letters S p.threshold X z):=by
       unfold Patron.letters; change HasSum _ (masked p.threshold {z.1} _ X); by_cases hv: Healthy p.threshold ({z.1}:Support c) X
       · rw [masked_eq _ _ _ _ hv]; simp only [if_pos hv]; let y:= till E z.2 z.1; let B:= till E z.2 0; have hz₁: y none=((m z.2:ℝ):ℂ) • (1:Spike):=by rw [show y=B from plumsB E z.2 hT he (hp _) z.1]; exact muse (portraitsB E z.2 hT he (hp _))
         change HasSum _ (loanP z.2 z.1 _); rw [←hz₁]; exact (loanP z.2 z.1).hasSum (concession E z.2 (hp _ _) z.1).hasSum
       simp_rw [masked_ne _ _ _ _ hv,if_neg hv]; exact hasSum_zero
    unfold Patron.total; rw [tsum_fintype]; apply (hasSum_sum (fun z (_:z∈(univ:Finset _))=>hl z)).congr_fun; intro i
    unfold Tall.breeze; let J0(q:Site c×Flavor N): EvenA c N:= if Healthy p.threshold ({q.1}:Support c) X then loanP q.2 q.1 (unitM E q.2 q.1 none i) else 0; let y:=(E.addr i).site
    change masked p.threshold {y} (fun _=>lampShelf E i) X=∑ z: Site c × Flavor N, J0 z
    rw [Fintype.sum_prod_type,sum_eq_single y]; rotate_left
    · intro j _ hj; apply sum_eq_zero; intro k _; unfold J0 unitM; rw [if_neg (show j≠ _ from hj),map_zero]; apply ite_self
    · simp
    by_cases hx:Healthy p.threshold ({y}:Support c) X
    · rw [masked_eq _ _ _ _ hx]; unfold lampShelf; apply sum_congr rfl; intro z _; unfold J0 unitM; rw [if_pos (show y=_ from rfl), if_pos hx]; rfl
    rw [masked_ne _ _ _ _ hx]; exact (sum_eq_zero (fun i _=> if_neg hx)).symm
end YM.QCD.Pith
#print axioms YM.QCD.Pith.rentRecept
