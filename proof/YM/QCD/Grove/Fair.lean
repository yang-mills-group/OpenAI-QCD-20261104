import YM.QCD.Grove.Tails
import YM.QCD.Grove.Fiery
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Slide Trio.Sharp
-- layout
variable {C:Side}{D D' w j:ℕ}{d r t t' p p':ℝ}{B:BudgetPoint}
section spin_scalar
variable {T: Finset I}{S:Gem c N I} (h:SoilB T S B w t)
noncomputable def viewS (f: Site c→ Grid c→ ℝ)(s:Strut c)(x:Site c)(V:Grid c):= f ((Strut.act s).symm x) (Strut.sky s V)
noncomputable def crests (f:Site c→ Grid c→ ℝ)(x:Site c)(V:Grid c):= (Fintype.card (Strut c):ℝ)⁻¹*∑ i:Strut c, viewS f i x V
lemma lunarS (f:Site c→ Grid c→ℝ) (s:Strut c) (x: Site c) (V:Grid c): crests f x (Strut.sky s V)=crests f (Strut.act s x) V:=by
    unfold crests; rw [← Equiv.sum_comp (skyEquiv s) (g:=fun i=> viewS f i (Strut.act s x) V)]; congr 1; refine sum_congr rfl fun i _=>?_ ; unfold viewS; rw [skying, show skyEquiv s i=pod s i from rfl,podA]; simp
lemma merries (n:ℕ)(x:Site c)(i:Strut c): AnalyticBridge.VerifiedReset.Seat.spread i (neighbors n ((Strut.act i).symm x))= neighbors n x:= by
    rw [show AnalyticBridge.VerifiedReset.Seat.spread i _= (neighbors n ((Strut.act i).symm x)).image (Push.Local.turnSites i.1 i.2) from rfl,neighbors, ← halo_map (Push.Local.turnSites i.1 i.2) (turn_sep _ _)]; rw [Finset.image_singleton,show Push.Local.turnSites i.1 i.2 _=x from (Strut.act i).apply_symm_apply _]; rfl
include h
lemma pleasant (hv:0≤t)(x:Site c) : B.Regular (neighbors w x) (duskQ T S x):=by
    let p(i:I):Grid c→ℝ:=(((S.addr i).support.card:ℝ))⁻¹ • ((Reggae.river c N) ∘ S.view i); rw [show duskQ T S x=∑ i∈ pondC T S x,p i from funext fun k=>by simp only [duskQ,p,Finset.sum_apply,Pi.smul_apply, Function.comp_apply,smul_eq_mul]; simp_rw [div_eq_mul_inv,mul_comm _ _⁻¹]]; apply regularA; intro i hi; have he:=mem_filter.mp hi; apply AnalyticBridge.CouplingShape.reg_scale; obtain ⟨a,hx⟩:=h.fees i he.1; exact AnalyticBridge.VerifiedReset.reg_larger ((spores _ _ _ hx (h.gauge i he.1) hv).1) (h.tortillas _ he.1 _ he.2)
omit h
lemma populous (V: Grid c)(Q: I→ Grid c → EvenA c N)(T:Finset I)(S:I→ RegularAddress c):
   ∑ x:Site c, ∑ i∈T.filter (fun i=> x∈(S i).support), (Reggae.river c N (Q i V))/ ((S i).support.card:ℝ)=Reggae.river c N (∑ i∈T,Q i V):=by
     rw [map_sum]; simp_rw [sum_filter]; rw [Finset.sum_comm]; refine sum_congr rfl fun i _=>?_ ; simp_rw [← sum_filter]; rw [show Finset.filter _ univ=(S i).support from Finset.filter_mem_eq_inter ..|>.trans (univ_inter _),sum_const, nsmul_eq_mul]; have hp:0 < ((S i).support.card:ℝ):=Nat.cast_pos.mpr (card_pos.mpr ⟨_,(S i).anchor⟩); field_simp
include h
lemma poetry (hv:0≤t)(x:Site c): B.Regular (neighbors w x) (crests (duskQ T S) x):=by
    rw [show crests _ x=(Fintype.card (Strut c):ℝ)⁻¹ • ∑ i:Strut c,viewS (duskQ T S) i x from funext fun V=> by simp only [crests,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]]
    apply AnalyticBridge.CouplingShape.reg_scale; apply regularA; intro i _; rw [← merries w x i]; apply AnalyticBridge.VerifiedReset.Seat.regular _ (pleasant h hv _)
omit h
lemma mintH (T : Finset I)(S : Gem c N I): Trio.froth (crests (duskQ T S))=(Fintype.card (Strut c):ℝ)⁻¹ • (∑ i:Strut c, fun V=> Reggae.river c N (primed T S (Strut.sky i V))):=by
   funext U; unfold Trio.froth crests; rw [← mul_sum, sum_comm]; simp only [Pi.smul_apply,Finset.sum_apply, smul_eq_mul]; apply congr_arg; refine sum_congr rfl fun i _=>?_ ; rw [show (∑ j:Site c, viewS (duskQ T S) i j U)= _ from Equiv.sum_comp (Strut.act i).symm (fun j=>duskQ T S j (Strut.sky i U))]; exact populous _ (Gem.view S) T S.addr
lemma lapS (s:Strut c)(T: Finset I)(S:Gem c N I)(V:Grid c)(t':ℝ)(b:ℝ) :
   Reggae.river c N (primed T S (Strut.sky s V))=Reggae.river c N (((songT t' ∘ primed T S) - (fun _=>Reggae.baker c N b):Grid c→EvenA c N) (Strut.sky s V))-b:=by
   let X:=primed T S (Strut.sky s V); let Y:=Reggae.river c N; change _=Reggae.river c N (wearK c N t' X- Reggae.baker c N b)- _; rw [map_sub,Kites.proofR,Reggae.toe]; ring -- defeq?
lemma vane (s:Strut c): (pull s.1 s.2 (1:Grid c))=1:=by funext i; unfold pull; cases h:((posDir i.2).rotate s.1) with | mk a t=> cases t <;> simp [Lattice.Step.read]
lemma clothS (T:Finset I)(S:Gem c N I)(b t':ℝ): let Γ:= ((songT t' ∘ primed T S) - fun _=> Reggae.baker c N b)
    Boulevard.stillA (Trio.froth (crests (duskQ T S)))=(Fintype.card (Strut c):ℝ)⁻¹ • ∑ i:Strut c, (Boulevard.stillA ((Reggae.river _ _) ∘ Γ))∘ pull i.1 i.2:=by
    intro Γ; funext x; rw [mintH]; simp only [Boulevard.stillA,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,Function.comp_apply]; simp_rw [lapS (t':=t') (b:=b), show ∀ i:Strut c,Strut.sky i (1:Grid c)=1 from fun i=>vane i]; rw [← mul_sub,← sum_sub_distrib]; congr 1; refine sum_congr rfl fun i _=>?_ ; exact sub_sub_sub_cancel_right ..
-- type edit EvenA
end spin_scalar
end YM.QCD.Grove
