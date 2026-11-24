import YM.MassiveQCD.Relight.Coherent
import YM.MassiveQCD.Relight.Seal
import YM.MassiveQCD.Relight.Generic
import YM.MassiveQCD.Tangent.Aisle
/-! # Rotate with respect to `Honest` occupancy; preserve weight classes
 before remasking (uses the robust `relight` eventual equality in the complex range). -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Relight
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Port Brick Dust Reggae Stem Stew Stew.Phased
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{N n:ℕ} {a r u t σ η ξ T θ x:ℝ}{p:BudgetPoint}{o:Site c}
open Villa Revolve Flume Quarry AnalyticBridge.VerifiedReset Footprint Jets.Touch Kites
variable {I J K K₀:Type}
open Ruby Ruby.LanternK Acre Acre.Rails
open Festival Shells Shells.Warmlet Finch Stem Grove Calm
variable (E G:Gem c N I)(X:Ruby.Hue c N J)(U:Grid c)(v:I→ℕ)(z:ℕ→ℂ)
-- actual priceable trade AND homogeneous flow (any bounded z; geometry unaffected). Later wear all (verify aperture captures), η stays high enough.
local notation "K*"=> v ∘ Prod.snd
noncomputable abbrev stitchCost (p:BudgetPoint)(σ b:ℝ):ℝ:=payment 1 (4*p.B+2) 0 1 1 σ b 0 -- cand ensure calendar reserv for Sophia (Op.Power) and Warm. α+η+? later.
noncomputable abbrev stitch (p:BudgetPoint): Ruby.Hue c N (ManyA c I):= Ruby.HGrace (lira E G p.threshold)
structure Bridge (p:BudgetPoint)(t u b C σ:ℝ):Prop where
    debit: Licence p u C t (glean G)
    alive: RotationE (glean G) (v ∘ Prod.snd)
    earn : Wax (stitch E G p) p.threshold p.B b (stitchCost p σ b) t
    glory: Yank (stitch E G p) (v ∘ Prod.snd)
    flow(z:ℕ→ℂ)(U:Grid c): UnitCoeff z → Stem.income (weight E v z) p.threshold U=Stem.income (weight (glean G) (K*) z) p.threshold U + swarm (bleach (stitch E G p) (K*) z) U
-- reads across base.Organ threshold. Nimbus
lemma bridges {b W:ℝ} (he:G.view=E.view)(ht:0<t)(hr:1 ≤ r)(hw:fareG 1 t N≤r)(hp:Noted E)(h:∃f:I→ℝ,Ac.Hit (fun i=>(E.addr i).support) p.B f a W ∧∀ i,Woven (E.addr i).site (E.addr i).support p r (E.view i) (f i))(hg:Licence p u σ r G)(hh:0≤u)(hx:0≤b)(hv:(b+1+1)*(frostQ n) ≤ a)(hψ:∀ i,(G.addr i).site∈(E.addr i).support ∧ (E.addr i).support ⊆(G.addr i).support ∧ (G.addr i).support ⊆ Lattice.halo (n*p.B) (E.addr i).support)(hc: Coherent E p.threshold v) :
      let K:=turnCost p.order p.power; Licence p a W r E ∧ Bridge E G v p t u b (K *σ) W ∧ Stem.income E p.threshold 1=Stem.income G p.threshold 1 :=by
    obtain ⟨f,hf,hF⟩:=h; have hp' i:0 ≤ f i:= (hF i).travel; have hr0:= zero_lt_one.trans_le hr
    have H: Valued G.addr (b+1+1) f p.B W:=by
      refine tiller (E:=G) hf hp' (fun i=>(hψ i).1) ?_ (by linarith) hv; intro i; rw [mul_comm]; exact_mod_cast (show coverNumber p.B _ ≤ coverNumber p.B (E.addr i).support*frostQ n from (Corona.cover_mono (hψ i).2.2 p.B).trans (touring _ n _ p.B p.B_pos le_rfl))
    have hL:Licence p a W r E:=⟨f,Stem.anchorM E f hp' hf,hF⟩
    let X:=lira E G p.threshold
    obtain ⟨hpZ,hT⟩:=burnY E G hL hp he.symm (Entr.Licence_g hg) hr0 (fun i=>(hψ i).1) (fun i=>(hψ i).2.1) f H (by
       intro i V; by_cases he:Healthy p.threshold (E.addr i).support V; · unfold letters; rw [masked_eq _ _ _ _ he]; exact (opticX _ _ _ hr0).trans ((hF i).sizeU _ he)
       unfold letters; rw [masked_ne _ _ _ _ he,map_zero,norm_zero]; exact hp' i) hx
    have hJ: Noted G:=⟨fun i=> (congr_fun he i).symm ▸ hp.gauge i, fun i=>(congr_fun he i).symm ▸ hp.num i, fun i=> (congr_fun he i).symm ▸ hp.real i⟩
    intro K; refine ⟨hL,⟨folded G hg hw ht, glimmer G v hJ,wax_grace X hT hw ht, hailed X v hpZ,?_⟩,?_⟩; swap
    · exact tsum_congr (fun i=> (masked_eq _ _ _ _ (flat_ok ..)).trans ((congr_fun (congr_fun he.symm i) 1).trans (masked_eq _ _ _ _ (flat_ok ..)).symm)) -- maybe infer
    intro z U hU
    let W:=weight E v z; let W':= weight G v z; let X':=bleach X v z
    have hh' U := permits W' (payments G v z (fun i=>hU _) zero_le_one hg) hr0 hh U; have ht' U := ((bleachPay X v z (fun i=>hU _) zero_le_one hT).heated hr hx U).1
    have hhZ: Stem.income W p.threshold=Stem.income W' p.threshold+Calm.netT X':=by
      funext U; refine (( (hh' U).hasSum.add (ht' U).hasSum).congr_fun (fun i=> ?eq)).tsum_eq
      case eq=> change letters (weight E v z) p.threshold U i=letters (weight G v z) _ U i+ z (v i) • (letters E p.threshold U i- letters G p.threshold U i); rw [earns,earns,← smul_add, add_sub_cancel]
    rw [←congr_fun (hc z hU) U,clean, cleaner]; refine Eq.trans (show potion (Stem.income W p.threshold) U=_ from ?_) ((congr_arg₂ (·+·) (fragrants W' hh' U) (fragrance X' ht' U)))
    rw [hhZ]; exact crestedX ..
end YM.QCD.Relight
#print axioms YM.QCD.Relight.bridges
