import YM.Cardinal.Quests
/-!
 # Single arrangements in actual Units. Caps pre weights on pointed/reference layouts.P composed with updates.Yes.
   No explicit global identity in this run of the one-source cone. (All labels including that one use actual indicators; net also pays that weight). 
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
namespace Plans
variable {u s t a b θ v A' D C ν Θ α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
namespace Stamp
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle
variable {I J K E Uv Fv Zt:Type}
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)
-- Step references. No common label-union across books demanded. `w x partial` eq at outgoing health.Loosen.a' . Seat.S. set covering.
variable (x:Label d) (q:Bool) (Pt:BudgetPoint)
-- General base rank+remainder.R Over variant.Mert.Lo.Q.S.Defs.K
section
variable {Pt A H x q b} (G:CentreFrame (c:=c) Pt v x q A b (r+1) E K)
set_option quotPrecheck false
local notation "o"=> wrap c b
local notation "bp"=> pot (r+1) c b
local notation "Z!"=>basePack A b q d x G.moor (r+1)
local notation "W'"=> seed_w (a*coverNumber Pt.B (pot (r+1) c b))*β*wealth x.val Pt.threshold v
variable (V:Grid c)
local notation "Tq"=> goldM q
local notation "p!"=>fun (_:Iris.alpha)=>wrap c b
local notation "r!"=>fun (_:Iris.alpha)=>q
namespace Flyer
variable (Q:Puff c 6 I q)(S:I→Support c) (hQ: Seal 6 (wrap c b) Q)
variable (hp: Pilot H A d m k n j r α β) (hs: Pt.order=m)(ht: Pt.power=k)(hb:30*(r+1) ≤ c.val)(hS: ∀ i, (Q.addr i).support ⊆ S i)(heP:∀ i,pot (r+1) c b ⊆ S i)
variable (f g:I→ℝ)(hf:∀ i, Flame (Q.fill i) Pt (S i) (wrap c b) v n j (f i))(hg:∀ i, Sight (Q.addr i).support (wrap c b) l Pt v (Q.fill i) (g i))
variable (eT':ℝ)(hA: Ac.Hit S Pt.B f eT' t)(hV:1≤v) (ha:0≤eT')(hΩ:Ac.Hit S Pt.B g eT' u)
open QCD.Relight QCD.Ruby -- maybe fail
variable {p:I→Label d}(hc:∀ i, Beacon.ActionTest H b (Q.fill i) (p i).val) (hw:∀ i, moored (p i).val q)
local notation "pc"=> fun i=> wealth (p i).val Pt.threshold v
variable (hψ:∀ i,wrap c b ∈ S i)
local notation "Y!"=>Ypack Q S hψ
local notation "V!"=>Vpack S Q A hw hψ
local notation "X!"=>sub_pack (Y!) (V!)
open QCD.Loom QCD.Stew QCD.Creek
local notation "M"=> ample 6 Iris.alpha
local notation "Σ'"=>∑' i,p i
local notation "τ"=>Pt.threshold
local notation "δC"=> v -- use
noncomputable abbrev tack (P:BudgetPoint)(v:ℝ):= Puff.stool 6 o (Y!) P v (fun i=>(Q.addr i).support) (fun _=>1)
noncomputable abbrev untack (A:Exhibit U)(hw:∀ i,moored (p i).val q)(P:BudgetPoint)(r:ℕ) (v:ℝ) :=Puff.stool 6 o (Vpack S Q A hw hψ) P v (fun _=> pot (r+1) c b) (fun _=> -1)
local notation "Y'"=> tack Q S hψ Pt v
local notation "V'"=>untack Q S hψ A hw Pt r v -- check
local notation "X'"=>HJoin (Y') (V')
local notation "Z'"=> u+β*(α*t)
local notation "D⁺"=> withdraw 6 (fun _:Iris.alpha=>o) v
local notation "U⁺"=>banknote 6 (fun _:Iris.alpha=>o) v
include hp hf hQ hA hs ht hb hV hc hS hw heP ha hΩ hg
set_option maxHeartbeats 480000 in
lemma advanced : Wax X' τ Pt.B eT' Z' v ∧ (∀ i,shadeG ((X').mean i))∧ (∀ i V,Mint 6 (fun _:Unit=>o) v (fun _=>q) topM ((X').mean i V)):=by
    have ht:=worked Q S hQ hp hs ht hb hS heP f hf eT' hA hV ha hc hw hψ; let z:= sub_pack (Y!) (V!); have hv:= zero_lt_one.trans_le hV
    let X₁:= Ypack Q S hψ; have hX(i):=ht.2.2.2.1 i; have hp' i U (h: Healthy Pt.threshold (Q.addr i).support U): load (fun _=>v) (X₁.fill i U) ≤ g i:= (viewer o _ l hv).trans ((hg i).pole U h [] (Nat.zero_le _) (fun _ h=>by simp at h)) -- b macro b overwritten
    have hQ' : Ac.Hit (fun i=> (X₁.addr i).support) Pt.B (fun i=>‖(1:ℂ)‖*g i) eT' u:= by simp only [norm_one,one_mul]; exact hΩ
    obtain ⟨hm,hY,hg'⟩:= paidSize 6 o X₁ Pt v _ hS (fun _=>1) ht.2.1 g (fun i=>(hg i).travels) hp' hQ' hv -- arguments
    let π:= Vpack S Q A hw hψ; have hh:=toll_ps Q S hQ hp hs (show Pt.power=k from by assumption) hS f hf eT' hA hV ha hc; let m i:=β*wealth (p i).val Pt.threshold v
    have ht' :Ac.Hit S Pt.B (fun i=> ‖(-1:ℂ)‖*m i) eT' (β*(α*t)):=by simp only [norm_neg,norm_one,one_mul]; apply spend_collect; convert! budget_scale (zero_le_one.trans hp.funds) hh.2.1 using 1; ext i; exact mul_assoc ..
    have hp'(i V)(hh:Healthy Pt.threshold bp V): load (fun _=> v) (π.fill i V) ≤ m i:=(viewer o _ 2 hv).trans ((hX i).sight.pole V hh [] (Nat.zero_le _) (fun _ h=>by simp at h))
    obtain ⟨hf',hν,hW⟩:= paidSize 6 o π Pt v _ heP (fun _=> -1) ht.1 m (fun i=>(hX _).sight.travels) hp' ht' hv
    exact ⟨reach_w hm hf',fun i=>by rcases i with i|i; exact hY i; exact hν i,fun i=>by rcases i with i|i; exact hg' i; exact hW i⟩
omit hΩ hg hA ha hp -- fix omit
-- pointwise, not just projected.Masks.Waxy inputs. value correction.
local notation "rwM"=> Reel.mist
local notation "ropeM"=>Reel.rope
omit hf hQ hs ht hb hS heP hc
lemma stepR (i:I): Reel.mist Q.roll Pt.threshold i V= Reel.mist (roll 6 (X!)) τ i V + D⁺ ((X').mean (.inl i) V)+ D⁺ ((X').mean (.inr i) V)+ vote A b (p i) q (hw i) Pt.threshold (r+1) c V:=by
    let t:= Pt.threshold; let D:= D⁺; let X:= X!; let Y:= Y!; let P:= V!; let K':= Keys c 6; let U₁:=fun (i:I) (V:Grid c)=> U⁺ (Y.roll.mark i V); let U₂:= fun (i:I) (V:Grid c)=> U⁺ (P.roll.mark i V); let φ(T:Support c):= masked (G:=su) (X:=tapeA c) t T
    have h : X.roll.mark i= Y.roll.mark i - P.roll.mark i:= by
       funext V; apply Subtype.ext; change stake K' (goldM q) ((Y.fill i V)-(P.fill i V))= (stake _ _ _ - stake _ _ _); exact map_sub _ _ _
    let X₀:= S i; let X₁:=(Q.addr i).support; let X₂:=pot (r+1) c b; have hv:= zero_lt_one.trans_le hV
    let y:= Reel.mist Q.roll t i V; let A':= φ X₀ (Y.roll.mark i) V; let B':= φ X₀ (P.roll.mark i) V; let C':= φ X₂ (P.roll.mark i) V; change y=_ + D ((1:ℂ) • (masked t X₁ (U₁ i) V- masked t X₀ (U₁ i) V))+ D ((-1:ℂ) • (masked t X₂ (U₂ i) V- masked t X₀ (U₂ i) V))+ C'
    have h1 : D (masked t X₀ (U₁ i) V)=A':= muting 6 o Y v t _ V i hv
    have h2 : D (masked t X₀ (U₂ i) V)=B':= muting 6 o P v t _ V i hv
    have h3 : D (masked t X₂ (U₂ i) V)=C':= muting 6 o P v t _ V i hv
    have h₀ : D (masked t X₁ (U₁ i) V)=y:= muting 6 o Y v t _ V i hv
    rw [one_smul,neg_one_smul,map_sub,map_neg,map_sub,h₀,h1,h2,h3,show Reel.mist _ _ _ _=A'-B' from ?_]; abel
    change φ X₀ ((Puff.roll 6 X).mark i) V= _; rw [h]; unfold A' B' φ; by_cases hp:Healthy t X₀ V; · rw [masked_eq _ _ _ _ hp,masked_eq _ _ _ _ hp,masked_eq _ _ _ _ hp]; rfl
    rw [masked_ne _ _ _ _ hp,masked_ne _ _ _ _ hp,masked_ne _ _ _ _ hp,sub_zero]
-- label sum. No measurable nuance. Over NormEarn.
omit hw hV
lemma voteSeq (h:moored (∑' i,p i).val q) (hz:Summable p)(hw:∀ i,moored (p i).val q) : HasSum (fun i=>vote A b (p i) q (hw i) Pt.threshold (r+1) c V) (vote A b (Σ') q h τ (r+1) c V):=by
    let f(i:I):= vote A b (p i) q (hw i) τ (r+1) c V
    change HasSum f _; by_cases hp: Healthy τ bp V
    · let X:= Realize.placed (A.t d) c b; let g: Label d →ₗ[ℂ] Alg (Keys c 6):= (ContinuousMap.evalCLM ℂ V).toLinearMap.comp (X.comp (A.lead d)); let Z:= (stake (Keys c 6) (goldM q)).comp g.toContinuousLinearMap; have hF(x:Label d)(h:moored x.val q) : (Cove.light _) (vote A b x q h τ (r+1) c V)=Z x:=by unfold vote; rw [masked_eq _ _ _ _ hp]; rfl
      have he: HasSum (fun i=> Cove.light _ (f i)) ((Cove.light _) (vote A b (Σ') q h τ (r+1) c V)):= (hF _ _).symm ▸ ((Z.hasSum hz.hasSum).congr_fun (fun i=>hF _ _))
      have hS : Summable f:=Summable.of_norm he.summable.norm
      apply Eq.subst (motive:=fun v=> HasSum f v) ?_ hS.hasSum; refine Subtype.ext ?_; exact ((Cove.light _).toLinearMap.toContinuousLinearMap.hasSum hS.hasSum).unique he
    have hh:f=0:= funext fun i=> masked_ne _ _ _ _ hp; rw [hh, show vote _ _ _ _ _ _ _ _ _=0 from masked_ne _ _ _ _ hp]; exact hasSum_zero
include hw hΩ hA ha hQ hp hf hs ht hV hg heP hb hS hc
lemma step_rit (hT:moored (∑' i,p i).val q): Reel.rope Q.roll τ V=vote A b (Σ') q hT τ (r+1) c V+Reel.rope (roll 6 (X!)) τ V+D⁺ (swarm X' V):=by
    obtain ⟨hm,-,-⟩:= advanced Q S hQ hp hs ht hb hS heP f g hf hg eT' hA hV ha hΩ hc hw hψ
    obtain ⟨_,_,he,_,_,x,hx,hh⟩:=worked Q S hQ hp hs ht hb hS heP f hf eT' hA hV ha hc hw hψ; let P:=V!; let X:=X!
    let p₁ (i:I):=(Y').mean i V; let p₂ (i:I):=(V').mean i V
    let v (i:I⊕I):=(X').mean i V; have hv:Summable v:=(hm.heated (p:=Pt) hV ha V).1; have h1 : Summable p₁:= hv.comp_injective (i:=Sum.inl) Sum.inl_injective; have h2: Summable p₂:=hv.comp_injective (i:=Sum.inr) Sum.inr_injective
    let D:= (D⁺).toLinearMap.toContinuousLinearMap
    have hZ : D⁺ (swarm X' V) = D (∑' i,p₁ i)+ D (∑' i,p₂ i):= by rw [show swarm X' V=_ from (h1.hasSum.sum (f:=v) h2.hasSum).tsum_eq,map_add]; rfl
    have hx':=grow_shape 6 o X V ⟨x,fun i=> (hx i).sight, hh⟩ ha hV he
    rw [hZ]; apply HasSum.tsum_eq; have hQ':= (voteSeq (r:=r) (A:=A) (b:=b) (Pt:=Pt) V hT (toll_ps Q S hQ hp hs ht hS f hf eT' hA hV ha hc).2.2 hw).add hx'.hasSum |>.add ((D.hasSum h1.hasSum).add (D.hasSum h2.hasSum)); refine hQ'.congr_fun fun i=>?_ ; rw [stepR (r:=r) (A:=A) V Q S hV hw hψ]; let A':= vote A b (p i) q (hw i) τ (r+1) c V; change Reel.mist (roll 6 X) Pt.threshold i V + D (p₁ i) + D (p₂ i)+ A'=A'+Reel.mist (roll 6 X) Pt.threshold i V + (D (p₁ i)+D (p₂ i)); abel
end Flyer
end
end Stamp
end Plans
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Plans.Stamp.Flyer.step_rit
