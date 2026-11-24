import YM.Profiles.Corsage
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Apron Apron.Grove Cupola Plate Card Iris
open MassiveQCD.Sample.LoomT Massive.Poised Massive.Poised.Plans Massive.Poised.Plans.Stamp Massive.UV Stative Massive.Poised.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical Stamp
variable {I J E D' :Type}[Fintype I][Fintype J]
open QCD.Kites QCD.Conductor QCD.Acre QCD.Acre.Rails QCD.Struck QCD.Struck.Library Weft
variable {c f L:Side}{v t Θ Γ α β κ:ℝ}{P:BudgetPoint}{k n l m d j:ℕ}
variable (N:ℕ)(q:I→Bool)(o:I→Site c)(i:I)
namespace ProfileL
open NormedSpace
set_option quotPrecheck false
local notation "q₀"=> fun (_:Unit)=> q i
local notation "p₀"=> fun (_:Unit)=> o i
local notation "A"=> Keys c N
local notation "R"=> wellAt i
local notation "H"=> pledgeAt q i
local notation "G"=> Sample.flame (Keys c N) q (q₀) (findV R ({()}:Finset Unit)) (fun (_:I) (_:Unit)=>1) -- ℝ binder syntax
local notation "Xu"=> Patio (A⊕Spine I)
local notation "p!"=> burst q ({i}:Finset I)
local notation "Ω"=> burst (q₀) ({()}:Finset Unit)
variable (x:Patio (Keys c N⊕Spine I)) (hw:Polite q {i} x) (Y:Film c N I E)
-- exact motion up to this aperture. No expectation used
local notation "Fx"=> fun (_:I) (_:Unit)=> (1:ℝ)
local notation "Tx"=> findV R ({()}:Finset Unit)
local notation "Zh"=> Patio (A⊕Spine Unit)
lemma shoves (x:EvenA c N): G (rootR (Spine I) (Keys c N) x)=rootR (Spine Unit) (Keys c N) x:=by
    apply Subtype.ext; change Sample.leaves A q (q₀) (Tx) (Fx) (fiber (Spine I) _) = _; rw [Sample.leaves, AlgHom.comp_apply, tarfib,blot_left]; rfl
lemma extinct (v:Finset I)(x:Xu)(he:Polite q v x)(hf:v.Nonempty) (hp:v ≠ {i}): G x=0:=by
    apply latentF _ _ _ _ _ (hym q (q₀) R H {()} (Set.mem_univ _)) _ _ he; intro h; have hx:v⊆ {i}:=by
        intro j hj; obtain ⟨k,hk⟩:=Option.ne_none_iff_exists'.1 (h.2 j hj); exact mem_singleton.mpr (show j=i from ((findG R (H).mast _ _ (Set.mem_univ _)).1 hk).2)
    obtain ⟨j,hj⟩:=hf; exact hp (Subset.antisymm hx (singleton_subset_iff.mpr ((mem_singleton.mp (hx hj)) ▸ hj)))
lemma vacant (x:Xu)(hv:Polite q ∅ x) : Polite (q₀) ∅ (G x):=by
    obtain ⟨s,hs,hF⟩:=flameStake _ _ _ (Tx) (Fx) (hym q (q₀) R H {()} (Set.mem_univ _)) ∅ x hv (by simp [Fare]); rw [show front (Tx) ∅ =∅ from (by ext i; rw [frontM]; simp)] at hF
    exact ⟨_,hF.symm⟩
lemma polarity (hF:ValidPieces (Keys c N) q Finset.univ x) : pluck A p! x=pluck A Ω (G x):=by
    have he(s:Finset I)(u: Xu) (hp:Polite q s u): pluck A p! u=pluck A Ω (G u):=by
        by_cases hx:s={i}; · subst s; exact (chosenAt N q i u hp).2.symm
        by_cases hv:s=∅; · subst s; rw [show pluck A p! u=0 from hp.spectral _ (fun e=>hx (burstUnique q e.symm))]; exact ((vacant N q i u hp).spectral _ (fun e=> not_nonempty_empty ((burstUnique (q₀) e) ▸ singleton_nonempty _))).symm -- name eq
        rw [show pluck A p! u=0 from hp.spectral _ (fun e=>hx (burstUnique q e.symm)),extinct N q i s u hp (nonempty_iff_ne_empty.mpr hv) hx,map_zero]
    rw [hF.wholeV,map_sum,map_sum,map_sum]; exact sum_congr rfl fun s _=>he s _ (choseTuft ..)
variable (hY:Y.Beat N o q t)(hΩ:∀ U, Summable fun i=>‖Y.mark i U‖)
local notation "Tv"=> twig N i Y
local notation "K"=> twigT N q i Y
variable (F:Patron.Rail c N D')(hG: ∀ U, Summable fun i=>‖F.warp i U‖)(U:Grid c)
include hY hΩ hG
lemma filings : G (Film.reports N Y F t U)= Film.reports N K F t U:=by
   let X:=Film.addressSets N Y F; let f(x):=Film.spruced N Y F x U; let v:= G; let X':=Film.addressSets N K F; let g(x):= Film.spruced N K F x U; let q:= RG.flags t U
   let P₀: Tv→ Patio (A⊕Spine Unit):=fun j=>v (Y.mark j.val U); let h(k):= rootR (Spine Unit) (Keys c N) (F.warp k U); let h_ρ(k):= rootR (Spine I) (Keys c N) (F.warp k U)
   have hx:= Film.payable (rootR (Spine I) (Keys c N)).toLinearMap.toContinuousLinearMap (hG U); have ht: Summable fun i=>‖f i‖:=Summable.sum _ hx (hΩ U); have hu:Summable fun i=>‖g i‖:=Summable.sum _ (Film.payable (rootR (Spine Unit) (Keys c N)).toLinearMap.toContinuousLinearMap (hG U)) ((Film.payable v.toLinearMap.toContinuousLinearMap (hΩ U)).comp_injective (i:=fun i:Tv=> i.val) Subtype.val_injective);
   have hp: v ∘ f= Sum.elim h (v ∘ (fun i=>Y.mark i U)) :=by funext i; rcases i with i|i; exact shoves N _ ..; rfl
   unfold Film.reports; rw [show v (∑' i,Plate.roof X f q i)=_ from Film.stamps X f q v ht, catalogue X (v∘f) q (Film.payable v.toLinearMap.toContinuousLinearMap ht), show (∑' i,Plate.roof X' g q i)=_ from catalogue X' g q hu]; apply congr_arg (fun x:Cove.Hat c → Patio (A⊕Spine Unit)=> ∑' i,Plate.roof id x q i); funext D; rw [hp]; change coin _ _ D=coin X' (Sum.elim h P₀) D
   have hS: Summable fun i=>‖h i‖:=Film.payable (rootR (Spine Unit) (Keys c N)).toLinearMap.toContinuousLinearMap (hG U); have hP: Summable fun i=>‖P₀ i‖:=hu.comp_injective (i:=Sum.inr (α:=D')) Sum.inr_injective
   change Plate.coin (Sum.elim _ _) _ _=Plate.coin (Sum.elim _ _) _ _; rw [Film.coin_merge, Film.coin_merge]; rotate_left; exact hS; exact hP; exact hS; exact Film.payable v.toLinearMap.toContinuousLinearMap (hΩ U) -- order inspect
   apply congr_arg; rw [fingerprint,fingerprint]; let f i:= if Y.addr i=D then v (Y.mark i U) else 0; have hb: Function.support f⊆ {a:E | Y.z a={i}}:=by
        intro j hj; change f j≠0 at hj; by_cases he:Y.addr j=D; swap; · exact (hj (if_neg he)).elim
        unfold f at hj; rw [if_pos he] at hj; exact (show Y.z j={i} from not_not.mp fun hz=> hj (extinct N _ i (Y.z j) _ (hY.budget j U).1 (hY.commits j) hz))
   exact (tsum_subtype_eq_of_support_subset hb).symm
end ProfileL
end YM.MassiveQCD.Sample
#print axioms YM.MassiveQCD.Sample.ProfileL.filings
