import YM.QCD.King.Fable
/-! # quoting H.sail derivatives uniformly on each Unit. -/
set_option autoImplicit false
noncomputable section
section
namespace YM.QCD.Kings
open Finset RG Filter Function Lattice ConnectedActivityE6 Blaze Coat
open scoped BigOperators ContDiff Matrix.Norms.Frobenius
open Lat Loom Fleet Brush
variable {c:Side}{V : Type}[NormedAddCommGroup V][NormedSpace ℝ V]{U:V→Grid c} {x:V}{k:ℕ}{p:ℝ}
lemma rColor (h:Mode U x k p)(i:Edge (Site c))(l j: Hue): Brush k (royalty su) p (fun y=> Lat.colour (U y i) l j) x:=by
    let P:su.Mat→ₗ[ℝ]ℂ:={toFun:= fun v=> Fork.colourRead v l j,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
    let Vq : su.Mat →L[ℝ] ℂ:=LinearMap.toContinuousLinearMap P; have hp := Vq.opNorm_le_bound zero_le_one (by intro v; rw [one_mul]; exact Fork.frob_entry v l j)
    have hv := (h.atLink i).report _ hp; rw [one_mul] at hv; exact hv
end YM.QCD.Kings
end
namespace YM.QCD.Kings
open Finset RG Filter Function Lattice Wilson ConnectedActivityE6 Blaze Coat Metric
open Fork Lat Loom Fleet Kit Port Jets Run Brush Tidings Cove Sun
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator Classical ContDiff
variable {c:Side}{V : Type}[NormedAddCommGroup V][NormedSpace ℝ V]{U:V → Grid c} {x:V}{k b B n:ℕ}{p a η w W:ℝ}
noncomputable def opBox : (Fin 3→Fin 3→ ℂ) →L[ℝ] Mat:= LinearMap.toContinuousLinearMap (show (Fin 3→ Fin 3→ℂ) →ₗ[ℝ] Mat from LinearMap.id)
def massQ :ℝ:= ‖opBox‖*(royalty su)
lemma retro (h:Mode U x k p):Brush k (massQ+massQ) p (Kit.settled∘U) x:=by
    have hP :0 ≤ royalty su:= zero_le_one.trans (royalty_ge su)
    have hf i : Brush k massQ p (fun y=>colour (U y i)) x:=by
       have hz :Brush k (royalty su) p (fun y (a b:Fin 3)=> colour (U y i) a b) x:=fold h.pos hP (fun a=>fold h.pos hP fun b=>rColor h i a b)
       exact hz.report opBox le_rfl
    have hv :0 ≤ massQ:=mul_nonneg (norm_nonneg opBox) hP
    let S := (starL ℝ : Mat≃L[ℝ]Mat).toContinuousLinearMap
    have hr: ‖S‖≤1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro i; change ‖star i‖≤_; rw [norm_star,one_mul])
    refine pair (fold h.pos hv hf) (fold h.pos hv (fun i=> ?_)); have hh:= (hf i).report _ hr; rw [one_mul] at hh; exact hh
variable {H:St c}{G:Land c (Site c) (Site c)}{Y:Pays c (Site c) (Site c)}
lemma fare_mat (h:Pack id id η p b H a G Y)(V:Kit.Pulse c)(hp:V∈ Kingdom c η)(Z:Grid c)(ht:0<η)(B N:ℕ)(x:Gaze c)(he:0 < w):
    let Q:= batch (singleR c) G x.1 x.2 B V-sheetP G B x Z
    ‖wearK c N w (paleF N (-Q))‖ ≤ gala Y x B N w :=by
     intro Q; change Creek.load _ (Grass.form (Lat.copies N (-Q))) ≤ _; apply (fauna (Lat.copies N (-Q)) he).trans
     unfold gala; rw [sum_add_distrib]; refine farm Q x.1 _ _ (fun i=>mul_nonneg zero_le_two (cups h ..).1) (fun i=> mul_nonneg zero_le_two (cups h ..).1) ?_
     intro i j
     let R (a b:Site c):= chipK x.1 B G a b x.2; let g a b:= R a b V-R a b (Kit.settled Z); let v a b:=2*Port.crease x.1 B Y a b x.2
     have hv (i j:Site c): ‖g i j‖≤ v i j:= (norm_sub_le ..).trans ((add_le_add ((cups h ..).2.2.2.1 _ hp) ((cups h ..).2.2.2.1 _ (citizenship c ht Z))).trans_eq (two_mul ..).symm)
     have hs(T: Pulse c):Run.cell (batch (singleR c) G x.1 x.2 B T) i j=sale x.1 i j (R i j T):=by rw [stack,monotype]
     change ‖Run.cell (batch (singleR c) G x.1 x.2 B V) i j-Run.cell (batch (singleR c) G x.1 x.2 B (Kit.settled Z)) i j‖≤_
     rw [hs V, hs (Kit.settled Z),show sale x.1 _ _ (R i j V)- sale _ _ _ (R i j (Kit.settled Z))= sale x.1 i j (g i j) from (smul_sub ..).symm]
     split
     next he'=> subst i; split; exact ((sold ..).trans (hv ..)).trans (le_add_of_nonneg_right ((norm_nonneg _).trans (hv ..))); rw [add_zero]; exact (sold ..).trans (hv ..)
     next he'=> split
                next hy=> subst j; rw [zero_add]; exact (sold ..).trans (hv ..)
                next hy=> unfold sale; rw [if_neg (Ne.symm he'),if_neg (Ne.symm hy)]; simp
-- advance charge on unsmeared rays. add league factor ratio width etc.
lemma circus (h:Pack id id η p b H a G Y)(ht:0 < η)(B N:ℕ)(ρ:Gaze c){f:Side}(F:Ratio c f)(V:Grid f)(he:0 < w)(hy:Mode U x k W): Brush k (k.factorial*(letterP η k*gala Y ρ B N w)) ((1+(massQ+massQ))*W)
     (fun i=> wearK c N w (dropG N G F B ρ V (U i))) x :=by
    let g y:= batch (singleR c) G ρ.1 ρ.2 B y; let f0 y:= -(g y-sheetP G B ρ (lowC F V)); let K:Sheet c→ EvenA c N:=paleF N
    let K':=LinearMap.toContinuousLinearMap (wearK c N w).toLinearMap; let Z: Kit.Pulse c → EvenA c N:= K' ∘ (K ∘ f0); let U':=Kit.settled ∘ U
    have hp:Set.MapsTo U' Set.univ (Kingdom c η):=fun i _=> citizenship _ ht _
    have he':ball (U' x) η⊆ Kingdom c η:=fun i hi=> Set.mem_iUnion.mpr ⟨_, hi⟩
    have hD :∀ i∈ball (U' x) η, DifferentiableAt ℂ Z i:=by
       intro i hi; refine K'.differentiableAt.comp _ ((Stew.nozzle c N).differentiableAt.comp i (f:=f0) ((DifferentiableAt.sub_const ?_ _).neg)); unfold g; -- via Run.bear
       apply (Run.bear (D:=Site c) (E:=Site c)).differentiableAt.comp (f:=fun Z=>fun i j=> sale ρ.1 i j (chipK ((singleR c).embed ρ.1) B G i j ρ.2 Z)) i
       exact differentiableAt_pi.mpr fun a=>differentiableAt_pi.mpr fun b=> ((cups h _ _ _ _ _).2.2.1 i (he' hi)).const_smul (_:ℂ)
    have hz:= Brush.pine (retro hy) (beau ht hD (fun i hi=>fare_mat h i (he' hi) (lowC F V) ht B N ρ he) _)
    exact hz
end YM.QCD.Kings
