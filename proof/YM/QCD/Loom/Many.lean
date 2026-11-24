import YM.QCD.Loom.Fiber

/-! # Full integration dictionary to output at actual densities. Includes all spectator effects. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Loom
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees Beam Beam.Pipe Cove Leaf Lat Creek
open Leaf Jets Fj Further.ShellBirth49.Fusing Collide Jets.Touch Fleet
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine Grass
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{P:Teller su}{δ β b τ μ W C:ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l n i j k:ℕ}
variable {κ γ γ' u z t θ a o' v:ℝ}{M:Rep su f}{S:StepData c f}{T:Tube su S}{L:Side}{F:Tree.Forest S.ratio}{H':Cash W τ μ L Q o C T M}
variable {D E J:Type}
open Footprint
lemma sumRide (x:D→Site f)(w:D→ℝ)(d:D→ℕ)(hp:Anchored x w d a u)(h:0≤w)(hv:0≤a): Summable w:=by
    let V (s:Site f) i:= if x i=s then w i*Real.exp (a*d i) else (0:ℝ)
    have hP (s:Site f) : Summable (V s) := (hp s).2.1
    refine Summable.of_nonneg_of_le h (f:=fun i=>∑ s:Site f,V s i) ?_ (summable_sum (s:=(univ: Finset (Site f))) fun i _=> hP i)
    intro i; simp only [V,sum_ite_eq,mem_univ,if_true]; exact le_mul_of_one_le_right (h _) (Real.one_le_exp (by positivity))
lemma fishes (s: D→Support f)(w:D→ℝ)(h:Ac.Hit s n w a u)(hv:0≤w)(he:0≤a)(hk:∀ i,w i ≠0→ (s i).Nonempty): Summable w:=by
    let v (f:Site f) i:= if f∈s i then w i*currency n a (s i) else 0
    refine Summable.of_nonneg_of_le hv (f:=fun i=> ∑ s: Site f,v s i) ?_ (summable_sum (s:=univ) fun i _=> (h i).2.1)
    intro i; by_cases ht:w i=0; · simp [ht,v]
    obtain ⟨x,hx⟩:=hk i ht; have hh : w i ≤ v x i:=by unfold v; rw [if_pos hx]; exact le_mul_of_one_le_right (hv i) (Real.one_le_exp (by positivity))
    exact hh.trans (single_le_sum (fun i hi=>(h i).1 _) (mem_univ x))
lemma grassE (r:Rise f N E J){g:E→ℝ}{p:J→ℝ}(h1:Cents r g p t θ)(hF:Fill r g p u u o' κ z n)(hv:1≤o')(hp:1≤t) :∀ X, Placid r θ X:=by
    have hG:=sumRide _ _ _ hF.χ h1.pos hF.bud; let a i:=(r.front i).inv.card; let v i:=p i*o'^(a i); have hh i:p i≤ v i:= le_mul_of_one_le_right (h1.non i) (one_le_pow₀ hv)
    have hS:Summable p:= Summable.of_nonneg_of_le h1.non hh (fishes _ v hF.ε (fun i=> (h1.non i).trans (hh i)) hF.bud (fun i _=> (r.front i).alive.mono (r.front i).part))
    intro X; refine ⟨Summable.of_norm_bounded hG (fun i=> (tore _ hp).trans (h1.cost i _)),?_ , Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> (tore _ hp).trans (h1.funds i _)) hS⟩
    refine Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> ((tore _ hp).trans (bought (fun _=> t) _ _ (h1.cost i X))).trans ?_) (hG.mul_left (Real.exp z))
    have he:=Real.add_one_le_exp (-g i); rw [Real.exp_neg] at he; have hC:= mul_le_mul_of_nonneg_right he (Real.exp_pos (g i)).le; rw [add_mul,inv_mul_cancel₀ (Real.exp_ne_zero (g i))] at hC
    have hx:= mul_le_mul_of_nonneg_left (Real.exp_monotone (anchored_each _ _ _ hF.χ hF.bud h1.pos i)) (h1.pos i); linarith
lemma sizeA (Y:Pipe H' F (EvenA c N) D) {w:D→ℝ}{b':Costs}(hx:Summable w)(h:Y.Depth b' w (fun _=>0))(X:Coat T F)(hp: Y.Viable)(hh:X.x=τ)(hw:X.width=o.K)(ht:1≤v)(hr:∀ i, ‖token c N v (Y.shootsP X i)‖ ≤∏ j∈i,Y.dues b' w j) : Summable (Y.heldP X):=by
    let w':=Y.dues b' w
    have he : Summable w':= Summable.sum _ (Summable.sum _ (hasSum_fintype _).summable (budgets_arr H')) hx -- w'.inl=in universe all; check
    refine Summable.of_norm_bounded (summable_finsetProd_of_summable_nonneg (fun i=>(Y.digits h i).1) he) ?_
    intro i; let p := Ac.Parts Y.gP i
    have hE : Y.legal p := ⟨fun j hj=> (Ac.lives Y.gP i hj).2,Ac.separate ..⟩
    have hQ:p.biUnion id=i:= Ac.reconstruct ..
    change ‖Y.heldP X i‖ ≤ ∏ j∈i,w' j; rw [← hQ,Y.shackledP hp X hh hw p hE, prod_biUnion (Y.diverse hE)]
    unfold drawP; split
    next H=> exact (Finset.norm_prod_le _ _).trans (prod_le_prod (fun i _=>norm_nonneg _) fun i _=> (tore _ ht).trans (hr _))
    rw [norm_zero]; exact prod_nonneg fun _ _=>prod_nonneg fun i _=> (Y.digits h i).1
variable (H:Cash W τ μ L Q o C T (trimP T R δ β b))
variable (Z:Rise f N E J)(Y:Send S.ratio N D){β':E→ℝ}{w':J→ℝ}{q:D→ℝ}{X': Fj D E J→Support c}
variable [Fintype D][Countable E][Countable J]
set_option quotPrecheck false
local notation "U"=> deckHue H Y Z X'
lemma applications (hv:0<δ)(hq:Peak Y R.threshold v a z q)(hs:Cents Z β' w' v R.threshold)(he:Z.Wave R.threshold)(ht:Cove.Count Y Z X')(hd:Ac.Hit (U).ground n (mintD H Y Z X' q β' w' z) u κ) (hw:0≤u)(hF:1≤a): Summable (mintD H Y Z X' q β' w' z) ∧ ∀ V, ((U).suitcase F).solves V :=by
    let K:= mintD H Y Z X' q β' w' z
    have hh V (x:Grid f) (i:Wound X'): ‖((U).works i x V)‖ ≤K i:=by
       change ‖_ ^ _ • hue Y Z R.threshold i.1 x‖ ≤ _; rw [norm_smul]; unfold K mintD; rw [Real.norm_of_nonneg (by positivity : 0≤ δ⁻¹^(budget Z i.1))]; exact mul_le_mul_of_nonneg_left ((tore _ hF).trans (pinches Y Z hq hs he x i.property)) (by positivity)
    have hΔ : Summable K:= by
       refine fishes _ _ hd (fun i=> (norm_nonneg _).trans (hh 1 1 i)) hw ?_; intro i hi
       have hv' : leftE i.1≠∅∨spent i.1≠∅:=by_contra (fun he=> hi (by change _* Cove.jewel Y Z _ _ _ _ z i.1=0; unfold Cove.jewel; rw [if_neg (fun h=>he h.2),mul_zero])) -- motive
       let v:=i.1; have hh x:(native Y Z x).image S.ratio.parent ⊆ X' x:= (image_subset_image (halo_subset _ _)).trans (ht.1 x)
       rcases hv' with hx|hx
       · obtain ⟨x,hx⟩:=Finset.nonempty_iff_ne_empty.mpr hx; have he: Sum.inr (Sum.inl x)∈i.1:=mem_toRight.mp (mem_toLeft.mp hx); exact Finset.Nonempty.mono ((hh (.inr (.inl x))).trans (subset_biUnion_of_mem X' he)) (Finset.Nonempty.image (⟨_,(Z.row x).anchor⟩ : (Z.row x).support.Nonempty) S.ratio.parent)
       obtain ⟨x,hx⟩:=Finset.nonempty_iff_ne_empty.mpr hx; have he: Sum.inr (Sum.inr x)∈i.1:= mem_toRight.mp (mem_toRight.mp hx); let v':= Z.front x; exact Finset.Nonempty.mono ((hh (.inr (.inr x))).trans (subset_biUnion_of_mem X' he)) (((v'.alive.mono v'.part)).image _)
    exact ⟨hΔ,fun V=>⟨K,hΔ,fun i x=> hh V x i⟩⟩
lemma legible (A:Fleet H E N)(B:Fleet H D N)(V:Grid c)(h:(A.suitcase F).solves V)(ht:(united A B).Famous) : ((united A B).suitcase F).solves V:=by
    obtain ⟨p,hp,hb⟩:=h; have hh(i:D):= ((Fleet.forwarded F _ ht).price (.inr i) V).cost; choose q hq using hh; exact ⟨Sum.elim p q, Summable.sum _ hp (hasSum_fintype _).summable, fun i x=> by cases i with | inl i=> exact hb i x | inr i=> exact hq i x⟩
end YM.QCD.Loom
