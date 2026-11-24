import Mathlib.Analysis.Convex.Integral
import YM.QCD.Loom.Net
/-! # Warm darkness on real site. -/
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
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}
variable {H:Cash W τ μ L Q o C T (trimP T R δ β b)}{ι D K J:Type}{N:ℕ}
namespace Fleet
def gator (Y:Fleet H ι N):Prop:=∀ i U V,Gated (Y.ground i) (Y.works i U V)
lemma mixT (a:ℝ)(x:EvenA c N)(V:Support c) (h:Gated V x): Gated V (a • x):=by
   unfold Gated; rw [show Cove.light (Keys c N) (a • x)= a • Cove.light (Keys c N) x from map_smul ((Cove.light (Keys c N)).toLinearMap.restrictScalars ℝ) ..]; exact ((region _).toSubmodule.restrictScalars ℝ).smul_mem a h
lemma spruce (V:Support c) : Gated (F:=N) V 0:=by unfold Gated; rw [map_zero]; exact Subalgebra.zero_mem _
lemma entwine (Y:Fleet H ι N)(Z:Fleet H K N)(hY:Y.gator)(hZ: Z.gator): (united Y Z).gator:=by rintro (i|i); exact hY i; exact hZ i
lemma parkGy (X:Coat T F)(P:Fleet H ι N)(h:P.Famous)(he:P.gator) (hx:X.x=τ)(ht:X.width=o.K)(s): Gated ((P.suitcase F).full s) ((P.suitcase F).shootsP X s):=by
   let W:=(P.suitcase F).full s; unfold shootsP; split
   swap; · exact spruce _
   next hs=>
    let C (i):=(Matter.planted X s.toLeft).taggedL i
    let Y:=(P.suitcase F).capacityP s (own s.toLeft)
    have hV:= P.forwarded F h -- orientation arg
    apply mixT; unfold Gated; rw [map_sum]; refine Subalgebra.sum_mem _ fun i _=>?_ ; change Cove.light (Keys c N) (call (C i) Y) ∈ region _
    let Q:= region (limits (F:=N) W); let g (X: EvenA c N):= Cove.light _ X
    let Ψ:= LinearMap.toContinuousLinearMap ((Cove.light (Keys c N)).toLinearMap.restrictScalars ℝ)
    have hp t z: Gated W (Y t z):=by
      apply mixT; exact gate_prod _ _ _ (fun j hj=> gateMon _ _ ((P.suitcase F).leP s hj) _ (Fleet.mixT _ _ _ (he _ _ _)))
    let A:= C i; let g (j:F.Slice su ×Air f su):= Y (A.wrapY j.1) j.2 -- type
    let B:= Q.toSubmodule.restrictScalars ℝ; have hB:IsClosed (B:Set (Alg (Keys c N))):=Submodule.closed_of_finiteDimensional B
    have hv:= envPlot ((P.suitcase F).ripeP (own (toLeft s)) s hV (C i) hx ht (Matter.planted_valid X _)) ((F.order su).prod A.dice)
    change Ψ (∫ i, g i ∂_)∈B; rw [← Ψ.integral_comp_comm hv]; exact B.convex.integral_mem hB (Eventually.of_forall (fun i=> hp (A.wrapY i.1) i.2)) (Ψ.integrable_comp hv) -- inspect
lemma parkFlags (X Z:Coat T F)(P:Fleet H ι N)(h:P.Famous) (hx:X.x=τ)(ht:X.width=o.K)(hy:Z.x=X.x)(hl:Z.width=X.width)(hχ:Z.χ=X.χ)(v) -- edit
  (hv: X.Y= Z.Y)(ha:Agrees ((P.suitcase F).full v) X.V Z.V)
  (hh : (P.suitcase F).full v ∩RG.flags (Pressure.temp X.x) X.V=(P.suitcase F).full v∩RG.flags (Pressure.temp Z.x) Z.V):
    (P.suitcase F).shootsP X v=(P.suitcase F).shootsP Z v:=by
     unfold shootsP; rw [inter_comm _ ((P.suitcase F).full v),hh,inter_comm]; split
     swap; · rfl
     next hE=>
       unfold draws; refine congr_arg choiceS (funext fun i=>?_); let Y:=(P.suitcase F); let s:=Y.full v; let A:=(Matter.planted X v.toLeft).taggedL i; let B:=(Matter.planted Z v.toLeft).taggedL i
       let k:=Matter.own v.toLeft
       refine call_critical H s _ (Y.ripeP k v (P.forwarded F h)) (Y.lullP k v (P.forwarded F h)) A B hx ht (planted_valid X _) (planted_valid Z _) ⟨hy.symm,hl.symm,hχ.symm,?_,fun p _=> ?_,fun _ _=>rfl,fun _ _=>rfl,ha⟩
       · intro j hj; unfold A B; simp only [Matter.planted, Matter.preps,Stores.place,Coat.taggedL,mem_union]; refine or_congr Iff.rfl ?_; have he := Finset.ext_iff.mp hh j; change j ∈ (P.suitcase F).full v at hj; simp only [mem_inter,hj,true_and] at he; exact he
       exact congr_fun hv _
variable {Γ:Land c (Site c) (Site c)}{Y:Pays c (Site c) (Site c)} {η p:ℝ}{i:ℕ}{D₀:St c}
lemma sailed (H:Cash W τ μ L Q o C T (trimP T R δ β b)){C':ℝ}(h:Run.Pack id id η p i D₀ C' Γ Y) (he:0<η): Fleet.gator (sailP H Γ N):=by
    intro z U V; let p':= dropG N Γ S.ratio (radiusB τ) z U V; let G:=sashP z (radiusB τ); let Z:=sailP H Γ N
    apply gate_exp; refine gateMon G (Z.ground z) (subset_trans subset_union_left ((halo_subset ..).trans (halo_subset ..))) p' ?_
    let M:= sheetP Γ (radiusB τ) z V-sheetP Γ (radiusB τ) z (lowC S.ratio U)
    let B:= region (limits (F:=N) G); change form (Lat.copies N (-M))∈B
    refine B.sum_mem (fun a _=> B.sum_mem (fun b _=>?_)); by_cases hp:Lat.copies N (-M) a b=0; · rw [hp,zero_smul]; exact B.zero_mem
    have hh:Run.cell M a.1.1 b.1.1≠0:=by
       intro hh; apply hp; simp only [Lat.copies,Matrix.blockDiagonal_apply,Matrix.neg_apply]; split
       · rw [show M a.1 b.1=0 from congr_fun (congr_fun hh a.1.2) b.1.2,neg_zero]
       · rfl
    let X U:=chipK z.1 (radiusB τ) Γ a.1.1 b.1.1 z.2 (Kit.settled U)
    have hp: X V≠0∨ X (lowC S.ratio U)≠0:=by
      by_contra! hv
      apply hh; unfold M; rw [drawnE]; unfold sale; unfold X at hv; rw [hv.1,hv.2,sub_self,smul_zero]
    have he':= cups h z.1 a.1.1 b.1.1 (radiusB τ) z.2
    have hf Y (h:X Y≠0): a.1.1∈G ∧ b.1.1∈G := he'.2.1 ((norm_pos_iff.mpr h).trans_le (he'.2.2.2.1 _ (Run.citizenship c he Y))|>.ne')
    have ht:= hp.elim (hf V) (hf _)
    exact B.smul_mem (B.mul_mem (Creek.marked (A:=Keys c N) (.inl b) _ (mem_filter.mpr ⟨mem_univ _,ht.2⟩)) (Creek.marked (A:=Keys c N) (.inr a) _ (mem_filter.mpr ⟨mem_univ _,ht.1⟩))) _

section targeted
variable {u:Ratio c f}(E:Rise f N J K)(Y:Send S.ratio N D){A:Fj D J K→Support c} (M:Cash W τ μ L Q o C T (trimP T R δ β b))
lemma huesL [Countable J][Countable K][Fintype D](hp:E.Wave R.threshold) (hb:Cove.Count Y E A):Fleet.gator (deckHue M Y E A):=by
    intro i X W; apply mixT; unfold hue; split
    next ht=>
     refine halo_dye Y E R.threshold _ X hp _ ?_; intro x hx
     obtain ⟨z,hz,rfl⟩:= mem_image.mp hx
     obtain ⟨a,ha,h⟩:=mem_biUnion.mp (show z∈ brimW Y E i.val from by rw [brim_eq]; exact Corona.halo_mono (by omega) (Subset.refl _) hz)
     exact mem_biUnion.mpr ⟨a,ha,hb.budget a (mem_image_of_mem _ h)⟩
    exact spruce _
end targeted
variable {j k:ℕ}{X:St f}{J':Flight j k}{H₀:f.val=c.val*J'.L.val}{O:Plan k}{W' :ℕ→Atom su 2}{v u z q:ℝ}
lemma branch (H :Cash W τ μ L Q o C T (trimP T R δ β b))(C:Swathe J' H₀ X W' O u v η z q i) (hv:0<v)(h:S.ratio=sliceL J' H₀): Fleet.gator (VarnC H C N):=by
    intro i U V; apply gate_exp; let P:= VarnC H C N; let T:= P.ground i
    have he:= Port.beveled C N (radiusB τ) i U hv; apply Creek.regionMon _ he; intro j hj; refine mem_filter.mpr ⟨mem_univ _,?_⟩
    have hf:(sliceL J' H₀).embed (locationP j) ∈ Port.payT (sliceL J' H₀) (radiusB τ) i:= (mem_filter.mp hj).2
    rw [← h] at hf; refine halo_subset _ _ (halo_subset _ _ ?_); rw [← S.ratio.embed_parent (locationP j)]; exact mem_image_of_mem _ hf
end Fleet
end YM.QCD.Loom
