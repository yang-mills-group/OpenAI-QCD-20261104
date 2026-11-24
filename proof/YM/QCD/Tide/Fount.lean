import YM.QCD.Tide.Iron
import YM.Push.STATIONARY_UNIFORM.FrameScore
import YM.QCD.Step.Breath
import YM.QCD.Jets.Slide
import YM.Next.FREE_KERNELS.Dispatch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Tide
open Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox Jets
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {A B C:Type*}[Fintype A][Fintype B][Fintype C] {n c f : Side} {F : ℕ} {β:ℝ} {R:Cells.Cut c} {r:Ratio c f}
open Flume YM.Next.Free
variable {i j:ℕ} (P:Flight i j)(K:KernelChoices)(hf:f.val=c.val*P.L.val)
local notation "J"=> P.patch
noncomputable def fuel (P:Patch):=20*P.radius
lemma trains: Kit.Reads (fun i : Modes c F=> (sliceL P hf).embed i.1.1) (fun i: Modes f F=>i.1.1) (fuel J) (ater P hf) :=by
   let r:= sliceL P hf
   have hu:Kit.Reads (perch r) eye (fuel J) (tied P hf 0):=by
       unfold tied lineF; refine Kit.Reads.coin (Kit.Reads.coin (Kit.Reads.collect fun a=>Kit.Reads.collect fun j=> Kit.Reads.coin (Kit.Reads.dilate ((scooping r).across (membership 0 _)) ?_) _) _) _
       rw [zero_add]; have h: (route 0 j.val a).length ≤ 8*Patch.radius J:= Push.Uniform.routeLe P.patch P.patch.center j a; unfold fuel; omega
   constructor
   · intro i j h U; unfold ater choir; rw [Matrix.blockDiagonal_apply]; split; · exact hu.absent _ _ h U
     rfl
   intro i j U V h; change ater _ _ U _ _=ater _ _ V _ _; unfold ater choir; simp only [Matrix.blockDiagonal_apply]; split
   next=> exact hu.sees _ _ U V h
   rfl
lemma mind (x:Site f)(p:ℕ): Kit.view x p⊆window x p:=by
   intro y h; have h: separation x y≤p:=h; rw [separation_comm] at h; let z:=y-x
   refine ⟨lift z,?_,?_⟩
   · rw [Finset.mem_coe,box_test]; constructor <;> intro i <;> have H:=(show (lift z i).natAbs ≤ p from (component_le ..).trans h) <;> omega
   simp only [wrap_lift]; unfold z; abel
noncomputable def nose (X:Set (Site c))(F:ℕ): Deck X F ↪ Modes c F := ⟨setDay X,fun i j h=> Prod.ext (Prod.ext (Subtype.ext (congr_arg (fun i=>i.1.1) h)) (congr_arg (fun i=>i.1.2) h)) (congr_arg (fun i=>i.2) h)⟩
noncomputable def offer (P:Flight i j)(K:KernelChoices)(hf:f.val=c.val*P.L.val)(β:ℝ)(x:Stud c F)(U:Grid f):= furnace (ater P hf U) (brook (P.visit K hf) β x U)
variable {K}
lemma offerL (h:P.patch.Branches K su)(x: Stud c F)(he:Stays x)(X:Set (Site c))(Y:Set (Site f))(hp:Uses X x)(hu:∀ i∈X,window ((sliceL P hf).embed i) (fuel J) ⊆ Y):Uses Y (offer P K hf β x):=by
    let Z:=brook (P.visit K hf) β x; let L:= nose X F; let M:=nose Y F
    have ht : LocalOn Y Z:= deltaL (S:=P.visit K hf) h X x he hp.1 Y (by
         intro i hi j hj; obtain ⟨z,hz,rfl⟩:=hj
         exact hu _ hi ⟨z,(show z ∈ box _ from box_larger (show z∈box _ from hz) (show Push.GridApprox.reach J ≤ fuel J by unfold Push.GridApprox.reach fuel; omega)),rfl⟩)
    have hr:= trains P hf (F:=F); let R:=ater P hf (F:=F); have hw(i:Deck X F)(j):LocalOn Y (fun U=>R U (L i) j):=fun U V he=>hr.sees _ _ U V (agrees_mono he (Set.Subset.trans (mind ..) (hu _ i.1.1.property)))
    have hv(i:Deck X F)(j: Modes f F)(U:Grid f)(hx:R U (L i) j≠ 0):j∈ Set.range M:=by
         have hz:j.1.1∈Y:= hu _ i.1.1.property ((mind ((sliceL P hf).embed i.1.1.val) (fuel P.patch)) (not_not.mp fun h=> hx (hr.absent (L i) j h U)))
         exact ⟨((⟨j.1.1,hz⟩,j.1.2),j.2),rfl⟩
    have ho(U:Grid f): ∃ q,Z U=pass L q:=hold h _ x he hp U
    constructor
    · intro U V H; change furnace _ (Z U)=furnace _ (Z V); rw [ht U V H]; obtain ⟨q,hq⟩:=ho V; rw [hq]; exact rowed L (fun i=> funext fun j=> hw i j U V H) _
    intro U; obtain ⟨q,hq⟩:= ho U; change inSlot Y (furnace _ (Z U)); rw [hq]; exact ⟨_,excite L M (fun i j=> hv i j U) q⟩
lemma article :Continuous (fun u:Matrix (Modes c F) (Modes f F) ℂ × Fields c F=> furnace u.1 u.2):=by
    simp_rw [← mingler]; have hc : Continuous (near (Modes c F) (Modes f F)):= (near _ _).toLinearMap.continuous_of_finiteDimensional
    unfold foam; fun_prop
lemma resident {X:Type*} [MeasurableSpace X][TopologicalSpace X][BorelSpace X][CompactSpace X][SecondCountableTopology X](Z:X × Alg A→Alg B)(Y:X→Alg A)(h: Continuous Z)(H:Stays Y): Stays (fun i=> Z (i,Y i)):=by
    obtain ⟨C,hC⟩:=H.bounded; let G:= Metric.closedBall (0: Alg A) C
    obtain ⟨u,hu⟩:= (((isCompact_univ.prod (isCompact_closedBall (0: Alg A) C)).image h).image continuous_norm).bddAbove
    exact ⟨h.measurable.comp (measurable_id.prodMk H.mes),u,fun i=>hu ⟨_,⟨(i,Y i),⟨Set.mem_univ i, Metric.mem_closedBall.mpr (by simpa using hC i)⟩,rfl⟩,rfl⟩⟩
lemma grew: Continuous (ater P hf (F:=F)):= (choir_cont F).comp (Pine.tied_cont _ _ _)
lemma comics (M: Grid f→ Matrix (Modes c F) (Modes f F) ℂ)(h:Continuous M): Continuous (fun i:Grid f×Fields c F=> furnace (M i.1) i.2):=by
    have hp:Continuous (fun i:Grid f×Fields c F=>(M i.1, i.2)):= (h.comp continuous_fst).prodMk continuous_snd
    change Continuous ((fun u:Matrix (Modes c F) (Modes f F) ℂ × Fields c F=> furnace u.1 u.2) ∘ (fun i:Grid f × Fields c F=>(M i.1,i.2)))
    exact (article (F:=F) (c:=c) (f:=f)).comp hp
lemma offers (h:P.patch.Branches K su)(x:Stud c F)(hp:Stays x): Stays (offer P K hf β x):=by
    let M:=ater P hf (F:=F); have hc:Continuous M:= grew P hf; let Z:= brook (P.visit K hf) β x
    let T:=fun i: Grid f×Fields c F=> furnace (M i.1) i.2
    have hT:Continuous T:= comics M hc
    have ht:Stays Z:= brain (S:=P.visit K hf) h _ hp β
    change Stays (fun i => T (i,Z i)); exact resident T Z hT ht
lemma acrossH (h:P.patch.Branches K su)(X Y:Set (Site c))(x y :Stud c F)(hx:Stays x)(hy:Stays y)(H:Uses X x)(W:Uses Y y)(he:Disjoint X Y): offer P K hf β (x*y)=offer P K hf β x * offer P K hf β y:=by
    funext U; unfold offer; let Z:=P.visit K hf
    rw [urban (S:=Z) h X Y x y hx hy H.1 W.1 he U,Pi.mul_apply]
    obtain ⟨v,hv⟩:= hold (S:=Z) (β:=β) h _ x hx H U; obtain ⟨u,hu⟩:= hold (S:=Z) (β:=β) h _ y hy W U
    change brook (P.visit K hf) β x U=_ at hv; change brook (P.visit K hf) β y U=_ at hu
    rw [hv,hu]; exact conjures (nose X F) (nose Y F) (fun i j h=> Set.disjoint_left.mp he i.1.1.property (by rw [show i.1.1.val=j.1.1.val from congr_arg (fun i=>i.1.1) h]; exact j.1.1.property)) v u _
lemma rolly (h:P.patch.Branches K su)(x:Stud c F)(hx:Stays x)(hp:Neutral x):Neutral (offer P K hf β x):=by
    intro k U; unfold offer ater; rw [gauges, Kit.choir_mul,Kit.choir_mul, replicas (star _) _,copies_star]
    let V:= k∘(sliceL P hf).embed; let S':= P.visit K hf; let T:= fun U=> brook S' β x U
    change disguise (rotates _ k) (furnace (rotates _ V*_ * star (rotates _ k)) (T _))= _; rw [roofed _ _ (rotates_law _ V) (rotates_law _ k)]; exact congr_arg _ (flowH (S:=P.visit K hf) h _ hx hp _ k)
end YM.QCD.Tide
