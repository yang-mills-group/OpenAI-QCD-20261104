import YM.QCD.Agate.Pour
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Agate
open Land Lattice Wilson Grass Lat NormedSpace Function MeasureTheory Filter RP Kit Finset RG Push.GridApprox
open scoped BigOperators Matrix.Norms.L2Operator Matrix Topology ComplexOrder Classical
variable {n c f G K L: Side}{F i j:ℕ}{β t:ℝ} {W:KernelChoices}
open Tide Flume YM.Next.Free
variable {D Y:Lot} {p:Site c}
noncomputable def rimH (D:Lot)(P:Patch):Lot := D.biUnion fun x=> (box (fuel P)).image (fun z=>z+P.L.val • x)
lemma punch (L:Patch)(x:Court D)(z:Cover)(hp:z ∈ box (fuel L)):z+L.L.val • x.val ∈ rimH D L:= mem_biUnion.mpr ⟨x,x.property,mem_image.mpr ⟨z,hp,rfl⟩⟩
lemma embeddedH (r:Ratio c f)(x:Cover): r.embed (leap p x)=leap (r.embed p) (r.count.val • x):=by unfold leap; rw [← r.root_embed,r.root.map_add, r.root_embed,r.embed_wrap]; rfl
lemma visitsB {r : ℕ} (w : Walk) (x : Cover) (h : x∈box r) :
    ∀ y ∈ visits x w, y∈box (r+w.length) := by
  induction w generalizing r x with
  | nil => simpa only [List.length_nil,Nat.add_zero,visits,List.mem_singleton,forall_eq] using h
  | cons d w ih =>
    have he : x+d.vec ∈ box (r+1) := by
      obtain ⟨hh,hH⟩ := box_test.mp h
      have ht (i : Axis) : -1 ≤ (d.vec : Cover) i ∧ (d.vec : Cover) i ≤ 1 := by
        unfold Step.vec; split <;> simp only [Pi.neg_apply, step_apply] <;> split <;> decide
      rw [box_test]; constructor <;> intro i <;> rw [Pi.add_apply] <;> have := ht i
      · have := hh i; omega
      have := hH i; omega
    intro y hy
    rcases List.mem_cons.mp hy with e|e
    · subst y; exact box_larger h (by omega)
    refine box_larger (ih (x+d.vec) he _ e) ?_
    simp; omega

variable (P:Flight i j)(h:f.val=c.val*P.L.val)(Q:Site G)(H:K.val=G.val*P.L.val)
variable (hP:Fits c D)(hQ:Fits G D) {U:Grid f}{V:Grid K}
variable (hw:crest (D:=rimH D P.patch) ((sliceL P h).embed p) U= crest ((sliceL P H).embed Q) V)
include hw hP hQ
lemma know (x:Court D):Agrees (Lattice.box (fuel P.patch)) (expandAt ((sliceL P h).embed (pins hP p x)) U) (expandAt ((sliceL P H).embed (pins hQ Q x)) V):=by
   rintro ⟨y,i⟩ hy hz; have he:=(pipe_view _ _).mp (show inspects (D:=rimH D P.patch) (expandAt ((sliceL P h).embed p) U)=inspects (expandAt ((sliceL P H).embed Q) V) from by
      exact hw)
   let a:=P.L.val • x.val; have h1:=punch P.patch x y hy; have h2:=punch P.patch x (y+step i) hz; change y+step i+a∈_ at h2; rw [add_right_comm y] at h2; have hK:=he (y+a,i) h1 h2
   change U ((wrap f) y+(sliceL P h).embed (leap p x.val), i)=V ((wrap K) y + (sliceL P H).embed (leap Q x.val),i); rw [embeddedH,embeddedH]; apply Eq.trans _ (Eq.trans hK _)
   · dsimp only [leap,expandAt,sliceL] ; rw [map_add,add_assoc]
   dsimp only [leap,expandAt,sliceL]; rw [map_add,add_assoc]
lemma tripping (x:Court D):Agrees (Lattice.box (Push.GridApprox.reach P.patch)) (expandAt ((sliceL P h).embed (pins hP p x)) U) (expandAt ((sliceL P H).embed (pins hQ Q x)) V) := fun i hi hk => know P h Q H hP hQ hw x i (box_larger hi (by unfold Push.GridApprox.reach fuel; omega)) (box_larger hk (by unfold fuel Push.GridApprox.reach; omega))
lemma sporty (u:Court D→ P.patch.FrameTag)(hp:P.patch.Branches W su)(x:Court D):
       (P.visit W h).frames U (capH (P.visit W h) hP p u) (pins hP p x)= (P.visit W H).frames V (capH (P.visit W H) hQ Q u) (pins hQ Q x) ∧ perSite (P.visit W h) U (pins hP p x) (u x)=perSite (P.visit W H) V (pins hQ Q x) (u x) :=by
   rw [StepData.frames,cappie,StepData.frames,cappie]; exact patch_dep P.patch hp (u x) (tripping P h Q H hP hQ hw x)
lemma striving (u: Court D→ P.patch.FrameTag)(hp:P.patch.Branches W su)(e:Pipe D): (P.visit W h).connector U (capH (P.visit W h) hP p u) (strike p e)=(P.visit W H).connector V (capH (P.visit W H) hQ Q u) (strike Q e):=by
   let i:= inlet e; have h₁:=sporty P h Q H hP hQ hw u hp i; have h₂:=sporty P h Q H hP hQ hw u hp (drain e)
   have hv (x:P.patch.Points): travel (expandAt ((sliceL P h).embed (leap p i.val)) U) x.val (List.replicate P.L.val (posDir (way e))) = travel (expandAt ((sliceL P H).embed (leap Q i.val)) V) x.val (List.replicate P.L.val (posDir (way e))) :=by
       apply travel_local; have he:=know P h Q H hP hQ hw i; intro j hi hj; have hh(y)(hy:y ∈ visits x.val (List.replicate P.L.val (posDir (way e)))): y∈box (fuel P.patch):=by
           refine box_larger (visitsB _ _ x.2 y hy) ?_; rw [List.length_replicate]; unfold fuel; have hp: P.L.val≤ P.patch.radius:=le_mul_of_one_le_left P.L.property.le (by omega); omega
       exact he j (hh _ hi) (hh _ hj)
   funext x; unfold StepData.connector; rw [← drainH,← drainH,show (P.visit W h).frames _ _ (strike p e).1 = _ from h₁.1, show (P.visit W h).frames _ _ (leap p (drain e).val)= _ from h₂.1]; exact congr_arg (fun i=> (P.visit W H).frames V (capH (P.visit W H) hQ Q u) (strike Q e).1 x * i * ((P.visit W H).frames V (capH (P.visit W H) hQ Q u) (pins hQ Q (drain e)) x)⁻¹) (hv x)
lemma props (hp:P.patch.Branches W su)(s:Trace D→ℂ) : united (P.visit W h) β hP p s U= united (P.visit W H) β hQ Q s V:=by
   unfold united; apply sum_congr rfl; intro i _; simp_rw [(fun j: Court D=> (sporty P h Q H hP hQ hw i hp j).2)] -- syntax
   refine congr_arg (fun A=> (∏ j:Court D,(↑(perSite (P.visit W H) V (pins hQ Q j) (i j)):ℂ))* A) ?_; unfold pram; apply integral_congr_ae; apply ae_of_all; intro x; dsimp only; apply congr_arg (· * s x); apply prod_congr rfl; intro e _; let t:= capH (P.visit W h) hP p i; let z:=capH (P.visit W H) hQ Q i; let k:=fun C:P.patch.Connector su=> ((↑(∑ r:P.patch.Points,P.patch.predictorMass W C r * noiseLink (P.visit W h) β (P.patch.predict W C r) (x e)):ℂ)); exact congr_arg k (striving P h Q H hP hQ hw i hp e)
lemma unite (hp:P.patch.Branches W su)(x:Paper D F)(hx:Tide.Stays x):brook (P.visit W h) β (x∘ crest p) U=brook (P.visit W H) β (x∘crest Q) V:=by
    nth_rw 1 [← Grass.write (brook ..)]; nth_rw 1 [← Grass.write (brook (P.visit W H) ..)]; apply sum_congr rfl; intro i _
    have ht: Tide.Stays (fun u=> coef i (x u)):=hx.flows (continuous_coef i)
    congr 1; rw [dink (S:=(P.visit W h)) hp _ (hx.travel ((crestC p).measurable)),dink (S:=(P.visit W H)) hp _ (hx.travel ((crestC Q).measurable))]; let g:=fun u=> coef i (x u)
    change Push.GridApprox.back (P.visit W h) β (g ∘ crest p) U=Push.GridApprox.back (P.visit W H) β (g∘ crest Q) V; rw [cup hP g ht U hp,cup hQ g ht V hp]; exact props P h Q H hP hQ hw hp g
end YM.QCD.Agate
