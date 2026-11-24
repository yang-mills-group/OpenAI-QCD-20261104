import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Searchlight
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Manifesto
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Shelter

/-! # A **single gauge patch** on exterior marker cliques, no change of
representations in individual or multiple shoots. This prices the actual
E6 predictor, angular flash & parallel transported curvature sign. No assertion
of global identity to another step. Here one works at the physical `g`
without rescaling apertures. Eliminate any unmasked derivative forecast
claims beyond startup bills. -/
set_option autoImplicit false
noncomputable section
namespace YM.Hypnos
open Filter Function Lattice Wilson Tree RG Pressure Finset MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations Push.SectorMeasure Push.SectorMeasure.Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Coat Blaze.Vine
open Shell Channel

open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Next.SectorChange
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Malachite PhysicalNext.JointLoad.Heir
open Matrix Census Green Mask Pulse Itinerary Matter Poll Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{β τ C μ W:ℝ} {o: ConnectedActivityE6.Target.Order G W}{Q:ConnectedActivityE6.Target G P} {X:S.Choices} {r u t d A M D:ℝ}{F:Tree.Forest S.ratio}{n:ℕ}
-- all carrying.Y assets from same assets.Mask.
section funds
variable (h: ConnectedActivityE6.SliceRows.Stamp T) (H : P.Funds S T)
include h H in
lemma booths : AnalyticBridge.LocalGaussianLaws.Lift.Booth P S T:=by
    obtain ⟨b,v,hD,hR,hS,hS',hA,hA',a,w,hF,x,y,hF'⟩:=h
    exact ⟨H,b,v,a,w,x,y,hF,hF',hA,hA',hS,hS',hD,hR⟩
end funds
-- local.Stores.manifest specifically
variable (X:Coat T F) (Y:Support c)
lemma pact {v : Directions G c} (h : X.V=increment 1 v) {i:Site c}(he : ¬Inside i X.seeds n) :
    Zone X (gem X v) i n:=by
    refine ⟨rfl,rfl,rfl,fun y hy=> ⟨fun h'=> (he ?_).elim,fun h'=> ?_⟩,fun _ _=>rfl,fun _ _=> congr_fun h _,fun _ _=>rfl,fun _ _=>rfl⟩
    · exact halo_spec.mpr ⟨_,h',(separation_comm ..).trans_le hy⟩
    simp [gem,dry,vary, blank,place] at h'
-- use on queries: no seeds in 31B from Y
variable {i:Site c}
lemma planted_safe (j : Molecule S) (hj : j=∅) (he: Disjoint (halo n Y) (RG.flags (temp X.x) X.V)) (hi:i∈Y): ¬Inside i (planted X j).seeds n:=by
    intro hz; obtain ⟨w,hw,hh⟩:=halo_spec.mp hz; apply Finset.disjoint_left.mp he (halo_spec.mpr ⟨_,hi,(separation_comm ..).trans_le hh⟩)
    simpa [place, planted,preps,hj,roster,Packets.store] using hw
-- noise watch obligations from Y: direct use on x at 17B for μ+α; safety at 30B.
def Calm (ξ β:ℝ)(z:Air f G):Prop:= ∀ i∈Y,X.watch i ξ β X.B z
lemma calm_bonds (h: Target.GrantBodies W X.x μ L Q o C T) (hx:X.width=o.K)(hf:X.manifest) {z:Air f G} (hc:Calm X Y o.ξ β z)(hβ:0<β)(q:Bond f)(hq:atEdge S q ∈ Y): ‖gStep β • X.atmos z q‖ ≤ X.t := by
    obtain ⟨_,_,hκ,H⟩:= h.safety; obtain ⟨hμ,H⟩:= H F X rfl hx hf
    have hr:=h.room.fiery
    have he:= X.watch_bonds _ hr o.rare.le hβ (hc _ hq) q (show separation (atEdge S q) (atEdge S q)≤X.B by simp) (hμ q)
    simpa only [liftA,Pi.add_apply,Pi.smul_apply,add_sub_cancel_left] using! (he.1.trans ((le_of_eq (Eq.symm <| mul_assoc _ _ _)).trans (mul_le_of_le_one_left hr.le hκ)))

lemma safe_H (h: Target.GrantBodies W X.x μ L Q o C T) (hx:X.width=o.K)(hf:X.manifest) (hp:ConnectedActivityE6.SliceRows.Stamp T) {z:Air f G} (hc:Calm X Y o.ξ β z)(hβ:0<β)(hy:∀ i∈Y, ¬Inside i X.seeds (30*X.B))(Z:Support f) (he: ∀ q : Cell f, ¬Disjoint (touched q) Z → S.ratio.parent q.1∈Y) {r:ℝ} (ht:X.t/4 ≤ r) :
    Healthy r Z (X.input (X.liftA β z)) := by
    apply Finset.disjoint_left.mpr; intro j hj hz; obtain ⟨p,hp',hf'⟩:= (flags_spec ..).mp hz
    have hJ:= he p (fun hh=> Finset.disjoint_left.mp hh hp' hj)
    have hπ := ((h.safety.2.2.2 F X rfl hx hf).2 hp _ (hy _ hJ) _ hβ z (hc _ hJ)).2.1 p rfl
    exact (hπ.trans_le ht).not_gt hf'
-- forecast replacement taking common noise
abbrev deposit (b : Directions G c) := expandBare F X.x (study X b-forecast T X.x F X.k b)
def growSeed (z:Air f G) : Directions G f:= fun i=> if i∈F.trunks then 0 else X.atmos z i
def cropSeed (z:Air f G) : Directions G f := fun i=> if S.ratio.parent i.1∈Y then growSeed X z i else 0
def stam (β:ℝ) (v:Directions G c) (z:Air f G): Deck G c f := (v,gStep β • cropSeed X Y z+deposit X v)
lemma concurs {v:Directions G c} (z:Air f G) (hV:X.V=increment 1 v)(h:X.manifest) (p:Room P S T X.x)(he:∀ i∈Y,¬Inside i X.seeds (30*X.B))
    (q:Bond f) (hq:atEdge S q∈Y)(β:ℝ): X.input (X.liftA β z) q=sounds T F X.x X.k false (stam X Y β v z) q:=by
    have h0:=pact X hV (he _ hq); unfold sounds JointLoad.Heir.touch; dsimp only [chord, Prod.fst,Prod.snd,stam]
    rw [show φ T F false=0 from rfl]; simp only [_root_.zero_apply,Pi.zero_apply,G.mat_lieExp_zero,inv_one,one_mul,mul_one]
    rw [show expandBare F X.x (forecast T X.x F X.k v) q+(gStep β • cropSeed X Y z + deposit X v) q=gStep β • cropSeed X Y z q+expandBare F X.x (study X v) q by rw [Pi.add_apply,Pi.smul_apply,deposit,map_sub,Pi.sub_apply]; abel]
    by_cases H:q∈F.trunks
    · rw [(X.sliced _) _ H,show cropSeed X Y z q=0 by unfold cropSeed growSeed; change S.ratio.parent q.1∈Y at hq; simp [H,hq],smul_zero]
      rw [show expandBare F X.x (study X v) q=0 from dif_neg (not_not.mpr H),add_zero,G.mat_lieExp_zero,one_mul,linearCopy,if_pos (F.trunk_internal H),G.mat_lieExp_zero];
    let q':Tree.Forest.Free F:= ⟨q,H⟩; let i : PhysicalNext.JointLoad.Heir.clear S X.x F:= ⟨q',notChilled S F X.x _⟩
    have hZ : X.Hot q:= (h0.tides q (by unfold distAt; rw [separation_self]; have hs:100≤X.B:=p.sight.1; omega)).mpr ((X.no_flat q).2 H)
    rw [X.viewing _ _ hZ,shine X p h,increment, hV, show (replica S.ratio (increment 1 v)) q=G.lieExp (linearCopy S.ratio v q) by unfold replica linearCopy; split; rw [G.mat_lieExp_zero]; exact mul_one _,cropSeed,growSeed, if_pos (show S.ratio.parent q.1∈Y from hq),if_neg H]
    congr 2
    rw [worldZ,Pi.add_apply,Pi.smul_apply,local_voltage p h0 q rfl (by omega),add_comm]; apply congr_arg
    change voltage (gem X v) q = awaken F X.x _ q; rw [awaken,dif_pos H]; rfl
-- compiled lead
lemma deposits (v:Directions G c) (hy: ‖v‖≤u) (hT: Photic X u t C 2)(hX: ‖expandBare F X.x (G:=G)‖≤M) :
    ‖deposit X v‖ ≤ M*(C*(t+u)*u):=by
    have hp := hT.light.zeroth_charge le_rfl hy le_rfl; rw [_root_.zero_apply,sub_zero,diver,Pi.sub_apply,norm_sub_rev] at hp
    exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul hX hp (norm_nonneg _) ((norm_nonneg _).trans hX))

lemma dawn (h: Target.GrantBodies W X.x μ L Q o A T) (hx:X.width=o.K)(hf:X.manifest) {z:Air f G} (hc:Calm X Y o.ξ β z)(hβ:0<β)(v : Directions G c)(hy:‖v‖≤u)(hT:Photic X u t C 2)(hX: ‖expandBare F X.x (G:=G)‖≤M) :
    ‖stam X Y β v z‖≤ u+ (X.t+ M*(C*(t+u)*u)):=by
    have hp:= deposits X v hy hT hX; have hs:0≤X.t:=h.room.fiery.le
    have hk := (norm_nonneg _).trans hp
    refine max_le (hy.trans (le_add_of_nonneg_right (add_nonneg hs hk))) ((norm_add_le ..).trans ((add_le_add ?_ hp).trans (le_add_of_nonneg_left ((norm_nonneg _).trans hy))))
    refine (pi_norm_le_iff_of_nonneg hs).mpr (fun i=>?_); simp only [Pi.smul_apply,cropSeed]
    split
    next hi => unfold growSeed; split; rw [smul_zero,norm_zero]; exact hs; exact calm_bonds X Y h hx hf hc hβ _ hi
    rw [smul_zero,norm_zero]; exact hs

structure HaloV (β r v :ℝ)(b:Directions G c)(z:Air f G):Prop where
    chosen : let σ:=gStep β; ∃ w : Directions G f, ‖w‖ ≤ r ∧ (∀ i : Bond f, S.ratio.parent i.1∈Y→X.input (X.liftA β z) i=increment 1 w i) ∧ ‖w-(woody T F b+σ • cropSeed X Y z)‖ ≤ v

lemma fought (h: Target.GrantBodies W X.x μ L Q o A T) (hx:X.width=o.K)(hf:X.manifest) {z:Air f G} (hc:Calm X Y o.ξ β z)(hβ:0<β)(b : Directions G c)(hy:‖b‖≤u)(hT:Photic X u t C 2)(hX: ‖expandBare F X.x (G:=G)‖≤M) (hh : Tour T F X.x X.k 2 r D)
    (hm: u+(X.t+M*(C*(t+u)*u))≤r)(he:∀ i∈Y,¬Inside i X.seeds (30*X.B))(hb:X.V=increment 1 b) :
       let v:= u+ (X.t+ M*(C*(t+u)*u)); HaloV X Y β (D*v) (D*(temp X.x+v)*v+M*(C*(t+u)*u)) b z:=by
    intro v; let Z:= display T F X.x X.k false; let a:=stam X Y β b z; let p:=mainStroke T F false
    have hf' : ‖a‖ ≤ v:= dawn X Y h hx hf hc hβ b hy hT hX
    have hp := hf'.trans hm
    refine ⟨Z a,(locate (hh.costs false).uniform (by omega) (hh.costs false).home hp).trans (mul_le_mul_of_nonneg_left hf' ((hh.costs false).uniform _ hp).nonneg),fun i hi=> ?_,?_⟩
    · rw [concurs X Y z hb hf h.room he i hi β,← hh.represents false a hp]
    refine (norm_sub_le_norm_sub_add_norm_sub _ (p a) _).trans (add_le_add ((hh.costs false).zeroth_charge le_rfl hf' hm) ?_)
    change ‖(woody T F b+(gStep β • cropSeed X Y z + deposit X b))-(woody T F b+gStep β • cropSeed X Y z)‖ ≤ _
    rw [← add_assoc,add_sub_cancel_left]; exact deposits X b hy hT hX
end YM.Hypnos
#print axioms YM.Hypnos.fought
#print axioms YM.Hypnos.safe_H
