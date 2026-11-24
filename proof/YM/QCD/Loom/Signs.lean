import YM.QCD.Loom.Capsule
/-! # Coarse bridge crossing. Short and Long receipts -/
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
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W} {R :Rep su f}{s : Ratio c f}
variable {H:Cash W τ μ L Q o C T R}{ι D E K:Type}{N:ℕ}
local notation "M"=> radiusB τ
variable {j k l m n i:ℕ}
def singleR (c:Side): Ratio c c:= ⟨1,by simp⟩
lemma monotype (x:Site c): (singleR c).embed x=x:=by
   unfold Ratio.embed singleR; simp -- edit
lemma ofOne : (singleR c).embed= id :=funext monotype
lemma garrulous : (singleR c).parent=id:=by
   funext i; rw [← show (singleR c).parent ((singleR c).embed i)=id i from (singleR c).embed_parent i]; rw [monotype]

abbrev Gaze (c:Side):= Site c ×Port.XMark c
def sheetP (L:Land c (Site c) (Site c))(B:ℕ)(x:Gaze c)(U:Grid c):= batch (singleR c) L x.1 x.2 B (Kit.settled U)
def sashP (x:Gaze c)(B:ℕ): Support c:= Port.punch x.1 B x.2
def dropG (F:ℕ)(L:Land c (Site c) (Site c))(s:Ratio c f)(B:ℕ)(x:Gaze c)(U:Grid f)(V:Grid c): EvenA c F := paleF F (-(sheetP L B x V-sheetP L B x (lowC s U)))

lemma homesB {U:Run.St c}{Γ:Land c (Site c) (Site c)}{Y:Pays c (Site c) (Site c)}{η p :ℝ}(h: Pack id id η p n U W Γ Y) (v:Gaze c)(B:ℕ): LocalOn (sashP v B) (sheetP Γ B v):=by
   intro V X hh; apply Sway.whist; intro i j; unfold sheetP; rw [stack,stack,monotype]; exact congr_arg (sale _ _ _) ((cups h v.1 _ _ B v.2).2.2.2.2.1 V X hh)
def plank (Z : Support c) (p:Ratio c f)(B : ℕ) := halo (6*B) (Z∪(rig p Z).image p.parent)
def sailP (H:Cash W τ μ L Q o C T R)(Γ:Land c (Site c) (Site c))(N:ℕ):Fleet H (Gaze c) N where
 limit _ :=∅
 ground i:= halo (30*M) (plank (sashP i M) S.ratio M)
 fine i:= rig S.ratio (sashP i M)
 window i:=plank (sashP i M) S.ratio M
 compat _ _:=True
 works i U V:=NormedSpace.exp (dropG N Γ S.ratio M i U V)-1
lemma seaP (V:Gaze c)(B:ℕ) (s :Ratio c f) : halo (6*B) {V.1}⊆plank (sashP V B) s B:= Corona.halo_mono le_rfl (singleton_subset_iff.mpr (mem_union_left _ (Port.cared ..)))
lemma clover (V:Gaze c)(b:ℕ) (s :Ratio c f)(hb:s.count.val+1 ≤ b): halo (30*b) (plank (sashP V b) s b)⊆ enlargement (singleR c) 37 b (sashP V b):=by
   let p:= sashP V b; intro i hi; obtain ⟨j,hj,hi⟩:=halo_spec.mp hi; obtain ⟨k,hk,hj⟩:=halo_spec.mp hj; unfold enlargement; rw [garrulous,image_id]; have hq:k∈halo b p:=by
      rcases mem_union.mp hk with hk|hk; · exact halo_subset b _ hk
      obtain ⟨x,hx,rfl⟩:=mem_image.mp hk; obtain ⟨y,hy,hx⟩:=halo_spec.mp hx; obtain ⟨w,hw,he⟩:= mem_image.mp hy; refine halo_spec.mpr ⟨w,hw,?_⟩; have hp:= Work.E04.parent_separation s (s.embed w) x; rw [s.embed_parent] at hp; rw [← he] at hx; omega
   obtain ⟨x,hx,hr⟩:=halo_spec.mp hq; exact halo_spec.mpr ⟨x,hx,(separation_triangle x k i).trans (by have h:= separation_triangle k j i; omega)⟩
lemma singleplus (o x:Site f)(n l:ℕ)(V: Grid f) (i:Axis)(h: separation o x+n≤l)(p:ℝ)(ht:∀ s:Site f,separation o s≤l→ su.chord (V (s,i))≤p): su.chord (travel V x (List.replicate n (posDir i))) ≤ n*p:=by
   induction n generalizing x with
   | zero=> simp [travel,su.chord_one]
   | succ n ih=>
     have he : separation o x≤l:=by omega
     let v:Site f:= (posDir i).vec; rw [List.replicate_succ]; unfold travel; change su.chord (V (x,i)*travel V (x+ v) _) ≤ _
     apply (su.chord_triangle ..).trans; refine (add_le_add (ht x he) (ih (x+v) ?_)).trans_eq ?_
     · have he:= separation_triangle o x (x+v); have hs: separation x (x+v)≤ 1:=sep_step x i; omega
     push_cast; ring
lemma actingL (o:Site c)(Y:Coat T F)(w: Directions su f)(p:ℝ)(b m :ℕ)(g:Site c→su.El)(e:LogField su c)(hp: Blanket S (Y.input w) Y.V o b g e p) (ht : m+S.ratio.count.val+1 ≤ b):
     ∀ i : Edge (Site c), separation o i.1≤ m → su.chord (gauge g (lowC S.ratio (Y.input w)) i)≤ S.ratio.count.val*p:=by
   intro i hi; let V:= (Y.input w); let U:= gauge (constantGauge g S.ratio) V
   have he:(constantGauge g S.ratio) ∘ S.ratio.embed=g:=funext fun j=> congr_arg g (S.ratio.embed_parent j)
   rw [← he,← framed_c S.ratio]; unfold lowC; apply singleplus (S.ratio.embed i.1) _ _ S.ratio.count.val _ _ (by simp); intro j hj
   have hz:= Work.E04.parent_separation S.ratio (S.ratio.embed i.1) j; rw [S.ratio.embed_parent] at hz; apply hp.fine (j,i.2); unfold distAt; change separation o (S.ratio.parent j)≤_; exact (separation_triangle o i.1 _).trans (by omega)

variable {U:Run.St c}{Γ:Land c (Site c) (Site c)}{Y:Pays c (Site c) (Site c)}{η σ p:ℝ}
lemma sailors (H:Cash W τ μ L Q o C T R) (h: Pack id id η p n U b Γ Y)(hv:0<η): (sailP H Γ N).Famous:=by
     let P:= S.ratio; let Y':=sailP H Γ N; have hx (i: Gaze c):(sashP i M∪(rig P (sashP i M)).image P.parent)⊆Y'.window i:= halo_subset ..
     have hC : Continuous (lowC P):= by unfold lowC; fun_prop-- inspect
     refine ⟨fun i=>subset_trans subset_union_right (hx i),fun _=>Subset.refl _,?_,?_,?_, ?_,fun _ _ hn=>False.elim (hn trivial),fun _ _ he=>False.elim (Finset.notMem_empty _ he)⟩
     · intro i V U X hp; change NormedSpace.exp _ -1= NormedSpace.exp _-1; unfold dropG; rw [homesB h _ _ (lowC P U) (lowC P X) (firm _ hp)]
     · intro i U V X hp; change NormedSpace.exp _-1= NormedSpace.exp _-1; unfold dropG; rw [homesB h i M V X (agrees_mono hp (Finset.Subset.trans subset_union_left (hx i)))]
     · intro i V; have hg:Continuous (sheetP Γ M i):=by
          refine continuous_pi fun x=>continuous_pi fun y=>?_ ; unfold sheetP batch; simp_rw [monotype]; have he:= Jets.Sun.breeze (cups h i.1 x.1 y.1 M i.2) hv
          have hs :Continuous (fun U:Grid c=> sale i.1 x.1 y.1 (chipK i.1 M Γ x.1 y.1 i.2 (Kit.settled U))):= he.const_smul (_:ℂ)
          exact (continuous_apply y.2).comp ((continuous_apply x.2).comp hs) -- sale
       let v t:= Lat.copies N (-(sheetP Γ M i V-sheetP Γ M i (lowC S.ratio t)))
       have hz:Continuous v:= (Lat.continuous_copies N).comp ((continuous_const.sub (hg.comp hC)).neg)
       have he:Continuous (dropG N Γ S.ratio M i · V):=by
          let f U : Grass.Dirac (Modes c N):=Grass.form (v U); have hf:Continuous f:= continuous_finsetSum _ (fun a _=>continuous_finsetSum _ (fun b _=>((continuous_apply b).comp ((continuous_apply a).comp hz)).smul (continuous_const (y:= Grass.psi b * Grass.bar a))))
          exact hf.subtype_mk _
       let g t:=NormedSpace.exp (dropG N Γ S.ratio M i t V)-1; have hm:Continuous g:= (NormedSpace.exp_continuous.comp he).sub continuous_const
       obtain ⟨j,hj,hJ⟩:=isCompact_univ.exists_isMaxOn Set.univ_nonempty hm.norm.continuousOn; exact ⟨hm.measurable,_,fun i=>hJ (Set.mem_univ _)⟩
     intro i V g hp U
     have he:gauge (g ∘ S.ratio.embed) (lowC S.ratio U)= lowC S.ratio U:=by funext i; simp [Lattice.gauge,hp]
     change NormedSpace.exp _-1=NormedSpace.exp _-1; unfold dropG; rw [framed_c,he]
end YM.QCD.Loom
