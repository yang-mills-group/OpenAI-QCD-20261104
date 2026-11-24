import YM.QCD.Loom.Tann
/-! # Varn on the star marks. Prices on operational contours. -/
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
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{δ β b τ μ W C:ℝ} {F:Tree.Forest S.ratio}{Q:Target su P}{o :Target.Order su W} {R:BudgetPoint}
variable {H:Cash W τ μ L Q o C T (trimP T R δ β b)}{ι D E K:Type}{N:ℕ}
local notation "M"=> radiusB τ
local notation "t0"=> R.threshold
variable {j k l m n i:ℕ}{L': Flight j k}{d:f.val=c.val*L'.L.val}
variable {X:Run.St f} {W':ℕ→Atom su 2}{J:Plan k}{η ξ p p' z r R' v u:ℝ}
local notation "G"=> sliceL L' d
variable (H : Cash W τ μ L Q o C T (trimP T R δ β b)) (G₁:Swathe L' d X W' J u v η p p' n)
def vap (i: Varn f c)(s:Ratio c f)(b:ℕ):=halo (6*b) ((payT s b i).image s.parent)
def siteH (i:Varn f c)(s:Ratio c f):= s.parent (orbitM s i)
def VarnC (N:ℕ): Fleet H (Varn f c) N where
 limit _:=∅
 ground i:= halo (30*M) (vap i S.ratio M)
 fine i:= payT S.ratio M i
 window i:= vap i S.ratio M
 compat _ _:=True
 works i U _:= Port.broke G₁ N M i U
lemma marks (i: Varn f c)(s:Ratio c f) (b:ℕ) : halo (6*b) {siteH i s}⊆ vap i s b:= Corona.halo_mono le_rfl (singleton_subset_iff.mpr (mem_image_of_mem _ (Port.cared ..)))
local notation "PI"=> (VarnC H G₁ N)
lemma bridgeC (h:S.ratio=G)(hp:0<v):Fleet.Famous (PI):=by
   refine ⟨fun i=>halo_subset _ _,fun _=> Finset.Subset.refl _,?_,fun _ _ _ _ _=> rfl,?_,?_, fun _ _ h=>False.elim (h trivial), fun _ _ h=> False.elim (Finset.notMem_empty _ h)⟩
   · intro i V U X hx; apply congr_arg (fun p:EvenA c N=> NormedSpace.exp p - 1); apply Port.disclosed; change Agrees (_:Set _) U X; rwa [← h]
   · intro i X; have he:Continuous (Port.broke G₁ N M i):=(NormedSpace.exp_continuous.comp (Port.forestV G₁ hp ..)).sub continuous_const
     obtain ⟨U,hu,hB⟩:= isCompact_univ.exists_isMaxOn Set.univ_nonempty he.norm.continuousOn
     exact ⟨he.measurable,_,fun j=>hB (Set.mem_univ j)⟩ -- λ infer
   intro i V g ht U; apply congr_arg (fun x:EvenA c N=> NormedSpace.exp x-1)
   have hp : g ∘ (G).embed= (fun _=>1):=by rw [← h]; exact funext ht
   have hh:= flower H _ hp (sliceF G₁ N M i (gauge g U)); exact hh.symm.trans (triumph ..)
lemma counters (V:Ratio c f) : let I:= (univ:Finset (Varn f c)).filter fun j=>waxV j=none
                                 ∀ y,(I.filter fun i=>siteH i V=y).card ≤ V.count.val^4+1:=by
   intro I y; let Qx := I.filter fun i=> siteH i V=y
   let X:=univ.filter fun i : Site f=> V.parent i=y
   have h Vc (hi:Vc∈ Qx): waxV Vc=none ∧ siteH Vc V=y:= ⟨(mem_filter.mp (mem_filter.mp hi).1).2,(mem_filter.mp hi).2⟩
   let p:= Finset.disjSum (X.image (fun x=>(x,(none:XMark f)))) ({(y,(none:XMark f))})
   apply (Finset.card_le_card (show Qx⊆p from ?_)).trans
   · unfold p; rw [Finset.card_disjSum,card_singleton]; apply Nat.add_le_add_right; apply Finset.card_image_le.trans
     have he:= crowd V {y}; simpa only [mem_singleton,card_singleton,one_mul] using he
   rintro (⟨v,j⟩|⟨u,j⟩) hi
   · obtain ⟨hn,hX⟩:=h _ hi; refine inl_mem_disjSum.mpr (mem_image.mpr ⟨v,mem_filter.mpr ⟨mem_univ _,hX⟩,Prod.ext rfl hn.symm⟩)
   obtain ⟨hn,hX⟩:= h _ hi; refine inr_mem_disjSum.mpr (mem_singleton.mpr (Prod.ext ?_ hn)); change V.parent (V.embed u)=y at hX; rwa [V.embed_parent] at hX
lemma metered (h : S.ratio=G)(ht : RentP G₁ N M (fiery su τ S.patch.L) z R' (wear L τ))
    (hW:∀ (Y:Coat T F), Y.x=τ→Y.width=o.K→Y.manifest →∀ i:Varn f c,waxV i= none →¬Inside (siteH i S.ratio) Y.seeds (18*M) →∀ w: Air f su, ((PI).riseP Y w i)≠0 → load (fun _=> R') (Cove.light _ (sliceF G₁ N M i (Y.input (Y.liftA β w)))) ≤ z) :
    Fleet.Theft (PI) F (fun i=>siteH i S.ratio) (fun i=>Real.exp 1*Port.shells G₁ N M R' z i) R' (fan L (1/4) τ) ((univ:Finset (Varn f c)).filter fun j=>waxV j=none) (18*M) (S.ratio.count.val^4+1):=by
   let p i:= Real.exp 1*Port.shells G₁ N M R' z i; let E:=fan L (1/4) τ
   have hE:0<E:=fan_pos ..; have hx i:0≤p i:=mul_nonneg (Real.exp_pos _).le (by unfold Port.shells; split; exact ht.profit.le; exact Port.grew G₁ _ ht.growth ht.toll)
   have hC Y w i : ‖token c N R' ((PI).coming (F:=F) i Y w)‖ ≤ ‖token c N R' (broke G₁ N M i (Y.input (Y.liftA β w)))‖:= (PI).riseTiny ..
   refine ⟨hE.le,hx,counters _,?_,fun i Z _ _ _ w=>le_trans (hC ..) ?_⟩
   · intro i Y hy hv hZ w hf; have hw:= mountains G₁ ht (Y.input (Y.liftA β w)) i
     have hh: waxV i=none:=by split at hw; exact ‹Port.zoneG ..›.1; exact False.elim ((not_lt.mpr ((hC ..).trans hw)) hf)
     have ht':p i=Real.exp 1*z:= congr_arg (Real.exp 1 * ·) (if_pos hh)
     have hT: z≤1:=(show Port.shells G₁ _ _ _ _ i=z from if_pos hh) ▸ ht.expR i
     refine ⟨mem_filter.mpr ⟨mem_univ _,hh⟩,?_⟩
     have he:Inside (siteH i S.ratio) Y.seeds (18*M) :=by
       by_contra! hs
       have hr : (PI).riseP Y w i ≠ 0:=by intro he; change p i < ‖token c N R' (_ • (_: EvenA c N))‖ at hf; rw [he,zero_smul,map_zero,norm_zero] at hf; exact not_lt_of_ge (hx _) hf
       exact not_lt_of_ge ((hC Y w i).trans (show ‖token _ _ R' (Port.broke ..)‖ ≤p i from (Cove.bought (fun _=> R') _ _ (hW Y hy hv hZ i hh hs w hr)).trans ((fastR z ht.profit.le hT).trans_eq ht'.symm))) hf
     obtain ⟨k,hk,h⟩:= halo_spec.mp he; refine ⟨k,?_,hk,h⟩
     exact halo_spec.mpr ⟨siteH i S.ratio,marks i _ _ (halo_subset _ _ (mem_singleton_self _)),(separation_comm ..).trans_le (h.trans (by omega))⟩
   have hv:=mountains G₁ ht (Z.input (Z.liftA β w)) i; split at hv
   next=> exact hv
   exact hv.trans (le_mul_of_one_le_left (hx _) ht.always)
lemma swaddled (i:Varn f c): (PI).ground i⊆ Footprint.enlargement S.ratio 36 M (payT S.ratio M i):=by
   intro x hx
   obtain ⟨k,hk,hx⟩:= halo_spec.mp hx; obtain ⟨j,hj,hk⟩:= halo_spec.mp hk; exact halo_spec.mpr ⟨j,hj,(separation_triangle ..).trans (show separation j k+ separation k x ≤ _ by omega)⟩
end YM.QCD.Loom
