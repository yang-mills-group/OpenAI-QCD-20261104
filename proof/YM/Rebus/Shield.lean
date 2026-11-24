import YM.Cape.Arch
import YM.Play.Lago
import YM.Play.Hug
import YM.Hypnos.Dryad
import YM.Hypnos.Tenuous
/-! # Paid one-step primary. COREVS.reducing to payouts
 Geometry over thermal counting stencils includes deterministic Wick-support. Propagating grade.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Rebus
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon Cape Play Play.Chamber QCD.Bera QCD.Anomaly Hypnos Hypnos.Fruit Rot
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{J K':Patch}{P:Teller su}{β x C μ W:ℝ}
variable {O:BudgetPoint}{ι κ I Z E D:Type}[Fintype I]
variable {N i j n k m l r t M B Q:ℕ}
-- native alph
abbrev Kh (c:Side):= Col su c
abbrev Dh (c:Side)(N:ℕ)(I:Type):= Keys c N⊕ Spine I
abbrev Quince (c:Side)(N:ℕ)(I:Type)[Fintype I]:= Finset I → Papers (Kh c) (Patio (Dh c N I))
section a
variable (p:I→Site c)
def spineP (N:ℕ)(v:ℕ)(i:I):Finset (Dh c N I):=(limits (halo v {p i})).disjSum (univ.filter (fun k=>k.1.1=i))
def can (v:ℕ)(i:I): Finset (Kh c):= Finset.univ.filter (fun k=>k.1∈ halo v {p i})
structure SetL (T:Finset (Finset I))(B l k m:ℕ)(f: Quince c N I):Prop where
   scope X: X∈T → X.Nonempty→ f X∈ Ledger (@Finset.biUnion _ _ (fun a b => Classical.propDecidable (a=b)) X (spineP p N (majorT l*B))) (@Finset.biUnion _ _ (fun a b=>Classical.propDecidable (a=b)) X (can p (majorT l*B))) (X.card*k) (X.card*m)
   core X:X∈T→ X.Nonempty→ f X≠ 0 → Ac.Spark (Play.Camp.Ray p (baseTZ B)) X
end a
open Play.Camp
variable {R: Ratio c f}
lemma rowL {y z: Site f}(R:Ratio c f)(hp: y∈halo r ({z}:Finset (Site f))): separation (R.parent z) (R.parent y) ≤ r+1:=by
  obtain ⟨x,hx,h⟩:=halo_spec.mp hp; rw [mem_singleton.mp hx] at h; apply Nat.le_of_mul_le_mul_left (le_trans (Corona.foreshorten ..) ?_) R.count.pos; have he:=Nat.mul_le_mul_right r (show 1≤ R.count.val from R.count.pos); nlinarith
-- need declare y,z
variable (S: Flight j n)(h:f.val=c.val*S.L.val)(K:KernelChoices)
local notation "T"=> S.visit K h
local notation "R"=> (sliceL S h)
variable (Hp Bp : Bed) (T' : Towers (Flight.visit S K h).patch.L)
variable (hu:(curtain su (Flight.visit S K h) Hp Bp T').IsSymm)
lemma fog {A:Matrix I I ℝ}(p:I→ Site c)(h:A.IsSymm) (b:ℕ): (stuns p p A b).IsSymm:=by
    unfold Matrix.IsSymm; ext i j; rw [Matrix.transpose_apply,stuns,Matrix.of_apply,Matrix.of_apply, show A j i=A i j from h.apply i j]; by_cases ht:p i∈ halo b {p j}
    · rw [if_pos ht]; symm; apply if_pos; obtain ⟨x,hx,he⟩:=halo_spec.mp ht; rw [mem_singleton.mp hx] at he; exact halo_spec.mpr ⟨_,mem_singleton_self _,(separation_comm ..).trans_le he⟩
    rw [if_neg ht]; symm; apply if_neg; intro h; apply ht; obtain ⟨x,hx,h⟩:=halo_spec.mp h; rw [mem_singleton.mp hx] at h; exact halo_spec.mpr ⟨_,mem_singleton_self _,(separation_comm ..).trans_le h⟩
abbrev raw (r:ℕ): Matrix (Kh f) (Kh c) ℂ:=(cones su (Flight.visit S K h) Hp Bp T' r).map Complex.ofReal
abbrev sineP (r:ℕ): Next.Rank.Normal.Symmetric (Kh f):= Oce.knock (sprig su (Flight.visit S K h) Hp Bp T' r) (fog _ hu r)
abbrev kpit (N r:ℕ)(I:Type)[Fintype I]: Matrix (Dh f N I) (Dh c N I) ℂ:= breezeP (Spine I) (shear S h N r)
abbrev sfan (N r:ℕ)(I:Type) : Matrix (Dh f N I) (Dh f N I) ℂ:= breezeX (Spine I) (stamping (shore S h N r)) -- inst?
set_option quotPrecheck false
local notation "V"=> raw S h K Hp Bp T' B
local notation "Jp"=> sineP S h K Hp Bp T' hu B
local notation "U" => kpit S h N B I
local notation "X0" => sfan S h N B I
-- row & cross tests.Small
variable (p:I→Site f)
local notation "za"=> (sliceL S h).parent∘ p
local notation "ax"=> (spineP p N (majorT l*Q))
local notation "aw"=> (can p (majorT l*Q))
local notation "ay"=> (Play.Camp.Ray za (baseTZ B))
local notation "Ui"=> (spineP za N (majorT l*B))
local notation "Vi"=> (can za (majorT l*B))
variable (hQ:Q ≤ 2*B)(hP:0<B)(hL:20*majorT l ≤ (S.L).val)
include hQ hP hL
lemma viewA (i:I)(j: Kh f)(hj:j∈ aw i)(k: Kh c)(hk:V j k≠0): k∈Vi i:=by
    have he:= (Play.Camp.portion ..).mp (puff R p l B Q hP hQ hL i (mem_image_of_mem _ (mem_filter.mp hj).2))
    unfold raw Matrix.map Hypnos.Fruit.cones stuns at hk; simp only [Matrix.of_apply] at hk; split at hk
    next hz=>
       obtain ⟨x,hx,hv⟩:=halo_spec.mp hz; rw [mem_singleton.mp hx] at hv
       exact mem_filter.mpr ⟨mem_univ _,halo_spec.mpr ⟨_,mem_singleton_self _,((separation_triangle ..).trans (Nat.add_le_add he hv)).trans (by apply le_trans _ (configurationD l B hP).2.2.2.2.2; omega)⟩⟩
    next => simp at hk
lemma marchA (i:I)(j: Dh f N I)(hj:j∈ ax i)(k:Dh c N I)(hk:U j k ≠0): k∈Ui i:=by
    cases j <;> cases k
    next j k=>
       apply inl_mem_disjSum.mpr; have he:= (Play.Camp.portion ..).mp (puff R p l B Q hP hQ hL i (mem_image_of_mem _ (mem_filter.mp (inl_mem_disjSum.mp hj)).2))
       change shear S h N B _ _≠0 at hk; unfold Rot.shear at hk; rw [Matrix.of_apply] at hk; split at hk
       next hz=>
           have hf:=rowL R hz; rw [Ratio.embed_parent] at hf; exact mem_filter.mpr ⟨mem_univ _,halo_spec.mpr ⟨_,mem_singleton_self _,((separation_triangle ..).trans (Nat.add_le_add he hf)).trans (by apply le_trans _ (configurationD l B hP).2.2.2.2.2; omega)⟩⟩ -- hf?
       exact (hk rfl).elim
    next => exact (hk rfl).elim
    next => exact (hk rfl).elim
    next j k =>
       apply inr_mem_disjSum.mpr; change (1:Matrix _ _ ℂ) j k≠0 at hk; rw [show k=j from Eq.symm (by_contra (fun hp=>hk (Matrix.one_apply_ne hp)))]; exact inr_mem_disjSum.mp hj
lemma crossing (i j:I)(hi:i≠ j)(hp:Disjoint (ay i) (ay j)):
    Disjoint (ax i) (ax j)∧(∀ m∈ax i,∀ n∈ax j,X0 m n=0∧X0 n m=0) ∧(∀ m∈aw i,∀ n∈aw j,(Jp).cov m n=0):=by
    have ht i j (hp:Disjoint (ay i) (ay j)) (x y:Site f) (hx:x∈halo (majorT l*Q) {p i})(hy:y∈halo (majorT l*Q) {p j})(hg:separation ((R).parent x) ((R).parent y)≤ B+1): False:=by
        have hz:=puff R p l B Q hP hQ hL i (mem_image_of_mem _ hx); have hb:= puff R p l B Q hP hQ hL j (mem_image_of_mem _ hy)
        apply disjoint_left.mp hp (_ : (R).parent y∈ ay i) ((Play.Camp.portion ..).mpr (((Play.Camp.portion ..).mp hb).trans (by unfold baseTZ; omega)))
        exact (Play.Camp.portion ..).mpr ((separation_triangle ..).trans ((Nat.add_le_add ((Play.Camp.portion ..).mp hz) hg).trans (by unfold baseTZ; omega)))
    have hz i j (hp:Disjoint (ay i) (ay j)) (a : Dh f N I)(ha:a∈ax i)(b:Dh f N I)(hb:b∈ax j) : X0 a b=0:= by
        rcases a with (a|a)|a <;> rcases b with (b|b)|b <;> first|rfl|skip
        change shore S h N B a b=0; exact if_neg (fun h=>ht i j hp _ _ (mem_filter.mp (inl_mem_disjSum.mp ha)).2 (mem_filter.mp (inl_mem_disjSum.mp hb)).2 (rowL R h))
    refine ⟨disjoint_left.mpr (fun x hx hy=> ?_),fun a ha b hb=>⟨hz _ _ hp a ha b hb,hz _ _ hp.symm b hb a ha⟩,fun a ha b hb=>?_⟩
    · cases x
      next x => exact ht i j hp (locationP x) _ (mem_filter.mp (inl_mem_disjSum.mp hx)).2 (mem_filter.mp (inl_mem_disjSum.mp hy)).2 (by rw [separation_self]; omega)
      next x => exact hi (((mem_filter.mp (inr_mem_disjSum.mp hx)).2).symm.trans (mem_filter.mp (inr_mem_disjSum.mp hy)).2)
    change (sprig su (Flight.visit S K h) Hp Bp T' B _ _:ℂ)=0; apply Complex.ofReal_eq_zero.mpr; apply if_neg; intro H; obtain ⟨x,hx,hZ⟩:=halo_spec.mp H; rw [mem_singleton.mp hx] at hZ
    exact ht i j hp _ _ (mem_filter.mp ha).2 (mem_filter.mp hb).2 (hZ.trans (by omega))
-- publish gr
abbrev novaQ (u':ℕ)(fP : Quince f N I) : Quince c N I := Play.Chamber.switch fP (raw S h K Hp Bp T' u') (sineP S h K Hp Bp T' hu u') (kpit S h N u' I) (sfan S h N u' I)
local notation "Eu"=> novaQ S h K Hp Bp T' hu B
variable (TS:Finset (Finset I))(fP:Quince f N I)
set_option maxHeartbeats 240000 in
lemma flick (hp:SetL p TS Q l k m fP) (hf:∀ i∈TS,∀ j:Finset I,j⊆ i→ j∈ TS): SetL za TS B l k m (Eu fP):=by
    have hem i (hi:i∈TS): ∀ a⊆ i,a.Nonempty→ fP a∈ QCD.Bera.Ledger (@Finset.biUnion _ _ (fun a b=>Classical.propDecidable (a=b)) a ax) (@Finset.biUnion _ _ (fun a b=>Classical.propDecidable (a=b)) a aw) (a.card*k) (a.card*m) := by intro a hv he; exact hp.scope a (hf i hi a hv) he
    constructor
    · intro i hi hz; change Play.Chamber.switch fP V Jp U X0 _ ∈ _; refine Play.Chamber.move fP aw ax V Jp U X0 (n:=k) (m:=m) (X:=i) (hem i hi) Vi Ui ?_ ?_; exact fun _ _ _ hj _=>viewA S h K _ _ _ p hQ hP hL _ _ hj _; exact fun _ _ _ hj _=>marchA S h p hQ hP hL _ _ hj _
    · intro i hi hz hW; refine Play.Chamber.cutoff (n:=k) (m:=m) (X:=i) fP aw ax V Jp U X0 (hem i hi) ay (?_) (fun i _ j _ he=> crossing S h K Hp Bp T' hu p hQ hP hL i j he) hW
      intro a ha hb hZ; have hh:= hp.core _ (hf _ hi _ ha) hb hZ
      have hSp i (b:Site f)(hv:b∈ Play.Camp.Ray p (baseTZ Q) i): (R).parent b∈ ay i:=by
         apply (Play.Camp.portion ..).mpr; apply le_trans ((Play.Camp.portion ..).mp (puff R p l B Q hP hQ hL i (mem_image_of_mem _ (show b∈ halo (majorT l*Q) _ from halo_spec.mpr ⟨_,mem_singleton_self _,((Play.Camp.portion ..).mp hv).trans (?_)⟩)))); unfold baseTZ; omega; unfold baseTZ majorT Cape.orbital innerT; nlinarith
      refine ⟨hb,fun i hi j hj=> Relation.ReflTransGen.mono (by intro a b h; obtain ⟨hp,hq,z,hx,hy⟩:=h; exact ⟨hp,hq,(R).parent z,hSp a z hx,hSp b z hy⟩) _ _ (hh.2 _ hi _ hj)⟩
end YM.MassiveQCD.Rebus
#print axioms YM.MassiveQCD.Rebus.flick
