import YM.QCD.Loom.Home
/-! # density through bridge and shader. -/
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
open Kit Fork Port Flume YM.Next.Free Leaf Tee Orbit Quarry Garden Footprint Bay Run Jets.Sun Pine
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f:Side}{P:Teller su}{δ β b τ μ W C:ℝ}{Q:Target su P}{o :Target.Order su W}{R:BudgetPoint}{N m l n i:ℕ}
section toss
variable {S:StepData c f}{T:Tube su S}{L:Side}{X:Rep su f}{H:Cash W τ μ L Q o C T X}
variable {K J:Type}(F:Tree.Forest S.ratio) (Y:Fleet H K N)(Z:Fleet H J N)
lemma unify (hk:∀ i j,Z.compat i j)(hp:∀ i,Z.limit i=∅)(s:Finset K)(p :Finset J)(U:Grid f)(V:Grid c):
    ((united Y Z).suitcase F).stumpP V (s.disjSum p) U=((Y.suitcase F).stumpP V s U)* ∏ i∈p,Z.works i U V :=by
   let A:=united Y Z
   let a:=Y.suitcase F; let b:=A.suitcase F
   have he (m) : b.eligibleP m ↔ a.eligibleP m.toLeft:=by
      constructor
      · intro h i hi j hj hn; exact h (mem_toLeft.mp hi) (mem_toLeft.mp hj) (Sum.inl_injective.ne hn)
      intro h; rintro (i|i) hi (j|j) hj hn
      · exact h (mem_toLeft.mpr hi) (mem_toLeft.mpr hj) (fun he=>hn (congr_arg Sum.inl he))
      · trivial
      · trivial
      exact hk i j
   have hv : b.filterP (s.disjSum p)=a.filterP s:=by
     ext i; simp only [Pipe.filterP,mem_biUnion]; constructor
     · rintro ⟨j,h,hj⟩; cases j
       next j=>exact ⟨j,inl_mem_disjSum.mp h,hj⟩
       next j=> exact False.elim (Finset.notMem_empty i (hp j ▸ (show i∈ Z.limit j from hj)))
     exact fun ⟨j,h,hj⟩=>⟨.inl j,inl_mem_disjSum.mpr h,hj⟩
   have hE:b.eligibleP (s.disjSum p) ↔ a.eligibleP s:=by rw [he,toLeft_disjSum]
   change b.stumpP V (s.disjSum p) U=a.stumpP V s U* _ -- edit
   unfold stumpP; split
   next h=> rw [if_pos (hE.1 h), Algebra.smul_mul_assoc] -- direction
            refine congr_arg₂ (· • ·) ?_ ?_
            · rw [hv]
            unfold sweepP; rw [prod_disjSum]; rfl
   next h=> rw [if_neg (mt hE.2 h),zero_mul]
variable [Fintype J]
lemma combining (hk:∀ i j,Z.compat i j)(hp1:∀ i,Z.limit i=∅)(U:Grid f)(V:Grid c)(hV: Summable (fun i=> (Y.suitcase F).stumpP V i U)):
 ((united Y Z).suitcase F).missP V U = ((Y.suitcase F).missP V U)*(∑ i:Finset J,∏ j∈i,Z.works j U V):=by
    unfold missP; let P':Finset K×Finset J≃ Finset (K⊕J):= {
      toFun:=fun p=>p.1.disjSum p.2
      invFun:=fun p=>(p.toLeft,p.toRight)
      left_inv p:=Prod.ext (toLeft_disjSum ..) (toRight_disjSum ..)
      right_inv p:=by ext i; cases i<;> simp
    }
    let A i:= (Y.suitcase F).stumpP V i U; let B1 i:=∏ j∈i,Z.works j U V; let A1 i:=((united Y Z).suitcase F).stumpP V i U
    have hp : HasSum B1 (∑ i, B1 i):=hasSum_fintype _
    have hS : A1 ∘ P'= fun i=> A i.1* B1 i.2:= funext fun i=> unify F Y Z hk hp1 i.1 i.2 U V
    have hz := toss_big hV.hasSum hp hV.norm hp.summable.norm
    have hm : HasSum A1 ((∑' i, A i) * ∑ i,B1 i):= (P'.hasSum_iff).mp (show HasSum (A1 ∘ P') _ from by rw [hS]; exact hz)
    exact hm.tsum_eq
lemma aloneC (c:Side) : lowC (singleR c) (1:Grid c)=1:= former .. -- harmless
lemma aloneW (V:Grid c) : lowC (singleR c) V=V:=by funext i; unfold lowC; rw [monotype]; change travel V _ (List.replicate 1 _) = _; change V i * 1=V i; rw [mul_one]
variable {D:St c}{Γ:Land c (Site c) (Site c)}{W':Pays c (Site c) (Site c)}{η p:ℝ}
lemma budgetJ (h: Pack id id η p n D b Γ W')(u:Grid f)(V:Grid c)(H:Cash W τ μ L Q o C T X) (N:ℕ):
    (∑ i:Finset (Gaze c),∏ x∈i,(sailP H Γ N).works x u V) = NormedSpace.exp (paleF N (D (lowC S.ratio u)-D V)):=by
   let d:=radiusB τ; let kX x:= dropG N Γ S.ratio d x u V
   have ht (x:Grid c): ∑ i:Gaze c, sheetP Γ d i x=D x:=by
     have hq: Pack (singleR c).embed (singleR c).embed η p n D b Γ W':=by rw [ofOne]; exact h
     unfold Gaze; rw [Fintype.sum_prod_type]; exact framesK hq x d
   have he:paleF N (D (lowC S.ratio u)-D V)=∑ i,kX i:=by
     rw [show _ - _=∑ x : Gaze c, -(sheetP Γ d x V-sheetP Γ d x (lowC S.ratio u)) from ?_,groups]; rfl -- rfl already?
     simp_rw [neg_sub, Finset.sum_sub_distrib,ht]
   rw [he,flicker _ univ, show (univ:Finset (Gaze c)).powerset=univ from by ext; simp]; rfl
lemma banner (J:Plan i)(p:ℝ) (hh:0≤p):∃ n:ℕ,∃ η b:ℝ, 0<η∧0<b∧∀ (c : Side)(z: Train i), Own c η p n (wood J 0 z) b:=by
   obtain ⟨n,v,w,hv,hw,hq⟩:= quest J hh (1:Side)
   refine ⟨n,v,w,hv,hw,fun c z=>?_⟩; have hs:=hq c c (singleR c) rfl n le_rfl z; rw [ofOne,show lowC (singleR c)=id from funext aloneW] at hs; exact hs
end toss
end YM.QCD.Loom
