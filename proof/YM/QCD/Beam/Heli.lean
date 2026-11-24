import YM.QCD.Beam.Saddle
/-! # Emission factorization. no probability products for shared z -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Beam
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{δ β τ μ W C:ℝ} {R:Rep G f}{F:Forest S.ratio}{Q:Target G P}{o :Target.Order G W}
variable {M: Type*} [NormedCommRing M][NormedAlgebra ℝ M][CompleteSpace M][MeasurableSpace M][BorelSpace M][SecondCountableTopology M][FiniteDimensional ℝ M]
-- conditional income per land
abbrev StampF (F : Forest S.ratio) (T:Tube G S) (M:Type*):=Coat T F→Air f G→M
variable (H:Cash W τ μ L Q o C T R)
def silence (_H: Cash W τ μ L Q o C T R) (w: Support c) (g:StampF F T M):Prop:=∀ (X X':Coat T F)(z z'),X.x=τ → Village X X' w → Pond.swim (podium S G w X.B) z=Pond.swim (podium S G w X.B) z' → g X z=g X' z'
def exposedG (_H: Cash W τ μ L Q o C T R)(g: StampF F T M):Prop:=∀ X : Coat T F,X.x=τ→ X.width=o.K → X.manifest→ Envelope (fun i:F.Slice G × Air f G=>g (X.wrapY i.1) i.2)
def call (X: Coat T F)(Y: StampF F T M): M:= ∫ i:F.Slice G × Air f G,Y (X.wrapY i.1) i.2 ∂((F.order G).prod X.dice)
def draws (X: Coat T F)(Y: StampF F T M) := choiceS (fun k:S.Choices=> call (X.taggedL k) Y)
lemma weight (X X':Coat T F)(w: Support c)(Y Z:StampF F T M)(he:X.x=τ)(hk :X.width=o.K)(hX:X.manifest)(hY:X'.manifest)(hs: exposedG H Y)(hu:exposedG H Z) (ht: Village X X' w)
 (hh : ∀ u (a b:Air f G), Pond.swim (podium S G w X.B) a=Pond.swim (podium S G w X.B) b → Y (X.wrapY u) a= Z (X'.wrapY u) b): call X Y=call X' Z:= by
   let A:=fun i:F.Slice G × Air f G=>Y (X.wrapY i.1) i.2; let B:=fun i:F.Slice G × Air f G=> Z (X'.wrapY i.1) i.2
   have hS:= hs X he hk hX; have hy:=hu X' (ht.weather ▸ he) (ht.width ▸ hk) hY
   have hm:Integrable A _:=envPlot hS ((F.order G).prod X.dice); have hn: Integrable B _:=envPlot hy ((F.order G).prod X'.dice)
   apply concrete; intro l
   change l (∫ i, A i ∂_)=l (∫ i,B i ∂_); rw [← ContinuousLinearMap.integral_comp_comm _ hm, ← ContinuousLinearMap.integral_comp_comm _ hn]
   rw [integral_prod _ (l.integrable_comp hm),integral_prod _ (l.integrable_comp hn)]
   apply integral_congr_ae; filter_upwards with p
   let I:= podium S G w X.B
   have hp : X.relating.PosDef := (H.laws.data.localP F X he hk hX).sails.fullC
   have hv : X'.relating.PosDef := (H.laws.data.localP F X' (ht.weather ▸ he) (ht.width ▸ hk) hY).sails.fullC
   have hT:circuit I X.relating=circuit I X'.relating:=by ext i j; exact ht.same_cov (he.symm ▸ H.laws.data.room) j.val j.2 i.val
   have hh' : MeasurePreserving (Pond.swim I) X'.dice (arch I X.relating) := by rw [arch,hT]; exact orbit hv.posSemidef I
   have hC x y (h:Pond.swim I x=Pond.swim I y): l (A (p,x))= l (B (p,y)):=congr_arg l (hh _ _ _ h)
   let A₁ x:=l (A (p,x)); let B₁ x:=l (B (p,x))
   rw [gathered (f:=A₁) (spill I) (spill_m I) (show MeasurePreserving (Pond.swim I) X.dice (arch I X.relating) from orbit hp.posSemidef I) (Pond.settled I)
       (fun x y h=> (hC x y h).trans (hC y y rfl).symm) (l.measurable.comp (hS.meas.comp (measurable_const.prodMk measurable_id))), gathered (f:=B₁) (spill I) (spill_m I) hh' (Pond.settled I) (fun x y h=>(hC x x rfl).symm.trans (hC x y h)) (l.measurable.comp (hy.meas.comp (measurable_const.prodMk measurable_id)))]
   exact integral_congr_ae (ae_of_all _ (fun x=>hC _ _ rfl))
lemma call_critical (w : Support c)(g:StampF F T M)(h:exposedG H g)(hr:silence H w g)(X X':Coat T F)(he:X.x=τ)(hp:X.width=o.K)(hX:X.manifest)(ht:X'.manifest)(hj:Village X X' w) : call X g=call X' g:=weight H X X' w g g he hp hX ht h h hj fun u a b ho=>hr (X.wrapY u) (X'.wrapY u) a b he (hj.wrap u u (fun _ _=>rfl)) ho
lemma codraft {A B:Type}[Fintype A][Fintype B](f:A×B→M):choiceS f=choiceS (fun i=>choiceS fun j=> f (i,j)):=by unfold choiceS; rw [Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,mul_inv,mul_smul,Finset.smul_sum]
lemma fairT {A I Y:Type} [Fintype I] [Fintype A] [Nonempty A] [Fintype Y] (g : Fintype (I→A))
 (f:Y→(I→A)→M) (Z : Y→Finset I) (h: (↑(univ:Finset Y):Set Y).PairwiseDisjoint Z) (hf:∀ i u v,(∀ j∈ Z i,u j=v j)→ f i u=f i v):
   @choiceS _ M _ _ g (fun v=>∏ i,f i v)= ∏ i,@choiceS _ M _ _ g (f i):= by
   rw [show g=inferInstanceAs (Fintype (I→A)) from Subsingleton.elim g (inferInstanceAs (Fintype (I→A)))]; apply volProd
   intro L
   convert! Pond.jurisdictions (S:=univ) Z h (fun i v=> L i (f i v)) (fun i _ u v h=>congr_arg (L i) (hf _ _ _ h)) -- likely takes old Fintype
lemma lance {ι:Type}[Fintype ι](w :ι→Support c)(g:ι→StampF F T M)(X:Coat T F)(hx:X.x=τ)(hk:X.width=o.K)(hX:X.manifest)(h:∀ i,exposedG H (g i))(hr:∀ i,silence H (w i) (g i)) (hv :(↑(univ:Finset ι):Set ι).PairwiseDisjoint w) : call X (fun x z=> ∏ i,g i x z)=∏ i,call X (g i):=by
   let Y (i:ι)(y:F.Slice G × Air f G):= g i (X.wrapY y.1) y.2
   have ht(i): Envelope (Y i):=h i X hx hk hX
   let f₀ i y:=∫ z,Y i (y,z) ∂X.dice
   let P i := podium S G (w i) X.B
   have hh : X.relating.PosSemidef:=(H.laws.data.localP F X hx hk hX).sails.fullC.posSemidef
   have hc:100≤X.B:=(H.laws.data.localP F X hx hk hX).sails.room.sight.1
   have hcw : Set.PairwiseDisjoint (↑(univ:Finset ι)) w:=hv
   have hm (u): (∫ z, ∏ i:ι,Y i (u,z) ∂X.dice)=∏ i,f₀ i u:=by
      refine wideProd _ X.dice (fun i=> Env.along (ht i) (measurable_const.prodMk measurable_id)) (fun l=>?_) -- inference
      have he i j (hi:i≠j) x (hx:x∈P i) z (hz:z∈P j): X.relating x z=0:=by
        apply X.shutter.width X.plate; by_contra hy
        have hp:= le_of_not_gt hy
        exact Finset.disjoint_left.mp (hcw (mem_univ _) (mem_univ _) hi) ((mem_filter.mp hx).2 (along S z) (hp.trans (by omega))) ((mem_filter.mp hz).2 (along S z) (by rw [separation_self]; omega))
      refine Pond.island hh univ P (fun i _ j _ hn=> he i j hn) _ (fun i _=> ((l i).measurable.comp ((ht i).meas.comp (measurable_const.prodMk measurable_id)))) (fun i _ a b ht=>?_)
      exact congr_arg (l i) (hr i (X.wrapY u) _ a b hx (Village.refl _ _) ht)
   have Hf i: Envelope (f₀ i):=by
      obtain ⟨C,H⟩:= (ht i).cost; refine ⟨(ht i).meas.stronglyMeasurable.integral_prod_right'.measurable,C,fun y=>?_⟩
      have h:Envelope (fun z=>Y i (y,z)):= Env.along (ht i) (measurable_const.prodMk measurable_id)
      exact (norm_integral_le_integral_norm _).trans ((integral_mono (envPlot h X.dice).norm (integrable_const _) (fun z=>H _)).trans_eq (by simp))
   have he i:call X (g i)=∫ z,f₀ i z ∂F.order G:=integral_prod (Y i) (envPlot (ht i) _)
   simp_rw [he]; change (∫ y, ∏ i,Y i y ∂((F.order G).prod X.dice))=_
   rw [integral_prod _ (envPlot (envCasting _ Y (fun i _=>ht i)) _)]; simp_rw [hm]
   apply wideProd _ _ Hf; let J i:= univ.filter fun j:F.Free=> atEdge S j.val∈w i
   have he': (↑(univ:Finset ι):Set ι).PairwiseDisjoint J:=fun i hi j hj hn=> Finset.disjoint_left.mpr fun p h h'=> Finset.disjoint_left.mp (hv hi hj hn) ((mem_filter.mp h).2) ((mem_filter.mp h').2)
   intro l
   apply Pond.marched _ univ J he' _ (fun i _=> (l i).measurable.comp (Hf i).1)
   intro i _ u v hh; apply congr_arg (l i); unfold f₀; apply integral_congr_ae; filter_upwards with z
   exact hr i (X.wrapY u) (X.wrapY v) z z hx ((Village.refl ..).wrap u v fun j h=> hh j (mem_filter.mpr ⟨mem_univ _,h⟩)) rfl
lemma products {ι:Type}[Fintype ι](w :ι→Support c)(g:ι→StampF F T M)(X:Coat T F)(hx:X.x=τ)(hk:X.width=o.K)(hX:X.manifest)(h:∀ i,exposedG H (g i))(hr:∀ i,silence H (w i) (g i)) (hv :(↑(univ:Finset ι):Set ι).PairwiseDisjoint w) : draws X (fun x z=>∏ i,g i x z)=∏ i,draws X (g i):=by
   let f i (j:S.Choices):=call (X.taggedL j) (g i)
   have hm i (p q : S.Choices)(hs:∀ b∈w i,p.1 b=q.1 b) (hp:∀ b:Bond c,b.1∈w i→ p.2 b=q.2 b): f i p=f i q:= call_critical H (w i) (g i) (h i) (hr i) (X.taggedL p) (X.taggedL q) hx hk hX hX ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=>rfl,hs,hp,fun _ _ _=>rfl⟩
   unfold draws; have he i:= lance H w g (X.taggedL i) hx hk hX h hr hv
   simp_rw [he]
   change choiceS (fun p:S.Choices=>∏ i,f i p)=∏ i,choiceS (f i)
   have hh (p:S.SitesChoice): choiceS (fun q:S.BondChoice=> ∏ i,f i (p,q))= ∏ i,choiceS (fun q:S.BondChoice=> f i (p,q)):=by
       let V i:= univ.filter (fun q:Bond c=> q.1∈w i)
       have hV: (↑(univ:Finset ι):Set ι).PairwiseDisjoint V:=fun i hi j hj hn=> Finset.disjoint_left.mpr fun q hz hs=> Finset.disjoint_left.mp (hv hi hj hn) ((mem_filter.mp hz).2) ((mem_filter.mp hs).2)
       let N (i:ι)(q:S.BondChoice):=f i (p,q); have he i (u v:S.BondChoice) (hh:∀ j∈V i,u j=v j): N i u=N i v:=hm i (p,u) (p,v) (fun _ _=>rfl) (fun q h=> hh q (mem_filter.mpr ⟨mem_univ _,h⟩))
       have ha:= fairT (A:=S.patch.Points) (inferInstanceAs (Fintype S.BondChoice)) N V hV he
       convert! ha
   simp_rw [codraft (A:=S.SitesChoice) (B:=S.BondChoice),hh]
   let N (i:ι)(p:S.SitesChoice):=choiceS fun q:S.BondChoice=> f i (p,q); have hN i (u v:S.SitesChoice)(he:∀ j∈w i,u j=v j):N i u=N i v:= congr_arg choiceS (funext fun j=> hm i (u,j) (v,j) he (fun _ _=>rfl))
   have hh:= fairT (inferInstanceAs (Fintype S.SitesChoice)) N w hv hN
   convert! hh
end YM.QCD.Beam
