import YM.Play.Bonnet
import YM.Play.Lago
set_option linter.unusedSectionVars false
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
variable {j k m i k₁ n:ℕ}
variable {z η p h a a' hQ v δ b s u q:ℝ}{P' : Plan k}{X:Run.St f}
variable (L':Flight j k)(d:f.val=c.val*L'.L.val)(K:KernelChoices)
local notation "S'"=> Flight.visit L' K d
variable {T:Tube su (Flight.visit L' K d)}{W' :ℕ→Atom su 2}
variable (H:Cash W τ μ L'.L Q o C T (trimP T O δ β b))
variable {P₀:Rise f N E J} [Countable E][Countable J]
variable (G:Sun L' c f d η h z a a' m X) (U :Swathe L' d X W' P' h η a u v i)
variable (Γ:Land c (Site c) (Site c)){D':Pays c (Site c) (Site c)}
variable [Fintype I] (Y:Stitch.Tablet P₀ I)(A:I→Site f)(φ:ℝ)
local notation "M"=> Ribbon.ample N I
local notation "R'"=> trimP T O δ β b
local notation "B"=> radiusB τ
local notation "M'"=> highR L τ
local notation "Z'"=> G.equip N (radiusB τ)
local notation "Zⁱ"=> roof (G.equip N (radiusB τ)) P₀ 30 B
local notation "Y'" => closet H (G.equip N (radiusB τ)) (Zⁱ) Y A φ
local notation "U'" => loommark I (VarnC H U N)
local notation "X'" => loommark I (sailP H Γ N)
local notation "Vx" => tableau L' d K P₀ H G U Γ
local notation "Tx"=> vantage L' d K H G U Γ Y A φ
local notation "Uq"=> deckHue H (Z') P₀ (Zⁱ)
open Anomaly Play Chamber Camp Cupola
open Stitch Stitch.Tablet
local notation "Ip"=> Wound Zⁱ
local notation "X0"=> Keys f N ⊕ Spine I
local notation "X1"=> Keys c N ⊕ Spine I
local notation "K0"=> Keys f N
local notation "K1"=> Keys c N
variable {m₁:ℕ}
namespace Grove
-- degree on arbitrary subsets.D
set_option quotPrecheck false
local notation "Az"=> Modes f N
local notation "Bz"=> Modes c N
local notation "Πz"=> picksV f m B
omit [Countable E] [Countable J] in
lemma tunneled (x:Patio X0)(U:Grid f)(s:Finset (Fj (Tr f) E J))(hp:ops s ⊆ Πz)(hx:x.val∈ Rim univ i): carry (Spine I) (tunnel (Z') s U) x.val ∈ Rim (univ:Finset X1) i:=by
    let P(v:Finset (Tr f)):=pin v (leftE s) (spent s); let A:=P (ops s); have hs:A=s:=pinch s
    let F(v:Finset (Tr f)):= tunnel (Z') (P v) U; let V v:=carry (Spine I) (F v) x.val; suffices he:∀ n:ℕ,∀ v:Finset (Tr f), v.card=n→ v⊆ ops s → V v ∈ Rim univ i by
       have ht:=he _ _ rfl (Subset.refl _); exact Eq.subst (motive:=fun j=> carry (Spine I) (tunnel (Z') j U) _ ∈ Rim univ i) hs ht
    intro k; induction k using Nat.strong_induction_on with
    | h k ih=>
      intro v hk he
      let T1:= ∑ j∈v,(Z').treats j U; let H:= (wipeL (Z') U).comp ((birth T1).comp (nearL f c N)); have hr:(∑ j∈v.powerset,V j)=carry (Spine I) H x.val:=by
         apply vista K1; intro p; rw [map_sum,wing]; unfold H; rw [show birth T1=_ from (dripe _ (fun i j=>(Z').hat U i j) v).symm]; dsimp only [_root_.ContinuousLinearMap.comp_apply]; rw [_root_.sum_apply,map_sum]; apply sum_congr rfl; intro j _; unfold V F Stitch.Tablet.tunnel Cove.axle; rw [wing]; simp only [P,pinC]; rfl
      have hh : v = v.toLeft.image (Sum.inl) :=by
         ext j; constructor; · intro hj; obtain ⟨i,h,rfl⟩:=mem_image.mp (hp (he hj)); exact mem_image.mpr ⟨_,mem_toLeft.mpr hj,rfl⟩
         intro hi; obtain ⟨b,h,rfl⟩:=mem_image.mp hi; exact mem_toLeft.mp h
      let W:=∑ j∈v.toLeft,ship G.X j (settled U) (F:= N); have hv:T1 = pond (head Az Bz) W:=by
        unfold T1; nth_rw 1 [hh]; rw [sum_image Sum.inl_injective.injOn]; exact pony G v.toLeft U
      have hf: (carry (Spine I) H x.val)∈ Rim univ i:=by
          unfold H; rw [hv]; exact (emitBy (Spine I) W ((Z').shortP U) x).symm ▸ (splashMem (breezeP (Spine I) _) (breezeX (Spine I) _) (fun _ _ j _=>mem_univ j) hx)
      have hQ : V v= (∑ i∈v.powerset,V i)-(∑ i∈ v.powerset.erase v,V i) :=by rw [← Finset.add_sum_erase _ V (mem_powerset_self v),add_sub_cancel_right]
      rw [hQ]; refine Submodule.sub_mem _ (hr.symm ▸ hf) (Submodule.sum_mem _ fun i hi=>ih _ ((Finset.card_lt_card (lt_of_le_of_ne (mem_powerset.mp (mem_of_mem_erase hi)) (ne_of_mem_erase hi))).trans_le hk.le) i rfl ((mem_powerset.mp (mem_of_mem_erase hi)).trans he))
-- hereditary cardinal bound
variable {q₀:I→Bool}
local notation "wP"=> X0
private lemma vague {A K:Type} [Fintype A](P:K→Finset I)(s:Finset K) (f:K→Patio (A⊕Spine I)) (h:∀ i∈ s,f i∈ VaultP A q₀ (P i)) (ht:∀ i∈ s,f i∈ Bera.vaultS univ ((P i).card*n)):
   (∏ i∈s,f i) ∈ Bera.vaultS univ ((s.biUnion P).card*n):=by
      induction s using Finset.induction_on with
      | empty=> rw [prod_empty]; exact Rim.one (univ : Finset (A⊕ Spine I)) (n:=((∅:Finset K).biUnion P).card*n)
      | insert i s hi ih=>
        rw [prod_insert hi,biUnion_insert]; have hh:= h i (mem_insert_self ..); have hx:=ht _ (mem_insert_self ..)
        by_cases hD: Disjoint (P i) (s.biUnion P)
        · rw [Finset.card_union_of_disjoint hD,Nat.add_mul]; exact Rim.multiply hx (ih (fun j hj=>h j (mem_insert_of_mem hj)) (fun j hj=>ht j (mem_insert_of_mem hj)))
        rw [smash hh (vp s (fun i hi=> h i (mem_insert_of_mem hi))) hD]; apply Submodule.zero_mem
variable (e:Finset E) 
local notation "Pe"=>pin (picksV f m B) e (∅:Finset J)
local notation "O+"=> omegaE Zⁱ Y (fun (_ : Varn f c⊕Gaze c)=>∅)
variable (hCost:∀ j∈e,∀ U:Grid f,Y.read O.threshold U j∈ QCD.Bera.vaultS univ ((Y.spine j).card*n))
variable (hw:Y.Wave O.threshold q₀ A) (he:∀ i∈ e,(Y.spine i).Nonempty)
include hCost hw he
lemma bonsai (U:Grid f) (s:Ip) (hp:s.val⊆Pe): Y.hue O.threshold (Z') s.val U∈ QCD.Bera.vaultS univ ((Y.markers s.val).card*n):=by
    have hD:ops s.val⊆Πz:= fun j hj=>inl_mem_disjSum.mp (hp (mem_toLeft.mp hj)); have hK:=TabletV.spentP s.val Pe hp (pinK ..)
    have ht i(hi:i∈leftE s.val):i∈e:=inl_mem_disjSum.mp (inr_mem_disjSum.mp (hp (mem_toRight.mp (mem_toLeft.mp hi))))
    let Z:= (Y.markers s.val).card*n; have hx: Y.made O.threshold U s.val∈ Bera.vaultS univ Z:=by
       unfold Z Stitch.Tablet.made markers; rw [hK,biUnion_empty,union_empty,prod_empty,mul_one]; let f i:=Y.read O.threshold U i; have hh i (hi:i∈leftE s.val):NormedSpace.exp (f i)-1=f i:=by rw [Chamber.launch ((Y.lights_read hw U i).1) (he _ (ht i hi)),add_comm,add_sub_cancel_right]; -- semicolon
       rw [prod_congr rfl (g:=f) hh]; exact vague Y.spine _ _ (fun j _=> (Y.lights_read hw ..).1) (fun j hj=>hCost _ (ht j hj) _)
    unfold Stitch.Tablet.hue; split; · exact tunneled L' d G (τ:=τ) _ U s.val hD hx
    exact Submodule.zero_mem _
-- outpost vertex color postage before log
local notation "loc"=> S'.ratio.parent∘A
local notation "TZ"=> (withdraw N ((S').ratio.parent∘ A) φ)
variable (V:Tree.Forest (Flight.visit L' K d).ratio)
open PhysicalNext.Repeat.Greenbelt
lemma hunch (i:Ip)(hv:i.val⊆Pe)(X:Coat T V)(z:Air f su)(hp:0<φ): TZ ((Tx).coming (.inl i) X z)∈ Bera.vaultS univ ((Y.markers i.val).card*n):=by
    let T:= X.input (X.liftA β z); let D:=(Tx).riseP X z (Sum.inl i); let P:=δ⁻¹^Loom.budget P₀ i.val
    let q:=(TZ).toLinearMap.restrictScalars ℝ; let C:=(QCD.Bera.vaultS (univ:Finset X1) ((Y.markers i.val).card*n)).restrictScalars ℝ
    change q (D • (P • banknote N _ φ (Y.hue O.threshold (Z') i.val T)))∈ C; rw [map_smul,map_smul,show q (banknote N _ _ _) = Y.hue O.threshold (Z') i.val T from Cupola.home N _ φ hp _]; exact C.smul_mem _ (C.smul_mem _ (bonsai L' d G _ A e hCost hw he T i hv))
set_option maxHeartbeats 450000 in
lemma afterglow (i:Ip)(hv:i.val⊆Pe)(Ux:Grid c)(χ:Chi)(hp:0<φ)(hh:(Tx).Famous): TZ ((Tx).vF (badge Zⁱ (S') _ i) χ Ux)∈ Bera.vaultS univ ((Y.markers i.val).card*n):=by
    let Q:= Tx; let s:= badge Zⁱ (S') (Varn f c ⊕ Gaze c) i; let q:= LinearMap.toContinuousLinearMap ((TZ).toLinearMap.restrictScalars ℝ); let C:=(Bera.vaultS (univ:Finset X1) ((Y.markers i.val).card*n)).restrictScalars ℝ
    change q ((Fintype.card (Reserve (S')):ℝ)⁻¹ • ∑ r:Reserve (S'),_)∈ C; rw [map_smul,map_sum]; refine C.smul_mem _ (Submodule.sum_mem _ fun l _=>?_); let p:= prism T τ χ o.K Ux (allot l); let Yt1:=Q.suitcase (allot l)
    change q (Yt1.shootsP p s)∈ _; unfold Pipe.shootsP; split; swap; · rw [map_zero]; exact Submodule.zero_mem _
    next hY =>
     unfold draws choiceS; rw [map_smul,map_sum]; refine C.smul_mem _ (Submodule.sum_mem _ fun t _=>?_); unfold call
     let H :=(Matter.planted p s.toLeft).taggedL t; let M₀:=((allot l).order su).prod H.dice; let g := Yt1.capacityP s (own s.toLeft); let f(x:(allot l).Slice su × Air f su):=g (H.wrapY x.1) x.2
     have he': Envelope f:= Yt1.ripeP _ s (Q.forwarded _ hh) H rfl rfl (planted_valid ..); have hI:= envPlot he' M₀
     change q (∫ x,f x ∂M₀)∈ C; rw [← q.integral_comp_comm hI]; refine C.convex.integral_mem (Submodule.closed_of_finiteDimensional C) (Eventually.of_forall (?_)) (q.integrable_comp hI); intro x; unfold f g Pipe.capacityP; rw [map_smul]; apply C.smul_mem; unfold Pipe.averageP; rw [show s.toRight={Sum.inl i} from (by ext; simp [s,badge]),prod_singleton]; exact hunch L' d K _ G U Γ Y A φ e hCost hw he (allot l) _ hv _ x.2 hp
lemma bitterV (i:Clusters (Tx).Bright) (Ux:Grid c)(χ:Chi)(hp:0<φ) (hh:(Tx).Famous)(hR:Regal N ((S').ratio.parent∘ A) φ q₀ (vantage L' d K H G U Γ Y A φ) (omegaE (Zⁱ) Y (fun _=>∅))): TZ (port H (Z') (Zⁱ) Y A φ (united (loommark I (VarnC H U N)) X') Pe χ Ux i)∈ Bera.vaultS univ ((swingE N (Tx) (O+) i).card*n):=by
    let F i:=(deathT (S:=S') O+ i); let p (j):=i.2 j; unfold Play.Camp.port; split; swap; · rw [map_zero]; apply Submodule.zero_mem
    next hW=>
     let S:=Tx; change TZ (S.honest _ _ _)∈ _; rw [Fleet.phoenix S χ Ux hh]; unfold termP; -- smul_map ℝ
     have hm x (r:ℝ): TZ (r • x)= r • TZ x:=map_smul ((TZ).toLinearMap.restrictScalars ℝ) ..
     let s:= (swingE N S (O+) i).card*n; let C:= (Bera.vaultS (univ:Finset X1) s).restrictScalars ℝ; rw [hm,hm, map_prod]; refine (C.smul_mem _ (C.smul_mem _ (vague (q₀:=q₀) (fun j=>F (p j).val) univ _ (fun j _=> ?_) (?_)))) -- coefficients real? inspect
     · exact (markets N ((S').ratio.parent∘A) φ q₀ (Tx) O+ hR hp _ χ Ux).shows
     intro j _; obtain ⟨k,hk,r⟩:=hW j; have hX: F (p j).val= Y.markers k.val:=by unfold F p; rw [r, deathT,show (badge Zⁱ (S') (Varn f c ⊕ Gaze c) k).toRight={Sum.inl k} from (by ext; simp [badge]),singleton_biUnion]; rfl; -- simp rer
     rw [hX]; change TZ (S.vF _ _ _)∈_; rw [r]; exact afterglow L' d K _ G U Γ Y A φ e hCost hw he k hk Ux χ hp hh
end Grove
end YM.MassiveQCD.Apron
#print axioms YM.MassiveQCD.Apron.Grove.bonsai
#print axioms YM.MassiveQCD.Apron.Grove.bitterV
