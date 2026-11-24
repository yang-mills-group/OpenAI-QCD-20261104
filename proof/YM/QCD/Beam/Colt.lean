import YM.QCD.Beam.Grape
/-! # Curve with nonpositive insertions. Transfer measure -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Beam.Pipe
open ConnectedActivityE6
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L:Side}{S:StepData c f}{T:Tube G S}{P:Teller G}{δ β τ μ W C:ℝ} {R:Rep G f}{F:Forest S.ratio}{Q:Target G P}{o :Target.Order G W}
variable {M: Type*} [NormedCommRing M][NormedAlgebra ℝ M][CompleteSpace M][MeasurableSpace M][BorelSpace M][SecondCountableTopology M][FiniteDimensional ℝ M]
variable {H:Cash W τ μ L Q o C T R}{ι:Type}
local notation "D" => Clump S ι
variable (Y:Pipe H F M ι)
def stumpP (V :Config G c)(l:Finset ι)(U:Config G f): M := if Y.eligibleP l then (Real.exp (R.exponent U)*R.activities.gasOccurrence R.p (Y.filterP l) U) • Y.sweepP l V U else 0
def missP (V :Config G c)(U:Config G f): M:=∑' l,Y.stumpP V l U
lemma gEnv (V:Config G c)(l:Finset ι)(h:Y.Viable): Envelope (Y.stumpP V l) :=by
   unfold stumpP; split
   next he=>
      have hp:=H.laws.intake.cap
      have hh : Envelope (fun U=>Real.exp (R.exponent U)):= Envelope.exp (R.exponentEnv hp)
      have hE : Envelope (R.activities.gasOccurrence R.p (Y.filterP l)):=by
         obtain ⟨b,hb,hQ⟩:=hp.labels.boundK
         unfold Activities.gasOccurrence; refine Envelope.piece (Activities.admissible_borel ..) (envCasting _ _ (fun i _ => ⟨hp.labels.forced.meas _,_,(hb _).2⟩)) (Envelope.const _)
      exact Env.scale (hh.mul hE) (envCasting _ _ (fun i _=> h.price i V))
   exact ⟨measurable_const,0,fun _=> (norm_zero : ‖(0:M)‖=0).le⟩
-- rq: R exponent gauge symmetry (can get from Path.Bounds from R.laws). Keep explicit for now.
lemma giB (V:Config G c)(l:Finset ι)(h:Y.Viable)(k:Site f→ G.El)(hp:∀ i,k (S.ratio.embed i)=1)(hg:GaugeInvariant R.exponent)(u:Config G f) : Y.stumpP V l (Lattice.gauge k u)= Y.stumpP V l u:=by
   unfold stumpP; split
   next he=>
      have hv p : R.activities.gasOccurrence R.p p (Lattice.gauge k u) = R.activities.gasOccurrence R.p p u:=by
          unfold Activities.gasOccurrence; simp only [Activities.admissible, gauge_flags,H.laws.intake.cap.labels.forced.sym _ k u]; congr!
      rw [hv,hg k]; apply congr_arg; unfold Pipe.sweepP; exact prod_congr rfl fun i hi=> h.allows i V k hp u
   next he=> rfl
lemma welcomeP (X:Coat T F)(s:D)(l:Finset ℕ): draws X (Y.capacityP s l)= welcome R Q W o.a X l (Y.averageP s.toRight) s.toLeft:=rfl
lemma placesP (X:Coat T F)(h:Y.Viable)(hx:X.x=τ)(hu:X.width=o.K)(v:Finset ι)(hg:GaugeInvariant R.exponent):
      HasSum (fun m:Molecule S=> overhead X R Q.table • Y.heldP X (Finset.disjSum m v)) (S.push R.beta (Y.stumpP X.V v) X.V):=by
   subst τ
   let A :Allocation G S X.x W:=X.χ.profiles G S X.x W H.laws.data.W_pos H.laws.data.room.fiery
   have he := Y.gEnv X.V v h
   let g := Y.stumpP X.V v
   let C (y:Molecule S):=Finset.disjSum y v
   by_cases ht:Y.eligibleP v
   · let w:=Y.averageP v; let f:=Y.sweepP v X.V
     let k:=Y.filterP v
     have hb:g=fun x=> (Real.exp (R.exponent x)*R.activities.gasOccurrence R.p k x) • f x:=funext (fun x=>if_pos ht)
     have hf :=rooted F R k X.V A f g (funds_branch H.laws.data.funds.funds) (fun i=>congr_fun hb i) he (fun u hp U=>Y.giB X.V v h u hp hg U) -- branch arg
     rw [← hf,hb]
     apply HasSum.congr_fun (sherpa X k w H hu (show Envelope f from envCasting _ _ (fun i hi=> h.price i X.V)) (fun a p hz=> let Z:=(preps X a).taggedL p;  envCasting v (fun j (i:F.Slice G × Air _ G)=> Y.virtual j (Z.wrapY i.1) i.2) (fun i _=> h.pays _ Z rfl hu hz.1)) (fun a K y z he hZ=> let J:=((preps X a).taggedL K).wrapY y; prod_congr rfl (fun i _=> h.clicks J rfl hu he.1 i z hZ)))
     intro i; unfold heldP; split
     next hg=>
        have hh:own i=k:=by have hh:= hg.1.2.2; simp only [toRight_disjSum,toLeft_disjSum] at hh; exact hh
        rw [if_pos hh]
        have hf : (preps X (roster i)).approve (own i) R ∧ Layout (roster i) Q.halo X.B i.toLeft := by
           have h₀ : (C i).toLeft=i:=toLeft_disjSum ..; obtain ⟨h0,h1⟩:=hg
           unfold born at h0; simp only [toLeft_disjSum,toRight_disjSum] at h0 h1
           exact ⟨⟨h1,h0.1.2⟩,h0.1.1⟩
        rw [decree,dif_pos hf]; simp only [welcomeP,toLeft_disjSum,toRight_disjSum]; rfl
     next hh=> by_cases hk:own i=k
               · rw [if_pos hk]; unfold decree; rw [dif_neg (fun h=> hh ?_),smul_zero]
                 rcases h with ⟨h,hp⟩; unfold born; simp only [toLeft_disjSum, toRight_disjSum]; exact ⟨⟨⟨hp,h.2⟩,ht,hk⟩,h.1⟩
               rw [if_neg hk,smul_zero]
   have hv i:Y.heldP X (C i)=0:= if_neg (fun h=> ht ((show (C i).toRight=v from toRight_disjSum ..) ▸ h.1.2.1)) -- edit
   have ht':g=fun _=> 0:=funext fun i=>if_neg ht
   change HasSum (fun m=> _ • Y.heldP X (C m)) (S.push _ g X.V)
   rw [ht']; unfold StepData.push; simp only [hv,smul_zero,integral_zero]; exact hasSum_zero
-- push scalarization carried
variable [Fintype ι]
lemma overallP (X:Coat T F)(h:Y.Viable)(hx:X.x=τ)(hu:X.width=o.K)(hg:GaugeInvariant R.exponent): HasSum (fun s:D=> overhead X R Q.table • Y.heldP X s) (S.push R.beta (Y.missP X.V) X.V):=by
    let g (p: Finset ι×Molecule S):D:= p.2.disjSum p.1
    have hi(v:D):Finset.disjSum v.toLeft v.toRight=v:=by ext i; cases i <;> simp
    have he:Injective g:= LeftInverse.injective (show LeftInverse (fun v=> (v.toRight,v.toLeft)) g from fun i=>Prod.ext (toRight_disjSum ..) (toLeft_disjSum ..))
    apply (he.hasSum_iff (fun i h=>False.elim (h ⟨(i.toRight,i.toLeft),hi i⟩))).1
    have hu' k : Integrable (fun U=> S.density R.beta U X.V • Y.stumpP X.V k U) (prior G f):= StepData.push_slice (S.isKernel (funds_branch H.laws.data.funds.funds) _) _ _ (envPlot (Y.gEnv X.V k h) _)
    have Hs : S.push R.beta (Y.missP X.V) X.V= ∑ k,S.push R.beta (Y.stumpP X.V k) X.V:=by unfold StepData.push missP; simp_rw [tsum_fintype,Finset.smul_sum, integral_finsetSum _ (fun i _=>hu' i)]
    rw [Hs]; exact Beam.lapis _ _ fun i=> Y.placesP X h hx hu i hg
lemma filledP (X:Coat T F)(h:Y.Viable)(hx:X.x=τ)(hu:X.width=o.K)(hg:GaugeInvariant R.exponent): HasSum (fun p:Finset D=> overhead X R Q.table • Y.drawP X p) (S.push R.beta (Y.missP X.V) X.V):=by
    let g(p:D):= Ac.Parts Y.gP p; have hh:Injective g:=LeftInverse.injective (show LeftInverse (fun p=>p.biUnion id) g from fun i=> Ac.reconstruct ..)
    have hp i: Y.heldP X i=Y.drawP X (g i):=by
      let s:= g i; have he : s.biUnion id=i:= Ac.reconstruct ..
      refine (congr_arg (Y.heldP X) he.symm).trans <| Y.shackledP h X hx hu s ⟨fun k hi=> (Ac.lives Y.gP i hi).2, Ac.separate ..⟩
    apply (hh.hasSum_iff (fun i ht=>?_)).1
    · apply (Y.overallP X h hx hu hg).congr_fun; intro i; exact congr_arg (overhead X R Q.table • ·) (hp i).symm -- hg shadow
    rw [drawP,if_neg (fun h=> ht ⟨i.biUnion id,Y.huesP h.1⟩),smul_zero]
omit [Fintype ι] -- deletion? variable order cannot omit? 
-- Compiled infinite inventory
-- `Solves` authorizes absolute interchange. Finite row dimensions sufficient real.
def solves (Y:Pipe H F M ι) (V:Config G c):Prop:= Dominated fun i U=>Y.actual i U V
set_option quotPrecheck false
lemma canopyH [NormOneClass M](V:Config G c)(hu:Y.solves V): Dominated (Y.stumpP V):=by
    obtain ⟨w,hw,hP⟩:=hu; have hw' i:0≤w i := (norm_nonneg _).trans (hP i 1)
    have he:= H.laws.intake.cap.labels
    obtain ⟨p₁,hp,hQ⟩:= RG.Activities.gasSeries he
    have hx i:0 ≤ p₁ i := (norm_nonneg _).trans (hQ i 1)
    obtain ⟨C,hC⟩:=(Envelope.exp (R.exponentEnv H.laws.intake.cap)).cost
    let p:=∑' i,p₁ i; have hh:0≤C:= (norm_nonneg _).trans (hC 1); have hh':0≤p:=tsum_nonneg hx
    let g s:=∏ i∈s,w i; refine ⟨fun i=>C*p*g i,(summable_finsetProd_of_summable_nonneg hw' hw).mul_left _,fun i U=>?_⟩
    unfold stumpP; split
    next he=> rw [norm_smul, norm_mul]; refine mul_le_mul (mul_le_mul (hC U) ((hQ _ U).trans ?_) (norm_nonneg _) hh) ((Finset.norm_prod_le i _).trans ?_) (norm_nonneg _) (by positivity)
              · exact hp.le_tsum _ (fun i _=>hx _) -- name
              exact Finset.prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> hP i U)
    rw [norm_zero]; exact mul_nonneg (by positivity) (prod_nonneg fun _ _=> hw' _)
lemma intC [Countable ι] (X:Coat T F)(h:Y.Viable)(hp:Dominated (Y.stumpP X.V)) : Integrable (Y.missP X.V) (prior G f):= by
    have hf i := Y.gEnv X.V i h; have h : Envelope (Y.missP X.V):= ⟨Measurable.tsum (fun i=> (hf i).meas),hp.bound⟩
    exact envPlot h _
lemma mouthsP [Countable ι](X:Coat T F)(h:Y.Viable)(hx:X.x=τ)(ht:X.width=o.K)(hw: GaugeInvariant R.exponent)(hc:Dominated (Y.stumpP X.V))(hp:Summable (Y.heldP X)):HasSum (fun s:D=> overhead X R Q.table • Y.heldP X s) (S.push R.beta (Y.missP X.V) X.V):=by
    let g (p: Finset ι×Molecule S):D:= p.2.disjSum p.1
    have hi(v:D):Finset.disjSum v.toLeft v.toRight=v:=by ext i; cases i <;> simp
    have he:Injective g:= LeftInverse.injective (show LeftInverse (fun v=> (v.toRight,v.toLeft)) g from fun i=>Prod.ext (toRight_disjSum ..) (toLeft_disjSum ..))
    let f₀ (U:Config G f):=S.density R.beta U X.V
    let W i U:=f₀ U • Y.stumpP X.V i U
    have hm:=funds_branch H.laws.data.funds.funds
    have hu' k : Integrable (W k) (prior G _):= StepData.push_slice (S.isKernel hm _) _ _ (envPlot (Y.gEnv X.V k h) _)
    have hΔ(U): (∑' i,W i U)=f₀ U • ((Y.missP X.V) U):=((hc.summable U).hasSum.const_smul (f₀ U)).tsum_eq
    obtain ⟨r,hr,hQ⟩:=hc
    obtain ⟨C',hC⟩:= StepData.density_bound S hm R.beta
    have hY: Summable (fun i=>∫ U, ‖W i U‖ ∂prior G _):=by
       refine Summable.of_nonneg_of_le (fun _=>integral_nonneg fun _=> norm_nonneg _) ?_ (hr.mul_left C')
       intro i; have heU U : ‖W i U‖ ≤ C'*r i:=by
          unfold W; rw [norm_smul]; have he : 0 ≤ f₀ U := StepData.density_positive ..; rw [Real.norm_of_nonneg he]; exact mul_le_mul (hC ..) (hQ _ _) (norm_nonneg _) (he.trans (hC ..))
       exact (integral_mono (hu' _).norm (integrable_const _) heU).trans_eq (by simp)
    have hf:=hasSum_integral_of_summable_integral_norm hu' hY; simp_rw [hΔ] at hf
    let Y' (i):=overhead X R Q.table • Y.heldP X i
    apply (he.hasSum_iff (fun i h=>False.elim (h ⟨(i.toRight,i.toLeft),hi i⟩))).1
    have h(S₀:Finset ι): HasSum (fun i=> Y' (g (S₀,i))) (∫ x,W S₀ x ∂prior G _) := Y.placesP X h hx ht S₀ hw
    have ht' : Summable (Y'∘ g) := (hp.const_smul _).comp_injective he
    have hv : ∑' i,(Y' ∘ g) i=S.push R.beta (Y.missP X.V) X.V:= (ht'.hasSum.prod_fiberwise h).unique hf
    exact hv ▸ ht'.hasSum
lemma allG [Countable ι][NormOneClass M](X:Coat T F)(h:Y.Viable)(hx:X.x=τ)(ht:X.width=o.K)(hw:GaugeInvariant R.exponent)(hp:Y.solves X.V)(hc:Summable (Y.heldP X)):HasSum (fun p: Finset D=> overhead X R Q.table • Y.drawP X p) (S.push R.beta (Y.missP X.V) X.V):=by
    let g(p:D):= Ac.Parts Y.gP p; have hh:Injective g:=LeftInverse.injective (show LeftInverse (fun p=>p.biUnion id) g from fun i=> Ac.reconstruct ..)
    have hp' i: Y.heldP X i=Y.drawP X (g i):=by
      let s:= g i; have he : s.biUnion id=i:= Ac.reconstruct ..
      refine (congr_arg (Y.heldP X) he.symm).trans <| Y.shackledP h X hx ht s ⟨fun k hi=> (Ac.lives Y.gP i hi).2, Ac.separate ..⟩
    apply (hh.hasSum_iff (fun i ht=>?_)).1
    · apply (Y.mouthsP X h hx ht hw (canopyH Y X.V hp) hc).congr_fun; intro i; exact congr_arg (overhead X R Q.table • ·) (hp' i).symm
    rw [drawP,if_neg (fun h=> ht ⟨i.biUnion id,Y.huesP h.1⟩),smul_zero]
end YM.QCD.Beam.Pipe
