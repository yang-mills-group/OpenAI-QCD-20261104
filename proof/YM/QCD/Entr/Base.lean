import YM.QCD.Entr.Draft
/-! # mass at a point tag and missing money. initiate inverse sign assembly. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Entr
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume
variable {Γ:Silo c}{A: BankP c}{U:St c}
variable {ι β:Type}(G:Gem c N ι)(F:Gem c N β)(b:Flavor N)
noncomputable def pointQ (N:ℕ) (c:Side):Gem c N (Site c):=⟨fogX,fun i _=> paleF N (localX i 1)⟩
lemma stemQ (N:ℕ)(p:BudgetPoint)(hz:0<a): AnchorT (pointQ N c) p a q (Real.exp q*9*fingers N^2*‖goldW‖*a^2) :=by
    let P:=pointQ N c; let C:=9*fingers N^2*‖goldW‖; have hh:0≤C:=by unfold C; positivity
    refine ⟨fun _=>C*a^2,fun i=>?_ ,fun i=>?_⟩
    · have hp(i: Site c):coverNumber p.B {i}=1:= by
        obtain ⟨D,hD,h'⟩:=coverNumber_realized p.B ({i}:Support c); apply le_antisymm _ _
        · have ht:=Corona.tile i 0 p.B p.B_pos; exact (Corona.cover_mono (halo_subset _ _) _).trans ht |>.trans (by omega)
        rw [← h']; have hh:= hD.1 (Finset.mem_singleton_self i); obtain ⟨j,hj,-⟩:=halo_spec.mp hh; exact card_pos.mpr ⟨j,hj⟩
      refine ⟨fun j => ite_nonneg (by positivity) le_rfl, Summable.of_finite,?_⟩; rw [tsum_fintype]; unfold pointQ fogX; simp only; simp [hp,C]; ring_nf; rfl
    let v:=P.view i 1; have hx: Sen i a v≤ C*a^2:=by simpa only [norm_one,mul_one,v,C,P,pointQ] using boardFee (o:=i) hz 1 N
    refine ⟨⟨fun _ _ _=> rfl, fun V=>?_ ,fun i _=> contDiffAt_const,?_ , measurable_const,by positivity⟩,fun _=>hx⟩
    · change Gated {i} v; unfold v P; change Gated {i} (paleF N _); rw [siteBl]; exact padBl _ _ _ (mem_singleton_self i) (mem_singleton_self i)
    intro W hv l he h; cases l with
    | nil=> exact hx
    | cons j l=> rw [←measures, show leftDerivs _ _ _=(0:EvenA c N) from Work.G07.left_const ..,map_zero,norm_zero]; positivity
lemma siteD (c:Side)(o:Site c):foldH (localX o 1)=localX o 1:=by
    change chirality c * star _*chirality c=_; rw [localStar,star_one]; unfold chirality; rw [rentsL,rent_rev,mul_one, g5_sq]
lemma passQ (N:ℕ)(c:Side): Crossing (pointQ N c):=by
    refine ⟨⟨fun i V k => ?_,fun i V=> form_fit (localX i 1) N,fun i V=> dusted c N (localX i 1) (siteD c i).symm⟩,fun s W g hv=>⟨act s,fun i=>⟨?_ ,fun U=>?_⟩⟩⟩
    · let B:=siteRot k
      apply congr_arg Subtype.val (Port.rayTrade (Lat.copies N B) (copies_unitary _ _ (siteRot_u k)) (localX i 1) (localX i 1) ?_); rw [←copies_star,← Lat.copies_mul,← Lat.copies_mul]; apply congr_arg; rw [show B * _=_ from (commG i 1 k).eq,Matrix.mul_assoc,(siteRot_u k).2,mul_one]
    · unfold pointQ fogX rotateL; simp
    apply rayTrade _ (copies_unitary _ _ (trail hv)); rw [←copies_star,← Lat.copies_mul,← Lat.copies_mul]; apply congr_arg; have he:=principal i 1 hv; rw [mul_one,hv.2.unit.2] at he; rw [← he, Matrix.mul_assoc,(trail hv).2, mul_one]
lemma stemSum (V:Grid c) (N:ℕ): (∑ i,(pointQ N c).view i V) = paleF N (1:Sheet c):=by change (∑ i:Site c,nozzle _ _ _ )=_; rw [← map_sum, volley 1 c,on_spin_one]; rfl
lemma choices : qMass (till (pointQ N c) b 0)=1 ∧ qWave (till (pointQ N c) b 0)=0:=by
    let i:Site c:=0; have hp:Nonwrapping {i} i:=fun j hj=> (mem_singleton.mp hj).symm ▸ (show 10* separation i i<c.val from by simp)
    let B:=till (pointQ N c) b 0; have he x : B x=if x=none then 1 else 0:=by
       unfold B till unitM; change _=_; rw [tsum_fintype,sum_eq_single (0:Site c)]; rotate_left
       · intro j _ hj; rw [if_neg]; exact hj.symm
       · simp
       rw [if_pos (show (0:Site c)= ((pointQ N c).addr 0).site from rfl)]; unfold Stew.lane Stew.mote; rw [if_pos (show Nonwrapping (((pointQ N c).addr 0).support) ((pointQ N c).addr 0).site from hp),show feeF b ((pointQ N c).view 0 1)=localX 0 1 from forceP (localX (0:Site c) 1) b]; exact atO ..
    change qMass B=1∧qWave B=0; unfold qMass qWave muVal sineVal; simp [he]
noncomputable def offT (E:Gem c N ι)(t:ℝ): Ruby.Hue c N ι:=⟨fun i=>(E.addr i).support, fun i U=> E.view i U-letters E t U i⟩
lemma starsX (h:AnchorT G p a u w)(hp:Crossing G)(hj:0<a)(ht:0≤ t)(hq:t+1+1 ≤ u): Purchases (offT G p.threshold) p.threshold p.B t (payment 1 (4*p.B+2) 0 1 1 w t 0) a :=by
    obtain ⟨f,hf,H⟩:=h.peg; have hV:= Licence_g h.law
    refine ⟨⟨?_,fun i U=> ?_,fun i U W hv=> ?_,?_⟩,⟨?_,?_,?_,?_⟩,f,?_,?_⟩
    · intro i U k; suffices g : sways (Lat.rotates N k) ((offT G p.threshold).mean i (gauge k U))=(offT G p.threshold).mean i U by exact congr_arg Subtype.val g
      have he:sways (Lat.rotates N k) (G.view i (gauge k U))=G.view i U:=Subtype.ext (hp.blank.gauge i U k); change sways _ (_-_)=_; rw [map_sub]; exact congr_arg₂ _ he (sprayer _ _ _ _ _ _ _ _ (by unfold Healthy; rw [gauge_flags]) he)
    · change Regal c N (_-_)=_; rw [map_sub]; exact congr_arg₂ _ (hp.blank.real i U) (sprayer _ _ _ _ _ _ _ _ Iff.rfl (hp.blank.real i U))
    · change sways _ (_-_)=_; rw [map_sub]; have he:= hp.blank.num i U W hv; exact congr_arg₂ _ he (sprayer _ _ _ _ _ _ _ _ Iff.rfl he)
    · intro s k g hv; obtain ⟨e,he⟩:=hp.rays s k g hv; have h1(i): (G.addr (e i)).support=(G.addr i).support.image (act s):=by rw [(he i).1]; rfl
      refine ⟨e,h1,fun i U=>?_⟩; change Diode _ _ _ _ (_-_)=_; rw [map_sub]; exact congr_arg₂ _ ((he i).2 U) (sprayer _ _ _ _ _ _ _ _ ((h1 i).symm ▸ (healthy_image ..).symm) ((he i).2 U))
    · intro i V U he hQ; exact congr_arg₂ (·-·) (hV.sees i _ _ he) (clearUse _ i (hV.sees _) _ V U he hQ)
    · intro i; exact (hV.reads i).sub (masked_measurable _ _ _ (hV.reads i))
    · intro i V hN hx; apply hN; change (G.view i V)- _ =_; rw [letters,masked_eq _ _ _ _ (show Healthy p.threshold (G.addr i).support V from hx),sub_self]
    · intro i V; exact wingsZ _ _ _ (hV.role i V) (licit G hV i V)
    · intro i V; apply le_trans (b:=Sen (G.addr i).site a ((offT G p.threshold).mean i V)) (shot (lens _) _ _ hj); change Sen _ _ (G.view i V- letters _ _ _ _ ) ≤ _
      by_cases hv:Healthy p.threshold (G.addr i).support V; · rw [letters,masked_eq _ _ _ _ hv,sub_self,← measures,map_zero,norm_zero]; exact (H i).1.travel
      rw [letters,masked_ne _ _ _ _ hv,sub_zero]; exact (H i).2 V
    exact Footprint.assigned (v':=1) id 1 (fun Y: Support c=> by simp) _ f (fun i=>(H i).1.travel) _ _ hf _ 0 _ (fun i x hx=> Geo.enlarged_dist p (G.addr i) x (show x∈expand _ from mem_union_left _ hx)) (fun i=> by change (coverNumber p.B (G.addr i).support:ℝ)≤ _; simp) zero_le_one ⟨ht,by norm_num,by linarith⟩ f (fun i=>(H i).1.travel) (by simp)
end YM.QCD.Entr
