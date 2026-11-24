import YM.Elms.Pruner
/-! # Rank readout with even pacing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace PrismD
variable (H: SourceRead.TaperHol)(K:Hol su)
open QCD.Kites Beacon -- glowing conflict
open Next.Foundations
lemma readSquare(f g:ℝ→ℂ) (d:ℕ)(hf:ContDiffAt ℝ d f 0)(hg:ContDiffAt ℝ d g 0)(hh: ∀ i:ℕ,i≤d/2→ iteratedDeriv i f 0=iteratedDeriv i g 0): Response d (fun t:ℝ=>f (t^2)) (fun t:ℝ=>g (t^2)) 0:=by
   let v(t:ℝ):=t^2; have hv:v 0=0:=by unfold v; norm_num
   have hx:ContDiffAt ℝ d v 0:=contDiffAt_id.pow _; have hg':ContDiffAt ℝ d g (v 0):= hv.symm ▸ hg; have hf':ContDiffAt ℝ d f (v 0):=hv.symm ▸ hf
   have ht {F G: ℝ→ℂ}{i:ℕ}(h: iteratedDeriv i F 0=iteratedDeriv i G 0): iteratedFDeriv ℝ i F 0=iteratedFDeriv ℝ i G 0:=by apply ContinuousMultilinearMap.ext; intro m; simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,h]
   refine ⟨hf'.comp (f:=v) _ hx,hg'.comp _ hx,fun i hi=> ht ?_⟩ -- f unification check
   change iteratedDeriv i (f∘v) 0=iteratedDeriv i (g ∘ v) 0; rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hf' hx (Nat.cast_le.mpr hi),iteratedDeriv_vcomp_eq_sum_orderedFinpartition hg' hx (Nat.cast_le.mpr hi),hv]; refine Finset.sum_congr rfl (fun p _=>?_); by_cases h:p.length ≤ d/2; · rw [ht (hh p.length h)]
   have hm: ∃ j:Fin p.length, p.partSize j ≠ 2:=by
      by_contra! he
      have hh:p.length*2=i:=by
        have h:(∑ j,p.partSize j)=i:= by simpa using p.sum_sigma_eq_sum (fun _=>(1:ℕ))
        simp only [he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at h; exact h
      omega
   obtain ⟨j,hj⟩:=hm; let f0:= fun i=> iteratedDeriv (p.partSize i) v 0; have hz: f0 j=0:=by unfold f0 v; rw [iteratedDeriv_fun_pow_zero,if_neg hj]; norm_num
   exact ((iteratedFDeriv ℝ p.length f 0).map_coord_zero j hz).trans ((iteratedFDeriv ℝ p.length g 0).map_coord_zero j hz).symm
lemma sight (S: Stenc) (d:ℕ):∃ N:ℕ,∀ n:Side,N ≤ n.val→Merian.SmallT n S d:=by
   obtain ⟨r,hr⟩:= (Permit.eventual S).exists; exact ⟨20*(r+d+2), fun n he x hx a=> (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right (hr x hx a) d) 2)).trans he⟩ -- right+ sig
lemma seesAll (S:Stenc)(x: Stenc)(v:ℝ)(p:Labels.Jet su)(hs: Merian.SmallT n S d): Lattice.Agrees (S:Set Cover) (expandAt (wrap n o) (current (c:=n) H o d p v)) (K.links (d/2) p (v^2)):=by
    intro i hi he; change views H o d _ _ = _; unfold views offset spark; simp only [add_sub_cancel_right, Merian.lift_gain S _ hs (show i.1∈S from hi)]; rw [← Beacon.focused]; exact Merian.localFlare H K S i hs hi p v d
lemma linearTime (p:Pol d)(Q: Labels.Jet su) (f:ℝ→SpinPol d)(h:SourceRead.Agrees f (SourceRead.desired p Q)): SourceRead.Agrees f (SourceRead.desired (setas d p).val Q):=by
   have ht:= PrismD.dry p Q; exact ⟨h.1,ht.2.1,fun i hi=>(h.2.2 i hi).trans (ht.2.2 i hi)⟩ -- dry submodule
lemma groundSlot(s:Slot)(i:su.ColorIndex) (p:GPol)(hp: Forms K (d/2) (Push.Mark.slotted su s i) p)(hq: Peg K (d/2)):TravelsP H (tendency s i) (setas d (coarse d p)):=by
    let S:= s.stencil; obtain ⟨N,hN⟩:=sight S d; refine ⟨N, fun n o hn J=>linearTime _ _ _ ?_⟩
    let b:=d/2; let A: ℂ→L[ℝ] SpinPol d:= (((LinearMap.toSpanSingleton ℂ (SpinPol d) 1).restrictScalars ℝ).toContinuousLinearMap)
    let f(t:ℝ):ℂ:= slotted su s i (K.links b J t); let g(t:ℝ):ℂ:=Labels.read (scaleJet J t) p; have hz : ContDiffAt ℝ d f 0:=by
        have hE {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E](i:ℕ)(x:E): ContDiffAt ℝ (d:WithTop ℕ∞) (fun t:ℝ=> t^i • x) 0:= (contDiffAt_id.pow i).smul contDiffAt_const
        let Z(t:ℝ): Snap su b:= trunk b (scaleJet J t); have hZ: ContDiffAt ℝ d Z 0:=contDiffAt_pi.mpr fun i=> by change ContDiffAt ℝ d (fun t:ℝ=> t^(i.val+2) • J i.val) _; exact hE (i.val+2) (J i.val)
        have hZ': Z 0=0:=by funext i; simp [Z,trunk,scaleJet]
        let L := Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜:=ℝ) i); rw [show f= L∘ takes K b s ∘ Z from funext fun i=> by unfold f; rw [Drops.scales]; rfl]; refine L.contDiff.contDiffAt.comp (f:=takes K b s ∘ Z) (0:ℝ) (ContDiffAt.comp (0:ℝ) ?_ hZ); rw [hZ']; exact (hq.shot s).contDiffAt.of_le le_top
    have h := (readSquare f g d hz (Next.Foundations.read_smooth J p _).contDiffAt (hp.through J)).linear A |>.smooth_compare
    have hh: Beacon.moment H o J (tendency s i n o)=fun v:ℝ=>A (f (v^2)):=by funext v; unfold Beacon.moment; change adapter _ _ (slotted su s i _ • _) = _; rw [map_smul,map_one]; unfold slotted f; rw [s.covered (expandAt (wrap n o) (current H o d J v)) (K.links b J (v^2)) (seesAll o H K S S v J (hN n hn))]; rfl
    rw [hh]; have hy(v:ℝ) : SourceRead.desired (coarse d p) J v=A (g (v^2)):=by rw [← observe,observation,LinearMap.comp_apply,coarse,ready_t,AlgHom.toLinearMap_apply,map_smul,map_one]; rfl
    rw [funext hy]; exact h
-- θ limit projection determined by lower number & one.
noncomputable abbrev stunt (d:ℕ)(p:Labels.Pol su)(t:ℝ):Mini d:= (t:ℂ)⁻¹ • (prism t 1 d (setas d (coarse d p)))
lemma spent (i: PowerPair d) (t:ℝ): prism t 1 d (setas d (gen i))=(t:ℂ)^Poised.Sieve.life i.1 • setas d (gen i):=by rw [prism_set,widths_m,map_smul]; simp
lemma speed0 (p:Labels.Pol su)(hp:p∈Push.Mark.floorSlots 2)(d:ℕ) : Tendsto (stunt d p) (𝓝[>] 0) (𝓝 0):=by
     -- weighted coefficients
     let m:=p.support; let f(i: UV.Powers):=MvPolynomial.monomial i (1:ℂ); let c(i):=MvPolynomial.coeff i p
     obtain ⟨L,hL⟩:=coarseL (d:=d); let F(t:ℝ):= prism t 1 d ∘ₗ setas d ∘ₗ L; have hx(i)(t:ℝ): F t (f i)=(t:ℂ)^life i • setas d (L (f i)):=by
        change prism _ _ _ (setas d (L _))=_; rw [hL]; exact Eq.mp (congr_arg (fun z=> prism t 1 d (setas d z)=(t:ℂ)^life i • setas d z) (show gen (d:=d) (i,∅)=coarse d (f i) by simp [gen, f,coarse])) (spent (i,∅) t)
     have he : p=∑ i∈m,c i • f i:=by unfold f; simp only [MvPolynomial.smul_monomial,smul_eq_mul,mul_one]; exact p.support_sum_monomial_coeff.symm
     have hh(i)(hi:i∈m): 2 ≤ life i:=by have hx: 2 ≤ (Push.Mark.weight i).2:= Push.Mark.stamp_monotone (a:=(0,2)) (b:= Push.Mark.weight i) ((MvPolynomial.mem_restrictSupport_iff ℂ).mp hp hi); unfold Push.Mark.weight at hx; rw [Labels.weight_slot] at hx; exact hx
     have hQ(t:ℝ)(ht:0<t): stunt d p t=∑ i∈m, c i • ((t:ℂ)^(life i-1) • setas d (L (f i))):=by
         change (t:ℂ)⁻¹ • _=_; rw [show prism t 1 d _=F t p from ?_]; swap; · change prism _ _ _ _=prism _ _ _ (setas d (L _)); rw [hL]
         rw [he,map_sum,Finset.smul_sum]; refine Finset.sum_congr rfl (fun i hi=>?_); rw [map_smul,hx,smul_comm (t:ℂ)⁻¹ (c i),smul_smul]; have hf:=hh i hi; rw [show (t:ℂ)^life i=(t:ℂ)*(t:ℂ)^(life i-1) from by rw [← pow_succ', Nat.sub_add_cancel (by omega)],smul_smul, mul_assoc, inv_mul_cancel_left₀ (by exact_mod_cast ht.ne'), smul_smul]
     let g(t:ℝ):=∑ i∈m,c i • ((t:ℂ)^(life i-1) • setas d (L (f i))); have hf:Continuous g:=continuous_finsetSum m fun i _=> ((Complex.continuous_ofReal.pow _).smul (continuous_const (y:=setas d (L (f i))))).const_smul (c i)
     rw [← (show g 0=0 from Finset.sum_eq_zero fun i hi=>by rw [Complex.ofReal_zero,zero_pow (by have :=hh i hi; omega),zero_smul, smul_zero])]; exact ((hf.tendsto 0).mono_left nhdsWithin_le_nhds).congr' (eventually_nhdsWithin_of_forall (fun i hi=> (hQ i hi).symm))
lemma speed1 (q:Pulled su (d/2))(v:ℝ)(hv:0<v): stunt d (spell (d/2) q) v=setas d (coarse d (spell (d/2) q)):=by
   have he(i:Labels.Key su):widths (d:=d) v 1 (coarse d (MvPolynomial.X i))=(v:ℂ) • coarse d (MvPolynomial.X i):=by
         let y:PowerPair d:= (Finsupp.single i 1,∅); have he:gen y=coarse d (MvPolynomial.X i):=by simp only [gen,mono_empty,y]; rfl
         rw [← he,widths_m]; simp [y,life]
   obtain ⟨L,hL⟩:=coarseL (d:=d); let p:= spell (d/2) q; have hp: widths v 1 (coarse d p)=(v:ℂ) • coarse d p:=by
       rw [←hL]; unfold p spell literal; simp only [map_sum,map_smul, Finset.smul_sum]; rw [hL]; simp_rw [he]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [smul_comm]
   rw [stunt,prism_set,hp,map_smul,inv_smul_smul₀ (by exact_mod_cast hv.ne')]
lemma growsSlot (s:Slot)(i:su.ColorIndex)(hq: Peg K (d/2)): Survey H (tendency s i) 1 0 (setas d (coarse d (spell (d/2) (safeLinear K (d/2) s i)))):=by
   obtain ⟨p,hp,hF⟩:= Push.Mark.slot_readout K s (d/2) i hq
   refine ⟨ratedS .., setas d (coarse d p),groundSlot H K _ _ _ hp hq,?_⟩ -- o? no
   obtain ⟨F,hf⟩:=coarseL (d:=d); let q:= spell (d/2) (safeLinear K (d/2) s i); let X:=setas d (coarse d q); let f:=speed0 (p-q) hF d; change Tendsto _ _ (𝓝 X); rw [show X= (0:Mini d)+X from (zero_add _).symm]; refine (f.add (tendsto_const_nhds (x:=X))).congr' ?_; refine eventually_nhdsWithin_of_forall (fun t ht=>?_); change stunt d (p-q) t+X=_; rw [show stunt d (p-q) t=stunt d p t - stunt d q t from (by unfold stunt; rw [←hf,map_sub,map_sub,map_sub,smul_sub]),show stunt d q t=X from speed1 _ _ ht,sub_add_cancel]; simp only [stunt,pow_one] -- `ht:p∈ _`
end PrismD
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.PrismD.growsSlot
