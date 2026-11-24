import YM.QCD.Dust.Peak
/-! # E pair-holonomy principal cost sans AUTH HaloMask. On pulled mean. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Dust
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Lat Kit Grass Brick Cove Stew ConnectedActivityE6.Blaze Push.Uniform Patron Reggae AnalyticBridge.LocalGaussian.Moments AnalyticBridge.VerifiedReset
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio} {L:Side}
    {P B : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q M m r t x τ W w σ G₀ ρ v R : ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N j : ℕ} {D : Slab su c l} {q : Chi} {d u : ℝ} {f' : Config su f → ℝ} {H:Grid f→EvenA f N}
variable {C: Libretto su n}{E: Record}
-- establish caller representation Sign.Shape
structure Feast (B:BudgetPoint)(X:Support f)(o:Site f)(b:Flavor N)(H:Grid f→EvenA f N)(W τ:ℝ) : Prop where
 wine : Woven o X B W H τ
 view : shadeG H
 art x: Fit (H x)
 joy x: Regal f N (H x)=H x
 rack : ∀ y,Stew.shape o (feeF b (H 1)) y=0
 base :Heir.Seed B o X ((Reggae.river f N) ∘ H)
lemma flour {b:Flavor N} (h:Feast B X o b H W τ)(hp:0 ≤ W): let y (v: Grid f):= octave (H v); Woven o X B W y (2*τ) ∧ Sign y b o:=by
    intro y; obtain ⟨h1,h2⟩:= spores o X _ h.wine h.view hp; have he := h.wine.addition ((wealthy N _ _ _ h1 h2 hp).byScalar (-1)); rw [norm_neg,norm_one,one_mul,neg_one_smul,←two_mul] at he
    have hc:y=H + (- (fun x=>ocean f N (Reggae.river f N (H x)))):=by funext x; exact sub_eq_add_neg ..
    refine ⟨hc.symm ▸ he,?_,?_,?_,?_⟩
    · intro i; exact chooseP _ (h.joy i)
    · intro i U; let p:= H (gauge U i); suffices a : sways (rotates N U) (octave p)= y i from congr_arg Subtype.val a
      have hg: sways (rotates N U) p=H i:=Subtype.ext (h.view ..); rw [octave,map_sub,hg, Reggae.thorough ..]; change _= octave (H i); rw [octave,← hg, mur]
    · intro U g hh; unfold y octave; rw [map_sub,h.art U g hh]; exact congr_arg₂ (·-·) rfl (Reggae.thorough ..)
    intro i; change Stew.shape o (meter b (H 1- _)) i=_; rw [map_sub,show meter b (ocean f N _)=0 from reduceF b _,sub_zero]; exact h.rack i
variable (Z:Hera.Rights su n)(a:Museum F x A X Y I) [Fintype I]
    (hp:Plays C E P B Pt T x) (hg :Canvas P (S.ratio.parent o) (reach x) V g n C.C)
variable (hz:Short S B X)(hk:5≤n)(ho:o∈X)(hV: Healthy P.threshold Y V) (U:Config su f)(hu:0 ≤u)
variable (p':Kit.Rail f c)(hΦ: Warp S.patch.L o (S.ratio.parent o) p' N W w t m)(G: Crate c N→L[ℝ]ℝ)(hG:∀ X, ‖G X‖ ≤ Stew.plank (S.ratio.parent o) w X)
variable {b:Flavor N}(h:Feast B X o b H W τ)(k q d) {Γ:Prices su I→ℝ}(hΓ:Silences su I n u (E.ε*B.threshold) Γ)
def carryFee (C : Libretto su n) (Z:Hera.Rights su n)(m:ℝ):= flareN Z 2 (Jive m)+2+Lute.phrase C
include hΦ hG Z hp hg hz hk ho hV hu hΓ h
local notation "θ₁"=> C.M * loom P (reach x) C.C
local notation "L₀"=>S.patch.L
set_option maxHeartbeats 380000 in
lemma flowers (ht : θ₁ ≤1)(hy:tender Z 1 θ₁ ≤fern L₀^5) (j:ℕ): let Y' := (carryFee C Z m)*τ *fern L₀^5
    Hera.Fugue a U (skimR (g∘ S.ratio.parent) G p' H) T C E P B j Γ u Y' k q d o V:=by
   intro y; obtain ⟨hX,hΘ⟩:= flour h hΦ.ready.le; let p:=g ∘ S.ratio.parent; let M (x):=octave (H x)
   have hP:=ebony k q d Z a hp hg hz hk ho hV U hu p' hΦ G hG hX hΘ hΓ ht hy j
   let v(x):=Reggae.river f N (H x); let L : ℝ→L[ℝ]ℝ:= G.comp ((bill p' N).comp (ocean f N)); let Y:= skimR p G p' M; let X₀:=skimR p G p' H
   have hh' r: ‖L r‖ ≤ ‖r‖:=by
       change ‖G (bill p' N (ocean f N r))‖≤_
       apply (hG _).trans; change Stew.plank (S.ratio.parent o) w (apple p' N (ocean f N r).val) ≤ _; exact (hΦ.along (ocean f N r).val).trans_eq (vintage o r _ hΦ.way.le)
   have hL : ‖L‖ ≤1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> (hh' _).trans (by rw [one_mul]))
   have he(z): X₀ z = Y z + L (v z):=by
       have hv:v (gauge p z)=v z:= (h.base.good.symmetry _ _) -- gaugeInvariant 
       unfold X₀ Y skimR; rw [show H (gauge p z)= M (gauge p z)+ocean f N (v z) from Eq.symm (by rw [← hv]; exact sub_add_cancel ..)]; rw [map_add,map_add]; rfl
   intro z hz'; let u':= u; obtain ⟨h1,h2⟩:= hP z hz'; obtain ⟨h3,h4⟩:= hp.prior (k:=k) (q:=q) (d:=d) a h.base hV YM.QCD.simple U z hu (hΓ.stay z hz') (spores _ _ _ h.wine h.view hΦ.ready.le).2
   refine ⟨?_,fun i hi D hD=>?_⟩
   · let f' (y: Directions su c × Prices su I):=a.received k T q d u (increment V y.1) U y.2
     change ContDiffAt ℝ (↑n) (fun y=> X₀ (f' y)) (0,z); rw [show (fun y=> X₀ (f' y))=(Y ∘ f')+(L ∘ (v ∘ f')) from funext fun i=>he _]
     have hh : ContDiffAt ℝ (↑n) (Y ∘ f') (0,z):=h1; exact hh.add (L.contDiff.contDiffAt.comp (f:=v ∘ f') (0,z) h3)
   let P₀ (x:Panels i):= a.received k T q d u (journey V i D x) U z
   let g(w):= X₀ (P₀ w); let v':= (v ∘ P₀)
   -- need smooth from h1,h3 with journey and point. via Germ.prod etc
   have ht (g:Grid f→ℝ)(he:ContDiffAt ℝ n (fun y : Directions su c × Prices su I=> g (a.received k T q d u (increment V y.1) U y.2)) (0,z)): ContDiffAt ℝ i (g∘P₀) 0 :=by
       let Q(x):=g (a.received k T q d u x U z); have hR:Germ n Q V:= he.comp (f:=fun i=> (i,z)) 0 (contDiffAt_id.prodMk contDiffAt_const)
       exact Germ.journeys D (hR.prod hi) -- inspect names
   have hy': v'=fun x=> Reggae.river f N (H (P₀ x)):=rfl
   change ‖iteratedFDeriv ℝ i g 0‖ ≤ _; rw [show g=(Y ∘ P₀)+(L ∘ v') from (funext fun x=> he _), iteratedFDeriv_add_apply (ht Y h1) (L.contDiff.contDiffAt.comp 0 (ht v h3))]
   have hd := (L.norm_iteratedFDeriv_comp_left (ht v h3) (n:=i) le_rfl).trans ((mul_le_of_le_one_left (norm_nonneg _) hL).trans (h4 i hi D hD))
   apply (norm_add_le ..).trans; apply (add_le_add (h2 i hi D hD) hd).trans

   apply (add_le_add_right (mul_le_mul_of_nonneg_right (Lute.pay_le (L:=S.patch.L) (X:=X) (C:=C) (D:=E) (P:=P) (B:=B) (r:=j) (x:=x) hu z) h.wine.travel) _).trans_eq; rw [show Lute.decay B S.patch.L X=fern S.patch.L^5 from if_pos hz]; unfold y carryFee flareN; ring
end YM.QCD.Dust
