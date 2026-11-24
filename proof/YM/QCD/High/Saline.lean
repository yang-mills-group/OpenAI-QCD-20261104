import YM.QCD.High.Petal

/-!
# Deterministic wrapping expansions at a fixed budget point
Uses finite equal distribution of minimum-cost pollen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.High
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k B n b j:ℕ}{p:BudgetPoint}{η u a r t w P q J δ z z' θ σ d A ε:ℝ}{i o:Site c}
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Entr Kites Lunar
variable {ι β:Type}
noncomputable def pinT (d:Bool)(A: RegularAddress c):Support c:= if d then {A.site} else ∅
lemma lessT (d:Bool)(A:RegularAddress c): pinT d A ⊆ A.support:=by cases d<;> simp [pinT,A.anchor]
structure Saline (G:Gem c N ι)(p:BudgetPoint)(t σ a:ℝ)(d:Bool):Prop where
  ink : ∃ f:ι→ℝ,Anchored (fun i=>(G.addr i).site) f (fun i=>coverNumber p.B (G.addr i).support) σ a ∧∀ i,Woven (G.addr i).site (G.addr i).support p t (G.view i) (f i) ∧∀ U,Healthy p.threshold (pinT d (G.addr i)) U→ Sen (G.addr i).site t (G.view i U)≤ f i
variable {h₁:Bool}(G:Gem c N ι)
lemma Saline.law {G:Gem c N ι} (h:Saline G p a t u h₁):Licence p t u a G:=by obtain ⟨f,hf,h⟩:=h.ink; exact ⟨f,hf,fun i=>(h i).1⟩
noncomputable def sheer (v:Bool)(s:ℝ)(i:ι):Grid c→EvenA c N:=masked s (pinT v (G.addr i)) (G.view i)
noncomputable def reef (t:ℝ)(d:Bool):Ruby.Hue c N ι:=⟨fun i=>(G.addr i).support,fun i U=>sheer G d t i U-letters G t U i⟩
lemma keen {Z Y:Support c}(h:Z⊆Y)(s:ℝ)(X:Grid c→EvenA c N)(hp:LocalOn Y X):UsesFinal s Y (masked s Z X):=by
    intro U V he hv; change Y∩_=Y∩_ at hv
    have hh:Healthy s Z U↔ Healthy s Z V:=by
        unfold Healthy; simp_rw [Finset.disjoint_iff_inter_eq_empty]; rw [show Z∩flags s U=Z∩(Y∩flags s U) from (by rw [←inter_assoc, inter_eq_left.mpr h]),hv, ← inter_assoc, inter_eq_left.mpr h]
    by_cases h': Healthy s Z U; · rw [masked_eq _ _ _ _ h',masked_eq _ _ _ _ (hh.mp h'),hp U V he]
    rw [masked_ne _ _ _ _ h',masked_ne _ _ _ _ (mt hh.mpr h')]
variable [Fintype ι]
lemma tilts (hz:0≤ σ)(hc:2 ≤ c.val)(h:Saline G p a σ u h₁) : Saline (air G p.B) p a σ (Φ p.B σ c*u) h₁:=by
    let F:=air G p.B; obtain ⟨f,hp,hQ⟩:=h.ink
    have he (j :Field G p.B): (coverNumber p.B (F.addr j).support:ℝ) ≤ coverNumber p.B (G.addr j.1).support+tollV p.B c:=by
         have hp : coverNumber p.B (F.addr j).support ≤ coverNumber p.B (G.addr j.1).support+tollV p.B c:=(Corona.meets_sum (G.addr j.1).anchor j.2.property.1 p.B).trans_eq (congr_arg _ j.2.property.2.2); exact_mod_cast hp
    refine ⟨fun j=> ‖salve G j‖*f j.1,fun i=>?_ , fun i=> ⟨((hQ i.1).1.byScalar (salve G i)).stretches (subset_union_left) le_rfl,fun U hk=>?_⟩⟩
    · refine ⟨fun j=> ite_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (hQ _).1.travel) (Real.exp_pos _).le) le_rfl,Summable.of_finite, ?_⟩
      apply le_trans _ (mul_le_mul_of_nonneg_left (hp i).2.2 (Real.exp_pos _).le); rw [tsum_fintype,tsum_fintype,Fintype.sum_sigma,Finset.mul_sum]; apply sum_le_sum; intro j _; by_cases hv:(G.addr j).site=i
      · rw [if_pos hv]
        let c':= Fintype.card (Pollen p.B (G.addr j).site); haveI:Nonempty (Pollen p.B (G.addr j).site):=lived hc; let k:ℝ:=c'; let W:= Real.exp (σ*coverNumber p.B (G.addr j).support); let v:=Φ p.B σ c*(f j*W); have hK:0<k:=by unfold k c'; positivity
        apply le_trans (b:=∑ _:Pollen p.B (G.addr j).site,k⁻¹*v) (sum_le_sum (fun r _=>?_))
        · rw [sum_const,card_univ,nsmul_eq_mul]; rw [show ↑(Fintype.card (Pollen _ _))= k from rfl]; rw [mul_inv_cancel_left₀ hK.ne']; -- edit
        · rw [if_pos (show (F.addr ⟨j,r⟩).site=i from hv)]; dsimp only; rw [show ‖salve G (⟨j,r⟩:Field G p.B)‖=k⁻¹ from Real.norm_of_nonneg (inv_nonneg.mpr hK.le)]; apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (he ⟨j,r⟩) hz)) (mul_nonneg (inv_nonneg.mpr hK.le) (hQ j).1.travel)); unfold v W Φ; rw [mul_add,Real.exp_add]; exact Eq.le (by ring)
      unfold air; simp [hv]
    let W:=G.addr i.1; rw [← measures]; change ‖needle W.site N a (salve G i • G.view i.1 U)‖≤_; rw [show needle W.site N a (salve G i • G.view i.1 U)= _ from (map_smul ((needle W.site N a).restrictScalars ℝ) (salve G i) (G.view i.1 U)),norm_smul] -- edit
    exact mul_le_mul_of_nonneg_left (by change ‖needle W.site N a _‖ ≤_; rw [measures]; exact (hQ _).2 _ hk) (norm_nonneg _)
lemma nightG (h:Saline G p a t w h₁)(hp:Crossing G)(hj:0<a)(ht:0≤ t): Purchases (reef G p.threshold h₁) p.threshold p.B t ((Fintype.card (Site c):ℝ)*w) a :=by
    obtain ⟨f,hf,H⟩:=h.ink; have hV:= Licence_g h.law
    refine ⟨⟨?_,fun i U=> ?_,fun i U W hv=> ?_,?_⟩,⟨?_,?_,?_,?_⟩,f,?_,?_⟩
    · intro i U k; suffices g : sways (Lat.rotates N k) ((reef G p.threshold h₁).mean i (gauge k U))=(reef G p.threshold h₁).mean i U by exact congr_arg Subtype.val g
      have he:sways (Lat.rotates N k) (G.view i (gauge k U))=G.view i U:=Subtype.ext (hp.blank.gauge i U k); change sways _ (_-_)=_; rw [map_sub]; exact congr_arg₂ _ (sprayer _ _ _ _ _ _ _ _ (by unfold Healthy; rw [gauge_flags]) he) (sprayer _ _ _ _ _ _ _ _ (by unfold Healthy; rw [gauge_flags]) he)
    · change Regal c N (_-_)=_; rw [map_sub]; exact congr_arg₂ _ (sprayer _ _ _ _ _ _ _ _ Iff.rfl (hp.blank.real i U)) (sprayer _ _ _ _ _ _ _ _ Iff.rfl (hp.blank.real i U))
    · change sways _ (_-_)=_; rw [map_sub]; have he:= hp.blank.num i U W hv; exact congr_arg₂ _ (sprayer _ _ _ _ _ _ _ _ Iff.rfl he) (sprayer _ _ _ _ _ _ _ _ Iff.rfl he)
    · intro s k g hv; obtain ⟨e,he⟩:=hp.rays s k g hv; have h1(i): (G.addr (e i)).support=(G.addr i).support.image (act s):=by rw [(he i).1]; rfl
      refine ⟨e,h1,fun i U=>?_⟩; change Diode _ _ _ _ (_-_)=_; rw [map_sub]; have hi:pinT h₁ (G.addr (e i))= (pinT h₁ (G.addr i)).image (act s):=by rw [(he i).1]; cases h₁ <;> simp [pinT,rotateL]
      exact congr_arg₂ _ (sprayer _ _ _ _ _ _ _ _ (hi.symm ▸ (healthy_image ..).symm) ((he i).2 U)) (sprayer _ _ _ _ _ _ _ _ ((h1 i).symm ▸ (healthy_image ..).symm) ((he i).2 U))
    · intro i V U he hQ; exact congr_arg₂ (·-·) (keen (lessT h₁ (G.addr i)) p.threshold (G.view i) (hV.sees i) V U he hQ) (clearUse _ i (hV.sees _) _ V U he hQ)
    · intro i; exact (masked_measurable _ _ _ (hV.reads i)).sub (masked_measurable _ _ _ (hV.reads i))
    · intro i V hN hx; apply hN; change (masked _ _ (G.view i) V)- _ =_; rw [masked_eq _ _ _ _ (hx.mono_left (lessT h₁ (G.addr i))),letters,masked_eq _ _ _ _ (show Healthy p.threshold (G.addr i).support V from hx),sub_self]
    · intro i V; refine wingsZ _ _ _ ?_ (licit G hV i V); unfold sheer
      by_cases hv:Healthy p.threshold (pinT h₁ (G.addr i)) V; · rw [masked_eq _ _ _ _ hv]; exact hV.role i V
      rw [masked_ne _ _ _ _ hv]; exact Fleet.spruce _
    · intro i V; apply le_trans (b:=Sen (G.addr i).site a ((reef G p.threshold h₁).mean i V)) (shot (lens _) _ _ hj); change Sen _ _ (masked p.threshold (pinT h₁ (G.addr i)) (G.view i) V- letters _ _ _ _ ) ≤ _
      by_cases hv:Healthy p.threshold (G.addr i).support V; · rw [letters,masked_eq _ _ _ _ hv,masked_eq _ _ _ _ (hv.mono_left (lessT h₁ (G.addr i))),sub_self,← measures,map_zero,norm_zero]; exact (H i).1.travel
      rw [letters,masked_ne _ _ _ _ hv,sub_zero]; by_cases hx:Healthy p.threshold (pinT h₁ (G.addr i)) V; · rw [masked_eq _ _ _ _ hx]; exact (H i).2 V hx
      rw [masked_ne _ _ _ _ hx,← measures,map_zero,norm_zero]; exact (H i).1.travel
    intro U; refine ⟨fun i=> ite_nonneg (mul_nonneg (H _).1.travel (Real.exp_pos _).le) le_rfl,Summable.of_finite,?_⟩; rw [tsum_fintype]
    let Z (i: ι):= f i*Real.exp (t*coverNumber p.B (G.addr i).support); let g (i:ι)(u: Site c):= if (G.addr i).site=u then Z i else 0; have hh(x: Site c): (∑ i,g i x)≤w:=by
        have hp := (hf x).2.2; rw [tsum_fintype] at hp; exact hp
    apply le_trans (b:= ∑ i:ι,∑ x:Site c,g i x) (sum_le_sum _); swap; · intro i _; unfold g; simp only [sum_ite_eq',mem_univ,↓reduceIte,sum_ite_eq]; split; exact le_rfl; exact mul_nonneg (H _).1.travel (Real.exp_pos _).le
    rw [sum_comm]; simpa using sum_le_sum (s:=univ) (fun i _=> hh i)
end YM.QCD.High
