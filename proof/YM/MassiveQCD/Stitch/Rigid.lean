import YM.MassiveQCD.Stitch.Mint
/-! # Full reading radii aperture valid for these Borel words on the charged system -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Stitch
open QCD QCD.Grass QCD.Lat QCD.Creek Lattice Wilson RG QCD.Cove QCD.Cove.Send QCD.Creek.Ledge
open Function Ribbon Finset Filter MeasureTheory NormedSpace Fj
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I E D J:Type} [Fintype I] {N:ℕ} {f c:Side}{P:Rise f N E J}
local notation "S"=> Spine I
local notation "X'"=> Keys f N⊕Spine I
local notation "Y'"=> Keys c N⊕Spine I
variable (X:Tablet P I)
namespace Tablet
variable {R:Ratio c f}{t:ℝ}
variable (G:Send R N D)
local notation "A"=> Modes f N
local notation "B"=> Modes c N
local notation "W"=> Junta c f N
variable {q:I→Bool}{o:I→Site f}(hw:X.Wave t q o) {M:Fj D E J→Support c} (h:Cove.Count G P M)
include hw
lemma mort (s:Finset (Fj D E J)) : UsesFinal t (brimW G P s) (fun U=> X.made t U s):=by
  intro U V h H
  unfold made; apply congr_arg₂
  · apply prod_congr rfl; intro i hi
    have hx : (P.row i).support ⊆ brimW G P s:= fun j hj=> (native_sub G P s) (mem_biUnion.mpr ⟨Sum.inr (.inl i),by simpa [Fj.leftE] using hi,hj⟩)
    have he:=flag_under t hx H
    have hA: Healthy t (P.row i).support U ↔ Healthy t (P.row i).support V:=by simp only [Healthy, Finset.disjoint_iff_inter_eq_empty,he]
    apply congr_arg (fun x:Tine f N I=> exp x-1); unfold read; by_cases H':Healthy t (P.row i).support U; · rw [masked_eq _ _ _ _ H', masked_eq _ _ _ _ (hA.1 H')]; exact hw.use i _ _ (agrees_mono h hx)
    rw [masked_ne _ _ _ _ H', masked_ne _ _ _ _ (mt hA.2 H')]
  apply prod_congr rfl; intro i hi
  have hx :(P.front i).place ⊆brimW G P s:=fun j hj=> (native_sub G P s) (mem_biUnion.mpr ⟨Sum.inr (.inr i), by simpa [Fj.spent] using hi,hj⟩)
  exact hw.oblige i _ _ (agrees_mono h hx) (flag_under t hx H)
lemma dyed (s:Finset (Fj D E J)): UsesFinal t (brimW G P s) (X.dye t G s):=by
  intro U V H h; apply Subtype.ext; change carry S _ _=carry S _ _; rw [show X.made t U s=X.made t V s from mort X G hw s U V H h]; apply vista (Keys c N); intro i; rw [wing,wing]; unfold tunnel; let x:=scrape _ i (light _ (X.made t V s)); rw [show axle G U s=axle G V s from ax_loc G P s U V (agrees_mono H (native_sub G P s))]; exact framed_eq G P s U V H _ (lamp G s V x ((X.lights_made G hw s V).2 i))
lemma ears (s: Finset (Fj D E J)) : UsesFinal t (brimW G P s) (X.hue t G s):=by
    intro U V h H; unfold hue closeS; rw [inter_comm (flags t U),H,inter_comm _ (flags t V)]; rw [dyed X G hw s U V h H]
lemma collectible (s:Finset (Fj D E J)): Measurable (fun x=>X.made t x s):=by
   unfold made; apply Measurable.mul; exact Finset.measurable_prod _ fun i _=> (NormedSpace.exp_continuous.measurable.comp (masked_measurable _ _ _ (hw.measure i))).sub measurable_const; exact Finset.measurable_prod _ fun i _=> hw.budget i
set_option maxHeartbeats 490000 in
lemma glory (s:Finset (Fj D E J)): Measurable (X.hue t G s):=by
   unfold hue; by_cases he:P.spare (Fj.spent s); swap; · simp only [he,false_and,if_false]; exact measurable_const
   simp only [he,true_and]; apply Measurable.ite (flag_s G P t s) _ measurable_const; have hx (i: Finset S): Measurable (fun U=> scrape _ i (X.dye t G s U).val):=by
      let f1 U:= scrape _ i (X.made t U s).val
      let w U:= tunnel G s U (f1 U); have hz : Continuous (fun z: Grid f × Fields f N=>tunnel G s z.1 z.2):=by
         apply wipeC.comp (f:=fun z: Grid f × Fields f N=> (G.shortP z.1, axle G z.1 s (near _ _ z.2))) (?_); exact (G.vibe.comp continuous_fst).prodMk (((ax_cont G s).comp continuous_fst).clm_apply (((nearL _ _ _).continuous).comp continuous_snd))
      have ht:Measurable f1:= ((scrape (Keys f N) _).measurable).comp ((lightC X').measurable.comp (collectible X hw s)); have he: Measurable w:=by letI : SecondCountableTopology (Grid f):=inferInstance; let g := fun U => (U,f1 U); let x := (fun z:Grid f × Fields f N=> tunnel G s z.1 z.2); have hm:Measurable g:=measurable_id.prodMk ht; haveI :SecondCountableTopology (Fields f N):=inferInstance; haveI :SecondCountableTopology (Fields c N):=inferInstance; have hH:Measurable x:= hz.measurable; change Measurable (x ∘ g); exact hH.comp hm
      change Measurable (fun U=>scrape (Keys c N) i (carry _ _ _)); simp_rw [wing]; exact he
   apply Measurable.subtype_mk; change Measurable fun U=>(X.dye t G s U).val; rw [show (fun U=>(X.dye t G s U).val)= _ from funext fun U=> (rewriteR ..).symm]; exact Finset.measurable_sum _ fun i _=> ((stake (Keys c N) _).measurable).comp (hx i) -- scope syntax
omit hw
lemma minimal (V:Type)[Fintype V](a:V→ℝ)(ha:∀ i,1 ≤ a i) (x:Patio V):‖x‖ ≤ load a x.val:=by
   rw [dry a (fun i=>zero_lt_one.trans_le (ha i))]; change ‖light _ x‖ ≤_; rw [Grass.norm_def]; refine sum_le_sum fun i _=>?_ ; exact le_mul_of_one_le_left (norm_nonneg _) (Finset.one_le_prod (fun a _=> ha a))
open QCD.Loom QCD.Jets QCD.Jets.Touch
-- copy
set_option maxHeartbeats 500000 in
lemma affordable {z κ o' h u:ℝ}{n:ℕ}{g:E→ℝ}{p:J→ℝ}(h1:Coins X g p h t)(hF:Fill P g p u u o' κ z n)(hv:1≤o')(hp:1≤h) :∀ x,X.Staid t x:=by
    have hG:=sumRide _ _ _ hF.χ h1.pos hF.bud; let a i:=(P.front i).inv.card; let v i:=p i*o'^(a i); have hh i:p i≤ v i:= le_mul_of_one_le_right (h1.non i) (one_le_pow₀ hv)
    have hS:Summable p:= Summable.of_nonneg_of_le h1.non hh (fishes _ v hF.ε (fun i=> (h1.non i).trans (hh i)) hF.bud (fun i _=> (P.front i).alive.mono (P.front i).part))
    have hf(i:X'):1 ≤ chip h _ _ i:=by cases i; exact hp; exact le_rfl
    intro U; refine ⟨Summable.of_norm_bounded hG (fun i=> (minimal X' _ hf (X.read t U i)).trans (h1.ready i _)),?_ , Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> (minimal X' _ hf (X.plug i U)).trans (h1.fee i _)) hS⟩
    refine Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> ((minimal X' _ hf (exp (X.read t U i)-1)).trans (bought (chip h (Keys f N) S) (X.read t U i) (g i) (h1.ready i U))).trans ?_) (hG.mul_left (Real.exp z))
    have he:=Real.add_one_le_exp (-g i); rw [Real.exp_neg] at he; have hC:= mul_le_mul_of_nonneg_right he (Real.exp_pos (g i)).le; rw [add_mul,inv_mul_cancel₀ (Real.exp_ne_zero (g i))] at hC
    have hx:= mul_le_mul_of_nonneg_left (Real.exp_monotone (anchored_each _ _ _ hF.χ hF.bud h1.pos i)) (h1.pos i); linarith

end Tablet
end YM.MassiveQCD.Stitch
