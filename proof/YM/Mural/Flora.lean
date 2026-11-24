import YM.MassiveQCD.Stitch.Rigid
/-! As Stitch, but the local estimates do not impose the scalar color law on the single component. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Stitch
open QCD QCD.Grass QCD.Lat QCD.Creek Lattice Wilson RG QCD.Cove QCD.Cove.Send QCD.Creek.Ledge
open Function Ribbon Finset Filter MeasureTheory NormedSpace
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I E D J:Type} [Fintype I] {N:ℕ} {f c:Side}
variable {P:Rise f N E J}
local notation "S"=> Spine I
local notation "X'"=> Keys f N⊕Spine I
local notation "Y'"=> Keys c N⊕Spine I
variable (X:Tablet P I)
namespace Tablet
structure Flora (t:ℝ)(q:I→Bool)(o:I→ Site f):Prop where
    use i: LocalOn (P.row i).support (X.main i)
    showAt i u : lights (X.spine i) (P.row i).support o q (X.main i u)
    measure i: Measurable (X.main i)
    oblige i: UsesFinal t (P.front i).place (X.plug i)
    chair i u: lights (X.shadow i) (P.front i).place o q (X.plug i u)
    budget i:Measurable (X.plug i)
    owes i u:(X.plug i u)≠0 → flags t u∩ (P.front i).place=(P.front i).inv
    spotE i: (X.spine i).image o ⊆ (P.row i).support
    spotK i: (X.shadow i).image o⊆ (P.front i).place
variable {t:ℝ} {R:Ratio c f}
variable (G:Send R N D)
open Fj
variable {q:I→Bool}{o:I→Site f}(hw:X.Flora t q o)
include hw
lemma lights_peek (u:Grid f)(i:E): lights (X.spine i) (P.row i).support o q (X.read t u i):=by
    unfold read; by_cases he:Healthy t (P.row i).support u
    · rw [masked_eq _ _ _ _ he]; exact hw.showAt i u
    rw [masked_ne _ _ _ _ he]; exact ⟨polite_nil ..,clad.nil _⟩
-- joint lands (Valuation carriers)
lemma lights_col (s: Finset (Fj D E J))(u:Grid f): lights (X.markers s) (coreW G P s) o q (X.made t u s):=by
    let e i:= exp (X.read t u i)-1; let Y:= coreW G P s
    have h(i)(hi:i∈leftE s):lights (X.spine i) Y o q (e i):=by
        obtain ⟨hv,hF⟩:=X.lights_peek hw u i; exact ⟨attire hv, hF.expR.raise (limitsMon _ _ (fun j hj=> mem_biUnion.mpr ⟨(.inr (.inl i)),by simpa [leftE] using hi,hj⟩))⟩
    let y i:=X.plug i u; have he(i)(hi:i∈spent s): lights (X.shadow i) Y o q (y i):=by
        obtain ⟨hv,hF⟩:=hw.chair i u; exact ⟨hv,hF.raise (limitsMon _ _ (fun j hj=>mem_biUnion.mpr ⟨(.inr (.inr i)),by simpa [spent] using hi,hj⟩))⟩
    obtain ⟨h1,h2⟩:= candlehouse e X.spine _ Y h; obtain ⟨h3,h4⟩:= candlehouse y X.shadow _ Y he; exact ⟨h1.attached h3,h2.mul h4⟩
end Tablet
end YM.MassiveQCD.Stitch
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
variable {q:I→Bool}{o:I→Site f}(hw:X.Flora t q o) {M:Fj D E J→Support c} (h:Cove.Count G P M)
include hw
lemma extent2 (s:Finset (Fj D E J)) : (X.markers s).image o ⊆ coreW G P s:=by
   intro i hi; obtain ⟨k,hk,rfl⟩:=mem_image.mp hi; rcases mem_union.mp hk with he|he
   · obtain ⟨i,hi,he'⟩:= mem_biUnion.mp he; exact mem_biUnion.mpr ⟨Sum.inr (Sum.inl i), by simpa [leftE] using hi,hw.spotE i (mem_image_of_mem _ he')⟩
   obtain ⟨i,hi,he'⟩:= mem_biUnion.mp he; exact mem_biUnion.mpr ⟨Sum.inr (Sum.inr i),by simpa [spent] using hi, hw.spotK i (mem_image_of_mem _ he')⟩
include h in
lemma endowment2 (s:Finset (Fj D E J)) : (X.markers s).image (R.parent∘o)⊆s.biUnion M:=by
   rw [← Finset.image_image]; exact (Finset.image_subset_image ((X.extent2 G hw s).trans (native_sub G P s))).trans (totalW G P h s)
omit hw

private lemma hatch2 (s:Finset (Fj D E J))(y:Grid f)(x: Alg (Keys f N))(ht:x∈ region (limits (coreW G P s)))(Z:Support c)(he:(halo G.trim (coreW G P s)).image R.parent ⊆ Z): tunnel G s y x ∈ region (limits Z):=by
   refine effects (wipe A B (G.shortP y)) ?_ _ (lamp G s y x ht); intro i hi; rcases splits_index i with ⟨v,rfl⟩|⟨v,rfl⟩
   · change ha _ _ _ v∈_ at hi; rw [hooked,rootA] at hi; rw [wiper]; refine Subalgebra.sum_mem _ (fun j _=>?_); by_cases hx:G.shortP y v j=0; · rw [hx,zero_smul]; exact Subalgebra.zero_mem _
     apply Subalgebra.smul_mem; apply marked; exact mem_filter.mpr ⟨mem_univ _,he (mem_image.mpr ⟨_, (Corona.halo_mono (le_refl _) (singleton_subset_iff.mpr hi) (G.sleeps v j y hx)), R.embed_parent _⟩)⟩
   change hb _ _ _ v∈_ at hi; rw [hooked,rootB] at hi; rw [tails]; apply marked; exact mem_filter.mpr ⟨mem_univ _,he (mem_image.mpr ⟨R.embed _,halo_subset _ _ hi,R.embed_parent _⟩)⟩
include hw h in
lemma lights_field (s:Finset (Fj D E J))(U:Grid f): lights (X.markers s) (s.biUnion M) (R.parent∘o) q (X.hue t G s U):=by
    unfold hue; split
    · obtain ⟨hp,hp'⟩:=X.lights_col G hw s U; exact ⟨politeStep _ hp rfl,reCarry _ _ _ (fun x hx=> hatch2 G _ U x hx _ (by
                                                                                                                                     exact (Finset.image_subset_image (show halo _ _⊆ brimW G P s by rw [brim_eq]; exact Corona.halo_mono (by omega) (Subset.refl _))).trans (totalW G P h s))) _ hp'⟩
    exact ⟨polite_nil ..,clad.nil _⟩
include h hw
lemma textured2 (s w:Finset (Fj D E J))(U:Grid f)(hp:Disjoint s w)(he:Disjoint (s.biUnion M) (w.biUnion M)): X.dye t G (s∪w) U=X.dye t G s U* X.dye t G w U:=by
   let NN:=carry S (nearL f c N); let p (i:Finset (Fj D E J)):= (X.made t U i).val; let W₁ (i:Finset (Fj D E J)):=carry S (axle G U i); let WW:= carry S (wipeL G U); have ht(i):clad (hooks (F:=N) R (coreW G P i)) (NN (p i)):= reCarry (nearL f c N) (limits _) _ (fun x h=>remit G i x h) _ (X.lights_col G hw i U).2; apply Subtype.ext; change carry S _ _ = carry S _ _*carry S _ _; unfold tunnel; simp_rw [← composes]; rw [unionM X t U hp];
   change WW (carry S (axle G U (s∪w)) (NN (p s*p w)))=WW (W₁ s _) *WW (W₁ w _); rw [show NN (p s*p w) = NN (p s)*NN (p w) from ledger_alg (near A B) (fun x=> (embed_grade _ x).symm) ..,join_ax G U hp,widespread _ _ (forces G P U s) (forces G P U w) (rotor G P h he) (ht _) (ht _)]; exact ledger_alg (wipe ..) (fun x=>(exterior_parity _ x).symm) ..
lemma hueSpare2 {U:Grid f}{s w:Finset (Fj D E J)}(hp:Disjoint s w)(he:Disjoint (s.biUnion M) (w.biUnion M)): X.hue t G (s∪w) U=X.hue t G s U *X.hue t G w U:=by
    unfold hue; rw [spares G P h he,close_join G P t h U he,textured2 X G hw h s w U hp he]; split_ifs <;> simp_all
open Further.ShellBirth49.Fusing Collide
lemma hue_product2 (s: Finset (Finset (Fj D E J)))(U:Grid f)(hp:(s:Set (Finset (Fj D E J))).PairwiseDisjoint (fun p=>p.biUnion M))(hr:(s:Set (Finset (Fj D E J))).PairwiseDisjoint id):
    X.hue t G (s.biUnion id) U=∏ p∈s,X.hue t G p U:=by
    induction s using Finset.induction_on with
    | empty=> rw [biUnion_empty,hue_empty,prod_empty]
    | insert i s hi ih=>
      have hQ : Disjoint i (s.biUnion id) := Finset.disjoint_left.mpr (fun j hj hk=>by
        obtain ⟨k,hk,hz⟩:=mem_biUnion.mp hk; exact Finset.disjoint_left.mp (hr (mem_insert_self ..) (mem_insert_of_mem hk) (fun he=>hi (he ▸ hk))) hj hz)
      have hP : Disjoint (i.biUnion M) ((s.biUnion id).biUnion M) := Finset.disjoint_left.mpr fun j hj hk=>by
        obtain ⟨k,hk,hz⟩:=mem_biUnion.mp hk; obtain ⟨p,hp',hk⟩:=mem_biUnion.mp hk; exact Finset.disjoint_left.mp (hp (mem_insert_self ..) (mem_insert_of_mem hp') (fun he=> hi (he ▸ hp'))) hj (mem_biUnion.mpr ⟨k,hk,hz⟩)
      rw [biUnion_insert,id_eq,prod_insert hi,hueSpare2 X G hw h hQ hP]; apply congr_arg
      exact ih (Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.subset_insert ..)) hp) (Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.subset_insert ..)) hr)
end Tablet
end YM.MassiveQCD.Stitch
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
variable {q:I→Bool}{o:I→Site f}(hw:X.Flora t q o) {M:Fj D E J→Support c} (h:Cove.Count G P M)
include hw
lemma mort2 (s:Finset (Fj D E J)) : UsesFinal t (brimW G P s) (fun U=> X.made t U s):=by
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
lemma tintedV (s:Finset (Fj D E J)): UsesFinal t (brimW G P s) (X.dye t G s):=by
  intro U V H h; apply Subtype.ext; change carry S _ _=carry S _ _; rw [show X.made t U s=X.made t V s from mort2 X G hw s U V H h]; apply vista (Keys c N); intro i; rw [wing,wing]; unfold tunnel; let x:=scrape _ i (light _ (X.made t V s)); rw [show axle G U s=axle G V s from ax_loc G P s U V (agrees_mono H (native_sub G P s))]; exact framed_eq G P s U V H _ (lamp G s V x ((X.lights_col G hw s V).2 i))
lemma ears2 (s: Finset (Fj D E J)) : UsesFinal t (brimW G P s) (X.hue t G s):=by
    intro U V h H; unfold hue closeS; rw [inter_comm (flags t U),H,inter_comm _ (flags t V)]; rw [tintedV X G hw s U V h H]
lemma collectionV (s:Finset (Fj D E J)): Measurable (fun x=>X.made t x s):=by
   unfold made; apply Measurable.mul; exact Finset.measurable_prod _ fun i _=> (NormedSpace.exp_continuous.measurable.comp (masked_measurable _ _ _ (hw.measure i))).sub measurable_const; exact Finset.measurable_prod _ fun i _=> hw.budget i
set_option maxHeartbeats 490000 in
lemma glory2 (s:Finset (Fj D E J)): Measurable (X.hue t G s):=by
   unfold hue; by_cases he:P.spare (Fj.spent s); swap; · simp only [he,false_and,if_false]; exact measurable_const
   simp only [he,true_and]; apply Measurable.ite (flag_s G P t s) _ measurable_const; have hx (i: Finset S): Measurable (fun U=> scrape _ i (X.dye t G s U).val):=by
      let f1 U:= scrape _ i (X.made t U s).val
      let w U:= tunnel G s U (f1 U); have hz : Continuous (fun z: Grid f × Fields f N=>tunnel G s z.1 z.2):=by
         apply wipeC.comp (f:=fun z: Grid f × Fields f N=> (G.shortP z.1, axle G z.1 s (near _ _ z.2))) (?_); exact (G.vibe.comp continuous_fst).prodMk (((ax_cont G s).comp continuous_fst).clm_apply (((nearL _ _ _).continuous).comp continuous_snd))
      have ht:Measurable f1:= ((scrape (Keys f N) _).measurable).comp ((lightC X').measurable.comp (collectionV X hw s)); have he: Measurable w:=by letI : SecondCountableTopology (Grid f):=inferInstance; let g := fun U => (U,f1 U); let x := (fun z:Grid f × Fields f N=> tunnel G s z.1 z.2); have hm:Measurable g:=measurable_id.prodMk ht; haveI :SecondCountableTopology (Fields f N):=inferInstance; haveI :SecondCountableTopology (Fields c N):=inferInstance; have hH:Measurable x:= hz.measurable; change Measurable (x ∘ g); exact hH.comp hm
      change Measurable (fun U=>scrape (Keys c N) i (carry _ _ _)); simp_rw [wing]; exact he
   apply Measurable.subtype_mk; change Measurable fun U=>(X.dye t G s U).val; rw [show (fun U=>(X.dye t G s U).val)= _ from funext fun U=> (rewriteR ..).symm]; exact Finset.measurable_sum _ fun i _=> ((stake (Keys c N) _).measurable).comp (hx i) -- scope syntax
end Tablet
end YM.MassiveQCD.Stitch
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
variable {q:I→Bool}{o:I→Site f}(hw:X.Flora t q o) {M:Fj D E J→Support c} (h:Cove.Count G P M)
variable (t)[Fintype D]
open Further.ShellBirth49.Fusing Collide
local notation "Γ"=> Fj D E J
include h in
omit [Fintype D] in
lemma dots2 (U:Grid f)(ht:X.Flora t q o) {K:Alg Y'}(hh: HasSum (fun i=>light _ (X.pawnU t G U i)) K): HasSum (fun s=>light _ (X.caller t G M U s)) K:=by
  let z i:= parts M i; have he : Injective z :=fun i j he=>by rw [← recombine M i, ←recombine M j,show parts M i=parts M j from he]
  have hi : taxes M=Set.range z:=by
    ext k; constructor
    · intro hv; change _ ∧_ at hv; exact ⟨ _,uncluttered M k hv.1 hv.2⟩
    rintro ⟨i,rfl⟩; exact ⟨Collide.separate M i,fun j hj=>(living M hj).2⟩
  apply (he.hasSum_iff _).1; rotate_left; · intro i hx; unfold caller; rw [hi,if_neg hx,map_zero]
  refine hh.congr_fun (fun i=>?_); change light _ (X.caller t G M U (z i))=_
  unfold caller; rw [hi, if_pos (Set.mem_range_self _)]; apply congr_arg; unfold dyes pawnU
  rw [← hue_product2 X G ht h _ U (Collide.separate M i) (erases M i),show (z i).biUnion id=i from recombine M i]

include h
lemma cashS2 (WS:Grid f)(hp:X.Flora t q o)(hh:X.Staid t WS): Summable (X.caller t G M WS):=by
   have ht:= dots2 X t G h WS hp (grand X t G WS hh); exact Summable.of_norm (show Summable fun i=> ‖light Y' (X.caller t G M WS i)‖ from ht.summable.norm) -- fintype D implicit?

end Tablet
end YM.MassiveQCD.Stitch
/-! # Joint graded rolls on the front.

 Actual new spin read at every marker monomial, remaining Gaussian. Push
 integral operates only on ACTUAL Keys, not in storage alphabet.
-/
namespace YM.MassiveQCD.Stitch
open QCD QCD.Grass QCD.Lat QCD.Creek Lattice Wilson RG QCD.Cove QCD.Cove.Send QCD.Creek.Ledge
open Function Ribbon Finset Filter MeasureTheory NormedSpace Fj QCD.Kit
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
variable {q:I→Bool}{o:I→Site f}(hw:X.Flora t q o) {M:Fj D E J→Support c} (h:Cove.Count G P M)
variable (t)[Fintype D]
include hw h
lemma grain_h (Q:Grid f→Matrix B A ℂ) (D₀:Grid f→Matrix A A ℂ) (W:Grid f)(hv:G.Cast Q (fun U=> D₀ U+(Q U)ᴴ*Q U)) (he:IsUnit (D₀ W+(Q W)ᴴ*Q W).det) (hs:X.Staid t W) (s:Finset S):
    let H:=D₀ W+(Q W)ᴴ*Q W; let q:= X.caller t G M W; sheath 1 (Q W) (gauss (D₀ W) * scrape (Keys f N) s (light _ (X.bluff t W)))= H.det • (scrape (Keys c N) s (light Y' (∑' i,q i))*gauss (1-Q W*H⁻¹*(Q W)ᴴ)):=by
      have hg:= dots2 X t G h W hw (grand X t G W hs); have hM:= (cashS2 X t G h W hw hs).hasSum.map (light _) (lightC _); intro H q; rw [G.drum _ _ hv _ _ he, ← hg.unique (show HasSum (fun i=> light _ (q i)) _ from hM),wing]; rfl
end Tablet
end YM.MassiveQCD.Stitch
#print axioms YM.MassiveQCD.Stitch.Tablet.grain_h
